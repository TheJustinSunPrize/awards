import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step16149 (p61 p62 : Prop)
    (h262 : p62)
    (h260 : (¬ p61) ∨ (¬ p62)) : (¬ p61) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p61 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p62 := by
    exact h262
  rcases h260 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16150 (p40 p61 : Prop)
    (h16149 : (¬ p61))
    (h258 : (¬ p40) ∨ p61) : (¬ p40) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p40 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p61) := by
    exact h16149
  rcases h258 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16151 (p65 p66 : Prop)
    (h268 : p66)
    (h266 : (¬ p65) ∨ (¬ p66)) : (¬ p65) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p65 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p66 := by
    exact h268
  rcases h266 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16152 (p7 p65 : Prop)
    (h16151 : (¬ p65))
    (h264 : (¬ p7) ∨ p65) : (¬ p7) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p7 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p65) := by
    exact h16151
  rcases h264 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16153 (p130 p131 : Prop)
    (h652 : p131)
    (h650 : (¬ p130) ∨ (¬ p131)) : (¬ p130) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p130 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p131 := by
    exact h652
  rcases h650 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16154 (p129 p130 : Prop)
    (h16153 : (¬ p130))
    (h648 : (¬ p129) ∨ p130) : (¬ p129) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p129 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p130) := by
    exact h16153
  rcases h648 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16155 (p7 p18 p49 p71 p85 p127 : Prop)
    (h16152 : (¬ p7))
    (h654 : p7 ∨ (¬ p18) ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p127)) : (¬ p18) ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p127) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h654 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16156 (p154 p155 : Prop)
    (h785 : p155)
    (h783 : (¬ p154) ∨ (¬ p155)) : (¬ p154) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p154 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p155 := by
    exact h785
  rcases h783 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16157 (p133 p154 : Prop)
    (h16156 : (¬ p154))
    (h781 : (¬ p133) ∨ p154) : (¬ p133) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p133 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p154) := by
    exact h16156
  rcases h781 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16158 (p7 p41 p156 p157 p158 p159 p160 p161 : Prop)
    (h16152 : (¬ p7))
    (h787 : p7 ∨ (¬ p41) ∨ (¬ p156) ∨ (¬ p157) ∨ (¬ p158) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161)) : (¬ p41) ∨ (¬ p156) ∨ (¬ p157) ∨ (¬ p158) ∨ (¬ p159) ∨ (¬ p160) ∨ (¬ p161) := by
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
  have u2 : p157 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p158 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16159 (p183 p184 : Prop)
    (h919 : p184)
    (h917 : (¬ p183) ∨ (¬ p184)) : (¬ p183) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p183 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p184 := by
    exact h919
  rcases h917 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16160 (p162 p183 : Prop)
    (h16159 : (¬ p183))
    (h915 : (¬ p162) ∨ p183) : (¬ p162) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p162 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p183) := by
    exact h16159
  rcases h915 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16161 (p7 p127 p134 p156 p185 p186 : Prop)
    (h16152 : (¬ p7))
    (h920 : p7 ∨ (¬ p127) ∨ (¬ p134) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p186)) : (¬ p127) ∨ (¬ p134) ∨ (¬ p156) ∨ (¬ p185) ∨ (¬ p186) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p134 := by
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
  have u4 : p186 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h920 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16162 (p3 p6 p7 p46 p142 p229 : Prop)
    (h16152 : (¬ p7))
    (h1172 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p229)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p46) ∨ (¬ p142) ∨ (¬ p229) := by
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
  have u2 : p46 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h1172 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16163 (p41 p46 p128 p230 : Prop)
    (h653 : p128)
    (h1173 : (¬ p41) ∨ p46 ∨ (¬ p128) ∨ p230) : (¬ p41) ∨ p46 ∨ p230 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p46) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p230) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p128 := by
    exact h653
  rcases h1173 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u2 q3)

theorem step16164 (p231 p232 : Prop)
    (h1178 : p232)
    (h1176 : (¬ p231) ∨ (¬ p232)) : (¬ p231) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p231 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p232 := by
    exact h1178
  rcases h1176 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16165 (p230 p231 : Prop)
    (h16164 : (¬ p231))
    (h1174 : (¬ p230) ∨ p231) : (¬ p230) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p230 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p231) := by
    exact h16164
  rcases h1174 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16166 (p129 p132 p139 p142 : Prop)
    (h16154 : (¬ p129))
    (h786 : p132)
    (h1305 : p129 ∨ (¬ p132) ∨ p139 ∨ (¬ p142)) : p139 ∨ (¬ p142) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p139) := fun hu => hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p129) := by
    exact h16154
  have u3 : p132 := by
    exact h786
  rcases h1305 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u1)

theorem step16167 (p7 p102 p139 p185 p255 p256 : Prop)
    (h16152 : (¬ p7))
    (h1306 : p7 ∨ (¬ p102) ∨ (¬ p139) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256)) : (¬ p102) ∨ (¬ p139) ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p139 := by
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
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h1306 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16168 (p7 p17 p42 p102 p193 p257 p258 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h1307 : p7 ∨ (¬ p17) ∨ (¬ p42) ∨ (¬ p102) ∨ (¬ p193) ∨ p257 ∨ (¬ p258)) : (¬ p17) ∨ (¬ p102) ∨ (¬ p193) ∨ p257 ∨ (¬ p258) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p257) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  rcases h1307 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u3 q5)
  · exact False.elim (q6 u4)

theorem step16169 (p259 p260 : Prop)
    (h1312 : p260)
    (h1310 : (¬ p259) ∨ (¬ p260)) : (¬ p259) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p259 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p260 := by
    exact h1312
  rcases h1310 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16170 (p257 p259 : Prop)
    (h16169 : (¬ p259))
    (h1308 : (¬ p257) ∨ p259) : (¬ p257) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p257 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p259) := by
    exact h16169
  rcases h1308 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16171 (p7 p10 p102 p136 p189 p258 p279 p280 : Prop)
    (h16152 : (¬ p7))
    (h1438 : p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p189) ∨ (¬ p258) ∨ (¬ p279) ∨ p280) : (¬ p10) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p189) ∨ (¬ p258) ∨ (¬ p279) ∨ p280 := by
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
  have u2 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p279 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : (¬ p280) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h1438 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u6 q7)

theorem step16172 (p281 p282 : Prop)
    (h1443 : p282)
    (h1441 : (¬ p281) ∨ (¬ p282)) : (¬ p281) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p281 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p282 := by
    exact h1443
  rcases h1441 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16173 (p280 p281 : Prop)
    (h16172 : (¬ p281))
    (h1439 : (¬ p280) ∨ p281) : (¬ p280) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p280 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p281) := by
    exact h16172
  rcases h1439 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16174 (p7 p17 p42 p193 p301 p302 p303 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h1571 : p7 ∨ (¬ p17) ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p301) ∨ p302 ∨ (¬ p303)) : (¬ p17) ∨ (¬ p193) ∨ (¬ p301) ∨ p302 ∨ (¬ p303) := by
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
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p302) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p42 := by
    exact h132
  rcases h1571 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u3 q5)
  · exact False.elim (q6 u4)

theorem step16175 (p280 p342 p343 p344 : Prop)
    (h16173 : (¬ p280))
    (h1824 : p280 ∨ p342 ∨ (¬ p343) ∨ (¬ p344)) : p342 ∨ (¬ p343) ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p342) := fun hu => hn (Or.inl hu)
  have u1 : p343 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : (¬ p280) := by
    exact h16173
  rcases h1824 with q0 | q1 | q2 | q3
  · exact False.elim (u3 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)

theorem step16176 (p7 p303 p304 p350 p368 p406 : Prop)
    (h16152 : (¬ p7))
    (h2331 : p7 ∨ (¬ p303) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p368) ∨ (¬ p406)) : (¬ p303) ∨ (¬ p304) ∨ (¬ p350) ∨ (¬ p368) ∨ (¬ p406) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p350 := by
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
  rcases h2331 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16177 (p428 p429 : Prop)
    (h2339 : p429)
    (h2337 : (¬ p428) ∨ (¬ p429)) : (¬ p428) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p428 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p429 := by
    exact h2339
  rcases h2337 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16178 (p426 p428 : Prop)
    (h16177 : (¬ p428))
    (h2335 : (¬ p426) ∨ p428) : (¬ p426) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p426 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p428) := by
    exact h16177
  rcases h2335 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16179 (p432 p433 : Prop)
    (h2344 : p433)
    (h2342 : (¬ p432) ∨ (¬ p433)) : (¬ p432) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p432 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p433 := by
    exact h2344
  rcases h2342 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16180 (p430 p432 : Prop)
    (h16179 : (¬ p432))
    (h2340 : (¬ p430) ∨ p432) : (¬ p430) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p430 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p432) := by
    exact h16179
  rcases h2340 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16181 (p7 p383 p420 p431 p438 p455 : Prop)
    (h16152 : (¬ p7))
    (h2472 : p7 ∨ (¬ p383) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p455)) : (¬ p383) ∨ (¬ p420) ∨ (¬ p431) ∨ (¬ p438) ∨ (¬ p455) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h2472 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16182 (p6 p7 p330 p406 p419 p475 : Prop)
    (h16152 : (¬ p7))
    (h2600 : (¬ p6) ∨ p7 ∨ (¬ p330) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475)) : (¬ p6) ∨ (¬ p330) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h2600 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16183 (p7 p126 p143 p324 p387 p419 : Prop)
    (h16152 : (¬ p7))
    (h2852 : p7 ∨ (¬ p126) ∨ (¬ p143) ∨ (¬ p324) ∨ (¬ p387) ∨ (¬ p419)) : (¬ p126) ∨ (¬ p143) ∨ (¬ p324) ∨ (¬ p387) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h2852 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16184 (p42 p123 p134 p143 : Prop)
    (h132 : p42)
    (h2853 : (¬ p42) ∨ p123 ∨ (¬ p134) ∨ p143) : p123 ∨ (¬ p134) ∨ p143 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p123) := fun hu => hn (Or.inl hu)
  have u1 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p143) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p42 := by
    exact h132
  rcases h2853 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)

theorem step16185 (p512 p513 : Prop)
    (h2858 : p513)
    (h2856 : (¬ p512) ∨ (¬ p513)) : (¬ p512) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p512 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p513 := by
    exact h2858
  rcases h2856 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16186 (p123 p512 : Prop)
    (h16185 : (¬ p512))
    (h2854 : (¬ p123) ∨ p512) : (¬ p123) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p123 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p512) := by
    exact h16185
  rcases h2854 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16187 (p3 p7 p70 p456 p495 p532 p533 p534 : Prop)
    (h16152 : (¬ p7))
    (h2984 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p534) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h2984 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16189 (p7 p301 p495 p583 p595 p596 : Prop)
    (h16152 : (¬ p7))
    (h3364 : p7 ∨ (¬ p301) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p595) ∨ (¬ p596)) : (¬ p301) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p595) ∨ (¬ p596) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h3364 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16190 (p7 p304 p327 p406 p419 p420 p494 p617 p633 : Prop)
    (h16152 : (¬ p7))
    (h3615 : p7 ∨ (¬ p304) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p494) ∨ (¬ p617) ∨ (¬ p633)) : (¬ p304) ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p494) ∨ (¬ p617) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
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
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h3615 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16191 (p7 p346 p406 p419 p495 p542 p617 p636 : Prop)
    (h16152 : (¬ p7))
    (h3741 : p7 ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p495) ∨ (¬ p542) ∨ (¬ p617) ∨ (¬ p636)) : (¬ p346) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p495) ∨ (¬ p542) ∨ (¬ p617) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h3741 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16192 (p233 p542 p544 p653 : Prop)
    (h2345 : p233)
    (h3742 : (¬ p233) ∨ p542 ∨ (¬ p544) ∨ p653) : p542 ∨ (¬ p544) ∨ p653 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p542) := fun hu => hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p653) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p233 := by
    exact h2345
  rcases h3742 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (u2 q3)

theorem step16193 (p654 p655 : Prop)
    (h3747 : p655)
    (h3745 : (¬ p654) ∨ (¬ p655)) : (¬ p654) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p654 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p655 := by
    exact h3747
  rcases h3745 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16194 (p653 p654 : Prop)
    (h16193 : (¬ p654))
    (h3743 : (¬ p653) ∨ p654) : (¬ p653) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p653 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p654) := by
    exact h16193
  rcases h3743 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16195 (p7 p106 p344 p406 p419 p539 p656 : Prop)
    (h16152 : (¬ p7))
    (h3748 : p7 ∨ (¬ p106) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p656)) : (¬ p106) ∨ (¬ p344) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p656) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
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
  have u5 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h3748 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16196 (p102 p106 p164 p257 : Prop)
    (h789 : p164)
    (h16170 : (¬ p257))
    (h3749 : (¬ p102) ∨ p106 ∨ (¬ p164) ∨ p257) : (¬ p102) ∨ p106 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p106) := fun hu => hn (Or.inr hu)
  have u2 : p164 := by
    exact h789
  have u3 : (¬ p257) := by
    exact h16170
  rcases h3749 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step16197 (p7 p8 p106 p306 p419 p539 p657 : Prop)
    (h16152 : (¬ p7))
    (h3750 : p7 ∨ (¬ p8) ∨ (¬ p106) ∨ (¬ p306) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p657)) : (¬ p8) ∨ (¬ p106) ∨ (¬ p306) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p306 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h3750 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16198 (p660 p661 : Prop)
    (h3758 : p661)
    (h3756 : (¬ p660) ∨ (¬ p661)) : (¬ p660) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p660 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p661 := by
    exact h3758
  rcases h3756 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16199 (p658 p660 : Prop)
    (h16198 : (¬ p660))
    (h3754 : (¬ p658) ∨ p660) : (¬ p658) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p658 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p660) := by
    exact h16198
  rcases h3754 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16200 (p7 p224 p225 p406 p563 p680 : Prop)
    (h16152 : (¬ p7))
    (h3884 : p7 ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p406) ∨ (¬ p563) ∨ (¬ p680)) : (¬ p224) ∨ (¬ p225) ∨ (¬ p406) ∨ (¬ p563) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h3884 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16201 (p7 p224 p312 p346 p406 p680 : Prop)
    (h16152 : (¬ p7))
    (h3885 : p7 ∨ (¬ p224) ∨ (¬ p312) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p680)) : (¬ p224) ∨ (¬ p312) ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p680) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h3885 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16202 (p683 p684 : Prop)
    (h3891 : p684)
    (h3889 : (¬ p683) ∨ (¬ p684)) : (¬ p683) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p683 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p684 := by
    exact h3891
  rcases h3889 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16203 (p682 p683 : Prop)
    (h16202 : (¬ p683))
    (h3887 : (¬ p682) ∨ p683) : (¬ p682) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p682 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p683) := by
    exact h16202
  rcases h3887 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16204 (p688 p689 : Prop)
    (h3897 : p689)
    (h3895 : (¬ p688) ∨ (¬ p689)) : (¬ p688) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p688 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p689 := by
    exact h3897
  rcases h3895 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16205 (p686 p688 : Prop)
    (h16204 : (¬ p688))
    (h3893 : (¬ p686) ∨ p688) : (¬ p686) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p686 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p688) := by
    exact h16204
  rcases h3893 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16206 (p7 p306 p406 p419 p543 p680 p726 p727 : Prop)
    (h16152 : (¬ p7))
    (h4150 : p7 ∨ (¬ p306) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p543) ∨ (¬ p680) ∨ (¬ p726) ∨ (¬ p727)) : (¬ p306) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p543) ∨ (¬ p680) ∨ (¬ p726) ∨ (¬ p727) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p306 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p543 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h4150 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16207 (p730 p731 : Prop)
    (h4155 : p731)
    (h4153 : (¬ p730) ∨ (¬ p731)) : (¬ p730) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p730 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p731 := by
    exact h4155
  rcases h4153 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16208 (p729 p730 : Prop)
    (h16207 : (¬ p730))
    (h4151 : (¬ p729) ∨ p730) : (¬ p729) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p729 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p730) := by
    exact h16207
  rcases h4151 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16209 (p7 p224 p343 p406 p680 p686 p756 p769 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16205 : (¬ p686))
    (h4406 : p7 ∨ (¬ p224) ∨ (¬ p343) ∨ (¬ p406) ∨ (¬ p680) ∨ p686 ∨ (¬ p756) ∨ (¬ p769)) : (¬ p224) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p756) ∨ (¬ p769) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p686) := by
    exact h16205
  rcases h4406 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16210 (p7 p129 p189 p324 p419 p788 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h4532 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p324) ∨ (¬ p419) ∨ (¬ p788) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p189) ∨ (¬ p324) ∨ (¬ p419) ∨ (¬ p788) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p788 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p129) := by
    exact h16154
  rcases h4532 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u6 q0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)

theorem step16211 (p7 p86 p327 p419 p420 p495 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h4533 : p7 ∨ (¬ p86) ∨ (¬ p327) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p86) ∨ (¬ p327) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h4533 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16212 (p793 p794 : Prop)
    (h4540 : p794)
    (h4538 : (¬ p793) ∨ (¬ p794)) : (¬ p793) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p793 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p794 := by
    exact h4540
  rcases h4538 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16213 (p791 p793 : Prop)
    (h16212 : (¬ p793))
    (h4536 : (¬ p791) ∨ p793) : (¬ p791) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p791 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p793) := by
    exact h16212
  rcases h4536 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16214 (p7 p195 p406 p419 p475 p796 : Prop)
    (h16152 : (¬ p7))
    (h4542 : p7 ∨ (¬ p195) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p796)) : (¬ p195) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h4542 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16215 (p854 p855 : Prop)
    (h4924 : p855)
    (h4922 : (¬ p854) ∨ (¬ p855)) : (¬ p854) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p854 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p855 := by
    exact h4924
  rcases h4922 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16216 (p853 p854 : Prop)
    (h16215 : (¬ p854))
    (h4920 : (¬ p853) ∨ p854) : (¬ p853) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p853 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p854) := by
    exact h16215
  rcases h4920 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16217 (p3 p7 p70 p167 p327 p420 p424 p495 : Prop)
    (h16152 : (¬ p7))
    (h4925 : (¬ p3) ∨ p7 ∨ (¬ p70) ∨ (¬ p167) ∨ (¬ p327) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p495)) : (¬ p3) ∨ (¬ p70) ∨ (¬ p167) ∨ (¬ p327) ∨ (¬ p420) ∨ (¬ p424) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p70 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h4925 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16218 (p7 p86 p224 p351 p420 p495 p789 p790 : Prop)
    (h16152 : (¬ p7))
    (h4926 : p7 ∨ (¬ p86) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p86) ∨ (¬ p224) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p789) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h4926 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16219 (p877 p878 : Prop)
    (h5059 : p878)
    (h5057 : (¬ p877) ∨ (¬ p878)) : (¬ p877) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p877 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p878 := by
    exact h5059
  rcases h5057 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16220 (p875 p877 : Prop)
    (h16219 : (¬ p877))
    (h5055 : (¬ p875) ∨ p877) : (¬ p875) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p875 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p877) := by
    exact h16219
  rcases h5055 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16221 (p7 p189 p406 p802 p820 p858 : Prop)
    (h16152 : (¬ p7))
    (h5060 : p7 ∨ (¬ p189) ∨ (¬ p406) ∨ (¬ p802) ∨ (¬ p820) ∨ (¬ p858)) : (¬ p189) ∨ (¬ p406) ∨ (¬ p802) ∨ (¬ p820) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p802 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p820 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h5060 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16222 (p42 p105 p108 p193 p791 : Prop)
    (h132 : p42)
    (h16213 : (¬ p791))
    (h5061 : (¬ p42) ∨ p105 ∨ (¬ p108) ∨ (¬ p193) ∨ p791) : p105 ∨ (¬ p108) ∨ (¬ p193) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p105) := fun hu => hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p42 := by
    exact h132
  have u4 : (¬ p791) := by
    exact h16213
  rcases h5061 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u4 q4)

theorem step16223 (p7 p105 p226 p324 p406 p419 p475 : Prop)
    (h16152 : (¬ p7))
    (h5062 : p7 ∨ (¬ p105) ∨ (¬ p226) ∨ (¬ p324) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475)) : (¬ p105) ∨ (¬ p226) ∨ (¬ p324) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p475) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p475 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h5062 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16224 (p15 p70 p128 p133 : Prop)
    (h653 : p128)
    (h16157 : (¬ p133))
    (h5063 : (¬ p15) ∨ p70 ∨ (¬ p128) ∨ p133) : (¬ p15) ∨ p70 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p70) := fun hu => hn (Or.inr hu)
  have u2 : p128 := by
    exact h653
  have u3 : (¬ p133) := by
    exact h16157
  rcases h5063 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step16225 (p7 p86 p163 p193 p351 p420 p495 p544 : Prop)
    (h16152 : (¬ p7))
    (h5064 : p7 ∨ (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p544)) : (¬ p86) ∨ (¬ p163) ∨ (¬ p193) ∨ (¬ p351) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p544) := by
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
  have u3 : p351 := by
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
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h5064 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16226 (p7 p346 p406 p495 p617 p636 p838 p858 : Prop)
    (h16152 : (¬ p7))
    (h5065 : p7 ∨ (¬ p346) ∨ (¬ p406) ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p636) ∨ (¬ p838) ∨ (¬ p858)) : (¬ p346) ∨ (¬ p406) ∨ (¬ p495) ∨ (¬ p617) ∨ (¬ p636) ∨ (¬ p838) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h5065 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16227 (p7 p102 p324 p342 p364 p406 p419 : Prop)
    (h16152 : (¬ p7))
    (h5069 : p7 ∨ (¬ p102) ∨ (¬ p324) ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p419)) : (¬ p102) ∨ (¬ p324) ∨ (¬ p342) ∨ (¬ p364) ∨ (¬ p406) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p324 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h5069 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16228 (p7 p237 p814 p835 p904 p917 : Prop)
    (h16152 : (¬ p7))
    (h5326 : p7 ∨ (¬ p237) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p904) ∨ (¬ p917)) : (¬ p237) ∨ (¬ p814) ∨ (¬ p835) ∨ (¬ p904) ∨ (¬ p917) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p835 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h5326 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16229 (p920 p921 : Prop)
    (h5332 : p921)
    (h5330 : (¬ p920) ∨ (¬ p921)) : (¬ p920) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p920 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p921 := by
    exact h5332
  rcases h5330 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16230 (p919 p920 : Prop)
    (h16229 : (¬ p920))
    (h5328 : (¬ p919) ∨ p920) : (¬ p919) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p919 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p920) := by
    exact h16229
  rcases h5328 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16231 (p7 p135 p170 p256 p351 p515 p537 p544 p814 p940 : Prop)
    (h16152 : (¬ p7))
    (h5459 : p7 ∨ (¬ p135) ∨ (¬ p170) ∨ (¬ p256) ∨ (¬ p351) ∨ (¬ p515) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p814) ∨ (¬ p940)) : (¬ p135) ∨ (¬ p170) ∨ (¬ p256) ∨ (¬ p351) ∨ (¬ p515) ∨ (¬ p537) ∨ (¬ p544) ∨ (¬ p814) ∨ (¬ p940) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p135 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p170 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p515 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p940 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h5459 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16232 (p7 p125 p227 p327 p383 p419 : Prop)
    (h16152 : (¬ p7))
    (h5585 : p7 ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p327) ∨ (¬ p383) ∨ (¬ p419)) : (¬ p125) ∨ (¬ p227) ∨ (¬ p327) ∨ (¬ p383) ∨ (¬ p419) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h5585 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16233 (p7 p327 p406 p419 p420 p455 p494 p617 p961 : Prop)
    (h16152 : (¬ p7))
    (h5711 : p7 ∨ (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p617) ∨ (¬ p961)) : (¬ p327) ∨ (¬ p406) ∨ (¬ p419) ∨ (¬ p420) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p617) ∨ (¬ p961) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p327 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p617 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h5711 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16234 (p7 p140 p189 p256 p326 p796 : Prop)
    (h16152 : (¬ p7))
    (h5963 : p7 ∨ (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p326) ∨ (¬ p796)) : (¬ p140) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p326) ∨ (¬ p796) := by
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
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h5963 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16235 (p7 p125 p264 p438 p519 p1022 : Prop)
    (h16152 : (¬ p7))
    (h6091 : p7 ∨ (¬ p125) ∨ (¬ p264) ∨ (¬ p438) ∨ (¬ p519) ∨ (¬ p1022)) : (¬ p125) ∨ (¬ p264) ∨ (¬ p438) ∨ (¬ p519) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p264 := by
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
  rcases h6091 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16237 (p7 p8 p419 p539 p563 p657 : Prop)
    (h16152 : (¬ p7))
    (h6094 : p7 ∨ (¬ p8) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p563) ∨ (¬ p657)) : (¬ p8) ∨ (¬ p419) ∨ (¬ p539) ∨ (¬ p563) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p539 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p563 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6094 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16238 (p7 p406 p544 p663 p715 p1036 : Prop)
    (h16152 : (¬ p7))
    (h6095 : p7 ∨ (¬ p406) ∨ (¬ p544) ∨ (¬ p663) ∨ (¬ p715) ∨ (¬ p1036)) : (¬ p406) ∨ (¬ p544) ∨ (¬ p663) ∨ (¬ p715) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p715 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6095 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16239 (p7 p12 p105 p127 p556 p1055 : Prop)
    (h16152 : (¬ p7))
    (h6221 : p7 ∨ (¬ p12) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p105) ∨ (¬ p127) ∨ (¬ p556) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p105 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6221 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16240 (p7 p9 p69 p885 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h6348 : p7 ∨ (¬ p9) ∨ (¬ p69) ∨ (¬ p885) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p69) ∨ (¬ p885) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p885 := by
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
  rcases h6348 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16241 (p7 p304 p497 p640 p1076 p1095 : Prop)
    (h16152 : (¬ p7))
    (h6475 : p7 ∨ (¬ p304) ∨ (¬ p497) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095)) : (¬ p304) ∨ (¬ p497) ∨ (¬ p640) ∨ (¬ p1076) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p497 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
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
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6475 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16242 (p7 p40 p69 p1075 p1076 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h6477 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p69) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1075 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  rcases h6477 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)

theorem step16243 (p7 p125 p310 p342 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h6605 : p7 ∨ (¬ p125) ∨ (¬ p310) ∨ (¬ p342) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p125) ∨ (¬ p310) ∨ (¬ p342) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6605 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16244 (p7 p45 p171 p927 p1095 p1115 : Prop)
    (h16152 : (¬ p7))
    (h6606 : p7 ∨ (¬ p45) ∨ (¬ p171) ∨ (¬ p927) ∨ (¬ p1095) ∨ (¬ p1115)) : (¬ p45) ∨ (¬ p171) ∨ (¬ p927) ∨ (¬ p1095) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6606 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16245 (p7 p45 p129 p928 p1075 p1076 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6478 : p1075)
    (h6607 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p928) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p45) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1075 := by
    exact h6478
  rcases h6607 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16247 (p7 p41 p169 p189 p230 p237 p343 p544 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h6735 : p7 ∨ (¬ p41) ∨ (¬ p169) ∨ (¬ p189) ∨ p230 ∨ (¬ p237) ∨ (¬ p343) ∨ (¬ p544)) : (¬ p41) ∨ (¬ p169) ∨ (¬ p189) ∨ (¬ p237) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p169 := by
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
  have u4 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p343 := by
    exact h1950
  rcases h6735 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16248 (p7 p8 p41 p164 p189 p225 p230 p242 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16165 : (¬ p230))
    (h6737 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p164) ∨ (¬ p189) ∨ (¬ p225) ∨ p230 ∨ (¬ p242)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p225) ∨ (¬ p242) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p164 := by
    exact h789
  have u7 : (¬ p230) := by
    exact h16165
  rcases h6737 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u7 q6)
  · exact False.elim (q7 u4)

theorem step16249 (p7 p8 p47 p87 p110 p189 p229 p262 p310 p346 p581 : Prop)
    (h16152 : (¬ p7))
    (h6738 : p7 ∨ (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p110) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p581)) : (¬ p8) ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p110) ∨ (¬ p189) ∨ (¬ p229) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h6738 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16250 (p7 p8 p171 p189 p242 p836 : Prop)
    (h16152 : (¬ p7))
    (h6742 : p7 ∨ (¬ p8) ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p836)) : (¬ p8) ∨ (¬ p171) ∨ (¬ p189) ∨ (¬ p242) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6742 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16252 (p7 p45 p129 p657 p840 p928 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h6744 : p1135)
    (h6745 : p7 ∨ (¬ p45) ∨ p129 ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928) ∨ (¬ p1135)) : (¬ p45) ∨ (¬ p657) ∨ (¬ p840) ∨ (¬ p928) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
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
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1135 := by
    exact h6744
  rcases h6745 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16254 (p7 p8 p123 p158 p576 p657 p928 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h6744 : p1135)
    (h6749 : p7 ∨ (¬ p8) ∨ p123 ∨ (¬ p158) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p928) ∨ (¬ p1135)) : (¬ p8) ∨ (¬ p158) ∨ (¬ p576) ∨ (¬ p657) ∨ (¬ p928) := by
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
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p123) := by
    exact h16186
  have u7 : p1135 := by
    exact h6744
  rcases h6749 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16255 (p7 p8 p41 p189 p230 p266 p310 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h6750 : p7 ∨ (¬ p8) ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p266) ∨ (¬ p310) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p8) ∨ (¬ p41) ∨ (¬ p189) ∨ (¬ p266) ∨ (¬ p310) ∨ (¬ p657) := by
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
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  have u8 : p1135 := by
    exact h6744
  rcases h6750 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step16256 (p7 p124 p230 p262 p344 p581 p657 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h6751 : p7 ∨ (¬ p124) ∨ p230 ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p657) ∨ (¬ p1135)) : (¬ p124) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h6751 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16257 (p63 p87 p279 p1136 : Prop)
    (h1444 : p279)
    (h6752 : (¬ p63) ∨ p87 ∨ (¬ p279) ∨ p1136) : (¬ p63) ∨ p87 ∨ p1136 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1136) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p279 := by
    exact h1444
  rcases h6752 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u2 q3)

theorem step16258 (p1137 p1138 : Prop)
    (h6757 : p1138)
    (h6755 : (¬ p1137) ∨ (¬ p1138)) : (¬ p1137) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1137 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1138 := by
    exact h6757
  rcases h6755 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16259 (p1136 p1137 : Prop)
    (h16258 : (¬ p1137))
    (h6753 : (¬ p1136) ∨ p1137) : (¬ p1136) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1136 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1137) := by
    exact h16258
  rcases h6753 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16260 (p101 p109 p164 p686 : Prop)
    (h789 : p164)
    (h16205 : (¬ p686))
    (h6758 : (¬ p101) ∨ p109 ∨ (¬ p164) ∨ p686) : (¬ p101) ∨ p109 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p109) := fun hu => hn (Or.inr hu)
  have u2 : p164 := by
    exact h789
  have u3 : (¬ p686) := by
    exact h16205
  rcases h6758 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step16261 (p7 p8 p158 p230 p346 p928 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6760 : p7 ∨ (¬ p8) ∨ (¬ p158) ∨ p230 ∨ (¬ p346) ∨ (¬ p928) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p8) ∨ (¬ p158) ∨ (¬ p346) ∨ (¬ p928) ∨ (¬ p1077) ∨ (¬ p1139) := by
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
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p230) := by
    exact h16165
  rcases h6760 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)

theorem step16262 (p101 p110 p653 p788 : Prop)
    (h16194 : (¬ p653))
    (h5066 : p788)
    (h6762 : (¬ p101) ∨ p110 ∨ p653 ∨ (¬ p788)) : (¬ p101) ∨ p110 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p110) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p653) := by
    exact h16194
  have u3 : p788 := by
    exact h5066
  rcases h6762 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step16263 (p7 p110 p226 p1041 p1076 p1140 : Prop)
    (h16152 : (¬ p7))
    (h6763 : p7 ∨ (¬ p110) ∨ (¬ p226) ∨ (¬ p1041) ∨ (¬ p1076) ∨ (¬ p1140)) : (¬ p110) ∨ (¬ p226) ∨ (¬ p1041) ∨ (¬ p1076) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h6763 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16264 (p1161 p1162 : Prop)
    (h6893 : p1162)
    (h6891 : (¬ p1161) ∨ (¬ p1162)) : (¬ p1161) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1161 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1162 := by
    exact h6893
  rcases h6891 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16265 (p1160 p1161 : Prop)
    (h16264 : (¬ p1161))
    (h6889 : (¬ p1160) ∨ p1161) : (¬ p1160) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1160 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1161) := by
    exact h16264
  rcases h6889 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16266 (p7 p19 p48 p87 p134 p189 : Prop)
    (h16152 : (¬ p7))
    (h7019 : p7 ∨ (¬ p19) ∨ (¬ p48) ∨ (¬ p87) ∨ (¬ p134) ∨ (¬ p189)) : (¬ p19) ∨ (¬ p48) ∨ (¬ p87) ∨ (¬ p134) ∨ (¬ p189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p48 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
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
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7019 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16267 (p6 p7 p41 p87 p142 p188 : Prop)
    (h16152 : (¬ p7))
    (h7020 : (¬ p6) ∨ p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p142) ∨ (¬ p188)) : (¬ p6) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p142) ∨ (¬ p188) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7020 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16268 (p7 p41 p127 p187 p230 p323 p387 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h7022 : p7 ∨ (¬ p41) ∨ (¬ p127) ∨ (¬ p187) ∨ p230 ∨ (¬ p323) ∨ (¬ p387) ∨ (¬ p1135)) : (¬ p41) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p323) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h7022 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16269 (p7 p87 p124 p185 p262 p344 p581 p664 p1115 : Prop)
    (h16152 : (¬ p7))
    (h7023 : p7 ∨ (¬ p87) ∨ (¬ p124) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p664) ∨ (¬ p1115)) : (¬ p87) ∨ (¬ p124) ∨ (¬ p185) ∨ (¬ p262) ∨ (¬ p344) ∨ (¬ p581) ∨ (¬ p664) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h7023 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16270 (p657 p664 p1135 p1181 : Prop)
    (h6744 : p1135)
    (h7024 : (¬ p657) ∨ p664 ∨ (¬ p1135) ∨ p1181) : (¬ p657) ∨ p664 ∨ p1181 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1181) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1135 := by
    exact h6744
  rcases h7024 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (u2 q3)

theorem step16271 (p1182 p1183 : Prop)
    (h7029 : p1183)
    (h7027 : (¬ p1182) ∨ (¬ p1183)) : (¬ p1182) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1182 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1183 := by
    exact h7029
  rcases h7027 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16272 (p1181 p1182 : Prop)
    (h16271 : (¬ p1182))
    (h7025 : (¬ p1181) ∨ p1182) : (¬ p1181) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1181 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1182) := by
    exact h16271
  rcases h7025 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16273 (p7 p230 p343 p344 p928 p1076 p1116 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h7030 : p7 ∨ p230 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116)) : (¬ p344) ∨ (¬ p928) ∨ (¬ p1076) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
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
  rcases h7030 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16274 (p7 p41 p102 p127 p187 p230 p343 p344 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h7034 : p7 ∨ (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ p230 ∨ (¬ p343) ∨ (¬ p344)) : (¬ p41) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p344) := by
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
  have u2 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p343 := by
    exact h1950
  rcases h7034 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16275 (p3 p7 p12 p41 p87 p187 p665 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h7036 : (¬ p3) ∨ p7 ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p3) ∨ (¬ p12) ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p187) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) := by
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
  have u2 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p87 := by
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
  rcases h7036 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16277 (p7 p101 p124 p230 p262 p323 p427 p581 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2334 : p427)
    (h7038 : p7 ∨ (¬ p101) ∨ (¬ p124) ∨ p230 ∨ (¬ p262) ∨ (¬ p323) ∨ (¬ p427) ∨ (¬ p581)) : (¬ p101) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p323) ∨ (¬ p581) := by
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
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p427 := by
    exact h2334
  rcases h7038 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16278 (p7 p224 p230 p262 p343 p362 p387 p581 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h7039 : p7 ∨ (¬ p224) ∨ p230 ∨ (¬ p262) ∨ (¬ p343) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581)) : (¬ p224) ∨ (¬ p262) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p262 := by
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
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p343 := by
    exact h1950
  rcases h7039 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16279 (p7 p10 p17 p230 p518 p581 p788 p790 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h5066 : p788)
    (h7040 : p7 ∨ (¬ p10) ∨ (¬ p17) ∨ p230 ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p788) ∨ (¬ p790)) : (¬ p10) ∨ (¬ p17) ∨ (¬ p518) ∨ (¬ p581) ∨ (¬ p790) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p518 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p788 := by
    exact h5066
  rcases h7040 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16280 (p7 p87 p382 p519 p581 p789 p815 : Prop)
    (h16152 : (¬ p7))
    (h7042 : p7 ∨ (¬ p87) ∨ (¬ p382) ∨ (¬ p519) ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p815)) : (¬ p87) ∨ (¬ p382) ∨ (¬ p519) ∨ (¬ p581) ∨ (¬ p789) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p519 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h7042 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16281 (p7 p103 p143 p288 p1036 p1077 : Prop)
    (h16152 : (¬ p7))
    (h7043 : p7 ∨ (¬ p103) ∨ (¬ p143) ∨ (¬ p288) ∨ (¬ p1036) ∨ (¬ p1077)) : (¬ p103) ∨ (¬ p143) ∨ (¬ p288) ∨ (¬ p1036) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7043 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16282 (p7 p87 p124 p262 p581 p665 p814 p858 p1077 : Prop)
    (h16152 : (¬ p7))
    (h7046 : p7 ∨ (¬ p87) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077)) : (¬ p87) ∨ (¬ p124) ∨ (¬ p262) ∨ (¬ p581) ∨ (¬ p665) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p87 := by
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
  have u3 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p665 := by
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
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h7046 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16283 (p7 p10 p18 p69 p302 p303 p1184 : Prop)
    (h16152 : (¬ p7))
    (h7052 : p7 ∨ (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ p302 ∨ (¬ p303) ∨ (¬ p1184)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ p302 ∨ (¬ p303) ∨ (¬ p1184) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
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
  have u3 : (¬ p302) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1184 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h7052 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16284 (p1185 p1186 : Prop)
    (h7058 : p1186)
    (h7056 : (¬ p1185) ∨ (¬ p1186)) : (¬ p1185) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1185 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1186 := by
    exact h7058
  rcases h7056 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16285 (p302 p1185 : Prop)
    (h16284 : (¬ p1185))
    (h7054 : (¬ p302) ∨ p1185) : (¬ p302) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p302 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1185) := by
    exact h16284
  rcases h7054 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16286 (p7 p18 p109 p225 p884 p904 : Prop)
    (h16152 : (¬ p7))
    (h7059 : p7 ∨ (¬ p18) ∨ (¬ p109) ∨ (¬ p225) ∨ (¬ p884) ∨ (¬ p904)) : (¬ p18) ∨ (¬ p109) ∨ (¬ p225) ∨ (¬ p884) ∨ (¬ p904) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p884 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7059 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16287 (p7 p69 p224 p225 p229 p302 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h7060 : p7 ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p229) ∨ p302 ∨ (¬ p1184)) : (¬ p69) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p1184 := by
    exact h7053
  rcases h7060 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step16288 (p7 p47 p87 p189 p224 p545 p789 p839 p928 p1187 : Prop)
    (h16152 : (¬ p7))
    (h7061 : p7 ∨ (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p928) ∨ (¬ p1187)) : (¬ p47) ∨ (¬ p87) ∨ (¬ p189) ∨ (¬ p224) ∨ (¬ p545) ∨ (¬ p789) ∨ (¬ p839) ∨ (¬ p928) ∨ (¬ p1187) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p839 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h7061 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16289 (p7 p8 p87 p158 p545 p814 p858 p928 p996 : Prop)
    (h16152 : (¬ p7))
    (h7062 : p7 ∨ (¬ p8) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p545) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p928) ∨ (¬ p996)) : (¬ p8) ∨ (¬ p87) ∨ (¬ p158) ∨ (¬ p545) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p928) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p545 := by
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
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h7062 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16290 (p7 p41 p189 p230 p346 p790 p833 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h7188 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p346) ∨ (¬ p790) ∨ (¬ p833) ∨ (¬ p1075)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p346) ∨ (¬ p790) ∨ (¬ p833) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p833 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1075 := by
    exact h6478
  rcases h7188 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16292 (p7 p41 p138 p288 p575 p636 : Prop)
    (h16152 : (¬ p7))
    (h7190 : p7 ∨ (¬ p41) ∨ (¬ p138) ∨ (¬ p288) ∨ (¬ p575) ∨ (¬ p636)) : (¬ p41) ∨ (¬ p138) ∨ (¬ p288) ∨ (¬ p575) ∨ (¬ p636) := by
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
  rcases h7190 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16293 (p123 p138 p142 p788 : Prop)
    (h16186 : (¬ p123))
    (h5066 : p788)
    (h7191 : p123 ∨ p138 ∨ (¬ p142) ∨ (¬ p788)) : p138 ∨ (¬ p142) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p138) := fun hu => hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p123) := by
    exact h16186
  have u3 : p788 := by
    exact h5066
  rcases h7191 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step16294 (p7 p8 p101 p143 p262 p310 p346 : Prop)
    (h16152 : (¬ p7))
    (h7193 : p7 ∨ (¬ p8) ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p346)) : (¬ p8) ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p143 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p262 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h7193 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16295 (p4 p7 p8 p10 p102 p642 p1098 : Prop)
    (h16152 : (¬ p7))
    (h7194 : (¬ p4) ∨ p7 ∨ (¬ p8) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p642) ∨ (¬ p1098)) : (¬ p4) ∨ (¬ p8) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p642) ∨ (¬ p1098) := by
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
  have u2 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1098 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h7194 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16296 (p7 p8 p310 p346 p961 p1080 : Prop)
    (h16152 : (¬ p7))
    (h7195 : p7 ∨ (¬ p8) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p961) ∨ (¬ p1080)) : (¬ p8) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p961) ∨ (¬ p1080) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7195 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16297 (p7 p41 p87 p121 p127 p187 p228 p814 p858 : Prop)
    (h16152 : (¬ p7))
    (h7197 : p7 ∨ (¬ p41) ∨ (¬ p87) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858)) : (¬ p41) ∨ (¬ p87) ∨ (¬ p121) ∨ (¬ p127) ∨ (¬ p187) ∨ (¬ p228) ∨ (¬ p814) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p87 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p228 := by
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
  rcases h7197 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16301 (p7 p15 p47 p85 p1249 p1251 : Prop)
    (h16152 : (¬ p7))
    (h7456 : p7 ∨ (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p1249) ∨ (¬ p1251)) : (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p1249) ∨ (¬ p1251) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1251 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7456 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16302 (p7 p41 p137 p330 p424 p576 : Prop)
    (h16152 : (¬ p7))
    (h7707 : p7 ∨ (¬ p41) ∨ (¬ p137) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p576)) : (¬ p41) ∨ (¬ p137) ∨ (¬ p330) ∨ (¬ p424) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p424 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7707 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16303 (p7 p41 p109 p137 p163 p576 : Prop)
    (h16152 : (¬ p7))
    (h7708 : p7 ∨ (¬ p41) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p163) ∨ (¬ p576)) : (¬ p41) ∨ (¬ p109) ∨ (¬ p137) ∨ (¬ p163) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p137 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h7708 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16304 (p7 p303 p420 p495 p875 p996 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16220 : (¬ p875))
    (h7053 : p1184)
    (h7709 : p7 ∨ (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ p875 ∨ (¬ p996) ∨ (¬ p1184)) : (¬ p303) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p996) := by
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
  have u2 : p495 := by
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
  have u6 : p1184 := by
    exact h7053
  rcases h7709 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16306 (p2 p7 p12 p64 p234 p653 p879 p1074 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h7053 : p1184)
    (h7965 : (¬ p2) ∨ p7 ∨ (¬ p12) ∨ (¬ p64) ∨ (¬ p234) ∨ p653 ∨ (¬ p879) ∨ (¬ p1074) ∨ (¬ p1184)) : (¬ p2) ∨ (¬ p12) ∨ (¬ p64) ∨ (¬ p234) ∨ (¬ p879) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p879 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p653) := by
    exact h16194
  have u8 : p1184 := by
    exact h7053
  rcases h7965 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

theorem step16308 (p1326 p1327 : Prop)
    (h7971 : p1327)
    (h7969 : (¬ p1326) ∨ (¬ p1327)) : (¬ p1326) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1326 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1327 := by
    exact h7971
  rcases h7969 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16309 (p1324 p1326 : Prop)
    (h16308 : (¬ p1326))
    (h7967 : (¬ p1324) ∨ p1326) : (¬ p1324) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1324 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1326) := by
    exact h16308
  rcases h7967 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16310 (p7 p302 p980 p1074 p1099 p1184 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h8599 : p7 ∨ p302 ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1184) ∨ (¬ p1333)) : (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1099 := by
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
  have u6 : p1184 := by
    exact h7053
  rcases h8599 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16311 (p7 p12 p161 p653 p983 p1184 p1232 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h7053 : p1184)
    (h8600 : p7 ∨ (¬ p12) ∨ (¬ p161) ∨ p653 ∨ (¬ p983) ∨ (¬ p1184) ∨ (¬ p1232)) : (¬ p12) ∨ (¬ p161) ∨ (¬ p983) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
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
  have u5 : (¬ p653) := by
    exact h16194
  have u6 : p1184 := by
    exact h7053
  rcases h8600 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16312 (p7 p39 p69 p89 p237 p918 : Prop)
    (h16152 : (¬ p7))
    (h8727 : p7 ∨ (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p918)) : (¬ p39) ∨ (¬ p69) ∨ (¬ p89) ∨ (¬ p237) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p69 := by
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
  have u4 : p918 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8727 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16313 (p7 p185 p255 p256 p583 p633 : Prop)
    (h16152 : (¬ p7))
    (h8728 : p7 ∨ (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p583) ∨ (¬ p633)) : (¬ p185) ∨ (¬ p255) ∨ (¬ p256) ∨ (¬ p583) ∨ (¬ p633) := by
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
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8728 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16314 (p7 p101 p143 p262 p310 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h8729 : p7 ∨ (¬ p101) ∨ (¬ p143) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p101) ∨ (¬ p143) ∨ (¬ p262) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p143 := by
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
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h8729 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16316 (p6 p7 p25 p67 p101 p633 : Prop)
    (h16152 : (¬ p7))
    (h8732 : (¬ p6) ∨ p7 ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p101) ∨ (¬ p633)) : (¬ p6) ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p101) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8732 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16317 (p3 p6 p7 p19 p40 p107 p343 p344 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h1950 : p343)
    (h8734 : (¬ p3) ∨ (¬ p6) ∨ p7 ∨ (¬ p19) ∨ p40 ∨ (¬ p107) ∨ (¬ p343) ∨ (¬ p344)) : (¬ p3) ∨ (¬ p6) ∨ (¬ p19) ∨ (¬ p107) ∨ (¬ p344) := by
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
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p107 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p40) := by
    exact h16150
  have u7 : p343 := by
    exact h1950
  rcases h8734 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16318 (p7 p642 p1076 p1099 p1229 p1310 : Prop)
    (h16152 : (¬ p7))
    (h8735 : p7 ∨ (¬ p642) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p642) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1229) ∨ (¬ p1310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8735 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16319 (p7 p237 p917 p1095 p1118 p1349 : Prop)
    (h16152 : (¬ p7))
    (h8744 : p7 ∨ (¬ p237) ∨ (¬ p917) ∨ (¬ p1095) ∨ (¬ p1118) ∨ (¬ p1349)) : (¬ p237) ∨ (¬ p917) ∨ (¬ p1095) ∨ (¬ p1118) ∨ (¬ p1349) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
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
  rcases h8744 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16320 (p7 p45 p85 p167 p362 p387 p496 p653 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16194 : (¬ p653))
    (h8348 : p1386)
    (h8746 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p167) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ p653 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p167) ∨ (¬ p362) ∨ (¬ p387) ∨ (¬ p496) ∨ (¬ p1333) := by
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
  have u2 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p496 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  have u8 : (¬ p653) := by
    exact h16194
  have u9 : p1386 := by
    exact h8348
  rcases h8746 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u8 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u9)

theorem step16321 (p7 p85 p86 p1249 p1346 : Prop)
    (h16152 : (¬ p7))
    (h8747 : p7 ∨ (¬ p85) ∨ (¬ p86) ∨ (¬ p1249) ∨ (¬ p1346)) : (¬ p85) ∨ (¬ p86) ∨ (¬ p1249) ∨ (¬ p1346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p86 := by
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
  rcases h8747 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step16322 (p7 p15 p17 p49 p83 p581 : Prop)
    (h16152 : (¬ p7))
    (h8748 : p7 ∨ (¬ p15) ∨ (¬ p17) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p581)) : (¬ p15) ∨ (¬ p17) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p581) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8748 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16323 (p7 p15 p47 p85 p138 p576 : Prop)
    (h16152 : (¬ p7))
    (h8749 : p7 ∨ (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p138) ∨ (¬ p576)) : (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p138) ∨ (¬ p576) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p138 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8749 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16324 (p7 p45 p85 p86 p193 : Prop)
    (h16152 : (¬ p7))
    (h8750 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p86) ∨ (¬ p193)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p86) ∨ (¬ p193) := by
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
  have u2 : p86 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  rcases h8750 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step16325 (p6 p7 p101 p192 p799 p814 p1076 p1120 p1346 : Prop)
    (h16152 : (¬ p7))
    (h8751 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1076) ∨ (¬ p1120) ∨ (¬ p1346)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p192) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1076) ∨ (¬ p1120) ∨ (¬ p1346) := by
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
  have u2 : p192 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h8751 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16326 (p7 p15 p19 p105 p880 p1099 : Prop)
    (h16152 : (¬ p7))
    (h8752 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p880) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p105) ∨ (¬ p880) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p105 := by
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
  rcases h8752 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16327 (p7 p15 p19 p85 p102 p230 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h8754 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p102) ∨ p230 ∨ (¬ p1075)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1075 := by
    exact h6478
  rcases h8754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step16329 (p7 p15 p49 p83 p185 p928 : Prop)
    (h16152 : (¬ p7))
    (h8760 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p928)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p185) ∨ (¬ p928) := by
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
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p185 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8760 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16330 (p7 p121 p139 p458 p499 p579 p1232 : Prop)
    (h16152 : (¬ p7))
    (h8761 : p7 ∨ (¬ p121) ∨ (¬ p139) ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p1232)) : (¬ p121) ∨ (¬ p139) ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p579) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p579 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h8761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16331 (p7 p12 p15 p128 p653 p1074 p1099 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16194 : (¬ p653))
    (h8769 : p7 ∨ (¬ p12) ∨ (¬ p15) ∨ (¬ p128) ∨ p653 ∨ (¬ p1074) ∨ (¬ p1099)) : (¬ p12) ∨ (¬ p15) ∨ (¬ p1074) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
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
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p653) := by
    exact h16194
  rcases h8769 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16332 (p7 p15 p21 p101 p128 p495 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16272 : (¬ p1181))
    (h8770 : p7 ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p128) ∨ (¬ p495) ∨ (¬ p1076) ∨ p1181) : (¬ p15) ∨ (¬ p21) ∨ (¬ p101) ∨ (¬ p495) ∨ (¬ p1076) := by
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
  have u2 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p1181) := by
    exact h16272
  rcases h8770 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step16333 (p7 p102 p344 p664 p1079 p1206 : Prop)
    (h16152 : (¬ p7))
    (h8771 : p7 ∨ (¬ p102) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1079) ∨ (¬ p1206)) : (¬ p102) ∨ (¬ p344) ∨ (¬ p664) ∨ (¬ p1079) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
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
  have u3 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8771 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16334 (p7 p8 p108 p346 p557 p1080 p1206 : Prop)
    (h16152 : (¬ p7))
    (h8772 : p7 ∨ (¬ p8) ∨ (¬ p108) ∨ (¬ p346) ∨ (¬ p557) ∨ (¬ p1080) ∨ (¬ p1206)) : (¬ p8) ∨ (¬ p108) ∨ (¬ p346) ∨ (¬ p557) ∨ (¬ p1080) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h8772 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16335 (p7 p15 p128 p224 p225 p302 p880 p1099 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h8774 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p224) ∨ (¬ p225) ∨ p302 ∨ (¬ p880) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p880) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
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
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p302) := by
    exact h16285
  rcases h8774 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16337 (p7 p544 p897 p1036 p1099 p1181 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16272 : (¬ p1181))
    (h7053 : p1184)
    (h8776 : p7 ∨ (¬ p544) ∨ (¬ p897) ∨ (¬ p1036) ∨ (¬ p1099) ∨ p1181 ∨ (¬ p1184)) : (¬ p544) ∨ (¬ p897) ∨ (¬ p1036) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p1181) := by
    exact h16272
  have u6 : p1184 := by
    exact h7053
  rcases h8776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step16338 (p7 p63 p426 p657 p792 p898 p1099 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h4535 : p792)
    (h8777 : p7 ∨ (¬ p63) ∨ p426 ∨ (¬ p657) ∨ (¬ p792) ∨ (¬ p898) ∨ (¬ p1099) ∨ (¬ p1287)) : (¬ p63) ∨ (¬ p657) ∨ (¬ p898) ∨ (¬ p1099) ∨ (¬ p1287) := by
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
  have u2 : p898 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p792 := by
    exact h4535
  rcases h8777 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16339 (p7 p15 p128 p980 p1074 p1099 p1324 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16309 : (¬ p1324))
    (h8779 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) ∨ p1324) : (¬ p15) ∨ (¬ p980) ∨ (¬ p1074) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
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
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h8779 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16341 (p6 p7 p532 p659 p983 p1181 p1206 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16272 : (¬ p1181))
    (h8782 : (¬ p6) ∨ p7 ∨ (¬ p532) ∨ (¬ p659) ∨ (¬ p983) ∨ p1181 ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p532) ∨ (¬ p983) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h8782 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step16342 (p7 p102 p1080 p1207 p1452 p1465 : Prop)
    (h16152 : (¬ p7))
    (h8908 : p7 ∨ (¬ p102) ∨ (¬ p1080) ∨ (¬ p1207) ∨ (¬ p1452) ∨ (¬ p1465)) : (¬ p102) ∨ (¬ p1080) ∨ (¬ p1207) ∨ (¬ p1452) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h8908 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16343 (p7 p15 p128 p161 p1035 p1232 p1484 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h9034 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p161) ∨ (¬ p1035) ∨ (¬ p1232) ∨ p1484) : (¬ p15) ∨ (¬ p161) ∨ (¬ p1035) ∨ (¬ p1232) ∨ p1484 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1484) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  rcases h9034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u4 q6)

theorem step16344 (p1485 p1486 : Prop)
    (h9039 : p1486)
    (h9037 : (¬ p1485) ∨ (¬ p1486)) : (¬ p1485) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1485 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1486 := by
    exact h9039
  rcases h9037 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16345 (p1484 p1485 : Prop)
    (h16344 : (¬ p1485))
    (h9035 : (¬ p1484) ∨ p1485) : (¬ p1484) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1484 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1485) := by
    exact h16344
  rcases h9035 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16346 (p224 p343 p669 p1181 : Prop)
    (h1950 : p343)
    (h16272 : (¬ p1181))
    (h9040 : (¬ p224) ∨ (¬ p343) ∨ p669 ∨ p1181) : (¬ p224) ∨ p669 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p669) := fun hu => hn (Or.inr hu)
  have u2 : p343 := by
    exact h1950
  have u3 : (¬ p1181) := by
    exact h16272
  rcases h9040 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)

theorem step16348 (p729 p980 p985 p1139 : Prop)
    (h16208 : (¬ p729))
    (h6761 : p1139)
    (h9042 : p729 ∨ (¬ p980) ∨ p985 ∨ (¬ p1139)) : (¬ p980) ∨ p985 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p985) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p729) := by
    exact h16208
  have u3 : p1139 := by
    exact h6761
  rcases h9042 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)

theorem step16349 (p1487 p1488 : Prop)
    (h9047 : p1488)
    (h9045 : (¬ p1487) ∨ (¬ p1488)) : (¬ p1487) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1487 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1488 := by
    exact h9047
  rcases h9045 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16350 (p1445 p1487 : Prop)
    (h16349 : (¬ p1487))
    (h9043 : (¬ p1445) ∨ p1487) : (¬ p1445) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1445 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1487) := by
    exact h16349
  rcases h9043 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16351 (p6 p7 p38 p49 p85 p499 p633 p1080 p1206 : Prop)
    (h16152 : (¬ p7))
    (h9052 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1080) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1080) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u4 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h9052 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16352 (p7 p15 p49 p1225 p1226 p1227 p1230 : Prop)
    (h16152 : (¬ p7))
    (h9304 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p1225) ∨ (¬ p1226) ∨ (¬ p1227) ∨ (¬ p1230)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p1225) ∨ (¬ p1226) ∨ (¬ p1227) ∨ (¬ p1230) := by
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
  have u2 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1230 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9304 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16353 (p7 p15 p49 p455 p494 p580 p961 : Prop)
    (h16152 : (¬ p7))
    (h9306 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p961)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p455) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p961) := by
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
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9306 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16355 (p7 p108 p309 p544 p710 p1080 p1206 : Prop)
    (h16152 : (¬ p7))
    (h9308 : p7 ∨ (¬ p108) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1080) ∨ (¬ p1206)) : (¬ p108) ∨ (¬ p309) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1080) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9308 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16356 (p7 p102 p209 p305 p344 p710 : Prop)
    (h16152 : (¬ p7))
    (h9309 : p7 ∨ (¬ p102) ∨ (¬ p209) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710)) : (¬ p102) ∨ (¬ p209) ∨ (¬ p305) ∨ (¬ p344) ∨ (¬ p710) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9309 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16357 (p85 p1184 p1385 p1387 p1394 p1527 : Prop)
    (h7053 : p1184)
    (h9311 : (¬ p85) ∨ (¬ p1184) ∨ (¬ p1385) ∨ (¬ p1387) ∨ p1394 ∨ p1527) : (¬ p85) ∨ (¬ p1385) ∨ (¬ p1387) ∨ p1394 ∨ p1527 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1394) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1527) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1184 := by
    exact h7053
  rcases h9311 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (u4 q5)

theorem step16358 (p1528 p1529 : Prop)
    (h9316 : p1529)
    (h9314 : (¬ p1528) ∨ (¬ p1529)) : (¬ p1528) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1528 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1529 := by
    exact h9316
  rcases h9314 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16359 (p1527 p1528 : Prop)
    (h16358 : (¬ p1528))
    (h9312 : (¬ p1527) ∨ p1528) : (¬ p1527) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1527 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1528) := by
    exact h16358
  rcases h9312 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16360 (p3 p7 p49 p71 p85 p229 : Prop)
    (h16152 : (¬ p7))
    (h9317 : (¬ p3) ∨ p7 ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p229)) : (¬ p3) ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p3 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p71 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9317 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16361 (p7 p15 p49 p435 p616 p1189 p1273 p1335 p1508 : Prop)
    (h16152 : (¬ p7))
    (h9318 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p435) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1508)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p435) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1273) ∨ (¬ p1335) ∨ (¬ p1508) := by
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
  have u2 : p435 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h9318 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16362 (p7 p15 p42 p85 p230 p234 p796 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16165 : (¬ p230))
    (h9320 : p7 ∨ (¬ p15) ∨ (¬ p42) ∨ (¬ p85) ∨ p230 ∨ (¬ p234) ∨ (¬ p796)) : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p796) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p230) := by
    exact h16165
  rcases h9320 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16363 (p7 p595 p664 p880 p902 p1036 p1099 : Prop)
    (h16152 : (¬ p7))
    (h9321 : p7 ∨ (¬ p595) ∨ (¬ p664) ∨ (¬ p880) ∨ (¬ p902) ∨ (¬ p1036) ∨ (¬ p1099)) : (¬ p595) ∨ (¬ p664) ∨ (¬ p880) ∨ (¬ p902) ∨ (¬ p1036) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9321 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16364 (p7 p127 p224 p225 p226 p302 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h9323 : p7 ∨ (¬ p127) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ p302 ∨ (¬ p788)) : (¬ p127) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p788 := by
    exact h5066
  rcases h9323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step16365 (p7 p85 p164 p230 p1036 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16165 : (¬ p230))
    (h9324 : p7 ∨ (¬ p85) ∨ (¬ p164) ∨ p230 ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p1036) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p230) := by
    exact h16165
  rcases h9324 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16366 (p7 p38 p49 p85 p544 p556 p710 p1036 p1229 p1309 : Prop)
    (h16152 : (¬ p7))
    (h9325 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
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
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h9325 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16368 (p7 p23 p121 p458 p499 p1232 : Prop)
    (h16152 : (¬ p7))
    (h9329 : p7 ∨ (¬ p23) ∨ (¬ p121) ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p1232)) : (¬ p23) ∨ (¬ p121) ∨ (¬ p458) ∨ (¬ p499) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p458 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9329 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16369 (p7 p38 p49 p544 p556 p581 p710 p1036 p1081 p1443 : Prop)
    (h16152 : (¬ p7))
    (h9331 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p581) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1443)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p581) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
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
  have u4 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h9331 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16370 (p6 p7 p101 p224 p302 p346 p659 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h3753 : p659)
    (h9332 : (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p224) ∨ p302 ∨ (¬ p346) ∨ (¬ p659)) : (¬ p6) ∨ (¬ p101) ∨ (¬ p224) ∨ (¬ p346) := by
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
  have u2 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p659 := by
    exact h3753
  rcases h9332 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16371 (p7 p544 p556 p659 p710 p980 p1036 p1324 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16309 : (¬ p1324))
    (h9333 : p7 ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p659) ∨ (¬ p710) ∨ (¬ p980) ∨ (¬ p1036) ∨ p1324) : (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p980) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p659 := by
    exact h3753
  have u7 : (¬ p1324) := by
    exact h16309
  rcases h9333 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step16373 (p7 p38 p49 p544 p556 p710 p1036 p1120 p1225 p1227 p1489 : Prop)
    (h16152 : (¬ p7))
    (h9336 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h9336 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16374 (p7 p544 p663 p728 p1036 p1334 : Prop)
    (h16152 : (¬ p7))
    (h9338 : p7 ∨ (¬ p544) ∨ (¬ p663) ∨ (¬ p728) ∨ (¬ p1036) ∨ (¬ p1334)) : (¬ p544) ∨ (¬ p663) ∨ (¬ p728) ∨ (¬ p1036) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9338 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16375 (p7 p42 p226 p481 p796 p1036 p1181 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16272 : (¬ p1181))
    (h9339 : p7 ∨ (¬ p42) ∨ (¬ p226) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p1036) ∨ p1181) : (¬ p226) ∨ (¬ p481) ∨ (¬ p796) ∨ (¬ p1036) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h9339 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16376 (p1 p7 p664 p734 p1036 p1366 : Prop)
    (h16152 : (¬ p7))
    (h9342 : (¬ p1) ∨ p7 ∨ (¬ p664) ∨ (¬ p734) ∨ (¬ p1036) ∨ (¬ p1366)) : (¬ p1) ∨ (¬ p664) ∨ (¬ p734) ∨ (¬ p1036) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9342 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16377 (p7 p15 p19 p85 p344 p582 p634 p710 p788 p1076 p1102 p1181 : Prop)
    (h16152 : (¬ p7))
    (h5066 : p788)
    (h16272 : (¬ p1181))
    (h9343 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p344) ∨ (¬ p582) ∨ (¬ p634) ∨ (¬ p710) ∨ (¬ p788) ∨ (¬ p1076) ∨ (¬ p1102) ∨ p1181) : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p344) ∨ (¬ p582) ∨ (¬ p634) ∨ (¬ p710) ∨ (¬ p1076) ∨ (¬ p1102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p788 := by
    exact h5066
  have u11 : (¬ p1181) := by
    exact h16272
  rcases h9343 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u10)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u8)
  · exact False.elim (u11 q11)

theorem step16378 (p7 p38 p49 p224 p225 p226 p228 p581 p1443 : Prop)
    (h16152 : (¬ p7))
    (h9347 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p1443)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p228) ∨ (¬ p581) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
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
  have u5 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h9347 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16379 (p7 p11 p227 p243 p266 p288 p544 p710 p1036 p1075 p1181 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16272 : (¬ p1181))
    (h9348 : p7 ∨ (¬ p11) ∨ (¬ p227) ∨ (¬ p243) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1036) ∨ (¬ p1075) ∨ p1181) : (¬ p11) ∨ (¬ p227) ∨ (¬ p243) ∨ (¬ p266) ∨ (¬ p288) ∨ (¬ p544) ∨ (¬ p710) ∨ (¬ p1036) := by
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
  have u2 : p243 := by
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
  have u5 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p1075 := by
    exact h6478
  have u10 : (¬ p1181) := by
    exact h16272
  rcases h9348 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u9)
  · exact False.elim (u10 q10)

theorem step16380 (p7 p21 p495 p639 p1080 p1096 p1206 : Prop)
    (h16152 : (¬ p7))
    (h9349 : p7 ∨ (¬ p21) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1080) ∨ (¬ p1096) ∨ (¬ p1206)) : (¬ p21) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1080) ∨ (¬ p1096) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p21 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9349 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16381 (p7 p15 p121 p128 p257 p456 p495 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16170 : (¬ p257))
    (h9350 : p7 ∨ (¬ p15) ∨ (¬ p121) ∨ (¬ p128) ∨ p257 ∨ (¬ p456) ∨ (¬ p495)) : (¬ p15) ∨ (¬ p121) ∨ (¬ p456) ∨ (¬ p495) := by
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
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p257) := by
    exact h16170
  rcases h9350 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16382 (p7 p11 p194 p224 p225 p226 p227 p266 p288 p302 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h9351 : p7 ∨ (¬ p11) ∨ (¬ p194) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) ∨ p302 ∨ (¬ p1075)) : (¬ p11) ∨ (¬ p194) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p227) ∨ (¬ p266) ∨ (¬ p288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p194 := by
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
  have u5 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p1075 := by
    exact h6478
  rcases h9351 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (u9 q9)
  · exact False.elim (q10 u10)

theorem step16383 (p2 p7 p38 p49 p85 p434 p435 p595 p599 : Prop)
    (h16152 : (¬ p7))
    (h9353 : (¬ p2) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p595) ∨ (¬ p599)) : (¬ p2) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p434) ∨ (¬ p435) ∨ (¬ p595) ∨ (¬ p599) := by
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
  have u4 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p435 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h9353 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16384 (p7 p85 p230 p1225 p1229 p1489 p1491 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h9051 : p1491)
    (h9354 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1489) ∨ (¬ p1491)) : (¬ p85) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1491 := by
    exact h9051
  rcases h9354 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16385 (p7 p38 p49 p85 p224 p225 p226 p302 p499 p633 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h9355 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ p302 ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p1075)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p499) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p1075 := by
    exact h6478
  rcases h9355 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u10)

theorem step16386 (p7 p323 p434 p663 p1079 p1206 p1334 : Prop)
    (h16152 : (¬ p7))
    (h9357 : p7 ∨ (¬ p323) ∨ (¬ p434) ∨ (¬ p663) ∨ (¬ p1079) ∨ (¬ p1206) ∨ (¬ p1334)) : (¬ p323) ∨ (¬ p434) ∨ (¬ p663) ∨ (¬ p1079) ∨ (¬ p1206) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p663 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1079 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9357 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16387 (p7 p102 p160 p206 p304 p1165 p1206 p1489 p1490 : Prop)
    (h16152 : (¬ p7))
    (h9358 : p7 ∨ (¬ p102) ∨ (¬ p160) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p1165) ∨ (¬ p1206) ∨ (¬ p1489) ∨ (¬ p1490)) : (¬ p102) ∨ (¬ p160) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p1165) ∨ (¬ p1206) ∨ (¬ p1489) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1165 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h9358 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16389 (p6 p7 p38 p49 p85 p103 p638 p1036 p1077 p1096 : Prop)
    (h16152 : (¬ p7))
    (h9361 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p103) ∨ (¬ p638) ∨ (¬ p1036) ∨ (¬ p1077) ∨ (¬ p1096)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p103) ∨ (¬ p638) ∨ (¬ p1036) ∨ (¬ p1077) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u4 : p103 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h9361 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16390 (p7 p225 p226 p344 p659 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16272 : (¬ p1181))
    (h9363 : p7 ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p659) ∨ (¬ p1076) ∨ p1181) : (¬ p225) ∨ (¬ p226) ∨ (¬ p344) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h9363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16391 (p7 p20 p128 p224 p302 p420 p438 p728 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h9364 : p7 ∨ (¬ p20) ∨ (¬ p128) ∨ (¬ p224) ∨ p302 ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p728)) : (¬ p20) ∨ (¬ p224) ∨ (¬ p420) ∨ (¬ p438) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
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
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p302) := by
    exact h16285
  rcases h9364 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16392 (p7 p38 p49 p85 p226 p664 p904 p1036 p1096 : Prop)
    (h16152 : (¬ p7))
    (h9366 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1036) ∨ (¬ p1096)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1036) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h9366 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16393 (p7 p8 p9 p85 p897 p929 : Prop)
    (h16152 : (¬ p7))
    (h9369 : p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p85) ∨ (¬ p897) ∨ (¬ p929)) : (¬ p8) ∨ (¬ p9) ∨ (¬ p85) ∨ (¬ p897) ∨ (¬ p929) := by
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
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9369 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16394 (p7 p15 p128 p686 p880 p1036 p1077 p1099 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16205 : (¬ p686))
    (h9370 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ p686 ∨ (¬ p880) ∨ (¬ p1036) ∨ (¬ p1077) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p880) ∨ (¬ p1036) ∨ (¬ p1077) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p880 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p686) := by
    exact h16205
  rcases h9370 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16395 (p7 p664 p904 p1096 p1232 p1307 : Prop)
    (h16152 : (¬ p7))
    (h9371 : p7 ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : (¬ p664) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9371 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16396 (p7 p346 p904 p1075 p1096 p1232 p1532 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h9372 : p7 ∨ (¬ p346) ∨ (¬ p904) ∨ (¬ p1075) ∨ (¬ p1096) ∨ (¬ p1232) ∨ p1532) : (¬ p346) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1232) ∨ p1532 := by
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
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1532) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1075 := by
    exact h6478
  rcases h9372 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u4 q6)

theorem step16397 (p1533 p1534 : Prop)
    (h9377 : p1534)
    (h9375 : (¬ p1533) ∨ (¬ p1534)) : (¬ p1533) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1533 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1534 := by
    exact h9377
  rcases h9375 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16398 (p1532 p1533 : Prop)
    (h16397 : (¬ p1533))
    (h9373 : (¬ p1532) ∨ p1533) : (¬ p1532) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1532 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1533) := by
    exact h16397
  rcases h9373 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16399 (p7 p85 p101 p230 p499 p633 p788 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h5066 : p788)
    (h9383 : p7 ∨ (¬ p85) ∨ (¬ p101) ∨ p230 ∨ (¬ p499) ∨ (¬ p633) ∨ (¬ p788)) : (¬ p85) ∨ (¬ p101) ∨ (¬ p499) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
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
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p788 := by
    exact h5066
  rcases h9383 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16400 (p7 p15 p49 p635 p1076 p1099 p1120 p1225 p1227 p1489 : Prop)
    (h16152 : (¬ p7))
    (h9384 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p635) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p635) ∨ (¬ p1076) ∨ (¬ p1099) ∨ (¬ p1120) ∨ (¬ p1225) ∨ (¬ p1227) ∨ (¬ p1489) := by
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
  have u2 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1120 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h9384 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16401 (p7 p85 p230 p233 p419 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2345 : p233)
    (h9386 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p233) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p233 := by
    exact h2345
  rcases h9386 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16402 (p7 p15 p85 p230 p234 p996 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h9387 : p7 ∨ (¬ p15) ∨ (¬ p85) ∨ p230 ∨ (¬ p234) ∨ (¬ p996) ∨ (¬ p1135)) : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1135 := by
    exact h6744
  rcases h9387 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16404 (p7 p15 p49 p83 p1273 p1349 : Prop)
    (h16152 : (¬ p7))
    (h9390 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p1273) ∨ (¬ p1349)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p83) ∨ (¬ p1273) ∨ (¬ p1349) := by
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
  have u2 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1349 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9390 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16405 (p1535 p1536 : Prop)
    (h9395 : p1536)
    (h9393 : (¬ p1535) ∨ (¬ p1536)) : (¬ p1535) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1535 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1536 := by
    exact h9395
  rcases h9393 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16406 (p1444 p1535 : Prop)
    (h16405 : (¬ p1535))
    (h9391 : (¬ p1444) ∨ p1535) : (¬ p1444) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1444 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1535) := by
    exact h16405
  rcases h9391 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16407 (p7 p258 p268 p310 p1061 p1076 : Prop)
    (h16152 : (¬ p7))
    (h9397 : p7 ∨ (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076)) : (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p1061) ∨ (¬ p1076) := by
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
  have u2 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9397 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16408 (p7 p138 p193 p238 p287 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h9398 : p7 ∨ (¬ p138) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p287) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p138) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p287) ∨ (¬ p1055) ∨ (¬ p1116) := by
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
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9398 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16409 (p7 p14 p15 p42 p85 p167 p230 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16165 : (¬ p230))
    (h9399 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p42) ∨ (¬ p85) ∨ (¬ p167) ∨ p230) : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p167) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p167 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p230) := by
    exact h16165
  rcases h9399 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16410 (p7 p85 p124 p498 p582 p636 : Prop)
    (h16152 : (¬ p7))
    (h9401 : p7 ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p498) ∨ (¬ p582) ∨ (¬ p636)) : (¬ p85) ∨ (¬ p124) ∨ (¬ p498) ∨ (¬ p582) ∨ (¬ p636) := by
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
  have u2 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9401 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16411 (p7 p258 p495 p583 p639 p1096 : Prop)
    (h16152 : (¬ p7))
    (h9402 : p7 ∨ (¬ p258) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p639) ∨ (¬ p1096)) : (¬ p258) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p639) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9402 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16412 (p7 p456 p495 p639 p1080 p1096 : Prop)
    (h16152 : (¬ p7))
    (h9404 : p7 ∨ (¬ p456) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1080) ∨ (¬ p1096)) : (¬ p456) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1080) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1080 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9404 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16413 (p7 p129 p189 p256 p576 p928 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16154 : (¬ p129))
    (h9400 : p1537)
    (h9408 : p7 ∨ p129 ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p928) ∨ (¬ p1537)) : (¬ p189) ∨ (¬ p256) ∨ (¬ p576) ∨ (¬ p928) := by
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
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p129) := by
    exact h16154
  have u6 : p1537 := by
    exact h9400
  rcases h9408 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16414 (p7 p126 p258 p348 p664 p1076 : Prop)
    (h16152 : (¬ p7))
    (h9411 : p7 ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p348) ∨ (¬ p664) ∨ (¬ p1076)) : (¬ p126) ∨ (¬ p258) ∨ (¬ p348) ∨ (¬ p664) ∨ (¬ p1076) := by
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
  have u2 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9411 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16416 (p7 p126 p227 p427 p658 p1452 p1489 p1492 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h16199 : (¬ p658))
    (h9415 : p7 ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p427) ∨ p658 ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492)) : (¬ p126) ∨ (¬ p227) ∨ (¬ p1452) ∨ (¬ p1489) ∨ (¬ p1492) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
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
  have u6 : p427 := by
    exact h2334
  have u7 : (¬ p658) := by
    exact h16199
  rcases h9415 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u6)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16417 (p7 p11 p126 p160 p427 p532 p1539 : Prop)
    (h16152 : (¬ p7))
    (h2334 : p427)
    (h9416 : p7 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p160) ∨ (¬ p427) ∨ (¬ p532) ∨ p1539) : (¬ p11) ∨ (¬ p126) ∨ (¬ p160) ∨ (¬ p532) ∨ p1539 := by
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
  have u2 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1539) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p427 := by
    exact h2334
  rcases h9416 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (u4 q6)

theorem step16418 (p1540 p1541 : Prop)
    (h9421 : p1541)
    (h9419 : (¬ p1540) ∨ (¬ p1541)) : (¬ p1540) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1540 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1541 := by
    exact h9421
  rcases h9419 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16419 (p1539 p1540 : Prop)
    (h16418 : (¬ p1540))
    (h9417 : (¬ p1539) ∨ p1540) : (¬ p1539) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1539 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1540) := by
    exact h16418
  rcases h9417 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16421 (p7 p124 p126 p258 p434 p658 p685 : Prop)
    (h16152 : (¬ p7))
    (h16199 : (¬ p658))
    (h3898 : p685)
    (h9423 : p7 ∨ (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p434) ∨ p658 ∨ (¬ p685)) : (¬ p124) ∨ (¬ p126) ∨ (¬ p258) ∨ (¬ p434) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p658) := by
    exact h16199
  have u6 : p685 := by
    exact h3898
  rcases h9423 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step16427 (p7 p49 p71 p85 p481 p1187 : Prop)
    (h16152 : (¬ p7))
    (h9555 : p7 ∨ (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p481) ∨ (¬ p1187)) : (¬ p49) ∨ (¬ p71) ∨ (¬ p85) ∨ (¬ p481) ∨ (¬ p1187) := by
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
  have u3 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1187 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9555 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16429 (p7 p15 p128 p419 p426 p616 p657 p1189 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16178 : (¬ p426))
    (h9557 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p419) ∨ p426 ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1189)) : (¬ p15) ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p657) ∨ (¬ p1189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p426) := by
    exact h16178
  rcases h9557 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16430 (p7 p15 p128 p616 p875 p996 p1287 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16220 : (¬ p875))
    (h9558 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p616) ∨ p875 ∨ (¬ p996) ∨ (¬ p1287)) : (¬ p15) ∨ (¬ p616) ∨ (¬ p996) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p875) := by
    exact h16220
  rcases h9558 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16431 (p7 p15 p49 p382 p614 p1286 p1392 : Prop)
    (h16152 : (¬ p7))
    (h9559 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p382) ∨ (¬ p614) ∨ (¬ p1286) ∨ (¬ p1392)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p382) ∨ (¬ p614) ∨ (¬ p1286) ∨ (¬ p1392) := by
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
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p614 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1392 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9559 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16433 (p1564 p1565 : Prop)
    (h9566 : p1565)
    (h9564 : (¬ p1564) ∨ (¬ p1565)) : (¬ p1564) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1564 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : p1565 := by
    exact h9566
  rcases h9564 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)

theorem step16434 (p1563 p1564 : Prop)
    (h16433 : (¬ p1564))
    (h9562 : (¬ p1563) ∨ p1564) : (¬ p1563) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1563 := by
    apply Classical.byContradiction
    intro hu
    exact hn hu
  have u1 : (¬ p1564) := by
    exact h16433
  rcases h9562 with q0 | q1
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)

theorem step16435 (p7 p193 p382 p789 p799 p815 : Prop)
    (h16152 : (¬ p7))
    (h9567 : p7 ∨ (¬ p193) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p799) ∨ (¬ p815)) : (¬ p193) ∨ (¬ p382) ∨ (¬ p789) ∨ (¬ p799) ∨ (¬ p815) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9567 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16437 (p7 p15 p47 p85 p156 p918 : Prop)
    (h16152 : (¬ p7))
    (h9569 : p7 ∨ (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p156) ∨ (¬ p918)) : (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p156) ∨ (¬ p918) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9569 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16438 (p7 p124 p258 p266 p516 p814 : Prop)
    (h16152 : (¬ p7))
    (h9570 : p7 ∨ (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p516) ∨ (¬ p814)) : (¬ p124) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p516) ∨ (¬ p814) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9570 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16439 (p7 p11 p18 p139 p423 p1211 : Prop)
    (h16152 : (¬ p7))
    (h9571 : p7 ∨ (¬ p11) ∨ (¬ p18) ∨ (¬ p139) ∨ (¬ p423) ∨ (¬ p1211)) : (¬ p11) ∨ (¬ p18) ∨ (¬ p139) ∨ (¬ p423) ∨ (¬ p1211) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p139 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1211 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9571 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16440 (p7 p11 p461 p495 p583 p1229 : Prop)
    (h16152 : (¬ p7))
    (h9572 : p7 ∨ (¬ p11) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p1229)) : (¬ p11) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p583) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p583 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9572 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16441 (p7 p8 p258 p268 p310 p346 : Prop)
    (h16152 : (¬ p7))
    (h9573 : p7 ∨ (¬ p8) ∨ (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p346)) : (¬ p8) ∨ (¬ p258) ∨ (¬ p268) ∨ (¬ p310) ∨ (¬ p346) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p268 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9573 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16442 (p7 p8 p310 p346 p501 p636 : Prop)
    (h16152 : (¬ p7))
    (h9574 : p7 ∨ (¬ p8) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p501) ∨ (¬ p636)) : (¬ p8) ∨ (¬ p310) ∨ (¬ p346) ∨ (¬ p501) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p501 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9574 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16443 (p7 p15 p49 p710 p904 p927 p1097 : Prop)
    (h16152 : (¬ p7))
    (h9575 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927) ∨ (¬ p1097)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p710) ∨ (¬ p904) ∨ (¬ p927) ∨ (¬ p1097) := by
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
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9575 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16444 (p7 p15 p49 p927 p1055 p1095 p1097 : Prop)
    (h16152 : (¬ p7))
    (h9576 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p927) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p1097)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p927) ∨ (¬ p1055) ∨ (¬ p1095) ∨ (¬ p1097) := by
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
  have u2 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1097 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9576 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16445 (p7 p85 p230 p1075 p1076 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h9578 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1075 := by
    exact h6478
  rcases h9578 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16446 (p7 p11 p160 p288 p532 p791 p1075 p1353 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6478 : p1075)
    (h9579 : p7 ∨ (¬ p11) ∨ (¬ p160) ∨ (¬ p288) ∨ (¬ p532) ∨ p791 ∨ (¬ p1075) ∨ (¬ p1353)) : (¬ p11) ∨ (¬ p160) ∨ (¬ p288) ∨ (¬ p532) ∨ (¬ p1353) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1075 := by
    exact h6478
  rcases h9579 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16448 (p7 p11 p125 p227 p280 p288 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h6478 : p1075)
    (h9581 : p7 ∨ (¬ p11) ∨ (¬ p125) ∨ (¬ p227) ∨ p280 ∨ (¬ p288) ∨ (¬ p1075)) : (¬ p11) ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p11 := by
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
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p280) := by
    exact h16173
  have u6 : p1075 := by
    exact h6478
  rcases h9581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16449 (p7 p194 p226 p789 p790 p940 p985 p1333 : Prop)
    (h16152 : (¬ p7))
    (h9583 : p7 ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333)) : (¬ p194) ∨ (¬ p226) ∨ (¬ p789) ∨ (¬ p790) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p790 := by
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
  have u6 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h9583 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16451 (p7 p108 p139 p258 p534 p726 : Prop)
    (h16152 : (¬ p7))
    (h9711 : p7 ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p534) ∨ (¬ p726)) : (¬ p108) ∨ (¬ p139) ∨ (¬ p258) ∨ (¬ p534) ∨ (¬ p726) := by
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
  rcases h9711 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16452 (p67 p229 p653 p659 : Prop)
    (h16194 : (¬ p653))
    (h3753 : p659)
    (h9838 : p67 ∨ (¬ p229) ∨ p653 ∨ (¬ p659)) : p67 ∨ (¬ p229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p653) := by
    exact h16194
  have u3 : p659 := by
    exact h3753
  rcases h9838 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step16455 (p7 p15 p22 p288 p301 p362 p421 p426 p897 p1075 p1099 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6478 : p1075)
    (h9844 : p7 ∨ (¬ p15) ∨ (¬ p22) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p421) ∨ p426 ∨ (¬ p897) ∨ (¬ p1075) ∨ (¬ p1099)) : (¬ p15) ∨ (¬ p22) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p421) ∨ (¬ p897) ∨ (¬ p1099) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1075 := by
    exact h6478
  rcases h9844 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (u9 q7)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u10)
  · exact False.elim (q10 u7)

theorem step16456 (p7 p346 p595 p642 p902 p1099 : Prop)
    (h16152 : (¬ p7))
    (h9847 : p7 ∨ (¬ p346) ∨ (¬ p595) ∨ (¬ p642) ∨ (¬ p902) ∨ (¬ p1099)) : (¬ p346) ∨ (¬ p595) ∨ (¬ p642) ∨ (¬ p902) ∨ (¬ p1099) := by
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
  have u2 : p642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h9847 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16457 (p7 p15 p49 p494 p580 p1611 p1624 : Prop)
    (h16152 : (¬ p7))
    (h9974 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p1611) ∨ (¬ p1624)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p1611) ∨ (¬ p1624) := by
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
  have u2 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h9974 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16458 (p7 p363 p382 p387 p443 p1631 : Prop)
    (h16152 : (¬ p7))
    (h10101 : p7 ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p443) ∨ (¬ p1631)) : (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p443) ∨ (¬ p1631) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10101 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16462 (p7 p595 p996 p1191 p1232 p1289 : Prop)
    (h16152 : (¬ p7))
    (h10234 : p7 ∨ (¬ p595) ∨ (¬ p996) ∨ (¬ p1191) ∨ (¬ p1232) ∨ (¬ p1289)) : (¬ p595) ∨ (¬ p996) ∨ (¬ p1191) ∨ (¬ p1232) ∨ (¬ p1289) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1191 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10234 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16464 (p7 p256 p288 p344 p685 p728 p791 : Prop)
    (h16152 : (¬ p7))
    (h3898 : p685)
    (h16213 : (¬ p791))
    (h10236 : p7 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p685) ∨ (¬ p728) ∨ p791) : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p728) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p685 := by
    exact h3898
  have u6 : (¬ p791) := by
    exact h16213
  rcases h10236 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16465 (p7 p664 p840 p983 p1117 p1489 : Prop)
    (h16152 : (¬ p7))
    (h10237 : p7 ∨ (¬ p664) ∨ (¬ p840) ∨ (¬ p983) ∨ (¬ p1117) ∨ (¬ p1489)) : (¬ p664) ∨ (¬ p840) ∨ (¬ p983) ∨ (¬ p1117) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1117 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10237 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16466 (p7 p157 p160 p244 p980 p1115 : Prop)
    (h16152 : (¬ p7))
    (h10238 : p7 ∨ (¬ p157) ∨ (¬ p160) ∨ (¬ p244) ∨ (¬ p980) ∨ (¬ p1115)) : (¬ p157) ∨ (¬ p160) ∨ (¬ p244) ∨ (¬ p980) ∨ (¬ p1115) := by
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
  have u2 : p244 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10238 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16467 (p2 p7 p194 p256 p419 p1325 p1449 p1651 : Prop)
    (h16152 : (¬ p7))
    (h10239 : (¬ p2) ∨ p7 ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1651)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p419) ∨ (¬ p1325) ∨ (¬ p1449) ∨ (¬ p1651) := by
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
  have u2 : p256 := by
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
  have u5 : p1449 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10239 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16469 (p7 p12 p882 p1096 p1232 p1307 : Prop)
    (h16152 : (¬ p7))
    (h10241 : p7 ∨ (¬ p12) ∨ (¬ p882) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307)) : (¬ p12) ∨ (¬ p882) ∨ (¬ p1096) ∨ (¬ p1232) ∨ (¬ p1307) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1307 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10241 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16470 (p7 p616 p738 p899 p1096 p1562 : Prop)
    (h16152 : (¬ p7))
    (h10242 : p7 ∨ (¬ p616) ∨ (¬ p738) ∨ (¬ p899) ∨ (¬ p1096) ∨ (¬ p1562)) : (¬ p616) ∨ (¬ p738) ∨ (¬ p899) ∨ (¬ p1096) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p616 := by
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
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10242 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16471 (p7 p595 p657 p901 p1232 p1289 : Prop)
    (h16152 : (¬ p7))
    (h10243 : p7 ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901) ∨ (¬ p1232) ∨ (¬ p1289)) : (¬ p595) ∨ (¬ p657) ∨ (¬ p901) ∨ (¬ p1232) ∨ (¬ p1289) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10243 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16472 (p7 p342 p420 p495 p639 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10246 : p7 ∨ (¬ p342) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1096)) : (¬ p342) ∨ (¬ p420) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1096) := by
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
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10246 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16473 (p7 p15 p49 p125 p494 p580 p601 : Prop)
    (h16152 : (¬ p7))
    (h10247 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p601)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p125) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p601) := by
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
  have u2 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10247 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16474 (p7 p15 p128 p161 p302 p1232 p1333 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h10249 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p161) ∨ p302 ∨ (¬ p1232) ∨ (¬ p1333)) : (¬ p15) ∨ (¬ p161) ∨ (¬ p1232) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p161 := by
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
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p302) := by
    exact h16285
  rcases h10249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16475 (p7 p346 p382 p666 p712 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10251 : p7 ∨ (¬ p346) ∨ (¬ p382) ∨ (¬ p666) ∨ (¬ p712) ∨ (¬ p1077)) : (¬ p346) ∨ (¬ p382) ∨ (¬ p666) ∨ (¬ p712) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10251 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16476 (p7 p15 p49 p228 p419 p532 p616 p1189 p1225 p1227 : Prop)
    (h16152 : (¬ p7))
    (h10253 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1225) ∨ (¬ p1227)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p228) ∨ (¬ p419) ∨ (¬ p532) ∨ (¬ p616) ∨ (¬ p1189) ∨ (¬ p1225) ∨ (¬ p1227) := by
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
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10253 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16477 (p7 p15 p128 p616 p1287 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16309 : (¬ p1324))
    (h10256 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p616) ∨ (¬ p1287) ∨ p1324 ∨ (¬ p1325)) : (¬ p15) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h10256 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step16478 (p7 p224 p404 p897 p1099 p1233 : Prop)
    (h16152 : (¬ p7))
    (h10257 : p7 ∨ (¬ p224) ∨ (¬ p404) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1233)) : (¬ p224) ∨ (¬ p404) ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1233) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p404 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1233 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10257 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16479 (p1228 p1229 p1233 p1539 : Prop)
    (h7327 : p1228)
    (h16419 : (¬ p1539))
    (h10258 : (¬ p1228) ∨ (¬ p1229) ∨ p1233 ∨ p1539) : (¬ p1229) ∨ p1233 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1233) := fun hu => hn (Or.inr hu)
  have u2 : p1228 := by
    exact h7327
  have u3 : (¬ p1539) := by
    exact h16419
  rcases h10258 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u2)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)
  · exact False.elim (u3 q3)

theorem step16480 (p7 p15 p49 p304 p494 p580 p633 : Prop)
    (h16152 : (¬ p7))
    (h10261 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p304) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p633)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p304) ∨ (¬ p494) ∨ (¬ p580) ∨ (¬ p633) := by
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
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p494 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p580 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10261 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16481 (p7 p15 p102 p128 p257 p495 p636 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16170 : (¬ p257))
    (h10262 : p7 ∨ (¬ p15) ∨ (¬ p102) ∨ (¬ p128) ∨ p257 ∨ (¬ p495) ∨ (¬ p636)) : (¬ p15) ∨ (¬ p102) ∨ (¬ p495) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
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
  have u5 : p128 := by
    exact h653
  have u6 : (¬ p257) := by
    exact h16170
  rcases h10262 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u5)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16482 (p7 p23 p102 p499 p635 p1099 : Prop)
    (h16152 : (¬ p7))
    (h10263 : p7 ∨ (¬ p23) ∨ (¬ p102) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1099)) : (¬ p23) ∨ (¬ p102) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10263 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16484 (p7 p132 p301 p304 p362 p1076 p1181 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16272 : (¬ p1181))
    (h10267 : p7 ∨ (¬ p132) ∨ (¬ p301) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p1076) ∨ p1181) : (¬ p301) ∨ (¬ p304) ∨ (¬ p362) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p301 := by
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
  have u3 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p1181) := by
    exact h16272
  rcases h10267 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16485 (p7 p348 p601 p636 p664 p1076 : Prop)
    (h16152 : (¬ p7))
    (h10268 : p7 ∨ (¬ p348) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p664) ∨ (¬ p1076)) : (¬ p348) ∨ (¬ p601) ∨ (¬ p636) ∨ (¬ p664) ∨ (¬ p1076) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p348 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p636 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10268 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16486 (p7 p85 p362 p420 p498 p582 : Prop)
    (h16152 : (¬ p7))
    (h10271 : p7 ∨ (¬ p85) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p582)) : (¬ p85) ∨ (¬ p362) ∨ (¬ p420) ∨ (¬ p498) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10271 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16487 (p7 p595 p635 p664 p902 p1076 p1099 : Prop)
    (h16152 : (¬ p7))
    (h10272 : p7 ∨ (¬ p595) ∨ (¬ p635) ∨ (¬ p664) ∨ (¬ p902) ∨ (¬ p1076) ∨ (¬ p1099)) : (¬ p595) ∨ (¬ p635) ∨ (¬ p664) ∨ (¬ p902) ∨ (¬ p1076) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10272 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16488 (p6 p7 p38 p49 p85 p101 p350 p499 p601 : Prop)
    (h16152 : (¬ p7))
    (h10274 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p350) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p601 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10274 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16489 (p7 p595 p836 p902 p917 p1099 : Prop)
    (h16152 : (¬ p7))
    (h10275 : p7 ∨ (¬ p595) ∨ (¬ p836) ∨ (¬ p902) ∨ (¬ p917) ∨ (¬ p1099)) : (¬ p595) ∨ (¬ p836) ∨ (¬ p902) ∨ (¬ p917) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10275 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16490 (p7 p387 p595 p599 p1232 p1289 : Prop)
    (h16152 : (¬ p7))
    (h10276 : p7 ∨ (¬ p387) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p1232) ∨ (¬ p1289)) : (¬ p387) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p1232) ∨ (¬ p1289) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10276 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16491 (p6 p7 p10 p194 p237 p303 p665 p1116 : Prop)
    (h16152 : (¬ p7))
    (h10277 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1116)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p303) ∨ (¬ p665) ∨ (¬ p1116) := by
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
  have u2 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10277 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16493 (p7 p13 p125 p237 p267 p323 p1116 p1206 : Prop)
    (h16152 : (¬ p7))
    (h10279 : p7 ∨ (¬ p13) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p267) ∨ (¬ p323) ∨ (¬ p1116) ∨ (¬ p1206)) : (¬ p13) ∨ (¬ p125) ∨ (¬ p237) ∨ (¬ p267) ∨ (¬ p323) ∨ (¬ p1116) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p13 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p267 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10279 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16494 (p7 p11 p126 p227 p304 p350 : Prop)
    (h16152 : (¬ p7))
    (h10280 : p7 ∨ (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p350)) : (¬ p11) ∨ (¬ p126) ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p350) := by
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
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p350 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10280 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16495 (p7 p344 p455 p634 p897 p1084 : Prop)
    (h16152 : (¬ p7))
    (h10281 : p7 ∨ (¬ p344) ∨ (¬ p455) ∨ (¬ p634) ∨ (¬ p897) ∨ (¬ p1084)) : (¬ p344) ∨ (¬ p455) ∨ (¬ p634) ∨ (¬ p897) ∨ (¬ p1084) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10281 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16496 (p7 p102 p256 p791 p1075 p1206 p1443 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6478 : p1075)
    (h10284 : p7 ∨ (¬ p102) ∨ (¬ p256) ∨ p791 ∨ (¬ p1075) ∨ (¬ p1206) ∨ (¬ p1443)) : (¬ p102) ∨ (¬ p256) ∨ (¬ p1206) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1075 := by
    exact h6478
  rcases h10284 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16497 (p7 p85 p304 p425 p582 p595 p669 p1076 p1286 : Prop)
    (h16152 : (¬ p7))
    (h10285 : p7 ∨ (¬ p85) ∨ (¬ p304) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1286)) : (¬ p85) ∨ (¬ p304) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1076) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10285 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16499 (p7 p15 p128 p161 p302 p616 p1288 p1333 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16285 : (¬ p302))
    (h10287 : p7 ∨ (¬ p15) ∨ (¬ p128) ∨ (¬ p161) ∨ p302 ∨ (¬ p616) ∨ (¬ p1288) ∨ (¬ p1333)) : (¬ p15) ∨ (¬ p161) ∨ (¬ p616) ∨ (¬ p1288) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
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
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p302) := by
    exact h16285
  rcases h10287 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16501 (p7 p256 p287 p346 p791 p840 p1077 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h6761 : p1139)
    (h10291 : p7 ∨ (¬ p256) ∨ (¬ p287) ∨ (¬ p346) ∨ p791 ∨ (¬ p840) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p256) ∨ (¬ p287) ∨ (¬ p346) ∨ (¬ p840) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p791) := by
    exact h16213
  have u7 : p1139 := by
    exact h6761
  rcases h10291 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16502 (p6 p7 p38 p49 p88 p237 p983 p1116 p1454 p1666 : Prop)
    (h16152 : (¬ p7))
    (h10293 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ p88 ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1454) ∨ (¬ p1666)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ p88 ∨ (¬ p237) ∨ (¬ p983) ∨ (¬ p1116) ∨ (¬ p1454) ∨ (¬ p1666) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : (¬ p88) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p237 := by
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
  have u7 : p1454 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10293 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u3 q4)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step16503 (p7 p302 p419 p734 p836 p1366 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h9400 : p1537)
    (h10294 : p7 ∨ p302 ∨ (¬ p419) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1366) ∨ (¬ p1537)) : (¬ p419) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p1537 := by
    exact h9400
  rcases h10294 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16504 (p7 p499 p635 p757 p1099 p1611 : Prop)
    (h16152 : (¬ p7))
    (h10295 : p7 ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p757) ∨ (¬ p1099) ∨ (¬ p1611)) : (¬ p499) ∨ (¬ p635) ∨ (¬ p757) ∨ (¬ p1099) ∨ (¬ p1611) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p757 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10295 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16505 (p7 p20 p128 p499 p534 p653 p1099 p1538 : Prop)
    (h16152 : (¬ p7))
    (h653 : p128)
    (h16194 : (¬ p653))
    (h10296 : p7 ∨ (¬ p20) ∨ (¬ p128) ∨ (¬ p499) ∨ (¬ p534) ∨ p653 ∨ (¬ p1099) ∨ (¬ p1538)) : (¬ p20) ∨ (¬ p499) ∨ (¬ p534) ∨ (¬ p1099) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p128 := by
    exact h653
  have u7 : (¬ p653) := by
    exact h16194
  rcases h10296 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u7 q5)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16506 (p6 p7 p38 p49 p532 p533 p537 p928 p1206 : Prop)
    (h16152 : (¬ p7))
    (h10297 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p928) ∨ (¬ p1206)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p533) ∨ (¬ p537) ∨ (¬ p928) ∨ (¬ p1206) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p537 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p928 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10297 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16507 (p7 p386 p517 p858 p1325 p1452 : Prop)
    (h16152 : (¬ p7))
    (h10298 : p7 ∨ (¬ p386) ∨ (¬ p517) ∨ (¬ p858) ∨ (¬ p1325) ∨ (¬ p1452)) : (¬ p386) ∨ (¬ p517) ∨ (¬ p858) ∨ (¬ p1325) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p386 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10298 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16508 (p7 p406 p822 p856 p1333 p1489 : Prop)
    (h16152 : (¬ p7))
    (h10299 : p7 ∨ (¬ p406) ∨ (¬ p822) ∨ (¬ p856) ∨ (¬ p1333) ∨ (¬ p1489)) : (¬ p406) ∨ (¬ p822) ∨ (¬ p856) ∨ (¬ p1333) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p822 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10299 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16513 (p7 p15 p49 p927 p1116 p1232 p1313 p1562 p1584 : Prop)
    (h16152 : (¬ p7))
    (h10555 : p7 ∨ (¬ p15) ∨ (¬ p49) ∨ (¬ p927) ∨ (¬ p1116) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1562) ∨ (¬ p1584)) : (¬ p15) ∨ (¬ p49) ∨ (¬ p927) ∨ (¬ p1116) ∨ (¬ p1232) ∨ (¬ p1313) ∨ (¬ p1562) ∨ (¬ p1584) := by
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
  have u2 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1313 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10555 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16514 (p7 p344 p499 p686 p897 p1099 p1530 : Prop)
    (h16152 : (¬ p7))
    (h16205 : (¬ p686))
    (h9352 : p1530)
    (h10556 : p7 ∨ (¬ p344) ∨ (¬ p499) ∨ p686 ∨ (¬ p897) ∨ (¬ p1099) ∨ (¬ p1530)) : (¬ p344) ∨ (¬ p499) ∨ (¬ p897) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p897 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p686) := by
    exact h16205
  have u6 : p1530 := by
    exact h9352
  rcases h10556 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16515 (p7 p242 p283 p516 p814 p1061 p1115 : Prop)
    (h16152 : (¬ p7))
    (h10557 : p7 ∨ (¬ p242) ∨ (¬ p283) ∨ (¬ p516) ∨ (¬ p814) ∨ (¬ p1061) ∨ (¬ p1115)) : (¬ p242) ∨ (¬ p283) ∨ (¬ p516) ∨ (¬ p814) ∨ (¬ p1061) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p242 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p516 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1061 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10557 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16516 (p7 p8 p244 p657 p834 p858 : Prop)
    (h16152 : (¬ p7))
    (h10558 : p7 ∨ (¬ p8) ∨ (¬ p244) ∨ (¬ p657) ∨ (¬ p834) ∨ (¬ p858)) : (¬ p8) ∨ (¬ p244) ∨ (¬ p657) ∨ (¬ p834) ∨ (¬ p858) := by
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
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p834 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10558 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16517 (p7 p224 p244 p406 p680 p836 : Prop)
    (h16152 : (¬ p7))
    (h10559 : p7 ∨ (¬ p224) ∨ (¬ p244) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p836)) : (¬ p224) ∨ (¬ p244) ∨ (¬ p406) ∨ (¬ p680) ∨ (¬ p836) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p244 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p406 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10559 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16520 (p7 p15 p19 p1142 p1209 p1232 : Prop)
    (h16152 : (¬ p7))
    (h10563 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p1142) ∨ (¬ p1209) ∨ (¬ p1232)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p1142) ∨ (¬ p1209) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10563 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16521 (p7 p85 p164 p225 p230 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16165 : (¬ p230))
    (h10567 : p7 ∨ (¬ p85) ∨ (¬ p164) ∨ (¬ p225) ∨ p230 ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p225) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p230) := by
    exact h16165
  rcases h10567 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (q3 u1)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16522 (p7 p194 p226 p256 p940 p985 p1443 p1452 : Prop)
    (h16152 : (¬ p7))
    (h10568 : p7 ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1443) ∨ (¬ p1452)) : (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1443) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p256 := by
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
  have u5 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10568 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16523 (p7 p160 p303 p370 p405 p1325 : Prop)
    (h16152 : (¬ p7))
    (h10569 : p7 ∨ (¬ p160) ∨ (¬ p303) ∨ (¬ p370) ∨ (¬ p405) ∨ (¬ p1325)) : (¬ p160) ∨ (¬ p303) ∨ (¬ p370) ∨ (¬ p405) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p370 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p405 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10569 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16525 (p7 p102 p304 p532 p681 p1206 p1324 : Prop)
    (h16152 : (¬ p7))
    (h3892 : p681)
    (h16309 : (¬ p1324))
    (h10573 : p7 ∨ (¬ p102) ∨ (¬ p304) ∨ (¬ p532) ∨ (¬ p681) ∨ (¬ p1206) ∨ p1324) : (¬ p102) ∨ (¬ p304) ∨ (¬ p532) ∨ (¬ p1206) := by
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
  have u5 : p681 := by
    exact h3892
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h10573 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16526 (p7 p38 p47 p102 p206 p304 p799 p814 p1206 p1346 p1490 : Prop)
    (h16152 : (¬ p7))
    (h10574 : p7 ∨ (¬ p38) ∨ (¬ p47) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1490)) : (¬ p38) ∨ (¬ p47) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p799) ∨ (¬ p814) ∨ (¬ p1206) ∨ (¬ p1346) ∨ (¬ p1490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h10574 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16527 (p7 p42 p193 p814 p858 p875 p996 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16220 : (¬ p875))
    (h10576 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ (¬ p814) ∨ (¬ p858) ∨ p875 ∨ (¬ p996)) : (¬ p193) ∨ (¬ p814) ∨ (¬ p858) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p814 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p875) := by
    exact h16220
  rcases h10576 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step16529 (p7 p917 p1099 p1115 p1229 p1310 : Prop)
    (h16152 : (¬ p7))
    (h10578 : p7 ∨ (¬ p917) ∨ (¬ p1099) ∨ (¬ p1115) ∨ (¬ p1229) ∨ (¬ p1310)) : (¬ p917) ∨ (¬ p1099) ∨ (¬ p1115) ∨ (¬ p1229) ∨ (¬ p1310) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p917 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1310 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10578 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16530 (p7 p9 p85 p929 p1061 p1074 : Prop)
    (h16152 : (¬ p7))
    (h10579 : p7 ∨ (¬ p9) ∨ (¬ p85) ∨ (¬ p929) ∨ (¬ p1061) ∨ (¬ p1074)) : (¬ p9) ∨ (¬ p85) ∨ (¬ p929) ∨ (¬ p1061) ∨ (¬ p1074) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p929 := by
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
  rcases h10579 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16531 (p7 p10 p85 p230 p499 p601 p788 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h5066 : p788)
    (h10580 : p7 ∨ (¬ p10) ∨ (¬ p85) ∨ p230 ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p788)) : (¬ p10) ∨ (¬ p85) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p788 := by
    exact h5066
  rcases h10580 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16532 (p7 p15 p19 p85 p230 p323 p427 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2334 : p427)
    (h10581 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ p230 ∨ (¬ p323) ∨ (¬ p427)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p323) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p427 := by
    exact h2334
  rcases h10581 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16533 (p7 p19 p38 p224 p225 p226 p302 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h10582 : p7 ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ p302 ∨ (¬ p788)) : (¬ p19) ∨ (¬ p38) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
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
  have u7 : p788 := by
    exact h5066
  rcases h10582 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u6 q6)
  · exact False.elim (q7 u7)

theorem step16534 (p7 p14 p15 p85 p230 p343 p544 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h10584 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ p230 ∨ (¬ p343) ∨ (¬ p544)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p343 := by
    exact h1950
  rcases h10584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16535 (p15 p128 p326 p329 p1136 : Prop)
    (h653 : p128)
    (h16259 : (¬ p1136))
    (h10585 : (¬ p15) ∨ (¬ p128) ∨ p326 ∨ (¬ p329) ∨ p1136) : (¬ p15) ∨ p326 ∨ (¬ p329) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p326) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p329 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr hu))
  have u3 : p128 := by
    exact h653
  have u4 : (¬ p1136) := by
    exact h16259
  rcases h10585 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u4 q4)

theorem step16536 (p7 p15 p19 p326 p616 p1189 : Prop)
    (h16152 : (¬ p7))
    (h10586 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p326) ∨ (¬ p616) ∨ (¬ p1189)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p326) ∨ (¬ p616) ∨ (¬ p1189) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p326 := by
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
  rcases h10586 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16537 (p7 p15 p19 p85 p326 p996 p1287 p1394 : Prop)
    (h16152 : (¬ p7))
    (h10587 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p326) ∨ (¬ p996) ∨ (¬ p1287) ∨ (¬ p1394)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p326) ∨ (¬ p996) ∨ (¬ p1287) ∨ (¬ p1394) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p326 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10587 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16538 (p2 p7 p19 p38 p419 p426 p657 p788 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h5066 : p788)
    (h10588 : (¬ p2) ∨ p7 ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p419) ∨ p426 ∨ (¬ p657) ∨ (¬ p788)) : (¬ p2) ∨ (¬ p19) ∨ (¬ p38) ∨ (¬ p419) ∨ (¬ p657) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p38 := by
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
  have u7 : p788 := by
    exact h5066
  rcases h10588 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16539 (p7 p85 p230 p303 p427 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2334 : p427)
    (h10589 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p303) ∨ (¬ p427) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p85) ∨ (¬ p303) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p427 := by
    exact h2334
  rcases h10589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16540 (p7 p14 p15 p21 p109 p495 : Prop)
    (h16152 : (¬ p7))
    (h10591 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p109) ∨ (¬ p495)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p109) ∨ (¬ p495) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
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
  have u3 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10591 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16542 (p7 p15 p85 p234 p304 p346 p425 p542 p582 : Prop)
    (h16152 : (¬ p7))
    (h10595 : p7 ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p542) ∨ (¬ p582)) : (¬ p15) ∨ (¬ p85) ∨ (¬ p234) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p542) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10595 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16543 (p7 p15 p19 p85 p224 p302 p304 p346 p425 p582 p788 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h5066 : p788)
    (h10596 : p7 ∨ (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p224) ∨ p302 ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p788)) : (¬ p15) ∨ (¬ p19) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p425) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
  have u6 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p302) := by
    exact h16285
  have u10 : p788 := by
    exact h5066
  rcases h10596 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16544 (p6 p7 p38 p49 p85 p101 p1076 p1229 p1309 : Prop)
    (h16152 : (¬ p7))
    (h10597 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p1076) ∨ (¬ p1229) ∨ (¬ p1309)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p1076) ∨ (¬ p1229) ∨ (¬ p1309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u4 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
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
  rcases h10597 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16545 (p7 p85 p230 p387 p499 p601 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h10598 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) ∨ (¬ p1135)) : (¬ p85) ∨ (¬ p387) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p387 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1135 := by
    exact h6744
  rcases h10598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16546 (p7 p85 p230 p455 p499 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h10599 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p85) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1386 := by
    exact h8348
  rcases h10599 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16548 (p7 p85 p122 p230 p532 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16165 : (¬ p230))
    (h10601 : p7 ∨ (¬ p85) ∨ (¬ p122) ∨ p230 ∨ (¬ p532) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p85) ∨ (¬ p532) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p122 := by
    exact h10260
  have u6 : (¬ p230) := by
    exact h16165
  rcases h10601 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16549 (p7 p14 p15 p85 p109 p161 p1035 p1212 p1274 : Prop)
    (h16152 : (¬ p7))
    (h10603 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p109) ∨ (¬ p161) ∨ (¬ p1035) ∨ (¬ p1212) ∨ (¬ p1274)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p109) ∨ (¬ p161) ∨ (¬ p1035) ∨ (¬ p1212) ∨ (¬ p1274) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1212 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10603 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16550 (p7 p15 p85 p423 p1000 p1226 p1235 p1274 p1333 : Prop)
    (h16152 : (¬ p7))
    (h10604 : p7 ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p423) ∨ (¬ p1000) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1274) ∨ (¬ p1333)) : (¬ p15) ∨ (¬ p85) ∨ (¬ p423) ∨ (¬ p1000) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1274) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p423 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1000 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1235 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10604 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16551 (p7 p14 p164 p302 p1141 p1333 p1465 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16285 : (¬ p302))
    (h10605 : p7 ∨ (¬ p14) ∨ (¬ p164) ∨ p302 ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465)) : (¬ p14) ∨ (¬ p1141) ∨ (¬ p1333) ∨ (¬ p1465) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1141 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1465 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p302) := by
    exact h16285
  rcases h10605 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16552 (p7 p85 p122 p224 p455 p499 p710 p929 p1102 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h10260 : p122)
    (h16309 : (¬ p1324))
    (h10607 : p7 ∨ (¬ p85) ∨ (¬ p122) ∨ (¬ p224) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) ∨ p1324 ∨ (¬ p1325)) : (¬ p85) ∨ (¬ p224) ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : p122 := by
    exact h10260
  have u10 : (¬ p1324) := by
    exact h16309
  rcases h10607 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u10 q9)
  · exact False.elim (q10 u7)

theorem step16553 (p2 p3 p7 p164 p419 p426 p657 : Prop)
    (h16152 : (¬ p7))
    (h789 : p164)
    (h16178 : (¬ p426))
    (h10608 : (¬ p2) ∨ (¬ p3) ∨ p7 ∨ (¬ p164) ∨ (¬ p419) ∨ p426 ∨ (¬ p657)) : (¬ p2) ∨ (¬ p3) ∨ (¬ p419) ∨ (¬ p657) := by
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
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p164 := by
    exact h789
  have u6 : (¬ p426) := by
    exact h16178
  rcases h10608 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u4 q2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u2)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step16554 (p7 p14 p15 p85 p106 p929 p1074 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10609 : p7 ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p929) ∨ (¬ p1074) ∨ (¬ p1077)) : (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ (¬ p106) ∨ (¬ p929) ∨ (¬ p1074) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p14 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p106 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10609 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16555 (p7 p12 p14 p15 p85 p230 p1139 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6761 : p1139)
    (h10610 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p85) ∨ p230 ∨ (¬ p1139)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p15) ∨ (¬ p85) := by
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
  have u3 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1139 := by
    exact h6761
  rcases h10610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u5 q5)
  · exact False.elim (q6 u6)

theorem step16556 (p7 p85 p230 p1095 p1096 p1115 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h9400 : p1537)
    (h10611 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1115) ∨ (¬ p1537)) : (¬ p85) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1115 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1537 := by
    exact h9400
  rcases h10611 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16557 (p7 p85 p351 p363 p382 p387 p425 p582 p662 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10612 : p7 ∨ (¬ p85) ∨ (¬ p351) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p662) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p351) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p662) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p351 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p662 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h10612 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16558 (p7 p85 p125 p303 p425 p582 p665 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10613 : p7 ∨ (¬ p85) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p125) ∨ (¬ p303) ∨ (¬ p425) ∨ (¬ p582) ∨ (¬ p665) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p425 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10613 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16561 (p7 p85 p230 p657 p904 p1096 p1135 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h10617 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1135)) : (¬ p85) ∨ (¬ p657) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1135 := by
    exact h6744
  rcases h10617 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16562 (p4 p7 p288 p301 p668 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10618 : (¬ p4) ∨ p7 ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p668) ∨ (¬ p1077)) : (¬ p4) ∨ (¬ p288) ∨ (¬ p301) ∨ (¬ p668) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p4 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10618 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16563 (p7 p224 p616 p906 p1229 p1292 : Prop)
    (h16152 : (¬ p7))
    (h10619 : p7 ∨ (¬ p224) ∨ (¬ p616) ∨ (¬ p906) ∨ (¬ p1229) ∨ (¬ p1292)) : (¬ p224) ∨ (¬ p616) ∨ (¬ p906) ∨ (¬ p1229) ∨ (¬ p1292) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p906 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10619 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16564 (p7 p85 p224 p230 p343 p595 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h10620 : p7 ∨ (¬ p85) ∨ (¬ p224) ∨ p230 ∨ (¬ p343) ∨ (¬ p595) ∨ (¬ p1286)) : (¬ p85) ∨ (¬ p224) ∨ (¬ p595) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p343 := by
    exact h1950
  rcases h10620 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16565 (p7 p85 p406 p620 p1287 p1394 : Prop)
    (h16152 : (¬ p7))
    (h10622 : p7 ∨ (¬ p85) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1394)) : (¬ p85) ∨ (¬ p406) ∨ (¬ p620) ∨ (¬ p1287) ∨ (¬ p1394) := by
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
  have u2 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10622 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16566 (p2 p7 p194 p256 p288 p419 p665 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10624 : (¬ p2) ∨ p7 ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1077)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p419) ∨ (¬ p665) ∨ (¬ p1077) := by
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
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p419 := by
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
  rcases h10624 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16569 (p7 p124 p136 p207 p258 p1213 p1256 : Prop)
    (h16152 : (¬ p7))
    (h10631 : p7 ∨ (¬ p124) ∨ (¬ p136) ∨ (¬ p207) ∨ (¬ p258) ∨ (¬ p1213) ∨ (¬ p1256)) : (¬ p124) ∨ (¬ p136) ∨ (¬ p207) ∨ (¬ p258) ∨ (¬ p1213) ∨ (¬ p1256) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p136 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p207 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10631 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16571 (p6 p7 p38 p49 p343 p532 p840 p927 p1206 p1324 p1562 p1584 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h10633 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p343) ∨ (¬ p532) ∨ (¬ p840) ∨ (¬ p927) ∨ (¬ p1206) ∨ p1324 ∨ (¬ p1562) ∨ (¬ p1584)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p840) ∨ (¬ p927) ∨ (¬ p1206) ∨ (¬ p1562) ∨ (¬ p1584) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p927 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1562 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1584 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : p343 := by
    exact h1950
  have u11 : (¬ p1324) := by
    exact h16309
  rcases h10633 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (q0 u0)
  · exact False.elim (u9 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (u11 q9)
  · exact False.elim (q10 u7)
  · exact False.elim (q11 u8)

theorem step16572 (p7 p595 p727 p902 p1099 p1538 : Prop)
    (h16152 : (¬ p7))
    (h10635 : p7 ∨ (¬ p595) ∨ (¬ p727) ∨ (¬ p902) ∨ (¬ p1099) ∨ (¬ p1538)) : (¬ p595) ∨ (¬ p727) ∨ (¬ p902) ∨ (¬ p1099) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p727 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p902 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10635 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16573 (p7 p85 p918 p980 p1115 p1184 p1324 : Prop)
    (h16152 : (¬ p7))
    (h7053 : p1184)
    (h16309 : (¬ p1324))
    (h10637 : p7 ∨ (¬ p85) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1184) ∨ p1324) : (¬ p85) ∨ (¬ p918) ∨ (¬ p980) ∨ (¬ p1115) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p918 := by
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
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p1184 := by
    exact h7053
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h10637 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step16574 (p7 p387 p599 p1226 p1235 p1288 p1333 : Prop)
    (h16152 : (¬ p7))
    (h10638 : p7 ∨ (¬ p387) ∨ (¬ p599) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1288) ∨ (¬ p1333)) : (¬ p387) ∨ (¬ p599) ∨ (¬ p1226) ∨ (¬ p1235) ∨ (¬ p1288) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1226 := by
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
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10638 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16576 (p7 p85 p230 p980 p1139 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6761 : p1139)
    (h10640 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p980) ∨ (¬ p1139) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p85) ∨ (¬ p980) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1139 := by
    exact h6761
  rcases h10640 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16577 (p7 p10 p121 p366 p382 p383 : Prop)
    (h16152 : (¬ p7))
    (h10641 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p366) ∨ (¬ p382) ∨ (¬ p383)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p366) ∨ (¬ p382) ∨ (¬ p383) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10641 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16578 (p7 p10 p38 p49 p85 p206 p595 p599 p1624 p1665 : Prop)
    (h16152 : (¬ p7))
    (h10642 : p7 ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p206) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p1624) ∨ (¬ p1665)) : (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p206) ∨ (¬ p595) ∨ (¬ p599) ∨ (¬ p1624) ∨ (¬ p1665) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
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
  have u4 : p206 := by
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
  have u7 : p1624 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1665 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10642 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16581 (p2 p7 p194 p256 p288 p343 p344 p419 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16309 : (¬ p1324))
    (h10653 : (¬ p2) ∨ p7 ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p419) ∨ p1324 ∨ (¬ p1325)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p419) ∨ (¬ p1325) := by
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
  have u2 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p419 := by
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
  rcases h10653 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u8)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (u9 q8)
  · exact False.elim (q9 u6)

theorem step16582 (p7 p256 p288 p344 p791 p836 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h9400 : p1537)
    (h10654 : p7 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ p791 ∨ (¬ p836) ∨ (¬ p1537)) : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p836) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1537 := by
    exact h9400
  rcases h10654 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16583 (p7 p256 p288 p344 p656 p821 : Prop)
    (h16152 : (¬ p7))
    (h10656 : p7 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p656) ∨ (¬ p821)) : (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p656) ∨ (¬ p821) := by
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
  have u2 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p656 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p821 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10656 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16584 (p7 p343 p344 p1076 p1095 p1096 p1136 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16259 : (¬ p1136))
    (h10658 : p7 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) ∨ p1136) : (¬ p344) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096) := by
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
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p1136) := by
    exact h16259
  rcases h10658 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16585 (p7 p11 p85 p126 p230 p427 p461 p1229 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h2334 : p427)
    (h10659 : p7 ∨ (¬ p11) ∨ (¬ p85) ∨ (¬ p126) ∨ p230 ∨ (¬ p427) ∨ (¬ p461) ∨ (¬ p1229)) : (¬ p11) ∨ (¬ p85) ∨ (¬ p126) ∨ (¬ p461) ∨ (¬ p1229) := by
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
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p427 := by
    exact h2334
  rcases h10659 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16587 (p7 p11 p126 p302 p427 p964 p1226 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h2334 : p427)
    (h10661 : p7 ∨ (¬ p11) ∨ (¬ p126) ∨ p302 ∨ (¬ p427) ∨ (¬ p964) ∨ (¬ p1226) ∨ (¬ p1333)) : (¬ p11) ∨ (¬ p126) ∨ (¬ p964) ∨ (¬ p1226) ∨ (¬ p1333) := by
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
  have u2 : p964 := by
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
  have u6 : (¬ p302) := by
    exact h16285
  have u7 : p427 := by
    exact h2334
  rcases h10661 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u7)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16588 (p7 p86 p124 p228 p258 p266 p616 p1287 p1443 : Prop)
    (h16152 : (¬ p7))
    (h10662 : p7 ∨ (¬ p86) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1443)) : (¬ p86) ∨ (¬ p124) ∨ (¬ p228) ∨ (¬ p258) ∨ (¬ p266) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p86 := by
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
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10662 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16589 (p7 p286 p343 p344 p980 p1115 p1225 p1532 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16398 : (¬ p1532))
    (h10663 : p7 ∨ (¬ p286) ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1225) ∨ p1532) : (¬ p286) ∨ (¬ p344) ∨ (¬ p980) ∨ (¬ p1115) ∨ (¬ p1225) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p1532) := by
    exact h16398
  rcases h10663 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step16590 (p7 p11 p227 p288 p343 p344 p658 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16199 : (¬ p658))
    (h10664 : p7 ∨ (¬ p11) ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p343) ∨ (¬ p344) ∨ p658) : (¬ p11) ∨ (¬ p227) ∨ (¬ p288) ∨ (¬ p344) := by
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
  have u2 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p343 := by
    exact h1950
  have u6 : (¬ p658) := by
    exact h16199
  rcases h10664 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u3)
  · exact False.elim (u6 q6)

theorem step16593 (p7 p455 p499 p635 p1084 p1099 : Prop)
    (h16152 : (¬ p7))
    (h10668 : p7 ∨ (¬ p455) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1084) ∨ (¬ p1099)) : (¬ p455) ∨ (¬ p499) ∨ (¬ p635) ∨ (¬ p1084) ∨ (¬ p1099) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p455 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p635 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1099 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10668 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16594 (p7 p461 p495 p636 p1084 p1229 : Prop)
    (h16152 : (¬ p7))
    (h10669 : p7 ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1084) ∨ (¬ p1229)) : (¬ p461) ∨ (¬ p495) ∨ (¬ p636) ∨ (¬ p1084) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p461 := by
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
  have u3 : p1084 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10669 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16595 (p4 p7 p8 p312 p420 p633 : Prop)
    (h16152 : (¬ p7))
    (h10671 : (¬ p4) ∨ p7 ∨ (¬ p8) ∨ (¬ p312) ∨ (¬ p420) ∨ (¬ p633)) : (¬ p4) ∨ (¬ p8) ∨ (¬ p312) ∨ (¬ p420) ∨ (¬ p633) := by
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
  have u2 : p312 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10671 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16596 (p7 p125 p227 p383 p517 p858 : Prop)
    (h16152 : (¬ p7))
    (h10673 : p7 ∨ (¬ p125) ∨ (¬ p227) ∨ (¬ p383) ∨ (¬ p517) ∨ (¬ p858)) : (¬ p125) ∨ (¬ p227) ∨ (¬ p383) ∨ (¬ p517) ∨ (¬ p858) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p858 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10673 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16597 (p7 p193 p690 p799 p815 p1022 : Prop)
    (h16152 : (¬ p7))
    (h10675 : p7 ∨ (¬ p193) ∨ (¬ p690) ∨ (¬ p799) ∨ (¬ p815) ∨ (¬ p1022)) : (¬ p193) ∨ (¬ p690) ∨ (¬ p799) ∨ (¬ p815) ∨ (¬ p1022) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p815 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10675 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16598 (p7 p42 p193 p280 p434 p814 p1015 : Prop)
    (h16152 : (¬ p7))
    (h132 : p42)
    (h16173 : (¬ p280))
    (h10676 : p7 ∨ (¬ p42) ∨ (¬ p193) ∨ p280 ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p1015)) : (¬ p193) ∨ (¬ p434) ∨ (¬ p814) ∨ (¬ p1015) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p434 := by
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
  have u5 : p42 := by
    exact h132
  have u6 : (¬ p280) := by
    exact h16173
  rcases h10676 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u5)
  · exact False.elim (q2 u0)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16600 (p7 p126 p265 p331 p384 p961 p996 : Prop)
    (h16152 : (¬ p7))
    (h10680 : p7 ∨ (¬ p126) ∨ (¬ p265) ∨ (¬ p331) ∨ (¬ p384) ∨ (¬ p961) ∨ (¬ p996)) : (¬ p126) ∨ (¬ p265) ∨ (¬ p331) ∨ (¬ p384) ∨ (¬ p961) ∨ (¬ p996) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p384 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10680 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16601 (p7 p430 p616 p789 p1015 p1184 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h7053 : p1184)
    (h10681 : p7 ∨ p430 ∨ (¬ p616) ∨ (¬ p789) ∨ (¬ p1015) ∨ (¬ p1184) ∨ (¬ p1287)) : (¬ p616) ∨ (¬ p789) ∨ (¬ p1015) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p430) := by
    exact h16180
  have u6 : p1184 := by
    exact h7053
  rcases h10681 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16602 (p1 p7 p110 p286 p734 p836 p1366 : Prop)
    (h16152 : (¬ p7))
    (h10682 : (¬ p1) ∨ p7 ∨ (¬ p110) ∨ (¬ p286) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1366)) : (¬ p1) ∨ (¬ p110) ∨ (¬ p286) ∨ (¬ p734) ∨ (¬ p836) ∨ (¬ p1366) := by
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
  have u2 : p286 := by
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
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10682 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16604 (p7 p85 p230 p1135 p1229 p1272 p1325 p1508 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6744 : p1135)
    (h10684 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p1135) ∨ (¬ p1229) ∨ (¬ p1272) ∨ (¬ p1325) ∨ (¬ p1508)) : (¬ p85) ∨ (¬ p1229) ∨ (¬ p1272) ∨ (¬ p1325) ∨ (¬ p1508) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1325 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1508 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1135 := by
    exact h6744
  rcases h10684 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16605 (p1 p7 p108 p139 p301 p438 p1366 : Prop)
    (h16152 : (¬ p7))
    (h10685 : (¬ p1) ∨ p7 ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p1366)) : (¬ p1) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p301) ∨ (¬ p438) ∨ (¬ p1366) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1 := by
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
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10685 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16606 (p2 p7 p194 p237 p431 p435 p657 p840 : Prop)
    (h16152 : (¬ p7))
    (h10686 : (¬ p2) ∨ p7 ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p840)) : (¬ p2) ∨ (¬ p194) ∨ (¬ p237) ∨ (¬ p431) ∨ (¬ p435) ∨ (¬ p657) ∨ (¬ p840) := by
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
  have u2 : p237 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p435 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10686 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u7 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16608 (p7 p18 p69 p101 p123 p288 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16186 : (¬ p123))
    (h7053 : p1184)
    (h10688 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ p123 ∨ (¬ p288) ∨ (¬ p1184)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p101) ∨ (¬ p288) := by
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
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p123) := by
    exact h16186
  have u6 : p1184 := by
    exact h7053
  rcases h10688 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16609 (p7 p27 p101 p309 p640 p1055 p1095 : Prop)
    (h16152 : (¬ p7))
    (h10689 : p7 ∨ (¬ p27) ∨ (¬ p101) ∨ (¬ p309) ∨ (¬ p640) ∨ (¬ p1055) ∨ (¬ p1095)) : (¬ p27) ∨ (¬ p101) ∨ (¬ p309) ∨ (¬ p640) ∨ (¬ p1055) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10689 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16610 (p7 p156 p193 p238 p1055 p1116 : Prop)
    (h16152 : (¬ p7))
    (h10690 : p7 ∨ (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p1055) ∨ (¬ p1116)) : (¬ p156) ∨ (¬ p193) ∨ (¬ p238) ∨ (¬ p1055) ∨ (¬ p1116) := by
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
  have u2 : p238 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10690 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16611 (p40 p67 p233 p481 : Prop)
    (h16150 : (¬ p40))
    (h2345 : p233)
    (h10691 : p40 ∨ p67 ∨ (¬ p233) ∨ (¬ p481)) : p67 ∨ (¬ p481) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p67) := fun hu => hn (Or.inl hu)
  have u1 : p481 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p40) := by
    exact h16150
  have u3 : p233 := by
    exact h2345
  rcases h10691 with q0 | q1 | q2 | q3
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u1)

theorem step16612 (p7 p25 p67 p226 p640 p1036 p1095 : Prop)
    (h16152 : (¬ p7))
    (h10693 : p7 ∨ (¬ p25) ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p640) ∨ (¬ p1036) ∨ (¬ p1095)) : (¬ p25) ∨ (¬ p67) ∨ (¬ p226) ∨ (¬ p640) ∨ (¬ p1036) ∨ (¬ p1095) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p25 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10693 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16613 (p7 p12 p14 p67 p556 p1055 : Prop)
    (h16152 : (¬ p7))
    (h10695 : p7 ∨ (¬ p12) ∨ (¬ p14) ∨ (¬ p67) ∨ (¬ p556) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p14) ∨ (¬ p67) ∨ (¬ p556) ∨ (¬ p1055) := by
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
  have u2 : p67 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10695 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16614 (p7 p70 p85 p102 p127 p344 p842 p1385 : Prop)
    (h16152 : (¬ p7))
    (h10696 : p7 ∨ (¬ p70) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p842) ∨ (¬ p1385)) : (¬ p70) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p127) ∨ (¬ p344) ∨ (¬ p842) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p70 := by
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
  have u3 : p127 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p842 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10696 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16615 (p7 p45 p85 p302 p419 p796 p1184 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h10697 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ p302 ∨ (¬ p419) ∨ (¬ p796) ∨ (¬ p1184)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p796) := by
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
  have u6 : p1184 := by
    exact h7053
  rcases h10697 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16616 (p7 p134 p330 p419 p789 p795 : Prop)
    (h16152 : (¬ p7))
    (h10698 : p7 ∨ (¬ p134) ∨ (¬ p330) ∨ (¬ p419) ∨ (¬ p789) ∨ (¬ p795)) : (¬ p134) ∨ (¬ p330) ∨ (¬ p419) ∨ (¬ p789) ∨ (¬ p795) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p795 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10698 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16617 (p2 p7 p50 p188 p193 p234 : Prop)
    (h16152 : (¬ p7))
    (h10699 : (¬ p2) ∨ p7 ∨ (¬ p50) ∨ (¬ p188) ∨ (¬ p193) ∨ (¬ p234)) : (¬ p2) ∨ (¬ p50) ∨ (¬ p188) ∨ (¬ p193) ∨ (¬ p234) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p2 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p50 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p188 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10699 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16618 (p7 p41 p83 p189 p1229 p1274 : Prop)
    (h16152 : (¬ p7))
    (h10701 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p1229) ∨ (¬ p1274)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p1229) ∨ (¬ p1274) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10701 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16619 (p7 p85 p289 p576 p926 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10702 : p7 ∨ (¬ p85) ∨ (¬ p289) ∨ (¬ p576) ∨ (¬ p926) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p289) ∨ (¬ p576) ∨ (¬ p926) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p289 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p576 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10702 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16620 (p7 p17 p83 p581 p929 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10703 : p7 ∨ (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p929) ∨ (¬ p1096)) : (¬ p17) ∨ (¬ p83) ∨ (¬ p581) ∨ (¬ p929) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10703 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16621 (p7 p85 p230 p836 p904 p1096 p1537 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h9400 : p1537)
    (h10704 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1537)) : (¬ p85) ∨ (¬ p836) ∨ (¬ p904) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p836 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1537 := by
    exact h9400
  rcases h10704 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16622 (p5 p6 p7 p101 p664 p904 p1076 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10705 : (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p101) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1076) ∨ (¬ p1096)) : (¬ p5) ∨ (¬ p6) ∨ (¬ p101) ∨ (¬ p664) ∨ (¬ p904) ∨ (¬ p1076) ∨ (¬ p1096) := by
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
  have u3 : p664 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10705 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (u7 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16623 (p5 p40 p69 p659 : Prop)
    (h16150 : (¬ p40))
    (h3753 : p659)
    (h10706 : p5 ∨ p40 ∨ (¬ p69) ∨ (¬ p659)) : p5 ∨ (¬ p69) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p5) := fun hu => hn (Or.inl hu)
  have u1 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p40) := by
    exact h16150
  have u3 : p659 := by
    exact h3753
  rcases h10706 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step16624 (p6 p7 p10 p38 p49 p85 p351 p904 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10707 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p351) ∨ (¬ p904) ∨ (¬ p1096)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p351) ∨ (¬ p904) ∨ (¬ p1096) := by
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
  have u2 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p351 := by
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
  rcases h10707 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16625 (p7 p102 p257 p343 p904 p1074 p1077 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1950 : p343)
    (h10708 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p343) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1077)) : (¬ p102) ∨ (¬ p904) ∨ (¬ p1074) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p343 := by
    exact h1950
  rcases h10708 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16626 (p7 p85 p230 p346 p840 p926 p1075 p1096 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h10709 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p346) ∨ (¬ p840) ∨ (¬ p926) ∨ (¬ p1075) ∨ (¬ p1096)) : (¬ p85) ∨ (¬ p346) ∨ (¬ p840) ∨ (¬ p926) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p230) := by
    exact h16165
  have u7 : p1075 := by
    exact h6478
  rcases h10709 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u6 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16627 (p7 p85 p230 p343 p344 p499 p633 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h1950 : p343)
    (h10711 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p343) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p85) ∨ (¬ p344) ∨ (¬ p499) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
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
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p343 := by
    exact h1950
  rcases h10711 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16628 (p7 p12 p108 p139 p265 p304 p1076 : Prop)
    (h16152 : (¬ p7))
    (h10712 : p7 ∨ (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p1076)) : (¬ p12) ∨ (¬ p108) ∨ (¬ p139) ∨ (¬ p265) ∨ (¬ p304) ∨ (¬ p1076) := by
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
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16629 (p7 p85 p230 p983 p1095 p1096 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h10713 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) ∨ (¬ p1386)) : (¬ p85) ∨ (¬ p983) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1386 := by
    exact h8348
  rcases h10713 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16630 (p7 p302 p343 p616 p904 p1096 p1287 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h1950 : p343)
    (h10715 : p7 ∨ p302 ∨ (¬ p343) ∨ (¬ p616) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1287)) : (¬ p616) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1287) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1287 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p302) := by
    exact h16285
  have u6 : p343 := by
    exact h1950
  rcases h10715 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u0)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16631 (p7 p102 p206 p304 p1140 p1213 : Prop)
    (h16152 : (¬ p7))
    (h10716 : p7 ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p1140) ∨ (¬ p1213)) : (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p1140) ∨ (¬ p1213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10716 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16632 (p7 p102 p257 p343 p756 p904 p1538 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h1950 : p343)
    (h10717 : p7 ∨ (¬ p102) ∨ p257 ∨ (¬ p343) ∨ (¬ p756) ∨ (¬ p904) ∨ (¬ p1538)) : (¬ p102) ∨ (¬ p756) ∨ (¬ p904) ∨ (¬ p1538) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p756 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p904 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1538 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p257) := by
    exact h16170
  have u6 : p343 := by
    exact h1950
  rcases h10717 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16633 (p7 p49 p85 p533 p1096 p1141 p1465 p1562 : Prop)
    (h16152 : (¬ p7))
    (h10718 : p7 ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1141) ∨ (¬ p1465) ∨ (¬ p1562)) : (¬ p49) ∨ (¬ p85) ∨ (¬ p533) ∨ (¬ p1096) ∨ (¬ p1141) ∨ (¬ p1465) ∨ (¬ p1562) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p533 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1141 := by
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
  rcases h10718 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16635 (p7 p346 p495 p840 p926 p1075 p1096 p1160 : Prop)
    (h16152 : (¬ p7))
    (h6478 : p1075)
    (h16265 : (¬ p1160))
    (h10721 : p7 ∨ (¬ p346) ∨ (¬ p495) ∨ (¬ p840) ∨ (¬ p926) ∨ (¬ p1075) ∨ (¬ p1096) ∨ p1160) : (¬ p346) ∨ (¬ p495) ∨ (¬ p840) ∨ (¬ p926) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p840 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p1075 := by
    exact h6478
  have u7 : (¬ p1160) := by
    exact h16265
  rcases h10721 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u4)
  · exact False.elim (u7 q7)

theorem step16636 (p7 p15 p21 p234 p330 p495 : Prop)
    (h16152 : (¬ p7))
    (h10723 : p7 ∨ (¬ p15) ∨ (¬ p21) ∨ (¬ p234) ∨ (¬ p330) ∨ (¬ p495)) : (¬ p15) ∨ (¬ p21) ∨ (¬ p234) ∨ (¬ p330) ∨ (¬ p495) := by
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
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10723 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16637 (p7 p12 p343 p653 p680 p687 p734 p1055 : Prop)
    (h16152 : (¬ p7))
    (h1950 : p343)
    (h16194 : (¬ p653))
    (h10724 : p7 ∨ (¬ p12) ∨ (¬ p343) ∨ p653 ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p680) ∨ (¬ p687) ∨ (¬ p734) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p680 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : p343 := by
    exact h1950
  have u7 : (¬ p653) := by
    exact h16194
  rcases h10724 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u6)
  · exact False.elim (u7 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)
  · exact False.elim (q7 u4)

theorem step16638 (p7 p88 p256 p288 p344 p545 p619 p690 p1366 p1394 : Prop)
    (h16152 : (¬ p7))
    (h10725 : p7 ∨ p88 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p619) ∨ (¬ p690) ∨ (¬ p1366) ∨ (¬ p1394)) : p88 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p344) ∨ (¬ p545) ∨ (¬ p619) ∨ (¬ p690) ∨ (¬ p1366) ∨ (¬ p1394) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p88) := fun hu => hn (Or.inl hu)
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
  have u4 : p545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1366 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1394 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10725 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
  · exact False.elim (u9 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)
  · exact False.elim (q9 u8)

theorem step16639 (p7 p38 p49 p85 p224 p225 p226 p1229 p1291 : Prop)
    (h16152 : (¬ p7))
    (h10727 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p1229) ∨ (¬ p1291)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p1229) ∨ (¬ p1291) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p226 := by
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
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10727 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16642 (p7 p85 p224 p434 p595 p596 p710 p929 p1102 p1334 : Prop)
    (h16152 : (¬ p7))
    (h10733 : p7 ∨ (¬ p85) ∨ (¬ p224) ∨ (¬ p434) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1334)) : (¬ p85) ∨ (¬ p224) ∨ (¬ p434) ∨ (¬ p595) ∨ (¬ p596) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1334) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p596 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10733 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16643 (p7 p110 p345 p438 p544 p728 : Prop)
    (h16152 : (¬ p7))
    (h10734 : p7 ∨ (¬ p110) ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p544) ∨ (¬ p728)) : (¬ p110) ∨ (¬ p345) ∨ (¬ p438) ∨ (¬ p544) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p345 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p438 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10734 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16644 (p7 p12 p559 p983 p1056 p1226 : Prop)
    (h16152 : (¬ p7))
    (h10736 : p7 ∨ (¬ p12) ∨ (¬ p559) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1226)) : (¬ p12) ∨ (¬ p559) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p559 := by
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
  rcases h10736 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16645 (p7 p224 p228 p532 p728 p1331 : Prop)
    (h16152 : (¬ p7))
    (h10738 : p7 ∨ (¬ p224) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1331)) : (¬ p224) ∨ (¬ p228) ∨ (¬ p532) ∨ (¬ p728) ∨ (¬ p1331) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p228 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1331 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10738 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16646 (p7 p15 p22 p434 p601 p616 p1287 p1334 : Prop)
    (h16152 : (¬ p7))
    (h10739 : p7 ∨ (¬ p15) ∨ (¬ p22) ∨ (¬ p434) ∨ (¬ p601) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1334)) : (¬ p15) ∨ (¬ p22) ∨ (¬ p434) ∨ (¬ p601) ∨ (¬ p616) ∨ (¬ p1287) ∨ (¬ p1334) := by
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
  have u2 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p601 := by
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
  have u6 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10739 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16647 (p7 p559 p980 p1035 p1042 p1055 : Prop)
    (h16152 : (¬ p7))
    (h10741 : p7 ∨ (¬ p559) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042) ∨ (¬ p1055)) : (¬ p559) ∨ (¬ p980) ∨ (¬ p1035) ∨ (¬ p1042) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1042 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10741 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16648 (p7 p85 p110 p499 p544 p633 p710 p929 p1102 : Prop)
    (h16152 : (¬ p7))
    (h10742 : p7 ∨ (¬ p85) ∨ (¬ p110) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p633) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102)) : (¬ p85) ∨ (¬ p110) ∨ (¬ p499) ∨ (¬ p544) ∨ (¬ p633) ∨ (¬ p710) ∨ (¬ p929) ∨ (¬ p1102) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10742 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16649 (p6 p7 p10 p303 p659 p1324 p1325 : Prop)
    (h16152 : (¬ p7))
    (h3753 : p659)
    (h16309 : (¬ p1324))
    (h10743 : (¬ p6) ∨ p7 ∨ (¬ p10) ∨ (¬ p303) ∨ (¬ p659) ∨ p1324 ∨ (¬ p1325)) : (¬ p6) ∨ (¬ p10) ∨ (¬ p303) ∨ (¬ p1325) := by
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
  have u5 : p659 := by
    exact h3753
  have u6 : (¬ p1324) := by
    exact h16309
  rcases h10743 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (u4 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u5)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u3)

theorem step16650 (p7 p38 p49 p85 p101 p125 p206 p323 p638 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10744 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p638) ∨ (¬ p1096)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p125) ∨ (¬ p206) ∨ (¬ p323) ∨ (¬ p638) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10744 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16651 (p7 p85 p710 p734 p929 p1102 p1225 p1229 p1335 : Prop)
    (h16152 : (¬ p7))
    (h10745 : p7 ∨ (¬ p85) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335)) : (¬ p85) ∨ (¬ p710) ∨ (¬ p734) ∨ (¬ p929) ∨ (¬ p1102) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1335) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
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
  have u7 : p1335 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10745 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16652 (p7 p308 p344 p690 p709 p728 : Prop)
    (h16152 : (¬ p7))
    (h10746 : p7 ∨ (¬ p308) ∨ (¬ p344) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728)) : (¬ p308) ∨ (¬ p344) ∨ (¬ p690) ∨ (¬ p709) ∨ (¬ p728) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10746 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16653 (p7 p45 p85 p1229 p1257 p1272 : Prop)
    (h16152 : (¬ p7))
    (h10748 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p1229) ∨ (¬ p1257) ∨ (¬ p1272)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p1229) ∨ (¬ p1257) ∨ (¬ p1272) := by
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
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1257 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10748 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16655 (p7 p227 p304 p346 p668 p1082 : Prop)
    (h16152 : (¬ p7))
    (h10753 : p7 ∨ (¬ p227) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1082)) : (¬ p227) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1082) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p227 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1082 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10753 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16656 (p7 p38 p49 p85 p206 p304 p346 p668 p1095 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10754 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p346) ∨ (¬ p668) ∨ (¬ p1095) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10754 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16657 (p7 p23 p102 p634 p1074 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10755 : p7 ∨ (¬ p23) ∨ (¬ p102) ∨ (¬ p634) ∨ (¬ p1074) ∨ (¬ p1077)) : (¬ p23) ∨ (¬ p102) ∨ (¬ p634) ∨ (¬ p1074) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p634 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1074 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10755 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16658 (p7 p38 p49 p85 p101 p121 p206 p638 p961 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10756 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p638) ∨ (¬ p961) ∨ (¬ p1096)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p101) ∨ (¬ p121) ∨ (¬ p206) ∨ (¬ p638) ∨ (¬ p961) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p101 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p961 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10756 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16659 (p7 p12 p104 p161 p346 p426 p983 p1228 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h7327 : p1228)
    (h10757 : p7 ∨ (¬ p12) ∨ (¬ p104) ∨ (¬ p161) ∨ (¬ p346) ∨ p426 ∨ (¬ p983) ∨ (¬ p1228)) : (¬ p12) ∨ (¬ p104) ∨ (¬ p161) ∨ (¬ p346) ∨ (¬ p983) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p426) := by
    exact h16178
  have u7 : p1228 := by
    exact h7327
  rcases h10757 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16660 (p4 p7 p10 p102 p668 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10758 : (¬ p4) ∨ p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p668) ∨ (¬ p1077)) : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p668) ∨ (¬ p1077) := by
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
  have u3 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1077 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10758 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16661 (p7 p23 p323 p499 p597 p616 : Prop)
    (h16152 : (¬ p7))
    (h10759 : p7 ∨ (¬ p23) ∨ (¬ p323) ∨ (¬ p499) ∨ (¬ p597) ∨ (¬ p616)) : (¬ p23) ∨ (¬ p323) ∨ (¬ p499) ∨ (¬ p597) ∨ (¬ p616) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p23 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p597 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10759 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16662 (p7 p303 p603 p616 p1229 p1292 : Prop)
    (h16152 : (¬ p7))
    (h10760 : p7 ∨ (¬ p303) ∨ (¬ p603) ∨ (¬ p616) ∨ (¬ p1229) ∨ (¬ p1292)) : (¬ p303) ∨ (¬ p603) ∨ (¬ p616) ∨ (¬ p1229) ∨ (¬ p1292) := by
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
  have u2 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10760 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16663 (p7 p85 p132 p230 p301 p499 p601 : Prop)
    (h16152 : (¬ p7))
    (h786 : p132)
    (h16165 : (¬ p230))
    (h10761 : p7 ∨ (¬ p85) ∨ (¬ p132) ∨ p230 ∨ (¬ p301) ∨ (¬ p499) ∨ (¬ p601)) : (¬ p85) ∨ (¬ p301) ∨ (¬ p499) ∨ (¬ p601) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p301 := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : p132 := by
    exact h786
  have u6 : (¬ p230) := by
    exact h16165
  rcases h10761 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u5)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16664 (p7 p305 p497 p633 p1055 p1077 : Prop)
    (h16152 : (¬ p7))
    (h10762 : p7 ∨ (¬ p305) ∨ (¬ p497) ∨ (¬ p633) ∨ (¬ p1055) ∨ (¬ p1077)) : (¬ p305) ∨ (¬ p497) ∨ (¬ p633) ∨ (¬ p1055) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p497 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p633 := by
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
  rcases h10762 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16665 (p7 p344 p616 p638 p899 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10763 : p7 ∨ (¬ p344) ∨ (¬ p616) ∨ (¬ p638) ∨ (¬ p899) ∨ (¬ p1096)) : (¬ p344) ∨ (¬ p616) ∨ (¬ p638) ∨ (¬ p899) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p638 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10763 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16666 (p7 p15 p47 p85 p799 p1385 : Prop)
    (h16152 : (¬ p7))
    (h10767 : p7 ∨ (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p799) ∨ (¬ p1385)) : (¬ p15) ∨ (¬ p47) ∨ (¬ p85) ∨ (¬ p799) ∨ (¬ p1385) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p47 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p799 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10767 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16667 (p6 p7 p38 p49 p532 p1022 p1206 p1330 p1393 : Prop)
    (h16152 : (¬ p7))
    (h10768 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p1022) ∨ (¬ p1206) ∨ (¬ p1330) ∨ (¬ p1393)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p532) ∨ (¬ p1022) ∨ (¬ p1206) ∨ (¬ p1330) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10768 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16668 (p7 p616 p1015 p1395 p1548 p1674 : Prop)
    (h16152 : (¬ p7))
    (h10770 : p7 ∨ (¬ p616) ∨ (¬ p1015) ∨ (¬ p1395) ∨ (¬ p1548) ∨ (¬ p1674)) : (¬ p616) ∨ (¬ p1015) ∨ (¬ p1395) ∨ (¬ p1548) ∨ (¬ p1674) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1548 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1674 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10770 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16669 (p7 p431 p616 p1229 p1292 p1545 : Prop)
    (h16152 : (¬ p7))
    (h10772 : p7 ∨ (¬ p431) ∨ (¬ p616) ∨ (¬ p1229) ∨ (¬ p1292) ∨ (¬ p1545)) : (¬ p431) ∨ (¬ p616) ∨ (¬ p1229) ∨ (¬ p1292) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p431 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1292 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10772 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16670 (p7 p12 p85 p104 p346 p426 p929 p1074 p1225 p1229 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h8348 : p1386)
    (h10773 : p7 ∨ (¬ p12) ∨ (¬ p85) ∨ (¬ p104) ∨ (¬ p346) ∨ p426 ∨ (¬ p929) ∨ (¬ p1074) ∨ (¬ p1225) ∨ (¬ p1229) ∨ (¬ p1386)) : (¬ p12) ∨ (¬ p85) ∨ (¬ p104) ∨ (¬ p346) ∨ (¬ p929) ∨ (¬ p1074) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p104 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1074 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  have u9 : (¬ p426) := by
    exact h16178
  have u10 : p1386 := by
    exact h8348
  rcases h10773 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16671 (p6 p7 p38 p49 p85 p389 p595 p1206 p1286 : Prop)
    (h16152 : (¬ p7))
    (h10774 : (¬ p6) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286)) : (¬ p6) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p389) ∨ (¬ p595) ∨ (¬ p1206) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
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
  have u4 : p389 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10774 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16672 (p7 p308 p344 p382 p657 p709 : Prop)
    (h16152 : (¬ p7))
    (h10775 : p7 ∨ (¬ p308) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p709)) : (¬ p308) ∨ (¬ p344) ∨ (¬ p382) ∨ (¬ p657) ∨ (¬ p709) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p308 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10775 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16674 (p7 p38 p49 p85 p102 p206 p304 p460 p1206 p1229 : Prop)
    (h16152 : (¬ p7))
    (h10777 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p460) ∨ (¬ p1206) ∨ (¬ p1229)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p460) ∨ (¬ p1206) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p460 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10777 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16675 (p7 p20 p49 p85 p124 p498 p636 : Prop)
    (h16152 : (¬ p7))
    (h10779 : p7 ∨ (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p498) ∨ (¬ p636)) : (¬ p20) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p124) ∨ (¬ p498) ∨ (¬ p636) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p20 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p124 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10779 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16676 (p7 p27 p461 p495 p1206 p1229 : Prop)
    (h16152 : (¬ p7))
    (h10780 : p7 ∨ (¬ p27) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p1206) ∨ (¬ p1229)) : (¬ p27) ∨ (¬ p461) ∨ (¬ p495) ∨ (¬ p1206) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p27 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p495 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10780 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16677 (p7 p342 p499 p597 p616 p633 : Prop)
    (h16152 : (¬ p7))
    (h10782 : p7 ∨ (¬ p342) ∨ (¬ p499) ∨ (¬ p597) ∨ (¬ p616) ∨ (¬ p633)) : (¬ p342) ∨ (¬ p499) ∨ (¬ p597) ∨ (¬ p616) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p597 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10782 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16678 (p7 p126 p256 p387 p791 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h8348 : p1386)
    (h10783 : p7 ∨ (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ p791 ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p126) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1386 := by
    exact h8348
  rcases h10783 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16679 (p7 p10 p121 p161 p280 p1306 p1452 p1531 : Prop)
    (h16152 : (¬ p7))
    (h16173 : (¬ p280))
    (h9335 : p1531)
    (h10785 : p7 ∨ (¬ p10) ∨ (¬ p121) ∨ (¬ p161) ∨ p280 ∨ (¬ p1306) ∨ (¬ p1452) ∨ (¬ p1531)) : (¬ p10) ∨ (¬ p121) ∨ (¬ p161) ∨ (¬ p1306) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p121 := by
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
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p280) := by
    exact h16173
  have u7 : p1531 := by
    exact h9335
  rcases h10785 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u6 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u7)

theorem step16680 (p7 p10 p38 p102 p206 p304 p517 p615 p687 p1015 p1190 : Prop)
    (h16152 : (¬ p7))
    (h10786 : p7 ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p517) ∨ (¬ p615) ∨ (¬ p687) ∨ (¬ p1015) ∨ (¬ p1190)) : (¬ p10) ∨ (¬ p38) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p517) ∨ (¬ p615) ∨ (¬ p687) ∨ (¬ p1015) ∨ (¬ p1190) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p38 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p517 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p615 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1015 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1190 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h10786 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16681 (p7 p38 p49 p107 p206 p304 p980 p1022 p1036 p1330 p1393 : Prop)
    (h16152 : (¬ p7))
    (h10787 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1036) ∨ (¬ p1330) ∨ (¬ p1393)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p107) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p980) ∨ (¬ p1022) ∨ (¬ p1036) ∨ (¬ p1330) ∨ (¬ p1393) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p107 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1022 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1330 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1393 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h10787 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16683 (p7 p194 p226 p266 p301 p362 p1036 p1081 p1443 : Prop)
    (h16152 : (¬ p7))
    (h10790 : p7 ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1443)) : (¬ p194) ∨ (¬ p226) ∨ (¬ p266) ∨ (¬ p301) ∨ (¬ p362) ∨ (¬ p1036) ∨ (¬ p1081) ∨ (¬ p1443) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p266 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10790 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16684 (p7 p126 p194 p226 p256 p387 p669 p1036 : Prop)
    (h16152 : (¬ p7))
    (h10791 : p7 ∨ (¬ p126) ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p669) ∨ (¬ p1036)) : (¬ p126) ∨ (¬ p194) ∨ (¬ p226) ∨ (¬ p256) ∨ (¬ p387) ∨ (¬ p669) ∨ (¬ p1036) := by
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
  have u2 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10791 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16685 (p7 p12 p126 p225 p243 p256 p347 p1055 : Prop)
    (h16152 : (¬ p7))
    (h10792 : p7 ∨ (¬ p12) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p243) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p1055)) : (¬ p12) ∨ (¬ p126) ∨ (¬ p225) ∨ (¬ p243) ∨ (¬ p256) ∨ (¬ p347) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p256 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p347 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
  have u7 : (¬ p7) := by
    exact h16152
  rcases h10792 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u7 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)

theorem step16686 (p7 p544 p616 p882 p899 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10793 : p7 ∨ (¬ p544) ∨ (¬ p616) ∨ (¬ p882) ∨ (¬ p899) ∨ (¬ p1096)) : (¬ p544) ∨ (¬ p616) ∨ (¬ p882) ∨ (¬ p899) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p882 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p899 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10793 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16687 (p7 p18 p69 p109 p883 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10794 : p7 ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p109) ∨ (¬ p883) ∨ (¬ p1096)) : (¬ p18) ∨ (¬ p69) ∨ (¬ p109) ∨ (¬ p883) ∨ (¬ p1096) := by
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
  have u2 : p109 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p883 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10794 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16688 (p7 p38 p49 p85 p226 p595 p669 p1036 p1286 : Prop)
    (h16152 : (¬ p7))
    (h10796 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1286)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p595) ∨ (¬ p669) ∨ (¬ p1036) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p669 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10796 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16689 (p7 p85 p160 p161 p1236 p1274 : Prop)
    (h16152 : (¬ p7))
    (h10797 : p7 ∨ (¬ p85) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p1236) ∨ (¬ p1274)) : (¬ p85) ∨ (¬ p160) ∨ (¬ p161) ∨ (¬ p1236) ∨ (¬ p1274) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
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
  have u3 : p1236 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10797 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16690 (p7 p382 p479 p1002 p1035 p1325 : Prop)
    (h16152 : (¬ p7))
    (h10798 : p7 ∨ (¬ p382) ∨ (¬ p479) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325)) : (¬ p382) ∨ (¬ p479) ∨ (¬ p1002) ∨ (¬ p1035) ∨ (¬ p1325) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p479 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1002 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10798 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16691 (p7 p161 p800 p856 p996 p1272 p1333 : Prop)
    (h16152 : (¬ p7))
    (h10800 : p7 ∨ (¬ p161) ∨ (¬ p800) ∨ (¬ p856) ∨ (¬ p996) ∨ (¬ p1272) ∨ (¬ p1333)) : (¬ p161) ∨ (¬ p800) ∨ (¬ p856) ∨ (¬ p996) ∨ (¬ p1272) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p800 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p856 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p996 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1272 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10800 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16692 (p2 p7 p38 p49 p85 p419 p595 p657 p901 : Prop)
    (h16152 : (¬ p7))
    (h10801 : (¬ p2) ∨ p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901)) : (¬ p2) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p419) ∨ (¬ p595) ∨ (¬ p657) ∨ (¬ p901) := by
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
  have u6 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p901 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10801 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (q0 u0)
  · exact False.elim (u8 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16693 (p7 p38 p49 p85 p226 p940 p985 p1225 p1229 : Prop)
    (h16152 : (¬ p7))
    (h10802 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p226) ∨ (¬ p940) ∨ (¬ p985) ∨ (¬ p1225) ∨ (¬ p1229) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p226 := by
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
  have u6 : p1225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10802 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16694 (p7 p38 p49 p85 p534 p556 p769 p1036 p1229 p1309 : Prop)
    (h16152 : (¬ p7))
    (h10803 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p534) ∨ (¬ p556) ∨ (¬ p769) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p534) ∨ (¬ p556) ∨ (¬ p769) ∨ (¬ p1036) ∨ (¬ p1229) ∨ (¬ p1309) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p534 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p769 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1036 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1309 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10803 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16695 (p7 p382 p536 p657 p709 p738 : Prop)
    (h16152 : (¬ p7))
    (h10804 : p7 ∨ (¬ p382) ∨ (¬ p536) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p738)) : (¬ p382) ∨ (¬ p536) ∨ (¬ p657) ∨ (¬ p709) ∨ (¬ p738) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p709 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p738 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10804 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16696 (p7 p38 p49 p85 p225 p226 p668 p926 p1096 p1116 : Prop)
    (h16152 : (¬ p7))
    (h10805 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p926) ∨ (¬ p1096) ∨ (¬ p1116)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p926) ∨ (¬ p1096) ∨ (¬ p1116) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
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
  have u5 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10805 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16697 (p7 p8 p12 p110 p346 p1055 : Prop)
    (h16152 : (¬ p7))
    (h10806 : p7 ∨ (¬ p8) ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p346) ∨ (¬ p1055)) : (¬ p8) ∨ (¬ p12) ∨ (¬ p110) ∨ (¬ p346) ∨ (¬ p1055) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p8 := by
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
  have u3 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10806 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16699 (p7 p12 p225 p382 p666 p712 : Prop)
    (h16152 : (¬ p7))
    (h10808 : p7 ∨ (¬ p12) ∨ (¬ p225) ∨ (¬ p382) ∨ (¬ p666) ∨ (¬ p712)) : (¬ p12) ∨ (¬ p225) ∨ (¬ p382) ∨ (¬ p666) ∨ (¬ p712) := by
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
  have u2 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p666 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p712 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10808 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16700 (p7 p12 p38 p49 p85 p225 p426 p556 p595 p1055 p1135 p1286 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h6744 : p1135)
    (h10809 : p7 ∨ (¬ p12) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p225) ∨ p426 ∨ (¬ p556) ∨ (¬ p595) ∨ (¬ p1055) ∨ (¬ p1135) ∨ (¬ p1286)) : (¬ p12) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p225) ∨ (¬ p556) ∨ (¬ p595) ∨ (¬ p1055) ∨ (¬ p1286) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p12 := by
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
  have u4 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  have u10 : (¬ p426) := by
    exact h16178
  have u11 : p1135 := by
    exact h6744
  rcases h10809 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10 | q11
  · exact False.elim (u9 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (u10 q6)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u6)
  · exact False.elim (q9 u7)
  · exact False.elim (q10 u11)
  · exact False.elim (q11 u8)

theorem step16701 (p7 p85 p230 p595 p1286 p1333 p1386 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h8348 : p1386)
    (h10810 : p7 ∨ (¬ p85) ∨ p230 ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) ∨ (¬ p1386)) : (¬ p85) ∨ (¬ p595) ∨ (¬ p1286) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1286 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1386 := by
    exact h8348
  rcases h10810 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u5 q2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16703 (p7 p38 p49 p85 p926 p1035 p1044 p1096 p1116 p1163 p1226 : Prop)
    (h16152 : (¬ p7))
    (h10812 : p7 ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p926) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1096) ∨ (¬ p1116) ∨ (¬ p1163) ∨ (¬ p1226)) : (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p926) ∨ (¬ p1035) ∨ (¬ p1044) ∨ (¬ p1096) ∨ (¬ p1116) ∨ (¬ p1163) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p38 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p49 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1044 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1116 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))))
  have u9 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))))
  have u10 : (¬ p7) := by
    exact h16152
  rcases h10812 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9 | q10
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

theorem step16704 (p7 p195 p1035 p1140 p1252 p1489 : Prop)
    (h16152 : (¬ p7))
    (h10813 : p7 ∨ (¬ p195) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1252) ∨ (¬ p1489)) : (¬ p195) ∨ (¬ p1035) ∨ (¬ p1140) ∨ (¬ p1252) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1140 := by
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
  rcases h10813 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16705 (p7 p225 p226 p668 p1041 p1140 : Prop)
    (h16152 : (¬ p7))
    (h10816 : p7 ∨ (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p1041) ∨ (¬ p1140)) : (¬ p225) ∨ (¬ p226) ∨ (¬ p668) ∨ (¬ p1041) ∨ (¬ p1140) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p225 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p668 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1041 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10816 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16706 (p7 p108 p544 p556 p710 p1140 p1213 : Prop)
    (h16152 : (¬ p7))
    (h10817 : p7 ∨ (¬ p108) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1140) ∨ (¬ p1213)) : (¬ p108) ∨ (¬ p544) ∨ (¬ p556) ∨ (¬ p710) ∨ (¬ p1140) ∨ (¬ p1213) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p108 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p556 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1140 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1213 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10817 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16707 (p4 p7 p10 p102 p304 p430 p681 p734 : Prop)
    (h16152 : (¬ p7))
    (h16180 : (¬ p430))
    (h3892 : p681)
    (h10818 : (¬ p4) ∨ p7 ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p304) ∨ p430 ∨ (¬ p681) ∨ (¬ p734)) : (¬ p4) ∨ (¬ p10) ∨ (¬ p102) ∨ (¬ p304) ∨ (¬ p734) := by
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
  have u3 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p734 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  have u6 : (¬ p430) := by
    exact h16180
  have u7 : p681 := by
    exact h3892
  rcases h10818 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u6 q5)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16708 (p7 p10 p38 p49 p85 p102 p206 p304 p595 p599 : Prop)
    (h16152 : (¬ p7))
    (h10819 : p7 ∨ (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p599)) : (¬ p10) ∨ (¬ p38) ∨ (¬ p49) ∨ (¬ p85) ∨ (¬ p102) ∨ (¬ p206) ∨ (¬ p304) ∨ (¬ p595) ∨ (¬ p599) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p10 := by
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
  have u4 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p206 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p595 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p599 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10819 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16709 (p7 p209 p323 p363 p382 p387 : Prop)
    (h16152 : (¬ p7))
    (h10820 : p7 ∨ (¬ p209) ∨ (¬ p323) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387)) : (¬ p209) ∨ (¬ p323) ∨ (¬ p363) ∨ (¬ p382) ∨ (¬ p387) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p209 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p323 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10820 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16711 (p7 p426 p616 p728 p1096 p1531 p1545 : Prop)
    (h16152 : (¬ p7))
    (h16178 : (¬ p426))
    (h9335 : p1531)
    (h10822 : p7 ∨ p426 ∨ (¬ p616) ∨ (¬ p728) ∨ (¬ p1096) ∨ (¬ p1531) ∨ (¬ p1545)) : (¬ p616) ∨ (¬ p728) ∨ (¬ p1096) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p616 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p728 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p426) := by
    exact h16178
  have u6 : p1531 := by
    exact h9335
  rcases h10822 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16712 (p7 p40 p69 p132 p258 p499 p633 : Prop)
    (h16152 : (¬ p7))
    (h16150 : (¬ p40))
    (h786 : p132)
    (h10824 : p7 ∨ p40 ∨ (¬ p69) ∨ (¬ p132) ∨ (¬ p258) ∨ (¬ p499) ∨ (¬ p633)) : (¬ p69) ∨ (¬ p258) ∨ (¬ p499) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
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
  have u5 : (¬ p40) := by
    exact h16150
  have u6 : p132 := by
    exact h786
  rcases h10824 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u6)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u3)

theorem step16713 (p7 p41 p83 p189 p499 p582 : Prop)
    (h16152 : (¬ p7))
    (h10825 : p7 ∨ (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p499) ∨ (¬ p582)) : (¬ p41) ∨ (¬ p83) ∨ (¬ p189) ∨ (¬ p499) ∨ (¬ p582) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p83 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p189 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p582 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10825 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16714 (p7 p124 p342 p363 p434 p690 : Prop)
    (h16152 : (¬ p7))
    (h10827 : p7 ∨ (¬ p124) ∨ (¬ p342) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p690)) : (¬ p124) ∨ (¬ p342) ∨ (¬ p363) ∨ (¬ p434) ∨ (¬ p690) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p124 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p434 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p690 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10827 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16715 (p7 p24 p102 p302 p456 p532 p1075 p1333 : Prop)
    (h16152 : (¬ p7))
    (h16285 : (¬ p302))
    (h6478 : p1075)
    (h10828 : p7 ∨ (¬ p24) ∨ (¬ p102) ∨ p302 ∨ (¬ p456) ∨ (¬ p532) ∨ (¬ p1075) ∨ (¬ p1333)) : (¬ p24) ∨ (¬ p102) ∨ (¬ p456) ∨ (¬ p532) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p24 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
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
  have u7 : p1075 := by
    exact h6478
  rcases h10828 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)
  · exact False.elim (q7 u4)

theorem step16716 (p7 p69 p224 p710 p885 p1102 p1229 p1288 p1334 p1542 : Prop)
    (h16152 : (¬ p7))
    (h10829 : p7 ∨ (¬ p69) ∨ (¬ p224) ∨ (¬ p710) ∨ (¬ p885) ∨ (¬ p1102) ∨ (¬ p1229) ∨ (¬ p1288) ∨ (¬ p1334) ∨ (¬ p1542)) : (¬ p69) ∨ (¬ p224) ∨ (¬ p710) ∨ (¬ p885) ∨ (¬ p1102) ∨ (¬ p1229) ∨ (¬ p1288) ∨ (¬ p1334) ∨ (¬ p1542) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p224 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p710 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p885 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1334 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))))
  have u8 : p1542 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))))
  have u9 : (¬ p7) := by
    exact h16152
  rcases h10829 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8 | q9
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

theorem step16717 (p7 p69 p620 p687 p1194 p1545 : Prop)
    (h16152 : (¬ p7))
    (h10830 : p7 ∨ (¬ p69) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1194) ∨ (¬ p1545)) : (¬ p69) ∨ (¬ p620) ∨ (¬ p687) ∨ (¬ p1194) ∨ (¬ p1545) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p620 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p687 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1194 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1545 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10830 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16718 (p7 p342 p382 p387 p594 p619 p633 : Prop)
    (h16152 : (¬ p7))
    (h10831 : p7 ∨ (¬ p342) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p594) ∨ (¬ p619) ∨ (¬ p633)) : (¬ p342) ∨ (¬ p382) ∨ (¬ p387) ∨ (¬ p594) ∨ (¬ p619) ∨ (¬ p633) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p594 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p619 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h10831 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)

theorem step16719 (p7 p126 p420 p575 p1273 p1497 : Prop)
    (h16152 : (¬ p7))
    (h10832 : p7 ∨ (¬ p126) ∨ (¬ p420) ∨ (¬ p575) ∨ (¬ p1273) ∨ (¬ p1497)) : (¬ p126) ∨ (¬ p420) ∨ (¬ p575) ∨ (¬ p1273) ∨ (¬ p1497) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p575 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1273 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1497 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10832 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16720 (p7 p41 p189 p230 p256 p288 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16165 : (¬ p230))
    (h6478 : p1075)
    (h10833 : p7 ∨ (¬ p41) ∨ (¬ p189) ∨ p230 ∨ (¬ p256) ∨ (¬ p288) ∨ (¬ p1075)) : (¬ p41) ∨ (¬ p189) ∨ (¬ p256) ∨ (¬ p288) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
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
  have u3 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p230) := by
    exact h16165
  have u6 : p1075 := by
    exact h6478
  rcases h10833 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (u5 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u6)

theorem step16721 (p7 p45 p85 p171 p926 p1096 : Prop)
    (h16152 : (¬ p7))
    (h10834 : p7 ∨ (¬ p45) ∨ (¬ p85) ∨ (¬ p171) ∨ (¬ p926) ∨ (¬ p1096)) : (¬ p45) ∨ (¬ p85) ∨ (¬ p171) ∨ (¬ p926) ∨ (¬ p1096) := by
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
  have u2 : p171 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p926 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10834 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16723 (p7 p121 p142 p193 p791 p1386 p1452 : Prop)
    (h16152 : (¬ p7))
    (h16213 : (¬ p791))
    (h8348 : p1386)
    (h10836 : p7 ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ p791 ∨ (¬ p1386) ∨ (¬ p1452)) : (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p7) := by
    exact h16152
  have u5 : (¬ p791) := by
    exact h16213
  have u6 : p1386 := by
    exact h8348
  rcases h10836 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u5 q4)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u3)

theorem step16724 (p7 p121 p142 p193 p243 p983 p1056 p1081 p1226 : Prop)
    (h16152 : (¬ p7))
    (h10837 : p7 ∨ (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p243) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226)) : (¬ p121) ∨ (¬ p142) ∨ (¬ p193) ∨ (¬ p243) ∨ (¬ p983) ∨ (¬ p1056) ∨ (¬ p1081) ∨ (¬ p1226) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p121 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p142 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p193 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p243 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p983 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1056 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1081 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10837 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16725 (p7 p85 p929 p980 p1055 p1102 p1229 p1291 p1333 : Prop)
    (h16152 : (¬ p7))
    (h10838 : p7 ∨ (¬ p85) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1102) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333)) : (¬ p85) ∨ (¬ p929) ∨ (¬ p980) ∨ (¬ p1055) ∨ (¬ p1102) ∨ (¬ p1229) ∨ (¬ p1291) ∨ (¬ p1333) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p929 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p980 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1055 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1102 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1229 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu))))))
  have u6 : p1291 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))))
  have u7 : p1333 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))))
  have u8 : (¬ p7) := by
    exact h16152
  rcases h10838 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u8 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)
  · exact False.elim (q6 u5)
  · exact False.elim (q7 u6)
  · exact False.elim (q8 u7)

theorem step16727 (p7 p90 p160 p1249 p1353 p1489 : Prop)
    (h16152 : (¬ p7))
    (h10845 : p7 ∨ (¬ p90) ∨ (¬ p160) ∨ (¬ p1249) ∨ (¬ p1353) ∨ (¬ p1489)) : (¬ p90) ∨ (¬ p160) ∨ (¬ p1249) ∨ (¬ p1353) ∨ (¬ p1489) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p90 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p160 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1249 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1353 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h10845 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (u5 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step16728 (p7 p18 p125 p234 p257 p265 p288 p328 p1075 : Prop)
    (h16152 : (¬ p7))
    (h16170 : (¬ p257))
    (h6478 : p1075)
    (h10846 : p7 ∨ (¬ p18) ∨ (¬ p125) ∨ (¬ p234) ∨ p257 ∨ (¬ p265) ∨ (¬ p288) ∨ (¬ p328) ∨ (¬ p1075)) : (¬ p18) ∨ (¬ p125) ∨ (¬ p234) ∨ (¬ p265) ∨ (¬ p288) ∨ (¬ p328) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p18 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p234 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p265 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p288 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p328 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  have u7 : (¬ p257) := by
    exact h16170
  have u8 : p1075 := by
    exact h6478
  rcases h10846 with q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | q8
  · exact False.elim (u6 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u2)
  · exact False.elim (u7 q4)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u4)
  · exact False.elim (q7 u5)
  · exact False.elim (q8 u8)

#print axioms step16728

end NineRUPTrial
