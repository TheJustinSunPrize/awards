import Mathlib.Tactic.Tauto

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace NineRUPTrial

theorem step20756 (p734 p737 p740 p741 p742 p743 p744 p745 : Prop)
    (h4256 : p740 ∨ p745)
    (h4261 : p741 ∨ p745)
    (h4266 : p742 ∨ p745)
    (h4271 : p743 ∨ p745)
    (h4276 : p744 ∨ p745)
    (h4167 : p734 ∨ p737 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p745 ∨ p734 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p745) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4256 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4261 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4266 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4271 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4276 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20757 (p734 p737 p740 p741 p742 p743 p744 p746 : Prop)
    (h4257 : p740 ∨ p746)
    (h4262 : p741 ∨ p746)
    (h4267 : p742 ∨ p746)
    (h4272 : p743 ∨ p746)
    (h4277 : p744 ∨ p746)
    (h4167 : p734 ∨ p737 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p746 ∨ p734 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p746) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4257 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4262 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4267 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4272 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4277 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20758 (p734 p737 p740 p741 p742 p743 p744 p747 : Prop)
    (h4258 : p740 ∨ p747)
    (h4263 : p741 ∨ p747)
    (h4268 : p742 ∨ p747)
    (h4273 : p743 ∨ p747)
    (h4278 : p744 ∨ p747)
    (h4167 : p734 ∨ p737 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : p747 ∨ p734 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p747) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p740 := by
    rcases h4258 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p741 := by
    rcases h4263 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p742 := by
    rcases h4268 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p743 := by
    rcases h4273 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p744 := by
    rcases h4278 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20759 (p734 p737 p740 p741 p742 p743 p744 p745 p746 p747 p748 p749 : Prop)
    (h4192 : p734 ∨ p737 ∨ (¬ p745) ∨ (¬ p746) ∨ (¬ p747) ∨ (¬ p748) ∨ (¬ p749))
    (h4259 : p740 ∨ p748)
    (h4264 : p741 ∨ p748)
    (h4269 : p742 ∨ p748)
    (h4274 : p743 ∨ p748)
    (h4279 : p744 ∨ p748)
    (h4167 : p734 ∨ p737 ∨ (¬ p740) ∨ (¬ p741) ∨ (¬ p742) ∨ (¬ p743) ∨ (¬ p744)) : (¬ p747) ∨ p734 ∨ p737 ∨ (¬ p749) ∨ (¬ p745) ∨ (¬ p746) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p747 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p734) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p737) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p749 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p745 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p746 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p748) := by
    rcases h4192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p740 := by
    rcases h4259 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p741 := by
    rcases h4264 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p742 := by
    rcases h4269 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p743 := by
    rcases h4274 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p744 := by
    rcases h4279 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4167 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20760 (p734 p737 p745 p746 p747 p749 : Prop)
    (h20755 : p749 ∨ p734 ∨ p737)
    (h20756 : p745 ∨ p734 ∨ p737)
    (h20757 : p746 ∨ p734 ∨ p737)
    (h20758 : p747 ∨ p734 ∨ p737)
    (h20759 : (¬ p747) ∨ p734 ∨ p737 ∨ (¬ p749) ∨ (¬ p745) ∨ (¬ p746)) : p734 ∨ p737 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p734) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p737) := fun hu => hn (Or.inr hu)
  have u2 : p749 := by
    rcases h20755 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p745 := by
    rcases h20756 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p746 := by
    rcases h20757 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p747 := by
    rcases h20758 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20759 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20761 (p687 p690 p699 p700 p701 p702 p703 p704 : Prop)
    (h3999 : p699 ∨ p704)
    (h4004 : p700 ∨ p704)
    (h4009 : p701 ∨ p704)
    (h4014 : p702 ∨ p704)
    (h4019 : p703 ∨ p704)
    (h3911 : p687 ∨ p690 ∨ (¬ p699) ∨ (¬ p700) ∨ (¬ p701) ∨ (¬ p702) ∨ (¬ p703)) : p704 ∨ p690 ∨ p687 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p704) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p690) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p687) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p699 := by
    rcases h3999 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p700 := by
    rcases h4004 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p701 := by
    rcases h4009 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p702 := by
    rcases h4014 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p703 := by
    rcases h4019 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3911 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20762 (p687 p690 p699 p700 p701 p702 p703 p705 : Prop)
    (h4000 : p699 ∨ p705)
    (h4005 : p700 ∨ p705)
    (h4010 : p701 ∨ p705)
    (h4015 : p702 ∨ p705)
    (h4020 : p703 ∨ p705)
    (h3911 : p687 ∨ p690 ∨ (¬ p699) ∨ (¬ p700) ∨ (¬ p701) ∨ (¬ p702) ∨ (¬ p703)) : p705 ∨ p690 ∨ p687 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p705) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p690) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p687) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p699 := by
    rcases h4000 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p700 := by
    rcases h4005 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p701 := by
    rcases h4010 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p702 := by
    rcases h4015 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p703 := by
    rcases h4020 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3911 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20763 (p687 p690 p699 p700 p701 p702 p703 p706 : Prop)
    (h4001 : p699 ∨ p706)
    (h4006 : p700 ∨ p706)
    (h4011 : p701 ∨ p706)
    (h4016 : p702 ∨ p706)
    (h4021 : p703 ∨ p706)
    (h3911 : p687 ∨ p690 ∨ (¬ p699) ∨ (¬ p700) ∨ (¬ p701) ∨ (¬ p702) ∨ (¬ p703)) : p706 ∨ p690 ∨ p687 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p706) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p690) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p687) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p699 := by
    rcases h4001 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p700 := by
    rcases h4006 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p701 := by
    rcases h4011 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p702 := by
    rcases h4016 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p703 := by
    rcases h4021 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3911 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20764 (p687 p690 p699 p700 p701 p702 p703 p707 : Prop)
    (h4002 : p699 ∨ p707)
    (h4007 : p700 ∨ p707)
    (h4012 : p701 ∨ p707)
    (h4017 : p702 ∨ p707)
    (h4022 : p703 ∨ p707)
    (h3911 : p687 ∨ p690 ∨ (¬ p699) ∨ (¬ p700) ∨ (¬ p701) ∨ (¬ p702) ∨ (¬ p703)) : p707 ∨ p690 ∨ p687 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p707) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p690) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p687) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p699 := by
    rcases h4002 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p700 := by
    rcases h4007 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p701 := by
    rcases h4012 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p702 := by
    rcases h4017 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p703 := by
    rcases h4022 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3911 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20765 (p687 p690 p699 p700 p701 p702 p703 p704 p705 p706 p707 p708 : Prop)
    (h3936 : p687 ∨ p690 ∨ (¬ p704) ∨ (¬ p705) ∨ (¬ p706) ∨ (¬ p707) ∨ (¬ p708))
    (h4003 : p699 ∨ p708)
    (h4008 : p700 ∨ p708)
    (h4013 : p701 ∨ p708)
    (h4018 : p702 ∨ p708)
    (h4023 : p703 ∨ p708)
    (h3911 : p687 ∨ p690 ∨ (¬ p699) ∨ (¬ p700) ∨ (¬ p701) ∨ (¬ p702) ∨ (¬ p703)) : (¬ p707) ∨ (¬ p706) ∨ p687 ∨ p690 ∨ (¬ p704) ∨ (¬ p705) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p707 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p706 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p687) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p690) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p704 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p705 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p708) := by
    rcases h3936 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p699 := by
    rcases h4003 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p700 := by
    rcases h4008 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p701 := by
    rcases h4013 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p702 := by
    rcases h4018 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p703 := by
    rcases h4023 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3911 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20766 (p687 p690 p704 p705 p706 p707 : Prop)
    (h20761 : p704 ∨ p690 ∨ p687)
    (h20762 : p705 ∨ p690 ∨ p687)
    (h20763 : p706 ∨ p690 ∨ p687)
    (h20764 : p707 ∨ p690 ∨ p687)
    (h20765 : (¬ p707) ∨ (¬ p706) ∨ p687 ∨ p690 ∨ (¬ p704) ∨ (¬ p705)) : p690 ∨ p687 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p690) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p687) := fun hu => hn (Or.inr hu)
  have u2 : p704 := by
    rcases h20761 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p705 := by
    rcases h20762 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p706 := by
    rcases h20763 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p707 := by
    rcases h20764 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20765 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20767 (p657 p664 p670 p671 p672 p673 p674 p675 : Prop)
    (h3859 : p670 ∨ p675)
    (h3864 : p671 ∨ p675)
    (h3869 : p672 ∨ p675)
    (h3874 : p673 ∨ p675)
    (h3879 : p674 ∨ p675)
    (h3776 : p657 ∨ p664 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p675 ∨ p664 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p675) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p670 := by
    rcases h3859 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p671 := by
    rcases h3864 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p672 := by
    rcases h3869 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p673 := by
    rcases h3874 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p674 := by
    rcases h3879 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20768 (p657 p664 p670 p671 p672 p673 p674 p676 : Prop)
    (h3860 : p670 ∨ p676)
    (h3865 : p671 ∨ p676)
    (h3870 : p672 ∨ p676)
    (h3875 : p673 ∨ p676)
    (h3880 : p674 ∨ p676)
    (h3776 : p657 ∨ p664 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p676 ∨ p664 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p676) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p670 := by
    rcases h3860 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p671 := by
    rcases h3865 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p672 := by
    rcases h3870 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p673 := by
    rcases h3875 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p674 := by
    rcases h3880 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20769 (p657 p664 p670 p671 p672 p673 p674 p677 : Prop)
    (h3861 : p670 ∨ p677)
    (h3866 : p671 ∨ p677)
    (h3871 : p672 ∨ p677)
    (h3876 : p673 ∨ p677)
    (h3881 : p674 ∨ p677)
    (h3776 : p657 ∨ p664 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p677 ∨ p664 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p677) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p670 := by
    rcases h3861 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p671 := by
    rcases h3866 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p672 := by
    rcases h3871 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p673 := by
    rcases h3876 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p674 := by
    rcases h3881 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20770 (p657 p664 p670 p671 p672 p673 p674 p678 : Prop)
    (h3862 : p670 ∨ p678)
    (h3867 : p671 ∨ p678)
    (h3872 : p672 ∨ p678)
    (h3877 : p673 ∨ p678)
    (h3882 : p674 ∨ p678)
    (h3776 : p657 ∨ p664 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p678 ∨ p664 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p678) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p670 := by
    rcases h3862 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p671 := by
    rcases h3867 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p672 := by
    rcases h3872 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p673 := by
    rcases h3877 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p674 := by
    rcases h3882 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3776 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20779 (p897 p904 p907 p908 p909 p910 p911 p912 : Prop)
    (h5301 : p907 ∨ p912)
    (h5306 : p908 ∨ p912)
    (h5311 : p909 ∨ p912)
    (h5316 : p910 ∨ p912)
    (h5321 : p911 ∨ p912)
    (h5213 : p897 ∨ p904 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p912 ∨ p897 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p912) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p904) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p907 := by
    rcases h5301 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p908 := by
    rcases h5306 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p909 := by
    rcases h5311 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p910 := by
    rcases h5316 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p911 := by
    rcases h5321 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20780 (p897 p904 p907 p908 p909 p910 p911 p913 : Prop)
    (h5302 : p907 ∨ p913)
    (h5307 : p908 ∨ p913)
    (h5312 : p909 ∨ p913)
    (h5317 : p910 ∨ p913)
    (h5322 : p911 ∨ p913)
    (h5213 : p897 ∨ p904 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p913 ∨ p897 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p913) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p904) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p907 := by
    rcases h5302 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p908 := by
    rcases h5307 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p909 := by
    rcases h5312 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p910 := by
    rcases h5317 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p911 := by
    rcases h5322 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20781 (p897 p904 p907 p908 p909 p910 p911 p914 : Prop)
    (h5303 : p907 ∨ p914)
    (h5308 : p908 ∨ p914)
    (h5313 : p909 ∨ p914)
    (h5318 : p910 ∨ p914)
    (h5323 : p911 ∨ p914)
    (h5213 : p897 ∨ p904 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p914 ∨ p897 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p914) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p904) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p907 := by
    rcases h5303 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p908 := by
    rcases h5308 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p909 := by
    rcases h5313 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p910 := by
    rcases h5318 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p911 := by
    rcases h5323 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20782 (p897 p904 p907 p908 p909 p910 p911 p915 : Prop)
    (h5304 : p907 ∨ p915)
    (h5309 : p908 ∨ p915)
    (h5314 : p909 ∨ p915)
    (h5319 : p910 ∨ p915)
    (h5324 : p911 ∨ p915)
    (h5213 : p897 ∨ p904 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : p915 ∨ p897 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p915) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p897) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p904) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20783 (p897 p904 p907 p908 p909 p910 p911 p912 p913 p914 p915 p916 : Prop)
    (h5238 : p897 ∨ p904 ∨ (¬ p912) ∨ (¬ p913) ∨ (¬ p914) ∨ (¬ p915) ∨ (¬ p916))
    (h5305 : p907 ∨ p916)
    (h5310 : p908 ∨ p916)
    (h5315 : p909 ∨ p916)
    (h5320 : p910 ∨ p916)
    (h5325 : p911 ∨ p916)
    (h5213 : p897 ∨ p904 ∨ (¬ p907) ∨ (¬ p908) ∨ (¬ p909) ∨ (¬ p910) ∨ (¬ p911)) : (¬ p915) ∨ (¬ p914) ∨ p904 ∨ p897 ∨ (¬ p912) ∨ (¬ p913) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p915 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p914 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p904) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p897) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p912 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p913 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p916) := by
    rcases h5238 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p907 := by
    rcases h5305 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p908 := by
    rcases h5310 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p909 := by
    rcases h5315 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p910 := by
    rcases h5320 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p911 := by
    rcases h5325 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5213 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20784 (p897 p904 p912 p913 p914 p915 : Prop)
    (h20779 : p912 ∨ p897 ∨ p904)
    (h20780 : p913 ∨ p897 ∨ p904)
    (h20781 : p914 ∨ p897 ∨ p904)
    (h20782 : p915 ∨ p897 ∨ p904)
    (h20783 : (¬ p915) ∨ (¬ p914) ∨ p904 ∨ p897 ∨ (¬ p912) ∨ (¬ p913)) : p897 ∨ p904 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p897) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p904) := fun hu => hn (Or.inr hu)
  have u2 : p912 := by
    rcases h20779 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p913 := by
    rcases h20780 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p914 := by
    rcases h20781 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p915 := by
    rcases h20782 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20783 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20785 (p616 p619 p623 p624 p625 p626 p627 p628 : Prop)
    (h3590 : p623 ∨ p628)
    (h3595 : p624 ∨ p628)
    (h3600 : p625 ∨ p628)
    (h3605 : p626 ∨ p628)
    (h3610 : p627 ∨ p628)
    (h3500 : p616 ∨ p619 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627)) : p628 ∨ p619 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p628) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p619) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p623 := by
    rcases h3590 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p624 := by
    rcases h3595 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p625 := by
    rcases h3600 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p626 := by
    rcases h3605 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p627 := by
    rcases h3610 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20786 (p616 p619 p623 p624 p625 p626 p627 p629 : Prop)
    (h3591 : p623 ∨ p629)
    (h3596 : p624 ∨ p629)
    (h3601 : p625 ∨ p629)
    (h3606 : p626 ∨ p629)
    (h3611 : p627 ∨ p629)
    (h3500 : p616 ∨ p619 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627)) : p629 ∨ p619 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p629) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p619) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p623 := by
    rcases h3591 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p624 := by
    rcases h3596 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p625 := by
    rcases h3601 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p626 := by
    rcases h3606 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p627 := by
    rcases h3611 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20787 (p616 p619 p623 p624 p625 p626 p627 p630 : Prop)
    (h3592 : p623 ∨ p630)
    (h3597 : p624 ∨ p630)
    (h3602 : p625 ∨ p630)
    (h3607 : p626 ∨ p630)
    (h3612 : p627 ∨ p630)
    (h3500 : p616 ∨ p619 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627)) : p630 ∨ p619 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p630) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p619) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p623 := by
    rcases h3592 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p624 := by
    rcases h3597 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p625 := by
    rcases h3602 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p626 := by
    rcases h3607 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p627 := by
    rcases h3612 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20788 (p616 p619 p623 p624 p625 p626 p627 p631 : Prop)
    (h3593 : p623 ∨ p631)
    (h3598 : p624 ∨ p631)
    (h3603 : p625 ∨ p631)
    (h3608 : p626 ∨ p631)
    (h3613 : p627 ∨ p631)
    (h3500 : p616 ∨ p619 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627)) : p631 ∨ p619 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p631) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p619) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p623 := by
    rcases h3593 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p624 := by
    rcases h3598 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p625 := by
    rcases h3603 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p626 := by
    rcases h3608 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p627 := by
    rcases h3613 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20789 (p616 p619 p623 p624 p625 p626 p627 p628 p629 p630 p631 p632 : Prop)
    (h3525 : p616 ∨ p619 ∨ (¬ p628) ∨ (¬ p629) ∨ (¬ p630) ∨ (¬ p631) ∨ (¬ p632))
    (h3594 : p623 ∨ p632)
    (h3599 : p624 ∨ p632)
    (h3604 : p625 ∨ p632)
    (h3609 : p626 ∨ p632)
    (h3614 : p627 ∨ p632)
    (h3500 : p616 ∨ p619 ∨ (¬ p623) ∨ (¬ p624) ∨ (¬ p625) ∨ (¬ p626) ∨ (¬ p627)) : (¬ p631) ∨ (¬ p630) ∨ p616 ∨ p619 ∨ (¬ p628) ∨ (¬ p629) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p631 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p630 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p616) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p619) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p628 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p629 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p632) := by
    rcases h3525 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p623 := by
    rcases h3594 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p624 := by
    rcases h3599 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p625 := by
    rcases h3604 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p626 := by
    rcases h3609 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p627 := by
    rcases h3614 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3500 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20790 (p616 p619 p628 p629 p630 p631 : Prop)
    (h20785 : p628 ∨ p619 ∨ p616)
    (h20786 : p629 ∨ p619 ∨ p616)
    (h20787 : p630 ∨ p619 ∨ p616)
    (h20788 : p631 ∨ p619 ∨ p616)
    (h20789 : (¬ p631) ∨ (¬ p630) ∨ p616 ∨ p619 ∨ (¬ p628) ∨ (¬ p629)) : p619 ∨ p616 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p619) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p616) := fun hu => hn (Or.inr hu)
  have u2 : p628 := by
    rcases h20785 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p629 := by
    rcases h20786 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p630 := by
    rcases h20787 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p631 := by
    rcases h20788 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20789 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20791 (p1187 p1192 p1196 p1197 p1198 p1199 p1200 p1201 : Prop)
    (h7163 : p1196 ∨ p1201)
    (h7168 : p1197 ∨ p1201)
    (h7173 : p1198 ∨ p1201)
    (h7178 : p1199 ∨ p1201)
    (h7183 : p1200 ∨ p1201)
    (h7073 : p1187 ∨ p1192 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1201 ∨ p1192 ∨ p1187 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1201) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1192) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1187) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1196 := by
    rcases h7163 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1197 := by
    rcases h7168 with q0 | q1
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
  rcases h7073 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20792 (p1187 p1192 p1196 p1197 p1198 p1199 p1200 p1202 : Prop)
    (h7164 : p1196 ∨ p1202)
    (h7169 : p1197 ∨ p1202)
    (h7174 : p1198 ∨ p1202)
    (h7179 : p1199 ∨ p1202)
    (h7184 : p1200 ∨ p1202)
    (h7073 : p1187 ∨ p1192 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1202 ∨ p1192 ∨ p1187 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1202) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1192) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1187) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1196 := by
    rcases h7164 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1197 := by
    rcases h7169 with q0 | q1
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
  rcases h7073 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20793 (p1187 p1192 p1196 p1197 p1198 p1199 p1200 p1203 : Prop)
    (h7165 : p1196 ∨ p1203)
    (h7170 : p1197 ∨ p1203)
    (h7175 : p1198 ∨ p1203)
    (h7180 : p1199 ∨ p1203)
    (h7185 : p1200 ∨ p1203)
    (h7073 : p1187 ∨ p1192 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1203 ∨ p1192 ∨ p1187 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1203) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1192) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1187) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1196 := by
    rcases h7165 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1197 := by
    rcases h7170 with q0 | q1
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
  rcases h7073 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20794 (p1187 p1192 p1196 p1197 p1198 p1199 p1200 p1204 : Prop)
    (h7166 : p1196 ∨ p1204)
    (h7171 : p1197 ∨ p1204)
    (h7176 : p1198 ∨ p1204)
    (h7181 : p1199 ∨ p1204)
    (h7186 : p1200 ∨ p1204)
    (h7073 : p1187 ∨ p1192 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : p1204 ∨ p1192 ∨ p1187 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1204) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1192) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1187) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1196 := by
    rcases h7166 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1197 := by
    rcases h7171 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1198 := by
    rcases h7176 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1199 := by
    rcases h7181 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1200 := by
    rcases h7186 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7073 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20795 (p1187 p1192 p1196 p1197 p1198 p1199 p1200 p1201 p1202 p1203 p1204 p1205 : Prop)
    (h7098 : p1187 ∨ p1192 ∨ (¬ p1201) ∨ (¬ p1202) ∨ (¬ p1203) ∨ (¬ p1204) ∨ (¬ p1205))
    (h7167 : p1196 ∨ p1205)
    (h7172 : p1197 ∨ p1205)
    (h7177 : p1198 ∨ p1205)
    (h7182 : p1199 ∨ p1205)
    (h7187 : p1200 ∨ p1205)
    (h7073 : p1187 ∨ p1192 ∨ (¬ p1196) ∨ (¬ p1197) ∨ (¬ p1198) ∨ (¬ p1199) ∨ (¬ p1200)) : (¬ p1204) ∨ (¬ p1203) ∨ p1187 ∨ p1192 ∨ (¬ p1201) ∨ (¬ p1202) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1204 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1203 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1187) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1192) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1201 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1202 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1205) := by
    rcases h7098 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1196 := by
    rcases h7167 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1197 := by
    rcases h7172 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1198 := by
    rcases h7177 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1199 := by
    rcases h7182 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1200 := by
    rcases h7187 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7073 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20796 (p1187 p1192 p1201 p1202 p1203 p1204 : Prop)
    (h20791 : p1201 ∨ p1192 ∨ p1187)
    (h20792 : p1202 ∨ p1192 ∨ p1187)
    (h20793 : p1203 ∨ p1192 ∨ p1187)
    (h20794 : p1204 ∨ p1192 ∨ p1187)
    (h20795 : (¬ p1204) ∨ (¬ p1203) ∨ p1187 ∨ p1192 ∨ (¬ p1201) ∨ (¬ p1202)) : p1192 ∨ p1187 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1192) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1187) := fun hu => hn (Or.inr hu)
  have u2 : p1201 := by
    rcases h20791 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1202 := by
    rcases h20792 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1203 := by
    rcases h20793 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1204 := by
    rcases h20794 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20795 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20797 (p1286 p1288 p1296 p1297 p1298 p1299 p1300 p1305 : Prop)
    (h7814 : p1296 ∨ p1305)
    (h7819 : p1297 ∨ p1305)
    (h7824 : p1298 ∨ p1305)
    (h7829 : p1299 ∨ p1305)
    (h7834 : p1300 ∨ p1305)
    (h7712 : p1286 ∨ p1288 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1305 ∨ p1286 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1305) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7814 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7819 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7824 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7829 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7834 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20798 (p1286 p1288 p1296 p1297 p1298 p1299 p1300 p1301 : Prop)
    (h7810 : p1296 ∨ p1301)
    (h7815 : p1297 ∨ p1301)
    (h7820 : p1298 ∨ p1301)
    (h7825 : p1299 ∨ p1301)
    (h7830 : p1300 ∨ p1301)
    (h7712 : p1286 ∨ p1288 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1301 ∨ p1286 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1301) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7810 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7815 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7820 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7825 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7830 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20799 (p1286 p1288 p1296 p1297 p1298 p1299 p1300 p1302 : Prop)
    (h7811 : p1296 ∨ p1302)
    (h7816 : p1297 ∨ p1302)
    (h7821 : p1298 ∨ p1302)
    (h7826 : p1299 ∨ p1302)
    (h7831 : p1300 ∨ p1302)
    (h7712 : p1286 ∨ p1288 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1302 ∨ p1286 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1302) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7811 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7816 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7821 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7826 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7831 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20800 (p1286 p1288 p1296 p1297 p1298 p1299 p1300 p1303 : Prop)
    (h7812 : p1296 ∨ p1303)
    (h7817 : p1297 ∨ p1303)
    (h7822 : p1298 ∨ p1303)
    (h7827 : p1299 ∨ p1303)
    (h7832 : p1300 ∨ p1303)
    (h7712 : p1286 ∨ p1288 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1303 ∨ p1286 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1303) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7812 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7817 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7822 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7827 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7832 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20802 (p1288 p1292 p1296 p1297 p1298 p1299 p1300 p1304 : Prop)
    (h7813 : p1296 ∨ p1304)
    (h7818 : p1297 ∨ p1304)
    (h7823 : p1298 ∨ p1304)
    (h7828 : p1299 ∨ p1304)
    (h7833 : p1300 ∨ p1304)
    (h7710 : p1288 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : p1304 ∨ p1292 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1304) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1292) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1296 := by
    rcases h7813 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1297 := by
    rcases h7818 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1298 := by
    rcases h7823 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1299 := by
    rcases h7828 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1300 := by
    rcases h7833 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20803 (p1288 p1292 p1296 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h20802 : p1304 ∨ p1292 ∨ p1288)
    (h7810 : p1296 ∨ p1301)
    (h7811 : p1296 ∨ p1302)
    (h7812 : p1296 ∨ p1303)
    (h7814 : p1296 ∨ p1305)
    (h7735 : p1288 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1296 ∨ p1292 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1296) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1292) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1304 := by
    rcases h20802 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1301 := by
    rcases h7810 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1302 := by
    rcases h7811 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1303 := by
    rcases h7812 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7814 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7735 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step20804 (p1288 p1292 p1297 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h20802 : p1304 ∨ p1292 ∨ p1288)
    (h7815 : p1297 ∨ p1301)
    (h7816 : p1297 ∨ p1302)
    (h7817 : p1297 ∨ p1303)
    (h7819 : p1297 ∨ p1305)
    (h7735 : p1288 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1297 ∨ p1292 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1297) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1292) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1304 := by
    rcases h20802 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1301 := by
    rcases h7815 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1302 := by
    rcases h7816 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1303 := by
    rcases h7817 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7819 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7735 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step20805 (p1288 p1292 p1298 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h20802 : p1304 ∨ p1292 ∨ p1288)
    (h7820 : p1298 ∨ p1301)
    (h7821 : p1298 ∨ p1302)
    (h7822 : p1298 ∨ p1303)
    (h7824 : p1298 ∨ p1305)
    (h7735 : p1288 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1298 ∨ p1292 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1298) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1292) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1304 := by
    rcases h20802 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1301 := by
    rcases h7820 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1302 := by
    rcases h7821 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1303 := by
    rcases h7822 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7824 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7735 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step20806 (p1288 p1292 p1299 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h20802 : p1304 ∨ p1292 ∨ p1288)
    (h7825 : p1299 ∨ p1301)
    (h7826 : p1299 ∨ p1302)
    (h7827 : p1299 ∨ p1303)
    (h7829 : p1299 ∨ p1305)
    (h7735 : p1288 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1299 ∨ p1292 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1299) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1292) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1288) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1304 := by
    rcases h20802 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p1301 := by
    rcases h7825 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1302 := by
    rcases h7826 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1303 := by
    rcases h7827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1305 := by
    rcases h7829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h7735 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step20807 (p1288 p1292 p1296 p1297 p1298 p1299 p1300 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h20802 : p1304 ∨ p1292 ∨ p1288)
    (h20803 : p1296 ∨ p1292 ∨ p1288)
    (h20804 : p1297 ∨ p1292 ∨ p1288)
    (h20805 : p1298 ∨ p1292 ∨ p1288)
    (h20806 : p1299 ∨ p1292 ∨ p1288)
    (h7710 : p1288 ∨ p1292 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300))
    (h7830 : p1300 ∨ p1301)
    (h7831 : p1300 ∨ p1302)
    (h7832 : p1300 ∨ p1303)
    (h7834 : p1300 ∨ p1305)
    (h7735 : p1288 ∨ p1292 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305)) : p1292 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1292) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1288) := fun hu => hn (Or.inr hu)
  have u2 : p1304 := by
    rcases h20802 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1296 := by
    rcases h20803 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1297 := by
    rcases h20804 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1298 := by
    rcases h20805 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1299 := by
    rcases h20806 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1300) := by
    rcases h7710 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1301 := by
    rcases h7830 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p1302 := by
    rcases h7831 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p1303 := by
    rcases h7832 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p1305 := by
    rcases h7834 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h7735 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step20808 (p419 p595 p616 p1195 p1229 p1288 p1292 : Prop)
    (h10651 : (¬ p595) ∨ (¬ p616))
    (h10625 : p595 ∨ (¬ p1229) ∨ (¬ p1288))
    (h16747 : (¬ p419) ∨ (¬ p616) ∨ (¬ p1195) ∨ (¬ p1229) ∨ (¬ p1292))
    (h20807 : p1292 ∨ p1288) : (¬ p1229) ∨ (¬ p419) ∨ (¬ p616) ∨ (¬ p1195) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1229 := by
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
  have u3 : p1195 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p595) := by
    rcases h10651 with q0 | q1
    · exact q0
    · exact False.elim (q1 u2)
  have u5 : (¬ p1288) := by
    rcases h10625 with q0 | q1 | q2
    · exact False.elim (u4 q0)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p1292) := by
    rcases h16747 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u1)
    · exact False.elim (q1 u2)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact q4
  rcases h20807 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step20809 (p224 p657 p670 p671 p672 p673 p674 p679 : Prop)
    (h3863 : p670 ∨ p679)
    (h3868 : p671 ∨ p679)
    (h3873 : p672 ∨ p679)
    (h3878 : p673 ∨ p679)
    (h3883 : p674 ∨ p679)
    (h3771 : p224 ∨ p657 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674)) : p679 ∨ p224 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p679) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3771 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20810 (p224 p657 p670 p675 p676 p677 p678 p679 : Prop)
    (h20809 : p679 ∨ p224 ∨ p657)
    (h3859 : p670 ∨ p675)
    (h3860 : p670 ∨ p676)
    (h3861 : p670 ∨ p677)
    (h3862 : p670 ∨ p678)
    (h3796 : p224 ∨ p657 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p670 ∨ p224 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p670) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h20809 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
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
  rcases h3796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20811 (p224 p657 p671 p675 p676 p677 p678 p679 : Prop)
    (h20809 : p679 ∨ p224 ∨ p657)
    (h3864 : p671 ∨ p675)
    (h3865 : p671 ∨ p676)
    (h3866 : p671 ∨ p677)
    (h3867 : p671 ∨ p678)
    (h3796 : p224 ∨ p657 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p671 ∨ p224 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p671) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h20809 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
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
  rcases h3796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20812 (p224 p657 p672 p675 p676 p677 p678 p679 : Prop)
    (h20809 : p679 ∨ p224 ∨ p657)
    (h3869 : p672 ∨ p675)
    (h3870 : p672 ∨ p676)
    (h3871 : p672 ∨ p677)
    (h3872 : p672 ∨ p678)
    (h3796 : p224 ∨ p657 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p672 ∨ p224 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p672) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h20809 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
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
  rcases h3796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20813 (p224 p657 p673 p675 p676 p677 p678 p679 : Prop)
    (h20809 : p679 ∨ p224 ∨ p657)
    (h3874 : p673 ∨ p675)
    (h3875 : p673 ∨ p676)
    (h3876 : p673 ∨ p677)
    (h3877 : p673 ∨ p678)
    (h3796 : p224 ∨ p657 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p673 ∨ p224 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p673) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p224) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p657) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p679 := by
    rcases h20809 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
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
  rcases h3796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20814 (p224 p657 p670 p671 p672 p673 p674 p675 p676 p677 p678 p679 : Prop)
    (h20809 : p679 ∨ p224 ∨ p657)
    (h20810 : p670 ∨ p224 ∨ p657)
    (h20811 : p671 ∨ p224 ∨ p657)
    (h20812 : p672 ∨ p224 ∨ p657)
    (h20813 : p673 ∨ p224 ∨ p657)
    (h3771 : p224 ∨ p657 ∨ (¬ p670) ∨ (¬ p671) ∨ (¬ p672) ∨ (¬ p673) ∨ (¬ p674))
    (h3879 : p674 ∨ p675)
    (h3880 : p674 ∨ p676)
    (h3881 : p674 ∨ p677)
    (h3882 : p674 ∨ p678)
    (h3796 : p224 ∨ p657 ∨ (¬ p675) ∨ (¬ p676) ∨ (¬ p677) ∨ (¬ p678) ∨ (¬ p679)) : p224 ∨ p657 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p224) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p657) := fun hu => hn (Or.inr hu)
  have u2 : p679 := by
    rcases h20809 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p670 := by
    rcases h20810 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p671 := by
    rcases h20811 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p672 := by
    rcases h20812 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p673 := by
    rcases h20813 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p674) := by
    rcases h3771 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h3796 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step20815 (p1286 p1288 p1296 p1297 p1298 p1299 p1300 p1301 p1302 p1303 p1304 p1305 : Prop)
    (h7737 : p1286 ∨ p1288 ∨ (¬ p1301) ∨ (¬ p1302) ∨ (¬ p1303) ∨ (¬ p1304) ∨ (¬ p1305))
    (h7813 : p1296 ∨ p1304)
    (h7818 : p1297 ∨ p1304)
    (h7823 : p1298 ∨ p1304)
    (h7828 : p1299 ∨ p1304)
    (h7833 : p1300 ∨ p1304)
    (h7712 : p1286 ∨ p1288 ∨ (¬ p1296) ∨ (¬ p1297) ∨ (¬ p1298) ∨ (¬ p1299) ∨ (¬ p1300)) : (¬ p1302) ∨ p1288 ∨ p1286 ∨ (¬ p1301) ∨ (¬ p1305) ∨ (¬ p1303) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1302 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1288) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1286) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1301 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1305 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1304) := by
    rcases h7737 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u5)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p1296 := by
    rcases h7813 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1297 := by
    rcases h7818 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1298 := by
    rcases h7823 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1299 := by
    rcases h7828 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1300 := by
    rcases h7833 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7712 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20816 (p1286 p1288 p1301 p1302 p1303 p1305 : Prop)
    (h20797 : p1305 ∨ p1286 ∨ p1288)
    (h20798 : p1301 ∨ p1286 ∨ p1288)
    (h20799 : p1302 ∨ p1286 ∨ p1288)
    (h20800 : p1303 ∨ p1286 ∨ p1288)
    (h20815 : (¬ p1302) ∨ p1288 ∨ p1286 ∨ (¬ p1301) ∨ (¬ p1305) ∨ (¬ p1303)) : p1286 ∨ p1288 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1286) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1288) := fun hu => hn (Or.inr hu)
  have u2 : p1305 := by
    rcases h20797 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1301 := by
    rcases h20798 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1302 := by
    rcases h20799 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1303 := by
    rcases h20800 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20815 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u4)
  · exact False.elim (u1 q1)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)

theorem step20817 (p1385 p1395 p1396 p1397 p1398 p1399 p1400 p1401 : Prop)
    (h8449 : p1396 ∨ p1401)
    (h8454 : p1397 ∨ p1401)
    (h8459 : p1398 ∨ p1401)
    (h8464 : p1399 ∨ p1401)
    (h8469 : p1400 ∨ p1401)
    (h8363 : p1385 ∨ p1395 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1401 ∨ p1395 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1401) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1395) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1396 := by
    rcases h8449 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1397 := by
    rcases h8454 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1398 := by
    rcases h8459 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1399 := by
    rcases h8464 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1400 := by
    rcases h8469 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20818 (p1385 p1395 p1396 p1397 p1398 p1399 p1400 p1402 : Prop)
    (h8450 : p1396 ∨ p1402)
    (h8455 : p1397 ∨ p1402)
    (h8460 : p1398 ∨ p1402)
    (h8465 : p1399 ∨ p1402)
    (h8470 : p1400 ∨ p1402)
    (h8363 : p1385 ∨ p1395 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1402 ∨ p1395 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1402) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1395) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1396 := by
    rcases h8450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1397 := by
    rcases h8455 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1398 := by
    rcases h8460 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1399 := by
    rcases h8465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1400 := by
    rcases h8470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20819 (p1385 p1395 p1396 p1397 p1398 p1399 p1400 p1403 : Prop)
    (h8451 : p1396 ∨ p1403)
    (h8456 : p1397 ∨ p1403)
    (h8461 : p1398 ∨ p1403)
    (h8466 : p1399 ∨ p1403)
    (h8471 : p1400 ∨ p1403)
    (h8363 : p1385 ∨ p1395 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1403 ∨ p1395 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1403) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1395) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1396 := by
    rcases h8451 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1397 := by
    rcases h8456 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1398 := by
    rcases h8461 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1399 := by
    rcases h8466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1400 := by
    rcases h8471 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20820 (p1385 p1395 p1396 p1397 p1398 p1399 p1400 p1404 : Prop)
    (h8452 : p1396 ∨ p1404)
    (h8457 : p1397 ∨ p1404)
    (h8462 : p1398 ∨ p1404)
    (h8467 : p1399 ∨ p1404)
    (h8472 : p1400 ∨ p1404)
    (h8363 : p1385 ∨ p1395 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1404 ∨ p1395 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1404) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1395) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1396 := by
    rcases h8452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1397 := by
    rcases h8457 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1398 := by
    rcases h8462 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1399 := by
    rcases h8467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1400 := by
    rcases h8472 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20821 (p1385 p1388 p1395 p1396 p1397 p1398 p1399 p1400 p1401 p1402 p1403 p1404 p1405 : Prop)
    (h20817 : p1401 ∨ p1395 ∨ p1385)
    (h20818 : p1402 ∨ p1395 ∨ p1385)
    (h20819 : p1403 ∨ p1395 ∨ p1385)
    (h20820 : p1404 ∨ p1395 ∨ p1385)
    (h8383 : p1388 ∨ p1395 ∨ (¬ p1401) ∨ (¬ p1402) ∨ (¬ p1403) ∨ (¬ p1404) ∨ (¬ p1405))
    (h8453 : p1396 ∨ p1405)
    (h8458 : p1397 ∨ p1405)
    (h8463 : p1398 ∨ p1405)
    (h8468 : p1399 ∨ p1405)
    (h8473 : p1400 ∨ p1405)
    (h8363 : p1385 ∨ p1395 ∨ (¬ p1396) ∨ (¬ p1397) ∨ (¬ p1398) ∨ (¬ p1399) ∨ (¬ p1400)) : p1395 ∨ p1388 ∨ p1385 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1395) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1388) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1385) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1401 := by
    rcases h20817 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p1402 := by
    rcases h20818 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p1403 := by
    rcases h20819 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p1404 := by
    rcases h20820 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p1405) := by
    rcases h8383 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p1396 := by
    rcases h8453 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1397 := by
    rcases h8458 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1398 := by
    rcases h8463 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1399 := by
    rcases h8468 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p1400 := by
    rcases h8473 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h8363 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step20822 (p1545 p1548 p1552 p1553 p1554 p1555 p1556 p1557 : Prop)
    (h9525 : p1552 ∨ p1557)
    (h9530 : p1553 ∨ p1557)
    (h9535 : p1554 ∨ p1557)
    (h9540 : p1555 ∨ p1557)
    (h9545 : p1556 ∨ p1557)
    (h9435 : p1545 ∨ p1548 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1557 ∨ p1548 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1557) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1548) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9525 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9530 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9535 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9540 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9545 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9435 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20823 (p1545 p1548 p1552 p1553 p1554 p1555 p1556 p1558 : Prop)
    (h9526 : p1552 ∨ p1558)
    (h9531 : p1553 ∨ p1558)
    (h9536 : p1554 ∨ p1558)
    (h9541 : p1555 ∨ p1558)
    (h9546 : p1556 ∨ p1558)
    (h9435 : p1545 ∨ p1548 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1558 ∨ p1548 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1558) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1548) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9526 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9531 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9536 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9541 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9546 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9435 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20824 (p1545 p1548 p1552 p1553 p1554 p1555 p1556 p1559 : Prop)
    (h9527 : p1552 ∨ p1559)
    (h9532 : p1553 ∨ p1559)
    (h9537 : p1554 ∨ p1559)
    (h9542 : p1555 ∨ p1559)
    (h9547 : p1556 ∨ p1559)
    (h9435 : p1545 ∨ p1548 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1559 ∨ p1548 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1559) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1548) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9527 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9532 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9537 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9542 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9547 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9435 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20825 (p1545 p1548 p1552 p1553 p1554 p1555 p1556 p1560 : Prop)
    (h9528 : p1552 ∨ p1560)
    (h9533 : p1553 ∨ p1560)
    (h9538 : p1554 ∨ p1560)
    (h9543 : p1555 ∨ p1560)
    (h9548 : p1556 ∨ p1560)
    (h9435 : p1545 ∨ p1548 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1560 ∨ p1548 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1560) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1548) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9528 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9533 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9538 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9543 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9548 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9435 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20826 (p1545 p1548 p1552 p1553 p1554 p1555 p1556 p1557 p1558 p1559 p1560 p1561 : Prop)
    (h9460 : p1545 ∨ p1548 ∨ (¬ p1557) ∨ (¬ p1558) ∨ (¬ p1559) ∨ (¬ p1560) ∨ (¬ p1561))
    (h9529 : p1552 ∨ p1561)
    (h9534 : p1553 ∨ p1561)
    (h9539 : p1554 ∨ p1561)
    (h9544 : p1555 ∨ p1561)
    (h9549 : p1556 ∨ p1561)
    (h9435 : p1545 ∨ p1548 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : (¬ p1560) ∨ (¬ p1559) ∨ p1545 ∨ p1548 ∨ (¬ p1557) ∨ (¬ p1558) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1560 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1548) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1558 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1561) := by
    rcases h9460 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1552 := by
    rcases h9529 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1553 := by
    rcases h9534 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1554 := by
    rcases h9539 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1555 := by
    rcases h9544 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1556 := by
    rcases h9549 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h9435 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20827 (p1545 p1548 p1557 p1558 p1559 p1560 : Prop)
    (h20822 : p1557 ∨ p1548 ∨ p1545)
    (h20823 : p1558 ∨ p1548 ∨ p1545)
    (h20824 : p1559 ∨ p1548 ∨ p1545)
    (h20825 : p1560 ∨ p1548 ∨ p1545)
    (h20826 : (¬ p1560) ∨ (¬ p1559) ∨ p1545 ∨ p1548 ∨ (¬ p1557) ∨ (¬ p1558)) : p1548 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1548) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1545) := fun hu => hn (Or.inr hu)
  have u2 : p1557 := by
    rcases h20822 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1558 := by
    rcases h20823 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1559 := by
    rcases h20824 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1560 := by
    rcases h20825 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20826 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20828 (p598 p600 p604 p605 p606 p607 p608 p609 : Prop)
    (h3465 : p604 ∨ p609)
    (h3470 : p605 ∨ p609)
    (h3475 : p606 ∨ p609)
    (h3480 : p607 ∨ p609)
    (h3485 : p608 ∨ p609)
    (h3381 : p598 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p609 ∨ p598 ∨ p600 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p609) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p598) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p600) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3475 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3480 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3485 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3381 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20829 (p598 p600 p604 p605 p606 p607 p608 p610 : Prop)
    (h3466 : p604 ∨ p610)
    (h3471 : p605 ∨ p610)
    (h3476 : p606 ∨ p610)
    (h3481 : p607 ∨ p610)
    (h3486 : p608 ∨ p610)
    (h3381 : p598 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p610 ∨ p598 ∨ p600 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p610) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p598) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p600) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3471 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3476 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3481 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3486 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3381 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20830 (p598 p600 p604 p605 p606 p607 p608 p611 : Prop)
    (h3467 : p604 ∨ p611)
    (h3472 : p605 ∨ p611)
    (h3477 : p606 ∨ p611)
    (h3482 : p607 ∨ p611)
    (h3487 : p608 ∨ p611)
    (h3381 : p598 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p611 ∨ p598 ∨ p600 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p611) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p598) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p600) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3472 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3477 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3482 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3487 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3381 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20831 (p598 p600 p604 p605 p606 p607 p608 p612 : Prop)
    (h3468 : p604 ∨ p612)
    (h3473 : p605 ∨ p612)
    (h3478 : p606 ∨ p612)
    (h3483 : p607 ∨ p612)
    (h3488 : p608 ∨ p612)
    (h3381 : p598 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p612 ∨ p598 ∨ p600 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p612) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p598) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p600) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3468 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3473 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3478 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3483 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3488 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3381 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20832 (p598 p600 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h3406 : p598 ∨ p600 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613))
    (h3469 : p604 ∨ p613)
    (h3474 : p605 ∨ p613)
    (h3479 : p606 ∨ p613)
    (h3484 : p607 ∨ p613)
    (h3489 : p608 ∨ p613)
    (h3381 : p598 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : (¬ p612) ∨ (¬ p611) ∨ p600 ∨ p598 ∨ (¬ p609) ∨ (¬ p610) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p612 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p600) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p598) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p609 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p610 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p613) := by
    rcases h3406 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p604 := by
    rcases h3469 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p605 := by
    rcases h3474 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p606 := by
    rcases h3479 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p607 := by
    rcases h3484 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p608 := by
    rcases h3489 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3381 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20833 (p598 p600 p609 p610 p611 p612 : Prop)
    (h20828 : p609 ∨ p598 ∨ p600)
    (h20829 : p610 ∨ p598 ∨ p600)
    (h20830 : p611 ∨ p598 ∨ p600)
    (h20831 : p612 ∨ p598 ∨ p600)
    (h20832 : (¬ p612) ∨ (¬ p611) ∨ p600 ∨ p598 ∨ (¬ p609) ∨ (¬ p610)) : p598 ∨ p600 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p598) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p600) := fun hu => hn (Or.inr hu)
  have u2 : p609 := by
    rcases h20828 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p610 := by
    rcases h20829 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p611 := by
    rcases h20830 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p612 := by
    rcases h20831 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20832 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20835 (p634 p639 p643 p644 p645 p646 p647 p648 : Prop)
    (h3716 : p643 ∨ p648)
    (h3721 : p644 ∨ p648)
    (h3726 : p645 ∨ p648)
    (h3731 : p646 ∨ p648)
    (h3736 : p647 ∨ p648)
    (h3616 : p634 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p648 ∨ p639 ∨ p634 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p648) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p639) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p634) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p643 := by
    rcases h3716 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p644 := by
    rcases h3721 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p645 := by
    rcases h3726 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p646 := by
    rcases h3731 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3736 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20836 (p634 p639 p643 p644 p645 p646 p647 p649 : Prop)
    (h3717 : p643 ∨ p649)
    (h3722 : p644 ∨ p649)
    (h3727 : p645 ∨ p649)
    (h3732 : p646 ∨ p649)
    (h3737 : p647 ∨ p649)
    (h3616 : p634 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p649 ∨ p639 ∨ p634 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p649) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p639) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p634) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p643 := by
    rcases h3717 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p644 := by
    rcases h3722 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p645 := by
    rcases h3727 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p646 := by
    rcases h3732 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3737 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20837 (p634 p639 p643 p644 p645 p646 p647 p650 : Prop)
    (h3718 : p643 ∨ p650)
    (h3723 : p644 ∨ p650)
    (h3728 : p645 ∨ p650)
    (h3733 : p646 ∨ p650)
    (h3738 : p647 ∨ p650)
    (h3616 : p634 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p650 ∨ p639 ∨ p634 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p650) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p639) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p634) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p643 := by
    rcases h3718 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p644 := by
    rcases h3723 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p645 := by
    rcases h3728 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p646 := by
    rcases h3733 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3738 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20838 (p634 p639 p643 p644 p645 p646 p647 p651 : Prop)
    (h3719 : p643 ∨ p651)
    (h3724 : p644 ∨ p651)
    (h3729 : p645 ∨ p651)
    (h3734 : p646 ∨ p651)
    (h3739 : p647 ∨ p651)
    (h3616 : p634 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : p651 ∨ p639 ∨ p634 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p651) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p639) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p634) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p643 := by
    rcases h3719 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p644 := by
    rcases h3724 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p645 := by
    rcases h3729 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p646 := by
    rcases h3734 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p647 := by
    rcases h3739 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20839 (p634 p639 p643 p644 p645 p646 p647 p648 p649 p650 p651 p652 : Prop)
    (h3641 : p634 ∨ p639 ∨ (¬ p648) ∨ (¬ p649) ∨ (¬ p650) ∨ (¬ p651) ∨ (¬ p652))
    (h3720 : p643 ∨ p652)
    (h3725 : p644 ∨ p652)
    (h3730 : p645 ∨ p652)
    (h3735 : p646 ∨ p652)
    (h3740 : p647 ∨ p652)
    (h3616 : p634 ∨ p639 ∨ (¬ p643) ∨ (¬ p644) ∨ (¬ p645) ∨ (¬ p646) ∨ (¬ p647)) : (¬ p651) ∨ (¬ p650) ∨ p639 ∨ p634 ∨ (¬ p648) ∨ (¬ p649) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p651 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p650 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p639) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p634) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p648 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p649 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p652) := by
    rcases h3641 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p643 := by
    rcases h3720 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p644 := by
    rcases h3725 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p645 := by
    rcases h3730 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p646 := by
    rcases h3735 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p647 := by
    rcases h3740 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3616 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20840 (p634 p639 p648 p649 p650 p651 : Prop)
    (h20835 : p648 ∨ p639 ∨ p634)
    (h20836 : p649 ∨ p639 ∨ p634)
    (h20837 : p650 ∨ p639 ∨ p634)
    (h20838 : p651 ∨ p639 ∨ p634)
    (h20839 : (¬ p651) ∨ (¬ p650) ∨ p639 ∨ p634 ∨ (¬ p648) ∨ (¬ p649)) : p639 ∨ p634 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p639) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p634) := fun hu => hn (Or.inr hu)
  have u2 : p648 := by
    rcases h20835 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p649 := by
    rcases h20836 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p650 := by
    rcases h20837 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p651 := by
    rcases h20838 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20839 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20841 (p710 p713 p716 p717 p718 p719 p720 p721 : Prop)
    (h4124 : p716 ∨ p721)
    (h4129 : p717 ∨ p721)
    (h4134 : p718 ∨ p721)
    (h4139 : p719 ∨ p721)
    (h4144 : p720 ∨ p721)
    (h4034 : p710 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : p721 ∨ p713 ∨ p710 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p721) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p710) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p716 := by
    rcases h4124 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p717 := by
    rcases h4129 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p718 := by
    rcases h4134 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p719 := by
    rcases h4139 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p720 := by
    rcases h4144 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20842 (p710 p713 p716 p717 p718 p719 p720 p722 : Prop)
    (h4125 : p716 ∨ p722)
    (h4130 : p717 ∨ p722)
    (h4135 : p718 ∨ p722)
    (h4140 : p719 ∨ p722)
    (h4145 : p720 ∨ p722)
    (h4034 : p710 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : p722 ∨ p713 ∨ p710 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p722) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p710) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p716 := by
    rcases h4125 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p717 := by
    rcases h4130 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p718 := by
    rcases h4135 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p719 := by
    rcases h4140 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p720 := by
    rcases h4145 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20843 (p710 p713 p716 p717 p718 p719 p720 p723 : Prop)
    (h4126 : p716 ∨ p723)
    (h4131 : p717 ∨ p723)
    (h4136 : p718 ∨ p723)
    (h4141 : p719 ∨ p723)
    (h4146 : p720 ∨ p723)
    (h4034 : p710 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : p723 ∨ p713 ∨ p710 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p723) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p710) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p716 := by
    rcases h4126 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p717 := by
    rcases h4131 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p718 := by
    rcases h4136 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p719 := by
    rcases h4141 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p720 := by
    rcases h4146 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20844 (p710 p713 p716 p717 p718 p719 p720 p724 : Prop)
    (h4127 : p716 ∨ p724)
    (h4132 : p717 ∨ p724)
    (h4137 : p718 ∨ p724)
    (h4142 : p719 ∨ p724)
    (h4147 : p720 ∨ p724)
    (h4034 : p710 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : p724 ∨ p713 ∨ p710 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p724) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p710) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20845 (p709 p710 p713 p716 p717 p718 p719 p720 p721 p722 p723 p724 p725 : Prop)
    (h20841 : p721 ∨ p713 ∨ p710)
    (h20842 : p722 ∨ p713 ∨ p710)
    (h20843 : p723 ∨ p713 ∨ p710)
    (h20844 : p724 ∨ p713 ∨ p710)
    (h4049 : p709 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725))
    (h4128 : p716 ∨ p725)
    (h4133 : p717 ∨ p725)
    (h4138 : p718 ∨ p725)
    (h4143 : p719 ∨ p725)
    (h4148 : p720 ∨ p725)
    (h4034 : p710 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : p713 ∨ p709 ∨ p710 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p713) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p709) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p710) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p721 := by
    rcases h20841 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p722 := by
    rcases h20842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p723 := by
    rcases h20843 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p724 := by
    rcases h20844 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p725) := by
    rcases h4049 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p716 := by
    rcases h4128 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p717 := by
    rcases h4133 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p718 := by
    rcases h4138 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p719 := by
    rcases h4143 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p720 := by
    rcases h4148 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h4034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step20846 (p1542 p1545 p1552 p1553 p1554 p1555 p1556 p1561 : Prop)
    (h9529 : p1552 ∨ p1561)
    (h9534 : p1553 ∨ p1561)
    (h9539 : p1554 ∨ p1561)
    (h9544 : p1555 ∨ p1561)
    (h9549 : p1556 ∨ p1561)
    (h9437 : p1542 ∨ p1545 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1561 ∨ p1542 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1561) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1542) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9529 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9534 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9539 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9544 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9549 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20847 (p1542 p1545 p1552 p1553 p1554 p1555 p1556 p1557 : Prop)
    (h9525 : p1552 ∨ p1557)
    (h9530 : p1553 ∨ p1557)
    (h9535 : p1554 ∨ p1557)
    (h9540 : p1555 ∨ p1557)
    (h9545 : p1556 ∨ p1557)
    (h9437 : p1542 ∨ p1545 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1557 ∨ p1542 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1557) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1542) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9525 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9530 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9535 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9540 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9545 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20848 (p1542 p1545 p1552 p1553 p1554 p1555 p1556 p1558 : Prop)
    (h9526 : p1552 ∨ p1558)
    (h9531 : p1553 ∨ p1558)
    (h9536 : p1554 ∨ p1558)
    (h9541 : p1555 ∨ p1558)
    (h9546 : p1556 ∨ p1558)
    (h9437 : p1542 ∨ p1545 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1558 ∨ p1542 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1558) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1542) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9526 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9531 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9536 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9541 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9546 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20849 (p1542 p1545 p1552 p1553 p1554 p1555 p1556 p1559 : Prop)
    (h9527 : p1552 ∨ p1559)
    (h9532 : p1553 ∨ p1559)
    (h9537 : p1554 ∨ p1559)
    (h9542 : p1555 ∨ p1559)
    (h9547 : p1556 ∨ p1559)
    (h9437 : p1542 ∨ p1545 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : p1559 ∨ p1542 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1559) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1542) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1552 := by
    rcases h9527 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1553 := by
    rcases h9532 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1554 := by
    rcases h9537 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1555 := by
    rcases h9542 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1556 := by
    rcases h9547 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20850 (p1542 p1545 p1552 p1553 p1554 p1555 p1556 p1557 p1558 p1559 p1560 p1561 : Prop)
    (h9462 : p1542 ∨ p1545 ∨ (¬ p1557) ∨ (¬ p1558) ∨ (¬ p1559) ∨ (¬ p1560) ∨ (¬ p1561))
    (h9528 : p1552 ∨ p1560)
    (h9533 : p1553 ∨ p1560)
    (h9538 : p1554 ∨ p1560)
    (h9543 : p1555 ∨ p1560)
    (h9548 : p1556 ∨ p1560)
    (h9437 : p1542 ∨ p1545 ∨ (¬ p1552) ∨ (¬ p1553) ∨ (¬ p1554) ∨ (¬ p1555) ∨ (¬ p1556)) : (¬ p1559) ∨ (¬ p1561) ∨ p1545 ∨ p1542 ∨ (¬ p1557) ∨ (¬ p1558) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1559 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1561 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1545) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1542) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1557 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1558 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1560) := by
    rcases h9462 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u1)
  have u7 : p1552 := by
    rcases h9528 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1553 := by
    rcases h9533 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1554 := by
    rcases h9538 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1555 := by
    rcases h9543 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1556 := by
    rcases h9548 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h9437 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20851 (p1542 p1545 p1557 p1558 p1559 p1561 : Prop)
    (h20846 : p1561 ∨ p1542 ∨ p1545)
    (h20847 : p1557 ∨ p1542 ∨ p1545)
    (h20848 : p1558 ∨ p1542 ∨ p1545)
    (h20849 : p1559 ∨ p1542 ∨ p1545)
    (h20850 : (¬ p1559) ∨ (¬ p1561) ∨ p1545 ∨ p1542 ∨ (¬ p1557) ∨ (¬ p1558)) : p1542 ∨ p1545 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1542) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1545) := fun hu => hn (Or.inr hu)
  have u2 : p1561 := by
    rcases h20846 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1557 := by
    rcases h20847 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1558 := by
    rcases h20848 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1559 := by
    rcases h20849 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20850 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step20853 (p710 p713 p716 p717 p718 p719 p720 p721 p722 p723 p724 p725 : Prop)
    (h4059 : p710 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) ∨ (¬ p723) ∨ (¬ p724) ∨ (¬ p725))
    (h4128 : p716 ∨ p725)
    (h4133 : p717 ∨ p725)
    (h4138 : p718 ∨ p725)
    (h4143 : p719 ∨ p725)
    (h4148 : p720 ∨ p725)
    (h4034 : p710 ∨ p713 ∨ (¬ p716) ∨ (¬ p717) ∨ (¬ p718) ∨ (¬ p719) ∨ (¬ p720)) : (¬ p724) ∨ (¬ p723) ∨ p710 ∨ p713 ∨ (¬ p721) ∨ (¬ p722) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p724 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p723 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p710) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p713) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p721 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p722 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p725) := by
    rcases h4059 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p716 := by
    rcases h4128 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p717 := by
    rcases h4133 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p718 := by
    rcases h4138 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p719 := by
    rcases h4143 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p720 := by
    rcases h4148 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4034 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20854 (p710 p713 p721 p722 p723 p724 : Prop)
    (h20841 : p721 ∨ p713 ∨ p710)
    (h20842 : p722 ∨ p713 ∨ p710)
    (h20843 : p723 ∨ p713 ∨ p710)
    (h20844 : p724 ∨ p713 ∨ p710)
    (h20853 : (¬ p724) ∨ (¬ p723) ∨ p710 ∨ p713 ∨ (¬ p721) ∨ (¬ p722)) : p710 ∨ p713 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p710) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p713) := fun hu => hn (Or.inr hu)
  have u2 : p721 := by
    rcases h20841 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u3 : p722 := by
    rcases h20842 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u4 : p723 := by
    rcases h20843 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  have u5 : p724 := by
    rcases h20844 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u0 q2)
  rcases h20853 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20855 (p576 p579 p584 p585 p586 p587 p588 p589 : Prop)
    (h3338 : p584 ∨ p589)
    (h3343 : p585 ∨ p589)
    (h3348 : p586 ∨ p589)
    (h3353 : p587 ∨ p589)
    (h3358 : p588 ∨ p589)
    (h3248 : p576 ∨ p579 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p589 ∨ p576 ∨ p579 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p589) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p579) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3348 with q0 | q1
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
  rcases h3248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20856 (p576 p579 p584 p585 p586 p587 p588 p590 : Prop)
    (h3339 : p584 ∨ p590)
    (h3344 : p585 ∨ p590)
    (h3349 : p586 ∨ p590)
    (h3354 : p587 ∨ p590)
    (h3359 : p588 ∨ p590)
    (h3248 : p576 ∨ p579 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p590 ∨ p576 ∨ p579 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p590) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p579) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3339 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3349 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3354 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3359 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20857 (p576 p579 p584 p585 p586 p587 p588 p591 : Prop)
    (h3340 : p584 ∨ p591)
    (h3345 : p585 ∨ p591)
    (h3350 : p586 ∨ p591)
    (h3355 : p587 ∨ p591)
    (h3360 : p588 ∨ p591)
    (h3248 : p576 ∨ p579 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p591 ∨ p576 ∨ p579 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p591) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p579) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3340 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3345 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3350 with q0 | q1
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
  rcases h3248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20858 (p576 p579 p584 p585 p586 p587 p588 p592 : Prop)
    (h3341 : p584 ∨ p592)
    (h3346 : p585 ∨ p592)
    (h3351 : p586 ∨ p592)
    (h3356 : p587 ∨ p592)
    (h3361 : p588 ∨ p592)
    (h3248 : p576 ∨ p579 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p592 ∨ p576 ∨ p579 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p592) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p579) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3341 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3346 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3351 with q0 | q1
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
  rcases h3248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20859 (p576 p579 p584 p585 p586 p587 p588 p589 p590 p591 p592 p593 : Prop)
    (h3273 : p576 ∨ p579 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593))
    (h3342 : p584 ∨ p593)
    (h3347 : p585 ∨ p593)
    (h3352 : p586 ∨ p593)
    (h3357 : p587 ∨ p593)
    (h3362 : p588 ∨ p593)
    (h3248 : p576 ∨ p579 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : (¬ p592) ∨ (¬ p591) ∨ p579 ∨ p576 ∨ (¬ p589) ∨ (¬ p590) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p592 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p591 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p579) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p589 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p590 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p593) := by
    rcases h3273 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p584 := by
    rcases h3342 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p585 := by
    rcases h3347 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p586 := by
    rcases h3352 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p587 := by
    rcases h3357 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p588 := by
    rcases h3362 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3248 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20860 (p576 p579 p589 p590 p591 p592 : Prop)
    (h20855 : p589 ∨ p576 ∨ p579)
    (h20856 : p590 ∨ p576 ∨ p579)
    (h20857 : p591 ∨ p576 ∨ p579)
    (h20858 : p592 ∨ p576 ∨ p579)
    (h20859 : (¬ p592) ∨ (¬ p591) ∨ p579 ∨ p576 ∨ (¬ p589) ∨ (¬ p590)) : p576 ∨ p579 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p579) := fun hu => hn (Or.inr hu)
  have u2 : p589 := by
    rcases h20855 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p590 := by
    rcases h20856 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p591 := by
    rcases h20857 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p592 := by
    rcases h20858 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20859 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20861 (p1269 p1273 p1276 p1277 p1278 p1279 p1280 p1281 : Prop)
    (h7682 : p1276 ∨ p1281)
    (h7687 : p1277 ∨ p1281)
    (h7692 : p1278 ∨ p1281)
    (h7697 : p1279 ∨ p1281)
    (h7702 : p1280 ∨ p1281)
    (h7589 : p1269 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1281 ∨ p1273 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1281) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20862 (p1269 p1273 p1276 p1277 p1278 p1279 p1280 p1282 : Prop)
    (h7683 : p1276 ∨ p1282)
    (h7688 : p1277 ∨ p1282)
    (h7693 : p1278 ∨ p1282)
    (h7698 : p1279 ∨ p1282)
    (h7703 : p1280 ∨ p1282)
    (h7589 : p1269 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1282 ∨ p1273 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1282) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20863 (p1269 p1273 p1276 p1277 p1278 p1279 p1280 p1283 : Prop)
    (h7684 : p1276 ∨ p1283)
    (h7689 : p1277 ∨ p1283)
    (h7694 : p1278 ∨ p1283)
    (h7699 : p1279 ∨ p1283)
    (h7704 : p1280 ∨ p1283)
    (h7589 : p1269 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1283 ∨ p1273 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1283) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20864 (p1269 p1273 p1276 p1277 p1278 p1279 p1280 p1284 : Prop)
    (h7685 : p1276 ∨ p1284)
    (h7690 : p1277 ∨ p1284)
    (h7695 : p1278 ∨ p1284)
    (h7700 : p1279 ∨ p1284)
    (h7705 : p1280 ∨ p1284)
    (h7589 : p1269 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : p1284 ∨ p1273 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1284) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1273) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1276 := by
    rcases h7685 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1277 := by
    rcases h7690 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1278 := by
    rcases h7695 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1279 := by
    rcases h7700 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1280 := by
    rcases h7705 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20865 (p1269 p1273 p1276 p1277 p1278 p1279 p1280 p1281 p1282 p1283 p1284 p1285 : Prop)
    (h7614 : p1269 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) ∨ (¬ p1283) ∨ (¬ p1284) ∨ (¬ p1285))
    (h7686 : p1276 ∨ p1285)
    (h7691 : p1277 ∨ p1285)
    (h7696 : p1278 ∨ p1285)
    (h7701 : p1279 ∨ p1285)
    (h7706 : p1280 ∨ p1285)
    (h7589 : p1269 ∨ p1273 ∨ (¬ p1276) ∨ (¬ p1277) ∨ (¬ p1278) ∨ (¬ p1279) ∨ (¬ p1280)) : (¬ p1284) ∨ (¬ p1283) ∨ p1269 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1284 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1283 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1269) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1273) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1281 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1282 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1285) := by
    rcases h7614 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1276 := by
    rcases h7686 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1277 := by
    rcases h7691 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1278 := by
    rcases h7696 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1279 := by
    rcases h7701 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1280 := by
    rcases h7706 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7589 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20866 (p1269 p1273 p1281 p1282 p1283 p1284 : Prop)
    (h20861 : p1281 ∨ p1273 ∨ p1269)
    (h20862 : p1282 ∨ p1273 ∨ p1269)
    (h20863 : p1283 ∨ p1273 ∨ p1269)
    (h20864 : p1284 ∨ p1273 ∨ p1269)
    (h20865 : (¬ p1284) ∨ (¬ p1283) ∨ p1269 ∨ p1273 ∨ (¬ p1281) ∨ (¬ p1282)) : p1273 ∨ p1269 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1273) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1269) := fun hu => hn (Or.inr hu)
  have u2 : p1281 := by
    rcases h20861 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1282 := by
    rcases h20862 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1283 := by
    rcases h20863 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1284 := by
    rcases h20864 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20865 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20867 (p495 p498 p502 p503 p504 p505 p506 p507 : Prop)
    (h2827 : p502 ∨ p507)
    (h2832 : p503 ∨ p507)
    (h2837 : p504 ∨ p507)
    (h2842 : p505 ∨ p507)
    (h2847 : p506 ∨ p507)
    (h2738 : p495 ∨ p498 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p507 ∨ p495 ∨ p498 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p507) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p498) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20868 (p495 p498 p502 p503 p504 p505 p506 p508 : Prop)
    (h2828 : p502 ∨ p508)
    (h2833 : p503 ∨ p508)
    (h2838 : p504 ∨ p508)
    (h2843 : p505 ∨ p508)
    (h2848 : p506 ∨ p508)
    (h2738 : p495 ∨ p498 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p508 ∨ p495 ∨ p498 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p508) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p498) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20869 (p495 p498 p502 p503 p504 p505 p506 p509 : Prop)
    (h2829 : p502 ∨ p509)
    (h2834 : p503 ∨ p509)
    (h2839 : p504 ∨ p509)
    (h2844 : p505 ∨ p509)
    (h2849 : p506 ∨ p509)
    (h2738 : p495 ∨ p498 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p509 ∨ p495 ∨ p498 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p509) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p498) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20870 (p495 p498 p502 p503 p504 p505 p506 p510 : Prop)
    (h2830 : p502 ∨ p510)
    (h2835 : p503 ∨ p510)
    (h2840 : p504 ∨ p510)
    (h2845 : p505 ∨ p510)
    (h2850 : p506 ∨ p510)
    (h2738 : p495 ∨ p498 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p510 ∨ p495 ∨ p498 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p510) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p498) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p502 := by
    rcases h2830 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p503 := by
    rcases h2835 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p504 := by
    rcases h2840 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p505 := by
    rcases h2845 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p506 := by
    rcases h2850 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20871 (p421 p495 p498 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h20867 : p507 ∨ p495 ∨ p498)
    (h20868 : p508 ∨ p495 ∨ p498)
    (h20869 : p509 ∨ p495 ∨ p498)
    (h20870 : p510 ∨ p495 ∨ p498)
    (h2758 : p421 ∨ p498 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511))
    (h2831 : p502 ∨ p511)
    (h2836 : p503 ∨ p511)
    (h2841 : p504 ∨ p511)
    (h2846 : p505 ∨ p511)
    (h2851 : p506 ∨ p511)
    (h2738 : p495 ∨ p498 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p495 ∨ p498 ∨ p421 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p498) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p421) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h20867 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p508 := by
    rcases h20868 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p509 := by
    rcases h20869 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p510 := by
    rcases h20870 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p511) := by
    rcases h2758 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p502 := by
    rcases h2831 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p503 := by
    rcases h2836 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p504 := by
    rcases h2841 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p505 := by
    rcases h2846 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p506 := by
    rcases h2851 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h2738 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step20872 (p421 p499 p502 p503 p504 p505 p506 p511 : Prop)
    (h2831 : p502 ∨ p511)
    (h2836 : p503 ∨ p511)
    (h2841 : p504 ∨ p511)
    (h2846 : p505 ∨ p511)
    (h2851 : p506 ∨ p511)
    (h2734 : p421 ∨ p499 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p511 ∨ p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p511) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p421) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20873 (p421 p499 p502 p507 p508 p509 p510 p511 : Prop)
    (h20872 : p511 ∨ p421 ∨ p499)
    (h2827 : p502 ∨ p507)
    (h2828 : p502 ∨ p508)
    (h2829 : p502 ∨ p509)
    (h2830 : p502 ∨ p510)
    (h2759 : p421 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p502 ∨ p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p421) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p511 := by
    rcases h20872 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p507 := by
    rcases h2827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p508 := by
    rcases h2828 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p509 := by
    rcases h2829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p510 := by
    rcases h2830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20874 (p421 p499 p503 p507 p508 p509 p510 p511 : Prop)
    (h20872 : p511 ∨ p421 ∨ p499)
    (h2832 : p503 ∨ p507)
    (h2833 : p503 ∨ p508)
    (h2834 : p503 ∨ p509)
    (h2835 : p503 ∨ p510)
    (h2759 : p421 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p503 ∨ p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p503) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p421) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p511 := by
    rcases h20872 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p507 := by
    rcases h2832 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p508 := by
    rcases h2833 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p509 := by
    rcases h2834 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p510 := by
    rcases h2835 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20875 (p421 p499 p504 p507 p508 p509 p510 p511 : Prop)
    (h20872 : p511 ∨ p421 ∨ p499)
    (h2837 : p504 ∨ p507)
    (h2838 : p504 ∨ p508)
    (h2839 : p504 ∨ p509)
    (h2840 : p504 ∨ p510)
    (h2759 : p421 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p504 ∨ p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p504) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p421) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p511 := by
    rcases h20872 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p507 := by
    rcases h2837 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p508 := by
    rcases h2838 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p509 := by
    rcases h2839 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p510 := by
    rcases h2840 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20876 (p421 p499 p505 p507 p508 p509 p510 p511 : Prop)
    (h20872 : p511 ∨ p421 ∨ p499)
    (h2842 : p505 ∨ p507)
    (h2843 : p505 ∨ p508)
    (h2844 : p505 ∨ p509)
    (h2845 : p505 ∨ p510)
    (h2759 : p421 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p505 ∨ p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p505) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p421) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p511 := by
    rcases h20872 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p507 := by
    rcases h2842 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p508 := by
    rcases h2843 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p509 := by
    rcases h2844 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p510 := by
    rcases h2845 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20877 (p421 p499 p506 p507 p508 p509 p510 p511 : Prop)
    (h20872 : p511 ∨ p421 ∨ p499)
    (h2847 : p506 ∨ p507)
    (h2848 : p506 ∨ p508)
    (h2849 : p506 ∨ p509)
    (h2850 : p506 ∨ p510)
    (h2759 : p421 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p506 ∨ p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p506) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p421) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p511 := by
    rcases h20872 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p507 := by
    rcases h2847 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p508 := by
    rcases h2848 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p509 := by
    rcases h2849 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p510 := by
    rcases h2850 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2759 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20878 (p421 p499 p502 p503 p504 p505 p506 : Prop)
    (h20873 : p502 ∨ p421 ∨ p499)
    (h20874 : p503 ∨ p421 ∨ p499)
    (h20875 : p504 ∨ p421 ∨ p499)
    (h20876 : p505 ∨ p421 ∨ p499)
    (h20877 : p506 ∨ p421 ∨ p499)
    (h2734 : p421 ∨ p499 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506)) : p421 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p421) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p499) := fun hu => hn (Or.inr hu)
  have u2 : p502 := by
    rcases h20873 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p503 := by
    rcases h20874 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p504 := by
    rcases h20875 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p505 := by
    rcases h20876 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p506 := by
    rcases h20877 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h2734 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step20879 (p2 p480 p484 p485 p486 p487 p488 p489 : Prop)
    (h2702 : p484 ∨ p489)
    (h2707 : p485 ∨ p489)
    (h2712 : p486 ∨ p489)
    (h2717 : p487 ∨ p489)
    (h2722 : p488 ∨ p489)
    (h2612 : p2 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p489 ∨ p2 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p489) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2612 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20880 (p2 p480 p484 p485 p486 p487 p488 p490 : Prop)
    (h2703 : p484 ∨ p490)
    (h2708 : p485 ∨ p490)
    (h2713 : p486 ∨ p490)
    (h2718 : p487 ∨ p490)
    (h2723 : p488 ∨ p490)
    (h2612 : p2 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p490 ∨ p2 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p490) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2612 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20881 (p2 p480 p484 p485 p486 p487 p488 p491 : Prop)
    (h2704 : p484 ∨ p491)
    (h2709 : p485 ∨ p491)
    (h2714 : p486 ∨ p491)
    (h2719 : p487 ∨ p491)
    (h2724 : p488 ∨ p491)
    (h2612 : p2 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p491 ∨ p2 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p491) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2612 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20882 (p2 p480 p484 p485 p486 p487 p488 p492 : Prop)
    (h2705 : p484 ∨ p492)
    (h2710 : p485 ∨ p492)
    (h2715 : p486 ∨ p492)
    (h2720 : p487 ∨ p492)
    (h2725 : p488 ∨ p492)
    (h2612 : p2 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : p492 ∨ p2 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p492) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p2) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p480) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p484 := by
    rcases h2705 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p485 := by
    rcases h2710 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p486 := by
    rcases h2715 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p487 := by
    rcases h2720 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p488 := by
    rcases h2725 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2612 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20883 (p2 p480 p484 p485 p486 p487 p488 p489 p490 p491 p492 p493 : Prop)
    (h2637 : p2 ∨ p480 ∨ (¬ p489) ∨ (¬ p490) ∨ (¬ p491) ∨ (¬ p492) ∨ (¬ p493))
    (h2706 : p484 ∨ p493)
    (h2711 : p485 ∨ p493)
    (h2716 : p486 ∨ p493)
    (h2721 : p487 ∨ p493)
    (h2726 : p488 ∨ p493)
    (h2612 : p2 ∨ p480 ∨ (¬ p484) ∨ (¬ p485) ∨ (¬ p486) ∨ (¬ p487) ∨ (¬ p488)) : (¬ p492) ∨ (¬ p491) ∨ p2 ∨ p480 ∨ (¬ p489) ∨ (¬ p490) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p492 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p491 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p2) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p480) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p489 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p490 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p493) := by
    rcases h2637 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p484 := by
    rcases h2706 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p485 := by
    rcases h2711 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p486 := by
    rcases h2716 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p487 := by
    rcases h2721 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p488 := by
    rcases h2726 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2612 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20884 (p2 p480 p489 p490 p491 p492 : Prop)
    (h20879 : p489 ∨ p2 ∨ p480)
    (h20880 : p490 ∨ p2 ∨ p480)
    (h20881 : p491 ∨ p2 ∨ p480)
    (h20882 : p492 ∨ p2 ∨ p480)
    (h20883 : (¬ p492) ∨ (¬ p491) ∨ p2 ∨ p480 ∨ (¬ p489) ∨ (¬ p490)) : p2 ∨ p480 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p2) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p480) := fun hu => hn (Or.inr hu)
  have u2 : p489 := by
    rcases h20879 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p490 := by
    rcases h20880 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p491 := by
    rcases h20881 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p492 := by
    rcases h20882 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20883 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20885 (p1140 p1164 p1171 p1172 p1173 p1174 p1175 p1176 : Prop)
    (h6994 : p1171 ∨ p1176)
    (h6999 : p1172 ∨ p1176)
    (h7004 : p1173 ∨ p1176)
    (h7009 : p1174 ∨ p1176)
    (h7014 : p1175 ∨ p1176)
    (h6901 : p1140 ∨ p1164 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1176 ∨ p1164 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1176) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1164) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20886 (p1140 p1164 p1171 p1172 p1173 p1174 p1175 p1177 : Prop)
    (h6995 : p1171 ∨ p1177)
    (h7000 : p1172 ∨ p1177)
    (h7005 : p1173 ∨ p1177)
    (h7010 : p1174 ∨ p1177)
    (h7015 : p1175 ∨ p1177)
    (h6901 : p1140 ∨ p1164 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1177 ∨ p1164 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1177) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1164) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20887 (p1140 p1164 p1171 p1172 p1173 p1174 p1175 p1178 : Prop)
    (h6996 : p1171 ∨ p1178)
    (h7001 : p1172 ∨ p1178)
    (h7006 : p1173 ∨ p1178)
    (h7011 : p1174 ∨ p1178)
    (h7016 : p1175 ∨ p1178)
    (h6901 : p1140 ∨ p1164 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1178 ∨ p1164 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1178) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1164) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20888 (p1140 p1164 p1171 p1172 p1173 p1174 p1175 p1179 : Prop)
    (h6997 : p1171 ∨ p1179)
    (h7002 : p1172 ∨ p1179)
    (h7007 : p1173 ∨ p1179)
    (h7012 : p1174 ∨ p1179)
    (h7017 : p1175 ∨ p1179)
    (h6901 : p1140 ∨ p1164 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : p1179 ∨ p1164 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1164) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20889 (p1140 p1164 p1171 p1172 p1173 p1174 p1175 p1176 p1177 p1178 p1179 p1180 : Prop)
    (h6926 : p1140 ∨ p1164 ∨ (¬ p1176) ∨ (¬ p1177) ∨ (¬ p1178) ∨ (¬ p1179) ∨ (¬ p1180))
    (h6998 : p1171 ∨ p1180)
    (h7003 : p1172 ∨ p1180)
    (h7008 : p1173 ∨ p1180)
    (h7013 : p1174 ∨ p1180)
    (h7018 : p1175 ∨ p1180)
    (h6901 : p1140 ∨ p1164 ∨ (¬ p1171) ∨ (¬ p1172) ∨ (¬ p1173) ∨ (¬ p1174) ∨ (¬ p1175)) : (¬ p1179) ∨ (¬ p1178) ∨ p1164 ∨ p1140 ∨ (¬ p1176) ∨ (¬ p1177) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1178 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1164) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1140) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1176 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1177 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1180) := by
    rcases h6926 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1171 := by
    rcases h6998 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1172 := by
    rcases h7003 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1173 := by
    rcases h7008 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1174 := by
    rcases h7013 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1175 := by
    rcases h7018 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6901 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20890 (p1140 p1164 p1176 p1177 p1178 p1179 : Prop)
    (h20885 : p1176 ∨ p1164 ∨ p1140)
    (h20886 : p1177 ∨ p1164 ∨ p1140)
    (h20887 : p1178 ∨ p1164 ∨ p1140)
    (h20888 : p1179 ∨ p1164 ∨ p1140)
    (h20889 : (¬ p1179) ∨ (¬ p1178) ∨ p1164 ∨ p1140 ∨ (¬ p1176) ∨ (¬ p1177)) : p1164 ∨ p1140 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1164) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1140) := fun hu => hn (Or.inr hu)
  have u2 : p1176 := by
    rcases h20885 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1177 := by
    rcases h20886 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1178 := by
    rcases h20887 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1179 := by
    rcases h20888 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20889 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20897 (p126 p517 p522 p523 p524 p525 p526 p527 : Prop)
    (h2959 : p522 ∨ p527)
    (h2964 : p523 ∨ p527)
    (h2969 : p524 ∨ p527)
    (h2974 : p525 ∨ p527)
    (h2979 : p526 ∨ p527)
    (h2881 : p126 ∨ p517 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p527 ∨ p517 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p527) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p517) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h2959 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p523 := by
    rcases h2964 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p524 := by
    rcases h2969 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p525 := by
    rcases h2974 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p526 := by
    rcases h2979 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2881 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20898 (p126 p517 p522 p523 p524 p525 p526 p528 : Prop)
    (h2960 : p522 ∨ p528)
    (h2965 : p523 ∨ p528)
    (h2970 : p524 ∨ p528)
    (h2975 : p525 ∨ p528)
    (h2980 : p526 ∨ p528)
    (h2881 : p126 ∨ p517 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p528 ∨ p517 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p528) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p517) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h2960 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p523 := by
    rcases h2965 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p524 := by
    rcases h2970 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p525 := by
    rcases h2975 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p526 := by
    rcases h2980 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2881 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20899 (p126 p517 p522 p523 p524 p525 p526 p529 : Prop)
    (h2961 : p522 ∨ p529)
    (h2966 : p523 ∨ p529)
    (h2971 : p524 ∨ p529)
    (h2976 : p525 ∨ p529)
    (h2981 : p526 ∨ p529)
    (h2881 : p126 ∨ p517 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p529 ∨ p517 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p529) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p517) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h2961 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p523 := by
    rcases h2966 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p524 := by
    rcases h2971 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p525 := by
    rcases h2976 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p526 := by
    rcases h2981 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2881 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20900 (p126 p517 p522 p523 p524 p525 p526 p530 : Prop)
    (h2962 : p522 ∨ p530)
    (h2967 : p523 ∨ p530)
    (h2972 : p524 ∨ p530)
    (h2977 : p525 ∨ p530)
    (h2982 : p526 ∨ p530)
    (h2881 : p126 ∨ p517 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p530 ∨ p517 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p530) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p517) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h2962 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p523 := by
    rcases h2967 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p524 := by
    rcases h2972 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p525 := by
    rcases h2977 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p526 := by
    rcases h2982 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2881 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20901 (p126 p517 p518 p522 p523 p524 p525 p526 p527 p528 p529 p530 p531 : Prop)
    (h20897 : p527 ∨ p517 ∨ p126)
    (h20898 : p528 ∨ p517 ∨ p126)
    (h20899 : p529 ∨ p517 ∨ p126)
    (h20900 : p530 ∨ p517 ∨ p126)
    (h2904 : p517 ∨ p518 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531))
    (h2963 : p522 ∨ p531)
    (h2968 : p523 ∨ p531)
    (h2973 : p524 ∨ p531)
    (h2978 : p525 ∨ p531)
    (h2983 : p526 ∨ p531)
    (h2881 : p126 ∨ p517 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p517 ∨ p518 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p517) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p518) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p527 := by
    rcases h20897 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p528 := by
    rcases h20898 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p529 := by
    rcases h20899 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p530 := by
    rcases h20900 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p531) := by
    rcases h2904 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p522 := by
    rcases h2963 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p523 := by
    rcases h2968 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p524 := by
    rcases h2973 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p525 := by
    rcases h2978 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p526 := by
    rcases h2983 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h2881 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step20908 (p381 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h2108 : p381 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399))
    (h2185 : p390 ∨ p399)
    (h2190 : p391 ∨ p399)
    (h2195 : p392 ∨ p399)
    (h2200 : p393 ∨ p399)
    (h2205 : p394 ∨ p399)
    (h2083 : p381 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p387 ∨ (¬ p395) ∨ p381 ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p396) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p387) := fun hu => hn (Or.inl hu)
  have u1 : p395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p381) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p397 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p396 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p399) := by
    rcases h2108 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u3)
    · exact False.elim (q5 u4)
    · exact q6
  have u7 : p390 := by
    rcases h2185 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p391 := by
    rcases h2190 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p392 := by
    rcases h2195 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p393 := by
    rcases h2200 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p394 := by
    rcases h2205 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20910 (p381 p387 p390 p391 p392 p393 p394 p395 : Prop)
    (h2181 : p390 ∨ p395)
    (h2186 : p391 ∨ p395)
    (h2191 : p392 ∨ p395)
    (h2196 : p393 ∨ p395)
    (h2201 : p394 ∨ p395)
    (h2083 : p381 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p395 ∨ p387 ∨ p381 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p395) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p381) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2181 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2186 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2191 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2196 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2201 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20911 (p381 p387 p390 p391 p392 p393 p394 p396 : Prop)
    (h2182 : p390 ∨ p396)
    (h2187 : p391 ∨ p396)
    (h2192 : p392 ∨ p396)
    (h2197 : p393 ∨ p396)
    (h2202 : p394 ∨ p396)
    (h2083 : p381 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p396 ∨ p387 ∨ p381 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p396) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p381) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2182 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2187 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2192 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2197 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2202 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20912 (p381 p387 p390 p391 p392 p393 p394 p397 : Prop)
    (h2183 : p390 ∨ p397)
    (h2188 : p391 ∨ p397)
    (h2193 : p392 ∨ p397)
    (h2198 : p393 ∨ p397)
    (h2203 : p394 ∨ p397)
    (h2083 : p381 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p397 ∨ p387 ∨ p381 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p397) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p381) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2183 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2188 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2193 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2203 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20913 (p381 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 : Prop)
    (h20908 : p387 ∨ (¬ p395) ∨ p381 ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p396))
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2083 : p381 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : (¬ p397) ∨ p387 ∨ p381 ∨ (¬ p395) ∨ (¬ p396) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p397 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p381) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p395 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p396 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p398) := by
    rcases h20908 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (u1 q0)
    · exact False.elim (q1 u3)
    · exact False.elim (u2 q2)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
  have u6 : p390 := by
    rcases h2184 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : p391 := by
    rcases h2189 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p392 := by
    rcases h2194 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p393 := by
    rcases h2199 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p394 := by
    rcases h2204 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h2083 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step20914 (p381 p387 p395 p396 p397 : Prop)
    (h20910 : p395 ∨ p387 ∨ p381)
    (h20911 : p396 ∨ p387 ∨ p381)
    (h20912 : p397 ∨ p387 ∨ p381)
    (h20913 : (¬ p397) ∨ p387 ∨ p381 ∨ (¬ p395) ∨ (¬ p396)) : p387 ∨ p381 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p387) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p381) := fun hu => hn (Or.inr hu)
  have u2 : p395 := by
    rcases h20910 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p396 := by
    rcases h20911 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p397 := by
    rcases h20912 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20913 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)

theorem step20915 (p362 p366 p371 p372 p373 p374 p375 p376 : Prop)
    (h2054 : p371 ∨ p376)
    (h2059 : p372 ∨ p376)
    (h2064 : p373 ∨ p376)
    (h2069 : p374 ∨ p376)
    (h2074 : p375 ∨ p376)
    (h1976 : p362 ∨ p366 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p376 ∨ p366 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p376) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p371 := by
    rcases h2054 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p372 := by
    rcases h2059 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p373 := by
    rcases h2064 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p374 := by
    rcases h2069 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p375 := by
    rcases h2074 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1976 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20916 (p362 p366 p371 p372 p373 p374 p375 p377 : Prop)
    (h2055 : p371 ∨ p377)
    (h2060 : p372 ∨ p377)
    (h2065 : p373 ∨ p377)
    (h2070 : p374 ∨ p377)
    (h2075 : p375 ∨ p377)
    (h1976 : p362 ∨ p366 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p377 ∨ p366 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p377) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p371 := by
    rcases h2055 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p372 := by
    rcases h2060 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p373 := by
    rcases h2065 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p374 := by
    rcases h2070 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p375 := by
    rcases h2075 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1976 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20917 (p362 p366 p371 p372 p373 p374 p375 p378 : Prop)
    (h2056 : p371 ∨ p378)
    (h2061 : p372 ∨ p378)
    (h2066 : p373 ∨ p378)
    (h2071 : p374 ∨ p378)
    (h2076 : p375 ∨ p378)
    (h1976 : p362 ∨ p366 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p378 ∨ p366 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p378) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p371 := by
    rcases h2056 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p372 := by
    rcases h2061 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p373 := by
    rcases h2066 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p374 := by
    rcases h2071 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p375 := by
    rcases h2076 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1976 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20918 (p362 p366 p371 p372 p373 p374 p375 p379 : Prop)
    (h2057 : p371 ∨ p379)
    (h2062 : p372 ∨ p379)
    (h2067 : p373 ∨ p379)
    (h2072 : p374 ∨ p379)
    (h2077 : p375 ∨ p379)
    (h1976 : p362 ∨ p366 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p379 ∨ p366 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p379) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p366) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p371 := by
    rcases h2057 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p372 := by
    rcases h2062 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p373 := by
    rcases h2067 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p374 := by
    rcases h2072 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p375 := by
    rcases h2077 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1976 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20919 (p362 p366 p367 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h20915 : p376 ∨ p366 ∨ p362)
    (h20916 : p377 ∨ p366 ∨ p362)
    (h20917 : p378 ∨ p366 ∨ p362)
    (h20918 : p379 ∨ p366 ∨ p362)
    (h1999 : p366 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380))
    (h2058 : p371 ∨ p380)
    (h2063 : p372 ∨ p380)
    (h2068 : p373 ∨ p380)
    (h2073 : p374 ∨ p380)
    (h2078 : p375 ∨ p380)
    (h1976 : p362 ∨ p366 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p366 ∨ p367 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p366) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p367) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p376 := by
    rcases h20915 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p377 := by
    rcases h20916 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p378 := by
    rcases h20917 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p379 := by
    rcases h20918 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p380) := by
    rcases h1999 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p371 := by
    rcases h2058 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p372 := by
    rcases h2063 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p373 := by
    rcases h2068 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p374 := by
    rcases h2073 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p375 := by
    rcases h2078 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h1976 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step20920 (p455 p456 p465 p466 p467 p468 p469 p470 : Prop)
    (h2575 : p465 ∨ p470)
    (h2580 : p466 ∨ p470)
    (h2585 : p467 ∨ p470)
    (h2590 : p468 ∨ p470)
    (h2595 : p469 ∨ p470)
    (h2487 : p455 ∨ p456 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : p470 ∨ p455 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p470) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p465 := by
    rcases h2575 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p466 := by
    rcases h2580 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p467 := by
    rcases h2585 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p468 := by
    rcases h2590 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p469 := by
    rcases h2595 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20921 (p455 p456 p465 p466 p467 p468 p469 p471 : Prop)
    (h2576 : p465 ∨ p471)
    (h2581 : p466 ∨ p471)
    (h2586 : p467 ∨ p471)
    (h2591 : p468 ∨ p471)
    (h2596 : p469 ∨ p471)
    (h2487 : p455 ∨ p456 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : p471 ∨ p455 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p471) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p465 := by
    rcases h2576 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p466 := by
    rcases h2581 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p467 := by
    rcases h2586 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p468 := by
    rcases h2591 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p469 := by
    rcases h2596 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20922 (p455 p456 p465 p466 p467 p468 p469 p472 : Prop)
    (h2577 : p465 ∨ p472)
    (h2582 : p466 ∨ p472)
    (h2587 : p467 ∨ p472)
    (h2592 : p468 ∨ p472)
    (h2597 : p469 ∨ p472)
    (h2487 : p455 ∨ p456 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : p472 ∨ p455 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p472) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p465 := by
    rcases h2577 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p466 := by
    rcases h2582 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p467 := by
    rcases h2587 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p468 := by
    rcases h2592 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p469 := by
    rcases h2597 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20923 (p455 p456 p465 p466 p467 p468 p469 p473 : Prop)
    (h2578 : p465 ∨ p473)
    (h2583 : p466 ∨ p473)
    (h2588 : p467 ∨ p473)
    (h2593 : p468 ∨ p473)
    (h2598 : p469 ∨ p473)
    (h2487 : p455 ∨ p456 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : p473 ∨ p455 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p473) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p455) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20924 (p455 p456 p465 p466 p467 p468 p469 p470 p471 p472 p473 p474 : Prop)
    (h2512 : p455 ∨ p456 ∨ (¬ p470) ∨ (¬ p471) ∨ (¬ p472) ∨ (¬ p473) ∨ (¬ p474))
    (h2579 : p465 ∨ p474)
    (h2584 : p466 ∨ p474)
    (h2589 : p467 ∨ p474)
    (h2594 : p468 ∨ p474)
    (h2599 : p469 ∨ p474)
    (h2487 : p455 ∨ p456 ∨ (¬ p465) ∨ (¬ p466) ∨ (¬ p467) ∨ (¬ p468) ∨ (¬ p469)) : (¬ p473) ∨ (¬ p472) ∨ p456 ∨ p455 ∨ (¬ p470) ∨ (¬ p471) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p473 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p472 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p456) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p455) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p470 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p471 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p474) := by
    rcases h2512 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p465 := by
    rcases h2579 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p466 := by
    rcases h2584 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p467 := by
    rcases h2589 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p468 := by
    rcases h2594 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p469 := by
    rcases h2599 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2487 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20925 (p455 p456 p470 p471 p472 p473 : Prop)
    (h20920 : p470 ∨ p455 ∨ p456)
    (h20921 : p471 ∨ p455 ∨ p456)
    (h20922 : p472 ∨ p455 ∨ p456)
    (h20923 : p473 ∨ p455 ∨ p456)
    (h20924 : (¬ p473) ∨ (¬ p472) ∨ p456 ∨ p455 ∨ (¬ p470) ∨ (¬ p471)) : p455 ∨ p456 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p455) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p456) := fun hu => hn (Or.inr hu)
  have u2 : p470 := by
    rcases h20920 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p471 := by
    rcases h20921 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p472 := by
    rcases h20922 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p473 := by
    rcases h20923 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20924 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20926 (p303 p383 p390 p391 p392 p393 p394 p398 : Prop)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2091 : p303 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p398 ∨ p383 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p383) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20927 (p303 p383 p390 p391 p392 p393 p394 p399 : Prop)
    (h2185 : p390 ∨ p399)
    (h2190 : p391 ∨ p399)
    (h2195 : p392 ∨ p399)
    (h2200 : p393 ∨ p399)
    (h2205 : p394 ∨ p399)
    (h2091 : p303 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p399 ∨ p383 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p399) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p383) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2185 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2190 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2195 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2200 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2205 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20928 (p303 p383 p390 p391 p392 p393 p394 p395 : Prop)
    (h2181 : p390 ∨ p395)
    (h2186 : p391 ∨ p395)
    (h2191 : p392 ∨ p395)
    (h2196 : p393 ∨ p395)
    (h2201 : p394 ∨ p395)
    (h2091 : p303 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p395 ∨ p383 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p395) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p383) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2181 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2186 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2191 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2196 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2201 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20929 (p303 p383 p390 p391 p392 p393 p394 p396 : Prop)
    (h2182 : p390 ∨ p396)
    (h2187 : p391 ∨ p396)
    (h2192 : p392 ∨ p396)
    (h2197 : p393 ∨ p396)
    (h2202 : p394 ∨ p396)
    (h2091 : p303 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p396 ∨ p383 ∨ p303 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p396) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p383) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p303) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h2182 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p391 := by
    rcases h2187 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p392 := by
    rcases h2192 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p393 := by
    rcases h2197 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p394 := by
    rcases h2202 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20930 (p303 p362 p366 p367 p381 p382 p383 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 p406 p420 p455 p456 : Prop)
    (h14119 : (¬ p381) ∨ (¬ p420) ∨ p456)
    (h20914 : p387 ∨ p381)
    (h12617 : (¬ p303) ∨ (¬ p387))
    (h14426 : (¬ p367) ∨ (¬ p387) ∨ p406)
    (h20919 : p366 ∨ p367 ∨ p362)
    (h20925 : p455 ∨ p456)
    (h17314 : (¬ p366) ∨ (¬ p382) ∨ (¬ p383) ∨ (¬ p420) ∨ (¬ p455))
    (h20926 : p398 ∨ p383 ∨ p303)
    (h20927 : p399 ∨ p383 ∨ p303)
    (h20928 : p395 ∨ p383 ∨ p303)
    (h20929 : p396 ∨ p383 ∨ p303)
    (h2106 : p381 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399))
    (h2183 : p390 ∨ p397)
    (h2188 : p391 ∨ p397)
    (h2193 : p392 ∨ p397)
    (h2198 : p393 ∨ p397)
    (h2203 : p394 ∨ p397)
    (h2091 : p303 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p456 ∨ p362 ∨ (¬ p420) ∨ (¬ p382) ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p456) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p362) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p406) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p381) := by
    rcases h14119 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u2)
    · exact False.elim (u0 q2)
  have u6 : p387 := by
    rcases h20914 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p303) := by
    rcases h12617 with q0 | q1
    · exact q0
    · exact False.elim (q1 u6)
  have u8 : (¬ p367) := by
    rcases h14426 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u6)
    · exact False.elim (u4 q2)
  have u9 : p366 := by
    rcases h20919 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u8 q1)
    · exact False.elim (u1 q2)
  have u10 : p455 := by
    rcases h20925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u11 : (¬ p383) := by
    rcases h17314 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u9)
    · exact False.elim (q1 u3)
    · exact q2
    · exact False.elim (q3 u2)
    · exact False.elim (q4 u10)
  have u12 : p398 := by
    rcases h20926 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u7 q2)
  have u13 : p399 := by
    rcases h20927 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u7 q2)
  have u14 : p395 := by
    rcases h20928 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u7 q2)
  have u15 : p396 := by
    rcases h20929 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u11 q1)
    · exact False.elim (u7 q2)
  have u16 : (¬ p397) := by
    rcases h2106 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u5 q0)
    · exact False.elim (u11 q1)
    · exact False.elim (q2 u14)
    · exact False.elim (q3 u15)
    · exact q4
    · exact False.elim (q5 u12)
    · exact False.elim (q6 u13)
  have u17 : p390 := by
    rcases h2183 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u18 : p391 := by
    rcases h2188 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u19 : p392 := by
    rcases h2193 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u20 : p393 := by
    rcases h2198 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  have u21 : p394 := by
    rcases h2203 with q0 | q1
    · exact q0
    · exact False.elim (u16 q1)
  rcases h2091 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u7 q0)
  · exact False.elim (u11 q1)
  · exact False.elim (q2 u17)
  · exact False.elim (q3 u18)
  · exact False.elim (q4 u19)
  · exact False.elim (q5 u20)
  · exact False.elim (q6 u21)

theorem step20931 (p1080 p1083 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6391 : p1080 ∨ p1083 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094))
    (h6454 : p1085 ∨ p1094)
    (h6459 : p1086 ∨ p1094)
    (h6464 : p1087 ∨ p1094)
    (h6469 : p1088 ∨ p1094)
    (h6474 : p1089 ∨ p1094)
    (h6366 : p1080 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1080 ∨ p1083 ∨ (¬ p1090) ∨ (¬ p1093) ∨ (¬ p1092) ∨ (¬ p1091) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1080) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1083) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p1090 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1093 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1092 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1091 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1094) := by
    rcases h6391 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u4)
    · exact False.elim (q5 u3)
    · exact q6
  have u7 : p1085 := by
    rcases h6454 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1086 := by
    rcases h6459 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1087 := by
    rcases h6464 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1088 := by
    rcases h6469 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1089 := by
    rcases h6474 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20932 (p1080 p1083 p1085 p1086 p1087 p1088 p1089 p1090 : Prop)
    (h6450 : p1085 ∨ p1090)
    (h6455 : p1086 ∨ p1090)
    (h6460 : p1087 ∨ p1090)
    (h6465 : p1088 ∨ p1090)
    (h6470 : p1089 ∨ p1090)
    (h6366 : p1080 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1090 ∨ p1080 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1090) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20933 (p1080 p1083 p1085 p1086 p1087 p1088 p1089 p1091 : Prop)
    (h6451 : p1085 ∨ p1091)
    (h6456 : p1086 ∨ p1091)
    (h6461 : p1087 ∨ p1091)
    (h6466 : p1088 ∨ p1091)
    (h6471 : p1089 ∨ p1091)
    (h6366 : p1080 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1091 ∨ p1080 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1091) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20934 (p1080 p1083 p1085 p1086 p1087 p1088 p1089 p1092 : Prop)
    (h6452 : p1085 ∨ p1092)
    (h6457 : p1086 ∨ p1092)
    (h6462 : p1087 ∨ p1092)
    (h6467 : p1088 ∨ p1092)
    (h6472 : p1089 ∨ p1092)
    (h6366 : p1080 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1092 ∨ p1080 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1092) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20935 (p1080 p1083 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 : Prop)
    (h20931 : p1080 ∨ p1083 ∨ (¬ p1090) ∨ (¬ p1093) ∨ (¬ p1092) ∨ (¬ p1091))
    (h6453 : p1085 ∨ p1093)
    (h6458 : p1086 ∨ p1093)
    (h6463 : p1087 ∨ p1093)
    (h6468 : p1088 ∨ p1093)
    (h6473 : p1089 ∨ p1093)
    (h6366 : p1080 ∨ p1083 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : (¬ p1092) ∨ p1080 ∨ p1083 ∨ (¬ p1091) ∨ (¬ p1090) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1092 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1083) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1091 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1090 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1093) := by
    rcases h20931 with q0 | q1 | q2 | q3 | q4 | q5
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact q3
    · exact False.elim (q4 u0)
    · exact False.elim (q5 u3)
  have u6 : p1085 := by
    rcases h6453 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : p1086 := by
    rcases h6458 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u8 : p1087 := by
    rcases h6463 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u9 : p1088 := by
    rcases h6468 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u10 : p1089 := by
    rcases h6473 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  rcases h6366 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u6)
  · exact False.elim (q3 u7)
  · exact False.elim (q4 u8)
  · exact False.elim (q5 u9)
  · exact False.elim (q6 u10)

theorem step20936 (p1080 p1083 p1090 p1091 p1092 : Prop)
    (h20932 : p1090 ∨ p1080 ∨ p1083)
    (h20933 : p1091 ∨ p1080 ∨ p1083)
    (h20934 : p1092 ∨ p1080 ∨ p1083)
    (h20935 : (¬ p1092) ∨ p1080 ∨ p1083 ∨ (¬ p1091) ∨ (¬ p1090)) : p1080 ∨ p1083 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1080) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1083) := fun hu => hn (Or.inr hu)
  have u2 : p1090 := by
    rcases h20932 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1091 := by
    rcases h20933 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1092 := by
    rcases h20934 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20935 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u4)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)

theorem step20937 (p495 p499 p502 p507 p508 p509 p510 p511 : Prop)
    (h2827 : p502 ∨ p507)
    (h2828 : p502 ∨ p508)
    (h2829 : p502 ∨ p509)
    (h2830 : p502 ∨ p510)
    (h2831 : p502 ∨ p511)
    (h2764 : p495 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p502 ∨ p495 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h2827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p508 := by
    rcases h2828 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p509 := by
    rcases h2829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p510 := by
    rcases h2830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p511 := by
    rcases h2831 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2764 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20938 (p495 p499 p503 p507 p508 p509 p510 p511 : Prop)
    (h2832 : p503 ∨ p507)
    (h2833 : p503 ∨ p508)
    (h2834 : p503 ∨ p509)
    (h2835 : p503 ∨ p510)
    (h2836 : p503 ∨ p511)
    (h2764 : p495 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p503 ∨ p495 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p503) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2764 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20939 (p495 p499 p504 p507 p508 p509 p510 p511 : Prop)
    (h2837 : p504 ∨ p507)
    (h2838 : p504 ∨ p508)
    (h2839 : p504 ∨ p509)
    (h2840 : p504 ∨ p510)
    (h2841 : p504 ∨ p511)
    (h2764 : p495 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p504 ∨ p495 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p504) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2764 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20940 (p495 p499 p505 p507 p508 p509 p510 p511 : Prop)
    (h2842 : p505 ∨ p507)
    (h2843 : p505 ∨ p508)
    (h2844 : p505 ∨ p509)
    (h2845 : p505 ∨ p510)
    (h2846 : p505 ∨ p511)
    (h2764 : p495 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p505 ∨ p495 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p505) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2764 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20941 (p495 p499 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h2739 : p495 ∨ p499 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506))
    (h2847 : p506 ∨ p507)
    (h2848 : p506 ∨ p508)
    (h2849 : p506 ∨ p509)
    (h2850 : p506 ∨ p510)
    (h2851 : p506 ∨ p511)
    (h2764 : p495 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : (¬ p505) ∨ (¬ p504) ∨ p499 ∨ p495 ∨ (¬ p502) ∨ (¬ p503) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p505 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p504 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p495) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p502 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p503 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p506) := by
    rcases h2739 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p507 := by
    rcases h2847 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p508 := by
    rcases h2848 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p509 := by
    rcases h2849 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p510 := by
    rcases h2850 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p511 := by
    rcases h2851 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h2764 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20942 (p495 p499 p502 p503 p504 p505 : Prop)
    (h20937 : p502 ∨ p495 ∨ p499)
    (h20938 : p503 ∨ p495 ∨ p499)
    (h20939 : p504 ∨ p495 ∨ p499)
    (h20940 : p505 ∨ p495 ∨ p499)
    (h20941 : (¬ p505) ∨ (¬ p504) ∨ p499 ∨ p495 ∨ (¬ p502) ∨ (¬ p503)) : p495 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p495) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p499) := fun hu => hn (Or.inr hu)
  have u2 : p502 := by
    rcases h20937 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p503 := by
    rcases h20938 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p504 := by
    rcases h20939 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p505 := by
    rcases h20940 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20941 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step20943 (p456 p495 p499 p633 p634 p639 p1080 p1083 p1096 : Prop)
    (h20942 : p495 ∨ p499)
    (h10764 : p499 ∨ (¬ p634) ∨ (¬ p1096))
    (h20840 : p639 ∨ p634)
    (h13966 : (¬ p456) ∨ (¬ p633) ∨ (¬ p1083))
    (h16412 : (¬ p456) ∨ (¬ p495) ∨ (¬ p639) ∨ (¬ p1080) ∨ (¬ p1096))
    (h20936 : p1080 ∨ p1083) : (¬ p456) ∨ (¬ p633) ∨ p499 ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p456 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p633 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p495 := by
    rcases h20942 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : (¬ p634) := by
    rcases h10764 with q0 | q1 | q2
    · exact False.elim (u2 q0)
    · exact q1
    · exact False.elim (q2 u3)
  have u6 : p639 := by
    rcases h20840 with q0 | q1
    · exact q0
    · exact False.elim (u5 q1)
  have u7 : (¬ p1083) := by
    rcases h13966 with q0 | q1 | q2
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u1)
    · exact q2
  have u8 : (¬ p1080) := by
    rcases h16412 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u0)
    · exact False.elim (q1 u4)
    · exact False.elim (q2 u6)
    · exact q3
    · exact False.elim (q4 u3)
  rcases h20936 with q0 | q1
  · exact False.elim (u8 q0)
  · exact False.elim (u7 q1)

theorem step20944 (p1077 p1080 p1085 p1086 p1087 p1088 p1089 p1093 : Prop)
    (h6453 : p1085 ∨ p1093)
    (h6458 : p1086 ∨ p1093)
    (h6463 : p1087 ∨ p1093)
    (h6468 : p1088 ∨ p1093)
    (h6473 : p1089 ∨ p1093)
    (h6367 : p1077 ∨ p1080 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1093 ∨ p1080 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1093) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1085 := by
    rcases h6453 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1086 := by
    rcases h6458 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1087 := by
    rcases h6463 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1088 := by
    rcases h6468 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1089 := by
    rcases h6473 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h6367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20945 (p1077 p1080 p1085 p1086 p1087 p1088 p1089 p1094 : Prop)
    (h6454 : p1085 ∨ p1094)
    (h6459 : p1086 ∨ p1094)
    (h6464 : p1087 ∨ p1094)
    (h6469 : p1088 ∨ p1094)
    (h6474 : p1089 ∨ p1094)
    (h6367 : p1077 ∨ p1080 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1094 ∨ p1080 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1094) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20946 (p1077 p1080 p1085 p1086 p1087 p1088 p1089 p1090 : Prop)
    (h6450 : p1085 ∨ p1090)
    (h6455 : p1086 ∨ p1090)
    (h6460 : p1087 ∨ p1090)
    (h6465 : p1088 ∨ p1090)
    (h6470 : p1089 ∨ p1090)
    (h6367 : p1077 ∨ p1080 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1090 ∨ p1080 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1090) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20947 (p1077 p1080 p1085 p1086 p1087 p1088 p1089 p1091 : Prop)
    (h6451 : p1085 ∨ p1091)
    (h6456 : p1086 ∨ p1091)
    (h6461 : p1087 ∨ p1091)
    (h6466 : p1088 ∨ p1091)
    (h6471 : p1089 ∨ p1091)
    (h6367 : p1077 ∨ p1080 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : p1091 ∨ p1080 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1091) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20948 (p1077 p1080 p1085 p1086 p1087 p1088 p1089 p1090 p1091 p1092 p1093 p1094 : Prop)
    (h6392 : p1077 ∨ p1080 ∨ (¬ p1090) ∨ (¬ p1091) ∨ (¬ p1092) ∨ (¬ p1093) ∨ (¬ p1094))
    (h6452 : p1085 ∨ p1092)
    (h6457 : p1086 ∨ p1092)
    (h6462 : p1087 ∨ p1092)
    (h6467 : p1088 ∨ p1092)
    (h6472 : p1089 ∨ p1092)
    (h6367 : p1077 ∨ p1080 ∨ (¬ p1085) ∨ (¬ p1086) ∨ (¬ p1087) ∨ (¬ p1088) ∨ (¬ p1089)) : (¬ p1091) ∨ p1080 ∨ p1077 ∨ (¬ p1094) ∨ (¬ p1093) ∨ (¬ p1090) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1091 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p1080) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1077) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1094 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1093 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1090 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1092) := by
    rcases h6392 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u7 : p1085 := by
    rcases h6452 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1086 := by
    rcases h6457 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1087 := by
    rcases h6462 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1088 := by
    rcases h6467 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1089 := by
    rcases h6472 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h6367 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20949 (p1077 p1080 p1090 p1091 p1093 p1094 : Prop)
    (h20944 : p1093 ∨ p1080 ∨ p1077)
    (h20945 : p1094 ∨ p1080 ∨ p1077)
    (h20946 : p1090 ∨ p1080 ∨ p1077)
    (h20947 : p1091 ∨ p1080 ∨ p1077)
    (h20948 : (¬ p1091) ∨ p1080 ∨ p1077 ∨ (¬ p1094) ∨ (¬ p1093) ∨ (¬ p1090)) : p1080 ∨ p1077 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1080) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1077) := fun hu => hn (Or.inr hu)
  have u2 : p1093 := by
    rcases h20944 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1094 := by
    rcases h20945 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1090 := by
    rcases h20946 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1091 := by
    rcases h20947 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20948 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step20950 (p362 p382 p406 p420 p421 p456 : Prop)
    (h11290 : (¬ p362) ∨ (¬ p420) ∨ (¬ p421))
    (h20930 : p456 ∨ p362 ∨ (¬ p420) ∨ (¬ p382) ∨ p406) : (¬ p420) ∨ p456 ∨ (¬ p421) ∨ (¬ p382) ∨ p406 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p456) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p406) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p362) := by
    rcases h11290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u2)
  rcases h20930 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (u1 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)

theorem step20951 (p420 p600 p604 p605 p606 p607 p608 p613 : Prop)
    (h3469 : p604 ∨ p613)
    (h3474 : p605 ∨ p613)
    (h3479 : p606 ∨ p613)
    (h3484 : p607 ∨ p613)
    (h3489 : p608 ∨ p613)
    (h3376 : p420 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p613 ∨ p600 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p613) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p600) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3469 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3474 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3479 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3484 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3489 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20952 (p420 p600 p604 p605 p606 p607 p608 p609 : Prop)
    (h3465 : p604 ∨ p609)
    (h3470 : p605 ∨ p609)
    (h3475 : p606 ∨ p609)
    (h3480 : p607 ∨ p609)
    (h3485 : p608 ∨ p609)
    (h3376 : p420 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p609 ∨ p600 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p609) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p600) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3465 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3470 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3475 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3480 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3485 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20953 (p420 p600 p604 p605 p606 p607 p608 p610 : Prop)
    (h3466 : p604 ∨ p610)
    (h3471 : p605 ∨ p610)
    (h3476 : p606 ∨ p610)
    (h3481 : p607 ∨ p610)
    (h3486 : p608 ∨ p610)
    (h3376 : p420 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p610 ∨ p600 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p610) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p600) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3466 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3471 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3476 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3481 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3486 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20954 (p420 p600 p604 p605 p606 p607 p608 p611 : Prop)
    (h3467 : p604 ∨ p611)
    (h3472 : p605 ∨ p611)
    (h3477 : p606 ∨ p611)
    (h3482 : p607 ∨ p611)
    (h3487 : p608 ∨ p611)
    (h3376 : p420 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : p611 ∨ p600 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p611) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p600) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p420) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p604 := by
    rcases h3467 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p605 := by
    rcases h3472 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p606 := by
    rcases h3477 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p607 := by
    rcases h3482 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p608 := by
    rcases h3487 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20955 (p420 p600 p604 p605 p606 p607 p608 p609 p610 p611 p612 p613 : Prop)
    (h3401 : p420 ∨ p600 ∨ (¬ p609) ∨ (¬ p610) ∨ (¬ p611) ∨ (¬ p612) ∨ (¬ p613))
    (h3468 : p604 ∨ p612)
    (h3473 : p605 ∨ p612)
    (h3478 : p606 ∨ p612)
    (h3483 : p607 ∨ p612)
    (h3488 : p608 ∨ p612)
    (h3376 : p420 ∨ p600 ∨ (¬ p604) ∨ (¬ p605) ∨ (¬ p606) ∨ (¬ p607) ∨ (¬ p608)) : (¬ p611) ∨ (¬ p609) ∨ p600 ∨ p420 ∨ (¬ p613) ∨ (¬ p610) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p611 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p609 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p600) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p420) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p613 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p610 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p612) := by
    rcases h3401 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p604 := by
    rcases h3468 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p605 := by
    rcases h3473 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p606 := by
    rcases h3478 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p607 := by
    rcases h3483 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p608 := by
    rcases h3488 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3376 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20956 (p420 p600 p609 p610 p611 p613 : Prop)
    (h20951 : p613 ∨ p600 ∨ p420)
    (h20952 : p609 ∨ p600 ∨ p420)
    (h20953 : p610 ∨ p600 ∨ p420)
    (h20954 : p611 ∨ p600 ∨ p420)
    (h20955 : (¬ p611) ∨ (¬ p609) ∨ p600 ∨ p420 ∨ (¬ p613) ∨ (¬ p610)) : p600 ∨ p420 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p600) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p420) := fun hu => hn (Or.inr hu)
  have u2 : p613 := by
    rcases h20951 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p609 := by
    rcases h20952 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p610 := by
    rcases h20953 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p611 := by
    rcases h20954 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20955 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step20957 (p576 p580 p584 p585 p586 p587 p588 p593 : Prop)
    (h3342 : p584 ∨ p593)
    (h3347 : p585 ∨ p593)
    (h3352 : p586 ∨ p593)
    (h3357 : p587 ∨ p593)
    (h3362 : p588 ∨ p593)
    (h3249 : p576 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p593 ∨ p576 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p593) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3342 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3347 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3352 with q0 | q1
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
  rcases h3249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20958 (p576 p580 p584 p585 p586 p587 p588 p589 : Prop)
    (h3338 : p584 ∨ p589)
    (h3343 : p585 ∨ p589)
    (h3348 : p586 ∨ p589)
    (h3353 : p587 ∨ p589)
    (h3358 : p588 ∨ p589)
    (h3249 : p576 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p589 ∨ p576 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p589) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3348 with q0 | q1
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
  rcases h3249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20959 (p576 p580 p584 p585 p586 p587 p588 p590 : Prop)
    (h3339 : p584 ∨ p590)
    (h3344 : p585 ∨ p590)
    (h3349 : p586 ∨ p590)
    (h3354 : p587 ∨ p590)
    (h3359 : p588 ∨ p590)
    (h3249 : p576 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p590 ∨ p576 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p590) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3339 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3349 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3354 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3359 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20960 (p576 p580 p584 p585 p586 p587 p588 p591 : Prop)
    (h3340 : p584 ∨ p591)
    (h3345 : p585 ∨ p591)
    (h3350 : p586 ∨ p591)
    (h3355 : p587 ∨ p591)
    (h3360 : p588 ∨ p591)
    (h3249 : p576 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p591 ∨ p576 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p591) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p576) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3340 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3345 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3350 with q0 | q1
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
  rcases h3249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20962 (p126 p301 p522 p527 p528 p529 p530 p531 : Prop)
    (h2959 : p522 ∨ p527)
    (h2960 : p522 ∨ p528)
    (h2961 : p522 ∨ p529)
    (h2962 : p522 ∨ p530)
    (h2896 : p126 ∨ p301 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p522 ∨ p301 ∨ (¬ p531) ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p522) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
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
  rcases h2896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step20963 (p126 p301 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2896 : p126 ∨ p301 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ p301 ∨ (¬ p531) ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
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
  rcases h2896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step20964 (p126 p301 p524 p527 p528 p529 p530 p531 : Prop)
    (h2969 : p524 ∨ p527)
    (h2970 : p524 ∨ p528)
    (h2971 : p524 ∨ p529)
    (h2972 : p524 ∨ p530)
    (h2896 : p126 ∨ p301 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p524 ∨ p301 ∨ (¬ p531) ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p524) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
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
  rcases h2896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step20965 (p126 p301 p525 p527 p528 p529 p530 p531 : Prop)
    (h2974 : p525 ∨ p527)
    (h2975 : p525 ∨ p528)
    (h2976 : p525 ∨ p529)
    (h2977 : p525 ∨ p530)
    (h2896 : p126 ∨ p301 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p525 ∨ p301 ∨ (¬ p531) ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p525) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p126) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2974 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2975 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2976 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2977 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step20966 (p126 p301 p522 p523 p524 p525 p526 p527 p528 p529 p530 p531 : Prop)
    (h20962 : p522 ∨ p301 ∨ (¬ p531) ∨ p126)
    (h20963 : p523 ∨ p301 ∨ (¬ p531) ∨ p126)
    (h20964 : p524 ∨ p301 ∨ (¬ p531) ∨ p126)
    (h20965 : p525 ∨ p301 ∨ (¬ p531) ∨ p126)
    (h2871 : p126 ∨ p301 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526))
    (h2979 : p526 ∨ p527)
    (h2980 : p526 ∨ p528)
    (h2981 : p526 ∨ p529)
    (h2982 : p526 ∨ p530)
    (h2896 : p126 ∨ p301 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p301 ∨ (¬ p531) ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p301) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p126) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h20962 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
  have u4 : p523 := by
    rcases h20963 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
  have u5 : p524 := by
    rcases h20964 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
  have u6 : p525 := by
    rcases h20965 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (u2 q3)
  have u7 : (¬ p526) := by
    rcases h2871 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p527 := by
    rcases h2979 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p528 := by
    rcases h2980 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p529 := by
    rcases h2981 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p530 := by
    rcases h2982 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2896 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u1)

theorem step20967 (p574 p580 p584 p585 p586 p587 p588 p592 : Prop)
    (h3341 : p584 ∨ p592)
    (h3346 : p585 ∨ p592)
    (h3351 : p586 ∨ p592)
    (h3356 : p587 ∨ p592)
    (h3361 : p588 ∨ p592)
    (h3244 : p574 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p592 ∨ p574 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p592) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p574) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3341 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3346 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3351 with q0 | q1
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
  rcases h3244 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20968 (p574 p580 p584 p585 p586 p587 p588 p593 : Prop)
    (h3342 : p584 ∨ p593)
    (h3347 : p585 ∨ p593)
    (h3352 : p586 ∨ p593)
    (h3357 : p587 ∨ p593)
    (h3362 : p588 ∨ p593)
    (h3244 : p574 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p593 ∨ p574 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p593) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p574) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3342 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3347 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3352 with q0 | q1
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
  rcases h3244 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20969 (p574 p580 p584 p585 p586 p587 p588 p589 : Prop)
    (h3338 : p584 ∨ p589)
    (h3343 : p585 ∨ p589)
    (h3348 : p586 ∨ p589)
    (h3353 : p587 ∨ p589)
    (h3358 : p588 ∨ p589)
    (h3244 : p574 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p589 ∨ p574 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p589) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p574) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3348 with q0 | q1
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
  rcases h3244 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20970 (p574 p580 p584 p585 p586 p587 p588 p590 : Prop)
    (h3339 : p584 ∨ p590)
    (h3344 : p585 ∨ p590)
    (h3349 : p586 ∨ p590)
    (h3354 : p587 ∨ p590)
    (h3359 : p588 ∨ p590)
    (h3244 : p574 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : p590 ∨ p574 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p590) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p574) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p584 := by
    rcases h3339 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p585 := by
    rcases h3344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p586 := by
    rcases h3349 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p587 := by
    rcases h3354 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p588 := by
    rcases h3359 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3244 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20971 (p574 p580 p584 p585 p586 p587 p588 p589 p590 p591 p592 p593 : Prop)
    (h3269 : p574 ∨ p580 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593))
    (h3340 : p584 ∨ p591)
    (h3345 : p585 ∨ p591)
    (h3350 : p586 ∨ p591)
    (h3355 : p587 ∨ p591)
    (h3360 : p588 ∨ p591)
    (h3244 : p574 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : (¬ p590) ∨ (¬ p589) ∨ p580 ∨ p574 ∨ (¬ p593) ∨ (¬ p592) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p590 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p589 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p580) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p574) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p593 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p592 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p591) := by
    rcases h3269 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u5)
    · exact False.elim (q6 u4)
  have u7 : p584 := by
    rcases h3340 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p585 := by
    rcases h3345 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p586 := by
    rcases h3350 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p587 := by
    rcases h3355 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p588 := by
    rcases h3360 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3244 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20972 (p574 p580 p589 p590 p592 p593 : Prop)
    (h20967 : p592 ∨ p574 ∨ p580)
    (h20968 : p593 ∨ p574 ∨ p580)
    (h20969 : p589 ∨ p574 ∨ p580)
    (h20970 : p590 ∨ p574 ∨ p580)
    (h20971 : (¬ p590) ∨ (¬ p589) ∨ p580 ∨ p574 ∨ (¬ p593) ∨ (¬ p592)) : p574 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p574) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p580) := fun hu => hn (Or.inr hu)
  have u2 : p592 := by
    rcases h20967 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p593 := by
    rcases h20968 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p589 := by
    rcases h20969 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p590 := by
    rcases h20970 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20971 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step20973 (p126 p301 p522 p523 p524 p525 p526 p531 : Prop)
    (h20966 : p301 ∨ (¬ p531) ∨ p126)
    (h2963 : p522 ∨ p531)
    (h2968 : p523 ∨ p531)
    (h2973 : p524 ∨ p531)
    (h2978 : p525 ∨ p531)
    (h2983 : p526 ∨ p531)
    (h2871 : p126 ∨ p301 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p301 ∨ p126 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p301) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p126) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p531) := by
    rcases h20966 with q0 | q1 | q2
    · exact False.elim (u0 q0)
    · exact q1
    · exact False.elim (u1 q2)
  have u3 : p522 := by
    rcases h2963 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p523 := by
    rcases h2968 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p524 := by
    rcases h2973 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p525 := by
    rcases h2978 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p526 := by
    rcases h2983 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h2871 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20974 (p856 p861 p865 p866 p867 p868 p869 p874 : Prop)
    (h5031 : p865 ∨ p874)
    (h5036 : p866 ∨ p874)
    (h5041 : p867 ∨ p874)
    (h5046 : p868 ∨ p874)
    (h5051 : p869 ∨ p874)
    (h4927 : p856 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p874 ∨ p856 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p874) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p856) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h4927 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20975 (p856 p861 p865 p866 p867 p868 p869 p870 : Prop)
    (h5027 : p865 ∨ p870)
    (h5032 : p866 ∨ p870)
    (h5037 : p867 ∨ p870)
    (h5042 : p868 ∨ p870)
    (h5047 : p869 ∨ p870)
    (h4927 : p856 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p870 ∨ p856 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p870) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p856) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h4927 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20976 (p856 p861 p865 p866 p867 p868 p869 p871 : Prop)
    (h5028 : p865 ∨ p871)
    (h5033 : p866 ∨ p871)
    (h5038 : p867 ∨ p871)
    (h5043 : p868 ∨ p871)
    (h5048 : p869 ∨ p871)
    (h4927 : p856 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p871 ∨ p856 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p871) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p856) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h4927 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20977 (p856 p861 p865 p866 p867 p868 p869 p872 : Prop)
    (h5029 : p865 ∨ p872)
    (h5034 : p866 ∨ p872)
    (h5039 : p867 ∨ p872)
    (h5044 : p868 ∨ p872)
    (h5049 : p869 ∨ p872)
    (h4927 : p856 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : p872 ∨ p856 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p872) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p856) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4927 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20978 (p856 p861 p865 p866 p867 p868 p869 p870 p871 p872 p873 p874 : Prop)
    (h4952 : p856 ∨ p861 ∨ (¬ p870) ∨ (¬ p871) ∨ (¬ p872) ∨ (¬ p873) ∨ (¬ p874))
    (h5030 : p865 ∨ p873)
    (h5035 : p866 ∨ p873)
    (h5040 : p867 ∨ p873)
    (h5045 : p868 ∨ p873)
    (h5050 : p869 ∨ p873)
    (h4927 : p856 ∨ p861 ∨ (¬ p865) ∨ (¬ p866) ∨ (¬ p867) ∨ (¬ p868) ∨ (¬ p869)) : (¬ p872) ∨ p856 ∨ p861 ∨ (¬ p870) ∨ (¬ p874) ∨ (¬ p871) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p872 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p856) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p861) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p870 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p874 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p871 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p873) := by
    rcases h4952 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p865 := by
    rcases h5030 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p866 := by
    rcases h5035 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p867 := by
    rcases h5040 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p868 := by
    rcases h5045 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p869 := by
    rcases h5050 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4927 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20979 (p856 p861 p870 p871 p872 p874 : Prop)
    (h20974 : p874 ∨ p856 ∨ p861)
    (h20975 : p870 ∨ p856 ∨ p861)
    (h20976 : p871 ∨ p856 ∨ p861)
    (h20977 : p872 ∨ p856 ∨ p861)
    (h20978 : (¬ p872) ∨ p856 ∨ p861 ∨ (¬ p870) ∨ (¬ p874) ∨ (¬ p871)) : p856 ∨ p861 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p856) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p861) := fun hu => hn (Or.inr hu)
  have u2 : p874 := by
    rcases h20974 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p870 := by
    rcases h20975 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p871 := by
    rcases h20976 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p872 := by
    rcases h20977 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20978 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step20980 (p814 p819 p823 p824 p825 p826 p827 p832 : Prop)
    (h4773 : p823 ∨ p832)
    (h4778 : p824 ∨ p832)
    (h4783 : p825 ∨ p832)
    (h4788 : p826 ∨ p832)
    (h4793 : p827 ∨ p832)
    (h4679 : p814 ∨ p819 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p832 ∨ p819 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p832) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p819) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h4679 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20981 (p814 p819 p823 p824 p825 p826 p827 p828 : Prop)
    (h4769 : p823 ∨ p828)
    (h4774 : p824 ∨ p828)
    (h4779 : p825 ∨ p828)
    (h4784 : p826 ∨ p828)
    (h4789 : p827 ∨ p828)
    (h4679 : p814 ∨ p819 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p828 ∨ p819 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p828) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p819) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h4679 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20982 (p814 p819 p823 p824 p825 p826 p827 p829 : Prop)
    (h4770 : p823 ∨ p829)
    (h4775 : p824 ∨ p829)
    (h4780 : p825 ∨ p829)
    (h4785 : p826 ∨ p829)
    (h4790 : p827 ∨ p829)
    (h4679 : p814 ∨ p819 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p829 ∨ p819 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p829) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p819) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h4679 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20983 (p814 p819 p823 p824 p825 p826 p827 p830 : Prop)
    (h4771 : p823 ∨ p830)
    (h4776 : p824 ∨ p830)
    (h4781 : p825 ∨ p830)
    (h4786 : p826 ∨ p830)
    (h4791 : p827 ∨ p830)
    (h4679 : p814 ∨ p819 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : p830 ∨ p819 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p830) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p819) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p823 := by
    rcases h4771 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p824 := by
    rcases h4776 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p825 := by
    rcases h4781 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p826 := by
    rcases h4786 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p827 := by
    rcases h4791 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4679 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20984 (p814 p819 p823 p824 p825 p826 p827 p828 p829 p830 p831 p832 : Prop)
    (h4704 : p814 ∨ p819 ∨ (¬ p828) ∨ (¬ p829) ∨ (¬ p830) ∨ (¬ p831) ∨ (¬ p832))
    (h4772 : p823 ∨ p831)
    (h4777 : p824 ∨ p831)
    (h4782 : p825 ∨ p831)
    (h4787 : p826 ∨ p831)
    (h4792 : p827 ∨ p831)
    (h4679 : p814 ∨ p819 ∨ (¬ p823) ∨ (¬ p824) ∨ (¬ p825) ∨ (¬ p826) ∨ (¬ p827)) : (¬ p830) ∨ p819 ∨ p814 ∨ (¬ p828) ∨ (¬ p832) ∨ (¬ p829) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p830 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p819) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p814) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p828 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p832 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p829 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p831) := by
    rcases h4704 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u4)
  have u7 : p823 := by
    rcases h4772 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p824 := by
    rcases h4777 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p825 := by
    rcases h4782 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p826 := by
    rcases h4787 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p827 := by
    rcases h4792 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4679 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step20985 (p814 p819 p828 p829 p830 p832 : Prop)
    (h20980 : p832 ∨ p819 ∨ p814)
    (h20981 : p828 ∨ p819 ∨ p814)
    (h20982 : p829 ∨ p819 ∨ p814)
    (h20983 : p830 ∨ p819 ∨ p814)
    (h20984 : (¬ p830) ∨ p819 ∨ p814 ∨ (¬ p828) ∨ (¬ p832) ∨ (¬ p829)) : p819 ∨ p814 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p819) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p814) := fun hu => hn (Or.inr hu)
  have u2 : p832 := by
    rcases h20980 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p828 := by
    rcases h20981 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p829 := by
    rcases h20982 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p830 := by
    rcases h20983 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h20984 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u4)

theorem step20986 (p301 p518 p522 p527 p528 p529 p530 p531 : Prop)
    (h2959 : p522 ∨ p527)
    (h2960 : p522 ∨ p528)
    (h2961 : p522 ∨ p529)
    (h2962 : p522 ∨ p530)
    (h2894 : p301 ∨ p518 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p522 ∨ (¬ p531) ∨ p301 ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p522) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p518) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step20987 (p301 p518 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2894 : p301 ∨ p518 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ (¬ p531) ∨ p301 ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p518) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step20988 (p301 p518 p524 p527 p528 p529 p530 p531 : Prop)
    (h2969 : p524 ∨ p527)
    (h2970 : p524 ∨ p528)
    (h2971 : p524 ∨ p529)
    (h2972 : p524 ∨ p530)
    (h2894 : p301 ∨ p518 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p524 ∨ (¬ p531) ∨ p301 ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p524) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p518) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step20989 (p301 p518 p525 p527 p528 p529 p530 p531 : Prop)
    (h2974 : p525 ∨ p527)
    (h2975 : p525 ∨ p528)
    (h2976 : p525 ∨ p529)
    (h2977 : p525 ∨ p530)
    (h2894 : p301 ∨ p518 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p525 ∨ (¬ p531) ∨ p301 ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p525) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p518) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2974 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2975 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2976 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2977 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step20990 (p301 p518 p522 p523 p524 p525 p526 p527 p528 p529 p530 p531 : Prop)
    (h20986 : p522 ∨ (¬ p531) ∨ p301 ∨ p518)
    (h20987 : p523 ∨ (¬ p531) ∨ p301 ∨ p518)
    (h20988 : p524 ∨ (¬ p531) ∨ p301 ∨ p518)
    (h20989 : p525 ∨ (¬ p531) ∨ p301 ∨ p518)
    (h2869 : p301 ∨ p518 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526))
    (h2979 : p526 ∨ p527)
    (h2980 : p526 ∨ p528)
    (h2981 : p526 ∨ p529)
    (h2982 : p526 ∨ p530)
    (h2894 : p301 ∨ p518 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : (¬ p531) ∨ p301 ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p518) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h20986 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p523 := by
    rcases h20987 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p524 := by
    rcases h20988 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p525 := by
    rcases h20989 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p526) := by
    rcases h2869 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p527 := by
    rcases h2979 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p528 := by
    rcases h2980 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p529 := by
    rcases h2981 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p530 := by
    rcases h2982 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2894 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step20992 (p301 p518 p522 p523 p524 p525 p526 p531 : Prop)
    (h20990 : (¬ p531) ∨ p301 ∨ p518)
    (h2963 : p522 ∨ p531)
    (h2968 : p523 ∨ p531)
    (h2973 : p524 ∨ p531)
    (h2978 : p525 ∨ p531)
    (h2983 : p526 ∨ p531)
    (h2869 : p301 ∨ p518 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p301 ∨ p518 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p301) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p518) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p531) := by
    rcases h20990 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p522 := by
    rcases h2963 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p523 := by
    rcases h2968 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p524 := by
    rcases h2973 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p525 := by
    rcases h2978 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p526 := by
    rcases h2983 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h2869 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20993 (p125 p367 p371 p372 p373 p374 p375 p380 : Prop)
    (h2058 : p371 ∨ p380)
    (h2063 : p372 ∨ p380)
    (h2068 : p373 ∨ p380)
    (h2073 : p374 ∨ p380)
    (h2078 : p375 ∨ p380)
    (h1964 : p125 ∨ p367 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p380 ∨ p125 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p380) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1964 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step20994 (p125 p367 p371 p376 p377 p378 p379 p380 : Prop)
    (h20993 : p380 ∨ p125 ∨ p367)
    (h2054 : p371 ∨ p376)
    (h2055 : p371 ∨ p377)
    (h2056 : p371 ∨ p378)
    (h2057 : p371 ∨ p379)
    (h1989 : p125 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p371 ∨ p125 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p371) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h20993 with q0 | q1 | q2
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
  rcases h1989 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20995 (p125 p367 p372 p376 p377 p378 p379 p380 : Prop)
    (h20993 : p380 ∨ p125 ∨ p367)
    (h2059 : p372 ∨ p376)
    (h2060 : p372 ∨ p377)
    (h2061 : p372 ∨ p378)
    (h2062 : p372 ∨ p379)
    (h1989 : p125 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p372 ∨ p125 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p372) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h20993 with q0 | q1 | q2
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
  rcases h1989 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20996 (p125 p367 p373 p376 p377 p378 p379 p380 : Prop)
    (h20993 : p380 ∨ p125 ∨ p367)
    (h2064 : p373 ∨ p376)
    (h2065 : p373 ∨ p377)
    (h2066 : p373 ∨ p378)
    (h2067 : p373 ∨ p379)
    (h1989 : p125 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p373 ∨ p125 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p373) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h20993 with q0 | q1 | q2
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
  rcases h1989 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20997 (p125 p367 p374 p376 p377 p378 p379 p380 : Prop)
    (h20993 : p380 ∨ p125 ∨ p367)
    (h2069 : p374 ∨ p376)
    (h2070 : p374 ∨ p377)
    (h2071 : p374 ∨ p378)
    (h2072 : p374 ∨ p379)
    (h1989 : p125 ∨ p367 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p374 ∨ p125 ∨ p367 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p374) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p367) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p380 := by
    rcases h20993 with q0 | q1 | q2
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
  rcases h1989 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step20999 (p4 p5 p6 p7 p8 p9 p10 : Prop)
    (h16152 : (¬ p7))
    (h2 : (¬ p4) ∨ (¬ p5) ∨ (¬ p6) ∨ p7 ∨ (¬ p8) ∨ (¬ p9) ∨ (¬ p10)) : (¬ p10) ∨ (¬ p4) ∨ (¬ p8) ∨ (¬ p5) ∨ (¬ p6) ∨ (¬ p9) := by
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
  have u2 : p8 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p5 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p9 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p7) := by
    exact h16152
  rcases h2 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u3)
  · exact False.elim (q2 u4)
  · exact False.elim (u6 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u0)

theorem step21001 (p39 p40 p41 p42 : Prop)
    (h16150 : (¬ p40))
    (h132 : p42)
    (h131 : p39 ∨ p40 ∨ (¬ p41) ∨ (¬ p42)) : p39 ∨ (¬ p41) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p39) := fun hu => hn (Or.inl hu)
  have u1 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p40) := by
    exact h16150
  have u3 : p42 := by
    exact h132
  rcases h131 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step21002 (p6 p7 p19 p39 p63 p64 : Prop)
    (h16152 : (¬ p7))
    (h263 : (¬ p6) ∨ p7 ∨ (¬ p19) ∨ (¬ p39) ∨ (¬ p63) ∨ (¬ p64)) : (¬ p6) ∨ (¬ p63) ∨ (¬ p19) ∨ (¬ p39) ∨ (¬ p64) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p19 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p39 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p64 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p7) := by
    exact h16152
  rcases h263 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u1)
  · exact False.elim (q5 u4)

theorem step21003 (p45 p49 p128 p129 : Prop)
    (h653 : p128)
    (h16154 : (¬ p129))
    (h647 : (¬ p45) ∨ p49 ∨ (¬ p128) ∨ p129) : (¬ p45) ∨ p49 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p45 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p49) := fun hu => hn (Or.inr hu)
  have u2 : p128 := by
    exact h653
  have u3 : (¬ p129) := by
    exact h16154
  rcases h647 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step21005 (p156 p162 p163 p164 : Prop)
    (h16160 : (¬ p162))
    (h789 : p164)
    (h788 : p156 ∨ p162 ∨ (¬ p163) ∨ (¬ p164)) : p156 ∨ (¬ p163) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p156) := fun hu => hn (Or.inl hu)
  have u1 : p163 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p162) := by
    exact h16160
  have u3 : p164 := by
    exact h789
  rcases h788 with q0 | q1 | q2 | q3
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)

theorem step21006 (p41 p46 p230 : Prop)
    (h16165 : (¬ p230))
    (h16163 : (¬ p41) ∨ p46 ∨ p230) : (¬ p41) ∨ p46 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p41 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p46) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p230) := by
    exact h16165
  rcases h16163 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)

theorem step21007 (p17 p102 p193 p257 p258 : Prop)
    (h16170 : (¬ p257))
    (h16168 : (¬ p17) ∨ (¬ p102) ∨ (¬ p193) ∨ p257 ∨ (¬ p258)) : (¬ p17) ∨ (¬ p102) ∨ (¬ p193) ∨ (¬ p258) := by
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
  have u3 : p258 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p257) := by
    exact h16170
  rcases h16168 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u3)

theorem step21008 (p10 p102 p136 p189 p258 p279 p280 : Prop)
    (h1444 : p279)
    (h16173 : (¬ p280))
    (h16171 : (¬ p10) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p189) ∨ (¬ p258) ∨ (¬ p279) ∨ p280) : (¬ p10) ∨ (¬ p102) ∨ (¬ p136) ∨ (¬ p189) ∨ (¬ p258) := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p279 := by
    exact h1444
  have u6 : (¬ p280) := by
    exact h16173
  rcases h16171 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (u6 q6)

theorem step21009 (p17 p193 p301 p302 p303 : Prop)
    (h16285 : (¬ p302))
    (h16174 : (¬ p17) ∨ (¬ p193) ∨ (¬ p301) ∨ p302 ∨ (¬ p303)) : (¬ p17) ∨ (¬ p193) ∨ (¬ p301) ∨ (¬ p303) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p302) := by
    exact h16285
  rcases h16174 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u3)

theorem step21010 (p342 p343 p344 : Prop)
    (h1950 : p343)
    (h16175 : p342 ∨ (¬ p343) ∨ (¬ p344)) : p342 ∨ (¬ p344) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p342) := fun hu => hn (Or.inl hu)
  have u1 : p344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : p343 := by
    exact h1950
  rcases h16175 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)

theorem step21011 (p346 p350 p426 p427 : Prop)
    (h16178 : (¬ p426))
    (h2334 : p427)
    (h2333 : (¬ p346) ∨ p350 ∨ p426 ∨ (¬ p427)) : (¬ p346) ∨ p350 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p350) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p426) := by
    exact h16178
  have u3 : p427 := by
    exact h2334
  rcases h2333 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step21012 (p123 p134 p143 : Prop)
    (h16186 : (¬ p123))
    (h16184 : p123 ∨ (¬ p134) ∨ p143) : (¬ p134) ∨ p143 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p134 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p143) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p123) := by
    exact h16186
  rcases h16184 with q0 | q1 | q2
  · exact False.elim (u2 q0)
  · exact False.elim (q1 u0)
  · exact False.elim (u1 q2)

theorem step21013 (p542 p544 p653 : Prop)
    (h16194 : (¬ p653))
    (h16192 : p542 ∨ (¬ p544) ∨ p653) : p542 ∨ (¬ p544) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p542) := fun hu => hn (Or.inl hu)
  have u1 : p544 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr hu)
  have u2 : (¬ p653) := by
    exact h16194
  rcases h16192 with q0 | q1 | q2
  · exact False.elim (u0 q0)
  · exact False.elim (q1 u1)
  · exact False.elim (u2 q2)

theorem step21014 (p6 p213 p658 p659 : Prop)
    (h16199 : (¬ p658))
    (h3753 : p659)
    (h3752 : (¬ p6) ∨ p213 ∨ p658 ∨ (¬ p659)) : (¬ p6) ∨ p213 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p6 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p213) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p658) := by
    exact h16199
  have u3 : p659 := by
    exact h3753
  rcases h3752 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step21015 (p304 p312 p681 p682 : Prop)
    (h3892 : p681)
    (h16203 : (¬ p682))
    (h3886 : (¬ p304) ∨ p312 ∨ (¬ p681) ∨ p682) : (¬ p304) ∨ p312 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p304 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p312) := fun hu => hn (Or.inr hu)
  have u2 : p681 := by
    exact h3892
  have u3 : (¬ p682) := by
    exact h16203
  rcases h3886 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (u3 q3)

theorem step21016 (p189 p324 p419 p788 p789 p790 : Prop)
    (h5066 : p788)
    (h16210 : (¬ p189) ∨ (¬ p324) ∨ (¬ p419) ∨ (¬ p788) ∨ (¬ p789) ∨ (¬ p790)) : (¬ p189) ∨ (¬ p324) ∨ (¬ p419) ∨ (¬ p789) ∨ (¬ p790) := by
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
  have u3 : p789 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p790 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p788 := by
    exact h5066
  rcases h16210 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21017 (p63 p86 p791 p792 : Prop)
    (h16213 : (¬ p791))
    (h4535 : p792)
    (h4534 : (¬ p63) ∨ p86 ∨ p791 ∨ (¬ p792)) : (¬ p63) ∨ p86 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p86) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p791) := by
    exact h16213
  have u3 : p792 := by
    exact h4535
  rcases h4534 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step21018 (p796 p802 p875 p876 : Prop)
    (h16220 : (¬ p875))
    (h5054 : p876)
    (h5053 : (¬ p796) ∨ p802 ∨ p875 ∨ (¬ p876)) : (¬ p796) ∨ p802 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p796 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p802) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p875) := by
    exact h16220
  have u3 : p876 := by
    exact h5054
  rcases h5053 with q0 | q1 | q2 | q3
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)
  · exact False.elim (q3 u3)

theorem step21019 (p69 p1075 p1076 p1095 p1096 : Prop)
    (h6478 : p1075)
    (h16242 : (¬ p69) ∨ (¬ p1075) ∨ (¬ p1076) ∨ (¬ p1095) ∨ (¬ p1096)) : (¬ p69) ∨ (¬ p1095) ∨ (¬ p1076) ∨ (¬ p1096) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p69 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1095 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1076 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1096 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p1075 := by
    exact h6478
  rcases h16242 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u4)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u1)
  · exact False.elim (q4 u3)

theorem step21021 (p63 p87 p1136 : Prop)
    (h16259 : (¬ p1136))
    (h16257 : (¬ p63) ∨ p87 ∨ p1136) : (¬ p63) ∨ p87 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p63 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p87) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1136) := by
    exact h16259
  rcases h16257 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)

theorem step21022 (p8 p158 p346 p928 p1077 p1139 : Prop)
    (h6761 : p1139)
    (h16261 : (¬ p8) ∨ (¬ p158) ∨ (¬ p346) ∨ (¬ p928) ∨ (¬ p1077) ∨ (¬ p1139)) : (¬ p158) ∨ (¬ p8) ∨ (¬ p346) ∨ (¬ p928) ∨ (¬ p1077) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p158 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p8 := by
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
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : p1139 := by
    exact h6761
  rcases h16261 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u0)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)

theorem step21023 (p657 p664 p1181 : Prop)
    (h16272 : (¬ p1181))
    (h16270 : (¬ p657) ∨ p664 ∨ p1181) : (¬ p657) ∨ p664 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p657 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p664) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p1181) := by
    exact h16272
  rcases h16270 with q0 | q1 | q2
  · exact False.elim (q0 u0)
  · exact False.elim (u1 q1)
  · exact False.elim (u2 q2)

theorem step21024 (p10 p18 p69 p302 p303 p1184 : Prop)
    (h16285 : (¬ p302))
    (h7053 : p1184)
    (h16283 : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ p302 ∨ (¬ p303) ∨ (¬ p1184)) : (¬ p10) ∨ (¬ p18) ∨ (¬ p69) ∨ (¬ p303) := by
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
  have u3 : p303 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p302) := by
    exact h16285
  have u5 : p1184 := by
    exact h7053
  rcases h16283 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u4 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u5)

theorem step21027 (p15 p161 p1035 p1232 p1484 : Prop)
    (h16345 : (¬ p1484))
    (h16343 : (¬ p15) ∨ (¬ p161) ∨ (¬ p1035) ∨ (¬ p1232) ∨ p1484) : (¬ p1035) ∨ (¬ p15) ∨ (¬ p161) ∨ (¬ p1232) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1035 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p15 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p161 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1232 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1484) := by
    exact h16345
  rcases h16343 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u1)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u0)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)

theorem step21028 (p85 p1385 p1387 p1394 p1527 : Prop)
    (h16359 : (¬ p1527))
    (h16357 : (¬ p85) ∨ (¬ p1385) ∨ (¬ p1387) ∨ p1394 ∨ p1527) : p1394 ∨ (¬ p1385) ∨ (¬ p1387) ∨ (¬ p85) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1394) := fun hu => hn (Or.inl hu)
  have u1 : p1385 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p1387 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p85 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1527) := by
    exact h16359
  rcases h16357 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u3)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (u0 q3)
  · exact False.elim (u4 q4)

theorem step21030 (p346 p904 p1096 p1232 p1532 : Prop)
    (h16398 : (¬ p1532))
    (h16396 : (¬ p346) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1232) ∨ p1532) : (¬ p346) ∨ (¬ p904) ∨ (¬ p1096) ∨ (¬ p1232) := by
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
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1532) := by
    exact h16398
  rcases h16396 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)

theorem step21031 (p11 p126 p160 p532 p1539 : Prop)
    (h16419 : (¬ p1539))
    (h16417 : (¬ p11) ∨ (¬ p126) ∨ (¬ p160) ∨ (¬ p532) ∨ p1539) : (¬ p11) ∨ (¬ p160) ∨ (¬ p126) ∨ (¬ p532) := by
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
  have u2 : p126 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p532 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : (¬ p1539) := by
    exact h16419
  rcases h16417 with q0 | q1 | q2 | q3 | q4
  · exact False.elim (q0 u0)
  · exact False.elim (q1 u2)
  · exact False.elim (q2 u1)
  · exact False.elim (q3 u3)
  · exact False.elim (u4 q4)

theorem step21033 (p125 p362 p375 p376 p377 p378 p379 p380 : Prop)
    (h2074 : p375 ∨ p376)
    (h2075 : p375 ∨ p377)
    (h2076 : p375 ∨ p378)
    (h2077 : p375 ∨ p379)
    (h1991 : p125 ∨ p362 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380)) : p375 ∨ (¬ p380) ∨ p125 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p375) := fun hu => hn (Or.inl hu)
  have u1 : p380 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p362) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1991 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21034 (p125 p362 p371 p372 p373 p374 p375 p376 : Prop)
    (h2054 : p371 ∨ p376)
    (h2059 : p372 ∨ p376)
    (h2064 : p373 ∨ p376)
    (h2069 : p374 ∨ p376)
    (h1966 : p125 ∨ p362 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p376 ∨ (¬ p375) ∨ p125 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p376) := fun hu => hn (Or.inl hu)
  have u1 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p362) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21035 (p125 p362 p371 p372 p373 p374 p375 p377 : Prop)
    (h2055 : p371 ∨ p377)
    (h2060 : p372 ∨ p377)
    (h2065 : p373 ∨ p377)
    (h2070 : p374 ∨ p377)
    (h1966 : p125 ∨ p362 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p377 ∨ (¬ p375) ∨ p125 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p377) := fun hu => hn (Or.inl hu)
  have u1 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p362) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21036 (p125 p362 p371 p372 p373 p374 p375 p378 : Prop)
    (h2056 : p371 ∨ p378)
    (h2061 : p372 ∨ p378)
    (h2066 : p373 ∨ p378)
    (h2071 : p374 ∨ p378)
    (h1966 : p125 ∨ p362 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p378 ∨ (¬ p375) ∨ p125 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p378) := fun hu => hn (Or.inl hu)
  have u1 : p375 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p125) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p362) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21037 (p125 p362 p371 p372 p373 p374 p375 p376 p377 p378 p379 p380 : Prop)
    (h21033 : p375 ∨ (¬ p380) ∨ p125 ∨ p362)
    (h21034 : p376 ∨ (¬ p375) ∨ p125 ∨ p362)
    (h21035 : p377 ∨ (¬ p375) ∨ p125 ∨ p362)
    (h21036 : p378 ∨ (¬ p375) ∨ p125 ∨ p362)
    (h1991 : p125 ∨ p362 ∨ (¬ p376) ∨ (¬ p377) ∨ (¬ p378) ∨ (¬ p379) ∨ (¬ p380))
    (h2057 : p371 ∨ p379)
    (h2062 : p372 ∨ p379)
    (h2067 : p373 ∨ p379)
    (h2072 : p374 ∨ p379)
    (h1966 : p125 ∨ p362 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : (¬ p380) ∨ p125 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p380 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p125) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p362) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p375 := by
    rcases h21033 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p376 := by
    rcases h21034 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p377 := by
    rcases h21035 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p378 := by
    rcases h21036 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u3)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p379) := by
    rcases h1991 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
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
  rcases h1966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u3)

theorem step21038 (p125 p362 p371 p372 p373 p374 p375 p380 : Prop)
    (h21037 : (¬ p380) ∨ p125 ∨ p362)
    (h2058 : p371 ∨ p380)
    (h2063 : p372 ∨ p380)
    (h2068 : p373 ∨ p380)
    (h2073 : p374 ∨ p380)
    (h2078 : p375 ∨ p380)
    (h1966 : p125 ∨ p362 ∨ (¬ p371) ∨ (¬ p372) ∨ (¬ p373) ∨ (¬ p374) ∨ (¬ p375)) : p125 ∨ p362 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p125) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p362) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p380) := by
    rcases h21037 with q0 | q1 | q2
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
  rcases h1966 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21039 (p227 p961 p967 p968 p969 p970 p971 p976 : Prop)
    (h5690 : p967 ∨ p976)
    (h5695 : p968 ∨ p976)
    (h5700 : p969 ∨ p976)
    (h5705 : p970 ∨ p976)
    (h5710 : p971 ∨ p976)
    (h5598 : p227 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p976 ∨ p961 ∨ p227 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p976) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p961) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p227) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21040 (p227 p961 p967 p968 p969 p970 p971 p972 : Prop)
    (h5686 : p967 ∨ p972)
    (h5691 : p968 ∨ p972)
    (h5696 : p969 ∨ p972)
    (h5701 : p970 ∨ p972)
    (h5706 : p971 ∨ p972)
    (h5598 : p227 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p972 ∨ p961 ∨ p227 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p972) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p961) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p227) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5686 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5691 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5696 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5701 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21041 (p227 p961 p967 p968 p969 p970 p971 p973 : Prop)
    (h5687 : p967 ∨ p973)
    (h5692 : p968 ∨ p973)
    (h5697 : p969 ∨ p973)
    (h5702 : p970 ∨ p973)
    (h5707 : p971 ∨ p973)
    (h5598 : p227 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p973 ∨ p961 ∨ p227 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p973) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p961) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p227) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21042 (p227 p961 p967 p968 p969 p970 p971 p974 : Prop)
    (h5688 : p967 ∨ p974)
    (h5693 : p968 ∨ p974)
    (h5698 : p969 ∨ p974)
    (h5703 : p970 ∨ p974)
    (h5708 : p971 ∨ p974)
    (h5598 : p227 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p974 ∨ p961 ∨ p227 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p974) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p961) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p227) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21043 (p227 p961 p967 p968 p969 p970 p971 p972 p973 p974 p975 p976 : Prop)
    (h5623 : p227 ∨ p961 ∨ (¬ p972) ∨ (¬ p973) ∨ (¬ p974) ∨ (¬ p975) ∨ (¬ p976))
    (h5689 : p967 ∨ p975)
    (h5694 : p968 ∨ p975)
    (h5699 : p969 ∨ p975)
    (h5704 : p970 ∨ p975)
    (h5709 : p971 ∨ p975)
    (h5598 : p227 ∨ p961 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : (¬ p974) ∨ (¬ p976) ∨ p961 ∨ p227 ∨ (¬ p972) ∨ (¬ p973) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p974 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p976 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p227) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p972 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p973 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p975) := by
    rcases h5623 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u1)
  have u7 : p967 := by
    rcases h5689 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p968 := by
    rcases h5694 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p969 := by
    rcases h5699 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p970 := by
    rcases h5704 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p971 := by
    rcases h5709 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5598 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21044 (p227 p961 p972 p973 p974 p976 : Prop)
    (h21039 : p976 ∨ p961 ∨ p227)
    (h21040 : p972 ∨ p961 ∨ p227)
    (h21041 : p973 ∨ p961 ∨ p227)
    (h21042 : p974 ∨ p961 ∨ p227)
    (h21043 : (¬ p974) ∨ (¬ p976) ∨ p961 ∨ p227 ∨ (¬ p972) ∨ (¬ p973)) : p961 ∨ p227 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p961) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p227) := fun hu => hn (Or.inr hu)
  have u2 : p976 := by
    rcases h21039 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p972 := by
    rcases h21040 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p973 := by
    rcases h21041 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p974 := by
    rcases h21042 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21043 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u2)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21045 (p494 p499 p506 p507 p508 p509 p510 p511 : Prop)
    (h2847 : p506 ∨ p507)
    (h2848 : p506 ∨ p508)
    (h2849 : p506 ∨ p509)
    (h2850 : p506 ∨ p510)
    (h2851 : p506 ∨ p511)
    (h2754 : p494 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p506 ∨ p494 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p506) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21046 (p494 p499 p502 p507 p508 p509 p510 p511 : Prop)
    (h2827 : p502 ∨ p507)
    (h2828 : p502 ∨ p508)
    (h2829 : p502 ∨ p509)
    (h2830 : p502 ∨ p510)
    (h2831 : p502 ∨ p511)
    (h2754 : p494 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p502 ∨ p494 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p502) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p507 := by
    rcases h2827 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p508 := by
    rcases h2828 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p509 := by
    rcases h2829 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p510 := by
    rcases h2830 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p511 := by
    rcases h2831 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21047 (p494 p499 p503 p507 p508 p509 p510 p511 : Prop)
    (h2832 : p503 ∨ p507)
    (h2833 : p503 ∨ p508)
    (h2834 : p503 ∨ p509)
    (h2835 : p503 ∨ p510)
    (h2836 : p503 ∨ p511)
    (h2754 : p494 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p503 ∨ p494 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p503) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21048 (p494 p499 p504 p507 p508 p509 p510 p511 : Prop)
    (h2837 : p504 ∨ p507)
    (h2838 : p504 ∨ p508)
    (h2839 : p504 ∨ p509)
    (h2840 : p504 ∨ p510)
    (h2841 : p504 ∨ p511)
    (h2754 : p494 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p504 ∨ p494 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p504) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p494) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21049 (p425 p494 p499 p502 p503 p504 p505 p506 p507 p508 p509 p510 p511 : Prop)
    (h21045 : p506 ∨ p494 ∨ p499)
    (h21046 : p502 ∨ p494 ∨ p499)
    (h21047 : p503 ∨ p494 ∨ p499)
    (h21048 : p504 ∨ p494 ∨ p499)
    (h2727 : p425 ∨ p494 ∨ (¬ p502) ∨ (¬ p503) ∨ (¬ p504) ∨ (¬ p505) ∨ (¬ p506))
    (h2842 : p505 ∨ p507)
    (h2843 : p505 ∨ p508)
    (h2844 : p505 ∨ p509)
    (h2845 : p505 ∨ p510)
    (h2846 : p505 ∨ p511)
    (h2754 : p494 ∨ p499 ∨ (¬ p507) ∨ (¬ p508) ∨ (¬ p509) ∨ (¬ p510) ∨ (¬ p511)) : p494 ∨ p425 ∨ p499 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p494) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p425) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p499) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p506 := by
    rcases h21045 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p502 := by
    rcases h21046 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p503 := by
    rcases h21047 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p504 := by
    rcases h21048 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p505) := by
    rcases h2727 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p507 := by
    rcases h2842 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p508 := by
    rcases h2843 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p509 := by
    rcases h2844 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p510 := by
    rcases h2845 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u12 : p511 := by
    rcases h2846 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2754 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21050 (p344 p347 p352 p353 p354 p355 p356 p357 : Prop)
    (h1925 : p352 ∨ p357)
    (h1930 : p353 ∨ p357)
    (h1935 : p354 ∨ p357)
    (h1940 : p355 ∨ p357)
    (h1945 : p356 ∨ p357)
    (h1847 : p344 ∨ p347 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p357 ∨ p347 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p357) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p352 := by
    rcases h1925 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p353 := by
    rcases h1930 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p354 := by
    rcases h1935 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p355 := by
    rcases h1940 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p356 := by
    rcases h1945 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21051 (p344 p347 p352 p353 p354 p355 p356 p358 : Prop)
    (h1926 : p352 ∨ p358)
    (h1931 : p353 ∨ p358)
    (h1936 : p354 ∨ p358)
    (h1941 : p355 ∨ p358)
    (h1946 : p356 ∨ p358)
    (h1847 : p344 ∨ p347 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p358 ∨ p347 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p358) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p352 := by
    rcases h1926 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p353 := by
    rcases h1931 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p354 := by
    rcases h1936 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p355 := by
    rcases h1941 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p356 := by
    rcases h1946 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21052 (p344 p347 p352 p353 p354 p355 p356 p359 : Prop)
    (h1927 : p352 ∨ p359)
    (h1932 : p353 ∨ p359)
    (h1937 : p354 ∨ p359)
    (h1942 : p355 ∨ p359)
    (h1947 : p356 ∨ p359)
    (h1847 : p344 ∨ p347 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p359 ∨ p347 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p359) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p352 := by
    rcases h1927 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p353 := by
    rcases h1932 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p354 := by
    rcases h1937 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p355 := by
    rcases h1942 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p356 := by
    rcases h1947 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21053 (p344 p347 p352 p353 p354 p355 p356 p360 : Prop)
    (h1928 : p352 ∨ p360)
    (h1933 : p353 ∨ p360)
    (h1938 : p354 ∨ p360)
    (h1943 : p355 ∨ p360)
    (h1948 : p356 ∨ p360)
    (h1847 : p344 ∨ p347 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p360 ∨ p347 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p360) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p347) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p352 := by
    rcases h1928 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p353 := by
    rcases h1933 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p354 := by
    rcases h1938 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p355 := by
    rcases h1943 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p356 := by
    rcases h1948 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21054 (p344 p347 p348 p352 p353 p354 p355 p356 p357 p358 p359 p360 p361 : Prop)
    (h21050 : p357 ∨ p347 ∨ p344)
    (h21051 : p358 ∨ p347 ∨ p344)
    (h21052 : p359 ∨ p347 ∨ p344)
    (h21053 : p360 ∨ p347 ∨ p344)
    (h1870 : p347 ∨ p348 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361))
    (h1929 : p352 ∨ p361)
    (h1934 : p353 ∨ p361)
    (h1939 : p354 ∨ p361)
    (h1944 : p355 ∨ p361)
    (h1949 : p356 ∨ p361)
    (h1847 : p344 ∨ p347 ∨ (¬ p352) ∨ (¬ p353) ∨ (¬ p354) ∨ (¬ p355) ∨ (¬ p356)) : p347 ∨ p348 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p347) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p348) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p344) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p357 := by
    rcases h21050 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p358 := by
    rcases h21051 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p359 := by
    rcases h21052 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p360 := by
    rcases h21053 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p361) := by
    rcases h1870 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p352 := by
    rcases h1929 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p353 := by
    rcases h1934 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p354 := by
    rcases h1939 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p355 := by
    rcases h1944 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p356 := by
    rcases h1949 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h1847 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21055 (p434 p438 p445 p446 p447 p448 p449 p450 : Prop)
    (h2447 : p445 ∨ p450)
    (h2452 : p446 ∨ p450)
    (h2457 : p447 ∨ p450)
    (h2462 : p448 ∨ p450)
    (h2467 : p449 ∨ p450)
    (h2359 : p434 ∨ p438 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p450 ∨ p438 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p450) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p438) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21056 (p434 p438 p445 p446 p447 p448 p449 p451 : Prop)
    (h2448 : p445 ∨ p451)
    (h2453 : p446 ∨ p451)
    (h2458 : p447 ∨ p451)
    (h2463 : p448 ∨ p451)
    (h2468 : p449 ∨ p451)
    (h2359 : p434 ∨ p438 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p451 ∨ p438 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p451) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p438) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21057 (p434 p438 p445 p446 p447 p448 p449 p452 : Prop)
    (h2449 : p445 ∨ p452)
    (h2454 : p446 ∨ p452)
    (h2459 : p447 ∨ p452)
    (h2464 : p448 ∨ p452)
    (h2469 : p449 ∨ p452)
    (h2359 : p434 ∨ p438 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p452 ∨ p438 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p452) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p438) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21058 (p434 p438 p445 p446 p447 p448 p449 p453 : Prop)
    (h2450 : p445 ∨ p453)
    (h2455 : p446 ∨ p453)
    (h2460 : p447 ∨ p453)
    (h2465 : p448 ∨ p453)
    (h2470 : p449 ∨ p453)
    (h2359 : p434 ∨ p438 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : p453 ∨ p438 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p453) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p438) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p434) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21059 (p434 p438 p445 p446 p447 p448 p449 p450 p451 p452 p453 p454 : Prop)
    (h2384 : p434 ∨ p438 ∨ (¬ p450) ∨ (¬ p451) ∨ (¬ p452) ∨ (¬ p453) ∨ (¬ p454))
    (h2451 : p445 ∨ p454)
    (h2456 : p446 ∨ p454)
    (h2461 : p447 ∨ p454)
    (h2466 : p448 ∨ p454)
    (h2471 : p449 ∨ p454)
    (h2359 : p434 ∨ p438 ∨ (¬ p445) ∨ (¬ p446) ∨ (¬ p447) ∨ (¬ p448) ∨ (¬ p449)) : (¬ p453) ∨ (¬ p452) ∨ p438 ∨ p434 ∨ (¬ p450) ∨ (¬ p451) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p453 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p438) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p434) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p450 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p451 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p454) := by
    rcases h2384 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p445 := by
    rcases h2451 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p446 := by
    rcases h2456 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p447 := by
    rcases h2461 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p448 := by
    rcases h2466 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p449 := by
    rcases h2471 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h2359 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21060 (p434 p438 p450 p451 p452 p453 : Prop)
    (h21055 : p450 ∨ p438 ∨ p434)
    (h21056 : p451 ∨ p438 ∨ p434)
    (h21057 : p452 ∨ p438 ∨ p434)
    (h21058 : p453 ∨ p438 ∨ p434)
    (h21059 : (¬ p453) ∨ (¬ p452) ∨ p438 ∨ p434 ∨ (¬ p450) ∨ (¬ p451)) : p438 ∨ p434 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p438) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p434) := fun hu => hn (Or.inr hu)
  have u2 : p450 := by
    rcases h21055 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p451 := by
    rcases h21056 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p452 := by
    rcases h21057 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p453 := by
    rcases h21058 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21059 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21061 (p1 p540 p546 p547 p548 p549 p550 p551 : Prop)
    (h3087 : p546 ∨ p551)
    (h3092 : p547 ∨ p551)
    (h3097 : p548 ∨ p551)
    (h3102 : p549 ∨ p551)
    (h3107 : p550 ∨ p551)
    (h2993 : p1 ∨ p540 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p551 ∨ p540 ∨ p1 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p551) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p546 := by
    rcases h3087 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p547 := by
    rcases h3092 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p548 := by
    rcases h3097 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p549 := by
    rcases h3102 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p550 := by
    rcases h3107 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2993 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21062 (p1 p540 p546 p547 p548 p549 p550 p552 : Prop)
    (h3088 : p546 ∨ p552)
    (h3093 : p547 ∨ p552)
    (h3098 : p548 ∨ p552)
    (h3103 : p549 ∨ p552)
    (h3108 : p550 ∨ p552)
    (h2993 : p1 ∨ p540 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p552 ∨ p540 ∨ p1 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p552) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p546 := by
    rcases h3088 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p547 := by
    rcases h3093 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p548 := by
    rcases h3098 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p549 := by
    rcases h3103 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p550 := by
    rcases h3108 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2993 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21063 (p1 p540 p546 p547 p548 p549 p550 p553 : Prop)
    (h3089 : p546 ∨ p553)
    (h3094 : p547 ∨ p553)
    (h3099 : p548 ∨ p553)
    (h3104 : p549 ∨ p553)
    (h3109 : p550 ∨ p553)
    (h2993 : p1 ∨ p540 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p553 ∨ p540 ∨ p1 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p553) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p546 := by
    rcases h3089 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p547 := by
    rcases h3094 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p548 := by
    rcases h3099 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p549 := by
    rcases h3104 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p550 := by
    rcases h3109 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2993 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21064 (p1 p540 p546 p547 p548 p549 p550 p554 : Prop)
    (h3090 : p546 ∨ p554)
    (h3095 : p547 ∨ p554)
    (h3100 : p548 ∨ p554)
    (h3105 : p549 ∨ p554)
    (h3110 : p550 ∨ p554)
    (h2993 : p1 ∨ p540 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p554 ∨ p540 ∨ p1 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p554) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p546 := by
    rcases h3090 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p547 := by
    rcases h3095 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p548 := by
    rcases h3100 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p549 := by
    rcases h3105 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p550 := by
    rcases h3110 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h2993 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21065 (p1 p540 p544 p546 p547 p548 p549 p550 p551 p552 p553 p554 p555 : Prop)
    (h21061 : p551 ∨ p540 ∨ p1)
    (h21062 : p552 ∨ p540 ∨ p1)
    (h21063 : p553 ∨ p540 ∨ p1)
    (h21064 : p554 ∨ p540 ∨ p1)
    (h3019 : p540 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555))
    (h3091 : p546 ∨ p555)
    (h3096 : p547 ∨ p555)
    (h3101 : p548 ∨ p555)
    (h3106 : p549 ∨ p555)
    (h3111 : p550 ∨ p555)
    (h2993 : p1 ∨ p540 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p540 ∨ p1 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p540) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p544) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p551 := by
    rcases h21061 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p552 := by
    rcases h21062 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p553 := by
    rcases h21063 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p554 := by
    rcases h21064 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p555) := by
    rcases h3019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21066 (p540 p544 p546 p547 p548 p549 p550 p555 : Prop)
    (h3091 : p546 ∨ p555)
    (h3096 : p547 ∨ p555)
    (h3101 : p548 ∨ p555)
    (h3106 : p549 ∨ p555)
    (h3111 : p550 ∨ p555)
    (h2994 : p540 ∨ p544 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550)) : p555 ∨ p540 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p555) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p544) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h2994 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21067 (p540 p544 p546 p551 p552 p553 p554 p555 : Prop)
    (h21066 : p555 ∨ p540 ∨ p544)
    (h3087 : p546 ∨ p551)
    (h3088 : p546 ∨ p552)
    (h3089 : p546 ∨ p553)
    (h3090 : p546 ∨ p554)
    (h3019 : p540 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p546 ∨ p540 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p546) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p544) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21066 with q0 | q1 | q2
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
  rcases h3019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21068 (p540 p544 p547 p551 p552 p553 p554 p555 : Prop)
    (h21066 : p555 ∨ p540 ∨ p544)
    (h3092 : p547 ∨ p551)
    (h3093 : p547 ∨ p552)
    (h3094 : p547 ∨ p553)
    (h3095 : p547 ∨ p554)
    (h3019 : p540 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p547 ∨ p540 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p547) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p544) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21066 with q0 | q1 | q2
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
  rcases h3019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21069 (p540 p544 p548 p551 p552 p553 p554 p555 : Prop)
    (h21066 : p555 ∨ p540 ∨ p544)
    (h3097 : p548 ∨ p551)
    (h3098 : p548 ∨ p552)
    (h3099 : p548 ∨ p553)
    (h3100 : p548 ∨ p554)
    (h3019 : p540 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p548 ∨ p540 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p548) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p544) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21066 with q0 | q1 | q2
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
  rcases h3019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21070 (p540 p544 p549 p551 p552 p553 p554 p555 : Prop)
    (h21066 : p555 ∨ p540 ∨ p544)
    (h3102 : p549 ∨ p551)
    (h3103 : p549 ∨ p552)
    (h3104 : p549 ∨ p553)
    (h3105 : p549 ∨ p554)
    (h3019 : p540 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p549 ∨ p540 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p549) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p540) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p544) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p555 := by
    rcases h21066 with q0 | q1 | q2
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
  rcases h3019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21071 (p540 p544 p546 p547 p548 p549 p550 p551 p552 p553 p554 p555 : Prop)
    (h21066 : p555 ∨ p540 ∨ p544)
    (h21067 : p546 ∨ p540 ∨ p544)
    (h21068 : p547 ∨ p540 ∨ p544)
    (h21069 : p548 ∨ p540 ∨ p544)
    (h21070 : p549 ∨ p540 ∨ p544)
    (h2994 : p540 ∨ p544 ∨ (¬ p546) ∨ (¬ p547) ∨ (¬ p548) ∨ (¬ p549) ∨ (¬ p550))
    (h3107 : p550 ∨ p551)
    (h3108 : p550 ∨ p552)
    (h3109 : p550 ∨ p553)
    (h3110 : p550 ∨ p554)
    (h3019 : p540 ∨ p544 ∨ (¬ p551) ∨ (¬ p552) ∨ (¬ p553) ∨ (¬ p554) ∨ (¬ p555)) : p540 ∨ p544 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p540) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p544) := fun hu => hn (Or.inr hu)
  have u2 : p555 := by
    rcases h21066 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p546 := by
    rcases h21067 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p547 := by
    rcases h21068 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p548 := by
    rcases h21069 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p549 := by
    rcases h21070 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p550) := by
    rcases h2994 with q0 | q1 | q2 | q3 | q4 | q5 | q6
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
  rcases h3019 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21072 (p435 p1371 p1375 p1376 p1377 p1378 p1379 p1380 : Prop)
    (h8323 : p1375 ∨ p1380)
    (h8328 : p1376 ∨ p1380)
    (h8333 : p1377 ∨ p1380)
    (h8338 : p1378 ∨ p1380)
    (h8343 : p1379 ∨ p1380)
    (h8233 : p435 ∨ p1371 ∨ (¬ p1375) ∨ (¬ p1376) ∨ (¬ p1377) ∨ (¬ p1378) ∨ (¬ p1379)) : p1380 ∨ p1371 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1380) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1371) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1375 := by
    rcases h8323 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1376 := by
    rcases h8328 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1377 := by
    rcases h8333 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1378 := by
    rcases h8338 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1379 := by
    rcases h8343 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21073 (p435 p1371 p1375 p1376 p1377 p1378 p1379 p1381 : Prop)
    (h8324 : p1375 ∨ p1381)
    (h8329 : p1376 ∨ p1381)
    (h8334 : p1377 ∨ p1381)
    (h8339 : p1378 ∨ p1381)
    (h8344 : p1379 ∨ p1381)
    (h8233 : p435 ∨ p1371 ∨ (¬ p1375) ∨ (¬ p1376) ∨ (¬ p1377) ∨ (¬ p1378) ∨ (¬ p1379)) : p1381 ∨ p1371 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1381) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1371) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1375 := by
    rcases h8324 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1376 := by
    rcases h8329 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1377 := by
    rcases h8334 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1378 := by
    rcases h8339 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1379 := by
    rcases h8344 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21074 (p435 p1371 p1375 p1376 p1377 p1378 p1379 p1382 : Prop)
    (h8325 : p1375 ∨ p1382)
    (h8330 : p1376 ∨ p1382)
    (h8335 : p1377 ∨ p1382)
    (h8340 : p1378 ∨ p1382)
    (h8345 : p1379 ∨ p1382)
    (h8233 : p435 ∨ p1371 ∨ (¬ p1375) ∨ (¬ p1376) ∨ (¬ p1377) ∨ (¬ p1378) ∨ (¬ p1379)) : p1382 ∨ p1371 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1382) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1371) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1375 := by
    rcases h8325 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1376 := by
    rcases h8330 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1377 := by
    rcases h8335 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1378 := by
    rcases h8340 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1379 := by
    rcases h8345 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21075 (p435 p1371 p1375 p1376 p1377 p1378 p1379 p1383 : Prop)
    (h8326 : p1375 ∨ p1383)
    (h8331 : p1376 ∨ p1383)
    (h8336 : p1377 ∨ p1383)
    (h8341 : p1378 ∨ p1383)
    (h8346 : p1379 ∨ p1383)
    (h8233 : p435 ∨ p1371 ∨ (¬ p1375) ∨ (¬ p1376) ∨ (¬ p1377) ∨ (¬ p1378) ∨ (¬ p1379)) : p1383 ∨ p1371 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1383) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1371) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1375 := by
    rcases h8326 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1376 := by
    rcases h8331 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1377 := by
    rcases h8336 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1378 := by
    rcases h8341 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1379 := by
    rcases h8346 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21076 (p435 p1371 p1375 p1376 p1377 p1378 p1379 p1380 p1381 p1382 p1383 p1384 : Prop)
    (h8258 : p435 ∨ p1371 ∨ (¬ p1380) ∨ (¬ p1381) ∨ (¬ p1382) ∨ (¬ p1383) ∨ (¬ p1384))
    (h8327 : p1375 ∨ p1384)
    (h8332 : p1376 ∨ p1384)
    (h8337 : p1377 ∨ p1384)
    (h8342 : p1378 ∨ p1384)
    (h8347 : p1379 ∨ p1384)
    (h8233 : p435 ∨ p1371 ∨ (¬ p1375) ∨ (¬ p1376) ∨ (¬ p1377) ∨ (¬ p1378) ∨ (¬ p1379)) : (¬ p1383) ∨ (¬ p1382) ∨ p435 ∨ p1371 ∨ (¬ p1380) ∨ (¬ p1381) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1383 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1382 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p435) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1371) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1380 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1381 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1384) := by
    rcases h8258 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1375 := by
    rcases h8327 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1376 := by
    rcases h8332 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1377 := by
    rcases h8337 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1378 := by
    rcases h8342 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1379 := by
    rcases h8347 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8233 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21077 (p435 p1371 p1380 p1381 p1382 p1383 : Prop)
    (h21072 : p1380 ∨ p1371 ∨ p435)
    (h21073 : p1381 ∨ p1371 ∨ p435)
    (h21074 : p1382 ∨ p1371 ∨ p435)
    (h21075 : p1383 ∨ p1371 ∨ p435)
    (h21076 : (¬ p1383) ∨ (¬ p1382) ∨ p435 ∨ p1371 ∨ (¬ p1380) ∨ (¬ p1381)) : p1371 ∨ p435 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1371) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p435) := fun hu => hn (Or.inr hu)
  have u2 : p1380 := by
    rcases h21072 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1381 := by
    rcases h21073 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1382 := by
    rcases h21074 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1383 := by
    rcases h21075 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21076 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21078 (p752 p756 p759 p760 p761 p762 p763 p764 : Prop)
    (h4381 : p759 ∨ p764)
    (h4386 : p760 ∨ p764)
    (h4391 : p761 ∨ p764)
    (h4396 : p762 ∨ p764)
    (h4401 : p763 ∨ p764)
    (h4298 : p752 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p764 ∨ p756 ∨ p752 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p764) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p756) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p752) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4298 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21079 (p752 p756 p759 p760 p761 p762 p763 p765 : Prop)
    (h4382 : p759 ∨ p765)
    (h4387 : p760 ∨ p765)
    (h4392 : p761 ∨ p765)
    (h4397 : p762 ∨ p765)
    (h4402 : p763 ∨ p765)
    (h4298 : p752 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p765 ∨ p756 ∨ p752 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p765) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p756) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p752) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4298 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21080 (p752 p756 p759 p760 p761 p762 p763 p766 : Prop)
    (h4383 : p759 ∨ p766)
    (h4388 : p760 ∨ p766)
    (h4393 : p761 ∨ p766)
    (h4398 : p762 ∨ p766)
    (h4403 : p763 ∨ p766)
    (h4298 : p752 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p766 ∨ p756 ∨ p752 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p766) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p756) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p752) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p759 := by
    rcases h4383 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p760 := by
    rcases h4388 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p761 := by
    rcases h4393 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p762 := by
    rcases h4398 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p763 := by
    rcases h4403 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4298 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21081 (p752 p756 p759 p760 p761 p762 p763 p767 : Prop)
    (h4384 : p759 ∨ p767)
    (h4389 : p760 ∨ p767)
    (h4394 : p761 ∨ p767)
    (h4399 : p762 ∨ p767)
    (h4404 : p763 ∨ p767)
    (h4298 : p752 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p767 ∨ p756 ∨ p752 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p767) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p756) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p752) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4298 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21082 (p752 p756 p759 p760 p761 p762 p763 p764 p765 p766 p767 p768 : Prop)
    (h4323 : p752 ∨ p756 ∨ (¬ p764) ∨ (¬ p765) ∨ (¬ p766) ∨ (¬ p767) ∨ (¬ p768))
    (h4385 : p759 ∨ p768)
    (h4390 : p760 ∨ p768)
    (h4395 : p761 ∨ p768)
    (h4400 : p762 ∨ p768)
    (h4405 : p763 ∨ p768)
    (h4298 : p752 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : (¬ p767) ∨ (¬ p766) ∨ p752 ∨ p756 ∨ (¬ p764) ∨ (¬ p765) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p767 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p766 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p752) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p756) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p764 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p765 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p768) := by
    rcases h4323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p759 := by
    rcases h4385 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p760 := by
    rcases h4390 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p761 := by
    rcases h4395 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p762 := by
    rcases h4400 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p763 := by
    rcases h4405 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4298 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21083 (p752 p756 p764 p765 p766 p767 : Prop)
    (h21078 : p764 ∨ p756 ∨ p752)
    (h21079 : p765 ∨ p756 ∨ p752)
    (h21080 : p766 ∨ p756 ∨ p752)
    (h21081 : p767 ∨ p756 ∨ p752)
    (h21082 : (¬ p767) ∨ (¬ p766) ∨ p752 ∨ p756 ∨ (¬ p764) ∨ (¬ p765)) : p756 ∨ p752 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p756) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p752) := fun hu => hn (Or.inr hu)
  have u2 : p764 := by
    rcases h21078 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p765 := by
    rcases h21079 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p766 := by
    rcases h21080 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p767 := by
    rcases h21081 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21082 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21084 (p3 p557 p564 p565 p566 p567 p568 p569 : Prop)
    (h3212 : p564 ∨ p569)
    (h3217 : p565 ∨ p569)
    (h3222 : p566 ∨ p569)
    (h3227 : p567 ∨ p569)
    (h3232 : p568 ∨ p569)
    (h3119 : p3 ∨ p557 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p569 ∨ p3 ∨ p557 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p569) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p557) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p564 := by
    rcases h3212 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p565 := by
    rcases h3217 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p566 := by
    rcases h3222 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p567 := by
    rcases h3227 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p568 := by
    rcases h3232 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3119 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21085 (p3 p557 p564 p565 p566 p567 p568 p570 : Prop)
    (h3213 : p564 ∨ p570)
    (h3218 : p565 ∨ p570)
    (h3223 : p566 ∨ p570)
    (h3228 : p567 ∨ p570)
    (h3233 : p568 ∨ p570)
    (h3119 : p3 ∨ p557 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p570 ∨ p3 ∨ p557 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p570) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p557) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p564 := by
    rcases h3213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p565 := by
    rcases h3218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p566 := by
    rcases h3223 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p567 := by
    rcases h3228 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p568 := by
    rcases h3233 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3119 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21086 (p3 p557 p564 p565 p566 p567 p568 p571 : Prop)
    (h3214 : p564 ∨ p571)
    (h3219 : p565 ∨ p571)
    (h3224 : p566 ∨ p571)
    (h3229 : p567 ∨ p571)
    (h3234 : p568 ∨ p571)
    (h3119 : p3 ∨ p557 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p571 ∨ p3 ∨ p557 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p571) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p557) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p564 := by
    rcases h3214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p565 := by
    rcases h3219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p566 := by
    rcases h3224 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p567 := by
    rcases h3229 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p568 := by
    rcases h3234 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h3119 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21087 (p3 p557 p564 p565 p566 p567 p568 p572 : Prop)
    (h3215 : p564 ∨ p572)
    (h3220 : p565 ∨ p572)
    (h3225 : p566 ∨ p572)
    (h3230 : p567 ∨ p572)
    (h3235 : p568 ∨ p572)
    (h3119 : p3 ∨ p557 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : p572 ∨ p3 ∨ p557 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p572) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p3) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p557) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h3119 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21088 (p3 p557 p564 p565 p566 p567 p568 p569 p570 p571 p572 p573 : Prop)
    (h3144 : p3 ∨ p557 ∨ (¬ p569) ∨ (¬ p570) ∨ (¬ p571) ∨ (¬ p572) ∨ (¬ p573))
    (h3216 : p564 ∨ p573)
    (h3221 : p565 ∨ p573)
    (h3226 : p566 ∨ p573)
    (h3231 : p567 ∨ p573)
    (h3236 : p568 ∨ p573)
    (h3119 : p3 ∨ p557 ∨ (¬ p564) ∨ (¬ p565) ∨ (¬ p566) ∨ (¬ p567) ∨ (¬ p568)) : (¬ p572) ∨ (¬ p571) ∨ p557 ∨ p3 ∨ (¬ p569) ∨ (¬ p570) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p572 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p571 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p557) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p3) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p569 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p570 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p573) := by
    rcases h3144 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p564 := by
    rcases h3216 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p565 := by
    rcases h3221 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p566 := by
    rcases h3226 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p567 := by
    rcases h3231 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p568 := by
    rcases h3236 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3119 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21089 (p3 p557 p569 p570 p571 p572 : Prop)
    (h21084 : p569 ∨ p3 ∨ p557)
    (h21085 : p570 ∨ p3 ∨ p557)
    (h21086 : p571 ∨ p3 ∨ p557)
    (h21087 : p572 ∨ p3 ∨ p557)
    (h21088 : (¬ p572) ∨ (¬ p571) ∨ p557 ∨ p3 ∨ (¬ p569) ∨ (¬ p570)) : p3 ∨ p557 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p3) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p557) := fun hu => hn (Or.inr hu)
  have u2 : p569 := by
    rcases h21084 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p570 := by
    rcases h21085 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p571 := by
    rcases h21086 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p572 := by
    rcases h21087 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21088 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21090 (p534 p940 p949 p950 p951 p952 p953 p954 : Prop)
    (h5560 : p949 ∨ p954)
    (h5565 : p950 ∨ p954)
    (h5570 : p951 ∨ p954)
    (h5575 : p952 ∨ p954)
    (h5580 : p953 ∨ p954)
    (h5472 : p534 ∨ p940 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p954 ∨ p940 ∨ p534 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p954) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p940) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p534) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5472 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21091 (p534 p940 p949 p950 p951 p952 p953 p955 : Prop)
    (h5561 : p949 ∨ p955)
    (h5566 : p950 ∨ p955)
    (h5571 : p951 ∨ p955)
    (h5576 : p952 ∨ p955)
    (h5581 : p953 ∨ p955)
    (h5472 : p534 ∨ p940 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p955 ∨ p940 ∨ p534 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p955) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p940) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p534) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5472 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21092 (p534 p940 p949 p950 p951 p952 p953 p956 : Prop)
    (h5562 : p949 ∨ p956)
    (h5567 : p950 ∨ p956)
    (h5572 : p951 ∨ p956)
    (h5577 : p952 ∨ p956)
    (h5582 : p953 ∨ p956)
    (h5472 : p534 ∨ p940 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p956 ∨ p940 ∨ p534 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p956) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p940) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p534) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5472 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21093 (p534 p940 p949 p950 p951 p952 p953 p957 : Prop)
    (h5563 : p949 ∨ p957)
    (h5568 : p950 ∨ p957)
    (h5573 : p951 ∨ p957)
    (h5578 : p952 ∨ p957)
    (h5583 : p953 ∨ p957)
    (h5472 : p534 ∨ p940 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : p957 ∨ p940 ∨ p534 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p957) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p940) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p534) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p949 := by
    rcases h5563 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p950 := by
    rcases h5568 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p951 := by
    rcases h5573 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p952 := by
    rcases h5578 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p953 := by
    rcases h5583 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5472 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21094 (p534 p940 p949 p950 p951 p952 p953 p954 p955 p956 p957 p958 : Prop)
    (h5497 : p534 ∨ p940 ∨ (¬ p954) ∨ (¬ p955) ∨ (¬ p956) ∨ (¬ p957) ∨ (¬ p958))
    (h5564 : p949 ∨ p958)
    (h5569 : p950 ∨ p958)
    (h5574 : p951 ∨ p958)
    (h5579 : p952 ∨ p958)
    (h5584 : p953 ∨ p958)
    (h5472 : p534 ∨ p940 ∨ (¬ p949) ∨ (¬ p950) ∨ (¬ p951) ∨ (¬ p952) ∨ (¬ p953)) : (¬ p957) ∨ (¬ p956) ∨ p534 ∨ p940 ∨ (¬ p954) ∨ (¬ p955) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p957 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p956 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p534) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p940) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p954 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p955 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p958) := by
    rcases h5497 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p949 := by
    rcases h5564 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p950 := by
    rcases h5569 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p951 := by
    rcases h5574 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p952 := by
    rcases h5579 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p953 := by
    rcases h5584 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5472 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21095 (p534 p940 p954 p955 p956 p957 : Prop)
    (h21090 : p954 ∨ p940 ∨ p534)
    (h21091 : p955 ∨ p940 ∨ p534)
    (h21092 : p956 ∨ p940 ∨ p534)
    (h21093 : p957 ∨ p940 ∨ p534)
    (h21094 : (¬ p957) ∨ (¬ p956) ∨ p534 ∨ p940 ∨ (¬ p954) ∨ (¬ p955)) : p940 ∨ p534 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p940) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p534) := fun hu => hn (Or.inr hu)
  have u2 : p954 := by
    rcases h21090 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p955 := by
    rcases h21091 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p956 := by
    rcases h21092 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p957 := by
    rcases h21093 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21094 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21096 (p124 p306 p313 p314 p315 p316 p317 p318 : Prop)
    (h1673 : p313 ∨ p318)
    (h1678 : p314 ∨ p318)
    (h1683 : p315 ∨ p318)
    (h1688 : p316 ∨ p318)
    (h1693 : p317 ∨ p318)
    (h1580 : p124 ∨ p306 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p318 ∨ p306 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p318) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p306) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p313 := by
    rcases h1673 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p314 := by
    rcases h1678 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p315 := by
    rcases h1683 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p316 := by
    rcases h1688 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p317 := by
    rcases h1693 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1580 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21097 (p124 p306 p313 p314 p315 p316 p317 p319 : Prop)
    (h1674 : p313 ∨ p319)
    (h1679 : p314 ∨ p319)
    (h1684 : p315 ∨ p319)
    (h1689 : p316 ∨ p319)
    (h1694 : p317 ∨ p319)
    (h1580 : p124 ∨ p306 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p319 ∨ p306 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p319) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p306) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p313 := by
    rcases h1674 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p314 := by
    rcases h1679 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p315 := by
    rcases h1684 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p316 := by
    rcases h1689 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p317 := by
    rcases h1694 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1580 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21098 (p124 p306 p313 p314 p315 p316 p317 p320 : Prop)
    (h1675 : p313 ∨ p320)
    (h1680 : p314 ∨ p320)
    (h1685 : p315 ∨ p320)
    (h1690 : p316 ∨ p320)
    (h1695 : p317 ∨ p320)
    (h1580 : p124 ∨ p306 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p320 ∨ p306 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p320) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p306) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p313 := by
    rcases h1675 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p314 := by
    rcases h1680 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p315 := by
    rcases h1685 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p316 := by
    rcases h1690 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p317 := by
    rcases h1695 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1580 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21099 (p124 p306 p313 p314 p315 p316 p317 p321 : Prop)
    (h1676 : p313 ∨ p321)
    (h1681 : p314 ∨ p321)
    (h1686 : p315 ∨ p321)
    (h1691 : p316 ∨ p321)
    (h1696 : p317 ∨ p321)
    (h1580 : p124 ∨ p306 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p321 ∨ p306 ∨ p124 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p321) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p306) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p124) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p313 := by
    rcases h1676 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p314 := by
    rcases h1681 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p315 := by
    rcases h1686 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p316 := by
    rcases h1691 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p317 := by
    rcases h1696 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1580 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21101 (p124 p304 p313 p314 p315 p316 p317 p322 : Prop)
    (h1677 : p313 ∨ p322)
    (h1682 : p314 ∨ p322)
    (h1687 : p315 ∨ p322)
    (h1692 : p316 ∨ p322)
    (h1697 : p317 ∨ p322)
    (h1585 : p124 ∨ p304 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p322 ∨ p124 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p322) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p313 := by
    rcases h1677 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p314 := by
    rcases h1682 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p315 := by
    rcases h1687 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p316 := by
    rcases h1692 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p317 := by
    rcases h1697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1585 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21102 (p124 p304 p313 p318 p319 p320 p321 p322 : Prop)
    (h21101 : p322 ∨ p124 ∨ p304)
    (h1673 : p313 ∨ p318)
    (h1674 : p313 ∨ p319)
    (h1675 : p313 ∨ p320)
    (h1676 : p313 ∨ p321)
    (h1610 : p124 ∨ p304 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p313 ∨ p124 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p313) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p322 := by
    rcases h21101 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p318 := by
    rcases h1673 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p319 := by
    rcases h1674 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p320 := by
    rcases h1675 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p321 := by
    rcases h1676 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21103 (p124 p304 p314 p318 p319 p320 p321 p322 : Prop)
    (h21101 : p322 ∨ p124 ∨ p304)
    (h1678 : p314 ∨ p318)
    (h1679 : p314 ∨ p319)
    (h1680 : p314 ∨ p320)
    (h1681 : p314 ∨ p321)
    (h1610 : p124 ∨ p304 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p314 ∨ p124 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p314) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p322 := by
    rcases h21101 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p318 := by
    rcases h1678 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p319 := by
    rcases h1679 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p320 := by
    rcases h1680 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p321 := by
    rcases h1681 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21104 (p124 p304 p315 p318 p319 p320 p321 p322 : Prop)
    (h21101 : p322 ∨ p124 ∨ p304)
    (h1683 : p315 ∨ p318)
    (h1684 : p315 ∨ p319)
    (h1685 : p315 ∨ p320)
    (h1686 : p315 ∨ p321)
    (h1610 : p124 ∨ p304 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p315 ∨ p124 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p315) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p322 := by
    rcases h21101 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p318 := by
    rcases h1683 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p319 := by
    rcases h1684 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p320 := by
    rcases h1685 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p321 := by
    rcases h1686 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21105 (p124 p304 p316 p318 p319 p320 p321 p322 : Prop)
    (h21101 : p322 ∨ p124 ∨ p304)
    (h1688 : p316 ∨ p318)
    (h1689 : p316 ∨ p319)
    (h1690 : p316 ∨ p320)
    (h1691 : p316 ∨ p321)
    (h1610 : p124 ∨ p304 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p316 ∨ p124 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p316) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p124) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p322 := by
    rcases h21101 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p318 := by
    rcases h1688 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p319 := by
    rcases h1689 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p320 := by
    rcases h1690 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p321 := by
    rcases h1691 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h1610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21106 (p124 p304 p313 p314 p315 p316 p317 p318 p319 p320 p321 p322 : Prop)
    (h21101 : p322 ∨ p124 ∨ p304)
    (h21102 : p313 ∨ p124 ∨ p304)
    (h21103 : p314 ∨ p124 ∨ p304)
    (h21104 : p315 ∨ p124 ∨ p304)
    (h21105 : p316 ∨ p124 ∨ p304)
    (h1585 : p124 ∨ p304 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317))
    (h1693 : p317 ∨ p318)
    (h1694 : p317 ∨ p319)
    (h1695 : p317 ∨ p320)
    (h1696 : p317 ∨ p321)
    (h1610 : p124 ∨ p304 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p124 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p124) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p304) := fun hu => hn (Or.inr hu)
  have u2 : p322 := by
    rcases h21101 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p313 := by
    rcases h21102 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p314 := by
    rcases h21103 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p315 := by
    rcases h21104 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p316 := by
    rcases h21105 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p317) := by
    rcases h1585 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p318 := by
    rcases h1693 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p319 := by
    rcases h1694 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p320 := by
    rcases h1695 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p321 := by
    rcases h1696 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h1610 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21107 (p726 p756 p759 p760 p761 p762 p763 p768 : Prop)
    (h4385 : p759 ∨ p768)
    (h4390 : p760 ∨ p768)
    (h4395 : p761 ∨ p768)
    (h4400 : p762 ∨ p768)
    (h4405 : p763 ∨ p768)
    (h4293 : p726 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p768 ∨ p726 ∨ p756 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p768) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p726) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p756) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4293 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21108 (p726 p756 p759 p760 p761 p762 p763 p764 : Prop)
    (h4381 : p759 ∨ p764)
    (h4386 : p760 ∨ p764)
    (h4391 : p761 ∨ p764)
    (h4396 : p762 ∨ p764)
    (h4401 : p763 ∨ p764)
    (h4293 : p726 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p764 ∨ p726 ∨ p756 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p764) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p726) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p756) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4293 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21109 (p726 p756 p759 p760 p761 p762 p763 p765 : Prop)
    (h4382 : p759 ∨ p765)
    (h4387 : p760 ∨ p765)
    (h4392 : p761 ∨ p765)
    (h4397 : p762 ∨ p765)
    (h4402 : p763 ∨ p765)
    (h4293 : p726 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p765 ∨ p726 ∨ p756 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p765) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p726) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p756) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4293 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21110 (p726 p756 p759 p760 p761 p762 p763 p766 : Prop)
    (h4383 : p759 ∨ p766)
    (h4388 : p760 ∨ p766)
    (h4393 : p761 ∨ p766)
    (h4398 : p762 ∨ p766)
    (h4403 : p763 ∨ p766)
    (h4293 : p726 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : p766 ∨ p726 ∨ p756 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p766) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p726) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p756) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p759 := by
    rcases h4383 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p760 := by
    rcases h4388 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p761 := by
    rcases h4393 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p762 := by
    rcases h4398 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p763 := by
    rcases h4403 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4293 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21111 (p726 p756 p759 p760 p761 p762 p763 p764 p765 p766 p767 p768 : Prop)
    (h4318 : p726 ∨ p756 ∨ (¬ p764) ∨ (¬ p765) ∨ (¬ p766) ∨ (¬ p767) ∨ (¬ p768))
    (h4384 : p759 ∨ p767)
    (h4389 : p760 ∨ p767)
    (h4394 : p761 ∨ p767)
    (h4399 : p762 ∨ p767)
    (h4404 : p763 ∨ p767)
    (h4293 : p726 ∨ p756 ∨ (¬ p759) ∨ (¬ p760) ∨ (¬ p761) ∨ (¬ p762) ∨ (¬ p763)) : (¬ p766) ∨ p726 ∨ p756 ∨ (¬ p768) ∨ (¬ p764) ∨ (¬ p765) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p766 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p726) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p756) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p768 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p764 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p765 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p767) := by
    rcases h4318 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p759 := by
    rcases h4384 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p760 := by
    rcases h4389 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p761 := by
    rcases h4394 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p762 := by
    rcases h4399 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p763 := by
    rcases h4404 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4293 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21112 (p726 p756 p764 p765 p766 p768 : Prop)
    (h21107 : p768 ∨ p726 ∨ p756)
    (h21108 : p764 ∨ p726 ∨ p756)
    (h21109 : p765 ∨ p726 ∨ p756)
    (h21110 : p766 ∨ p726 ∨ p756)
    (h21111 : (¬ p766) ∨ p726 ∨ p756 ∨ (¬ p768) ∨ (¬ p764) ∨ (¬ p765)) : p726 ∨ p756 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p726) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p756) := fun hu => hn (Or.inr hu)
  have u2 : p768 := by
    rcases h21107 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p764 := by
    rcases h21108 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p765 := by
    rcases h21109 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p766 := by
    rcases h21110 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21111 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u4)

theorem step21114 (p342 p344 p352 p357 p358 p359 p360 p361 : Prop)
    (h1925 : p352 ∨ p357)
    (h1926 : p352 ∨ p358)
    (h1927 : p352 ∨ p359)
    (h1928 : p352 ∨ p360)
    (h1867 : p342 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p352 ∨ (¬ p361) ∨ p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p352) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p342) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1867 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21115 (p342 p344 p353 p357 p358 p359 p360 p361 : Prop)
    (h1930 : p353 ∨ p357)
    (h1931 : p353 ∨ p358)
    (h1932 : p353 ∨ p359)
    (h1933 : p353 ∨ p360)
    (h1867 : p342 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p353 ∨ (¬ p361) ∨ p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p353) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p342) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1867 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21116 (p342 p344 p354 p357 p358 p359 p360 p361 : Prop)
    (h1935 : p354 ∨ p357)
    (h1936 : p354 ∨ p358)
    (h1937 : p354 ∨ p359)
    (h1938 : p354 ∨ p360)
    (h1867 : p342 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p354 ∨ (¬ p361) ∨ p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p354) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p342) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1867 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21117 (p342 p344 p355 p357 p358 p359 p360 p361 : Prop)
    (h1940 : p355 ∨ p357)
    (h1941 : p355 ∨ p358)
    (h1942 : p355 ∨ p359)
    (h1943 : p355 ∨ p360)
    (h1867 : p342 ∨ p344 ∨ (¬ p357) ∨ (¬ p358) ∨ (¬ p359) ∨ (¬ p360) ∨ (¬ p361)) : p355 ∨ (¬ p361) ∨ p342 ∨ p344 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p355) := fun hu => hn (Or.inl hu)
  have u1 : p361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p342) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p344) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1867 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21119 (p306 p310 p317 p318 p319 p320 p321 p322 : Prop)
    (h1693 : p317 ∨ p318)
    (h1694 : p317 ∨ p319)
    (h1695 : p317 ∨ p320)
    (h1696 : p317 ∨ p321)
    (h1604 : p306 ∨ p310 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p317 ∨ (¬ p322) ∨ p310 ∨ p306 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p317) := fun hu => hn (Or.inl hu)
  have u1 : p322 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p310) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p306) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1604 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21120 (p304 p310 p313 p314 p315 p316 p317 p318 : Prop)
    (h1673 : p313 ∨ p318)
    (h1678 : p314 ∨ p318)
    (h1683 : p315 ∨ p318)
    (h1688 : p316 ∨ p318)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p318 ∨ (¬ p317) ∨ p310 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p318) := fun hu => hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p310) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21121 (p304 p310 p313 p314 p315 p316 p317 p319 : Prop)
    (h1674 : p313 ∨ p319)
    (h1679 : p314 ∨ p319)
    (h1684 : p315 ∨ p319)
    (h1689 : p316 ∨ p319)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p319 ∨ (¬ p317) ∨ p310 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p319) := fun hu => hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p310) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21122 (p304 p310 p313 p314 p315 p316 p317 p320 : Prop)
    (h1675 : p313 ∨ p320)
    (h1680 : p314 ∨ p320)
    (h1685 : p315 ∨ p320)
    (h1690 : p316 ∨ p320)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p320 ∨ (¬ p317) ∨ p310 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p320) := fun hu => hn (Or.inl hu)
  have u1 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p310) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21123 (p304 p306 p310 p313 p314 p315 p316 p317 p318 p319 p320 p321 p322 : Prop)
    (h21119 : p317 ∨ (¬ p322) ∨ p310 ∨ p306)
    (h21120 : p318 ∨ (¬ p317) ∨ p310 ∨ p304)
    (h21121 : p319 ∨ (¬ p317) ∨ p310 ∨ p304)
    (h21122 : p320 ∨ (¬ p317) ∨ p310 ∨ p304)
    (h1609 : p304 ∨ p310 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322))
    (h1676 : p313 ∨ p321)
    (h1681 : p314 ∨ p321)
    (h1686 : p315 ∨ p321)
    (h1691 : p316 ∨ p321)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : (¬ p322) ∨ p310 ∨ p306 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p322 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p306) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p317 := by
    rcases h21119 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p318 := by
    rcases h21120 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u6 : p319 := by
    rcases h21121 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u7 : p320 := by
    rcases h21122 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u4)
    · exact False.elim (u1 q2)
    · exact False.elim (u3 q3)
  have u8 : (¬ p321) := by
    rcases h1609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u6)
    · exact False.elim (q4 u7)
    · exact q5
    · exact False.elim (q6 u0)
  have u9 : p313 := by
    rcases h1676 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u10 : p314 := by
    rcases h1681 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u11 : p315 := by
    rcases h1686 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  have u12 : p316 := by
    rcases h1691 with q0 | q1
    · exact q0
    · exact False.elim (u8 q1)
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u9)
  · exact False.elim (q3 u10)
  · exact False.elim (q4 u11)
  · exact False.elim (q5 u12)
  · exact False.elim (q6 u4)

theorem step21124 (p304 p306 p310 p313 p314 p315 p316 p317 p322 : Prop)
    (h21123 : (¬ p322) ∨ p310 ∨ p306 ∨ p304)
    (h1677 : p313 ∨ p322)
    (h1682 : p314 ∨ p322)
    (h1687 : p315 ∨ p322)
    (h1692 : p316 ∨ p322)
    (h1697 : p317 ∨ p322)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p310 ∨ p306 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p310) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p306) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : (¬ p322) := by
    rcases h21123 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p313 := by
    rcases h1677 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u5 : p314 := by
    rcases h1682 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u6 : p315 := by
    rcases h1687 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u7 : p316 := by
    rcases h1692 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  have u8 : p317 := by
    rcases h1697 with q0 | q1
    · exact q0
    · exact False.elim (u3 q1)
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u8)

theorem step21125 (p125 p304 p306 p310 p342 p536 p726 : Prop)
    (h14732 : (¬ p306) ∨ (¬ p536) ∨ (¬ p726))
    (h17036 : (¬ p125) ∨ (¬ p310) ∨ (¬ p342) ∨ (¬ p536) ∨ (¬ p726))
    (h21124 : p310 ∨ p306 ∨ p304) : (¬ p536) ∨ (¬ p726) ∨ (¬ p342) ∨ p304 ∨ (¬ p125) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p536 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p726 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p304) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p125 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p306) := by
    rcases h14732 with q0 | q1 | q2
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (q2 u1)
  have u6 : (¬ p310) := by
    rcases h17036 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u4)
    · exact q1
    · exact False.elim (q2 u2)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u1)
  rcases h21124 with q0 | q1 | q2
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (u3 q2)

theorem step21126 (p304 p310 p313 p314 p315 p316 p317 p322 : Prop)
    (h1677 : p313 ∨ p322)
    (h1682 : p314 ∨ p322)
    (h1687 : p315 ∨ p322)
    (h1692 : p316 ∨ p322)
    (h1697 : p317 ∨ p322)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : p322 ∨ p310 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p322) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p313 := by
    rcases h1677 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p314 := by
    rcases h1682 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p315 := by
    rcases h1687 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p316 := by
    rcases h1692 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p317 := by
    rcases h1697 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21127 (p304 p310 p313 p314 p315 p316 p317 p318 p319 p320 p321 p322 : Prop)
    (h21126 : p322 ∨ p310 ∨ p304)
    (h21120 : p318 ∨ (¬ p317) ∨ p310 ∨ p304)
    (h21121 : p319 ∨ (¬ p317) ∨ p310 ∨ p304)
    (h21122 : p320 ∨ (¬ p317) ∨ p310 ∨ p304)
    (h1609 : p304 ∨ p310 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322))
    (h1676 : p313 ∨ p321)
    (h1681 : p314 ∨ p321)
    (h1686 : p315 ∨ p321)
    (h1691 : p316 ∨ p321)
    (h1584 : p304 ∨ p310 ∨ (¬ p313) ∨ (¬ p314) ∨ (¬ p315) ∨ (¬ p316) ∨ (¬ p317)) : (¬ p317) ∨ p310 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p317 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p310) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p304) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p322 := by
    rcases h21126 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p318 := by
    rcases h21120 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p319 := by
    rcases h21121 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p320 := by
    rcases h21122 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p321) := by
    rcases h1609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
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
  rcases h1584 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step21128 (p304 p310 p317 p318 p319 p320 p321 p322 : Prop)
    (h21126 : p322 ∨ p310 ∨ p304)
    (h21127 : (¬ p317) ∨ p310 ∨ p304)
    (h1693 : p317 ∨ p318)
    (h1694 : p317 ∨ p319)
    (h1695 : p317 ∨ p320)
    (h1696 : p317 ∨ p321)
    (h1609 : p304 ∨ p310 ∨ (¬ p318) ∨ (¬ p319) ∨ (¬ p320) ∨ (¬ p321) ∨ (¬ p322)) : p310 ∨ p304 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p310) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p304) := fun hu => hn (Or.inr hu)
  have u2 : p322 := by
    rcases h21126 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : (¬ p317) := by
    rcases h21127 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p318 := by
    rcases h1693 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u5 : p319 := by
    rcases h1694 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u6 : p320 := by
    rcases h1695 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  have u7 : p321 := by
    rcases h1696 with q0 | q1
    · exact False.elim (u3 q0)
    · exact q1
  rcases h1609 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u2)

theorem step21129 (p121 p1206 p1215 p1216 p1217 p1218 p1219 p1220 : Prop)
    (h7298 : p1215 ∨ p1220)
    (h7303 : p1216 ∨ p1220)
    (h7308 : p1217 ∨ p1220)
    (h7313 : p1218 ∨ p1220)
    (h7318 : p1219 ∨ p1220)
    (h7210 : p121 ∨ p1206 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1220 ∨ p121 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1220) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21130 (p121 p1206 p1215 p1216 p1217 p1218 p1219 p1221 : Prop)
    (h7299 : p1215 ∨ p1221)
    (h7304 : p1216 ∨ p1221)
    (h7309 : p1217 ∨ p1221)
    (h7314 : p1218 ∨ p1221)
    (h7319 : p1219 ∨ p1221)
    (h7210 : p121 ∨ p1206 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1221 ∨ p121 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1221) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21131 (p121 p1206 p1215 p1216 p1217 p1218 p1219 p1222 : Prop)
    (h7300 : p1215 ∨ p1222)
    (h7305 : p1216 ∨ p1222)
    (h7310 : p1217 ∨ p1222)
    (h7315 : p1218 ∨ p1222)
    (h7320 : p1219 ∨ p1222)
    (h7210 : p121 ∨ p1206 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1222 ∨ p121 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1222) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21132 (p121 p1206 p1215 p1216 p1217 p1218 p1219 p1223 : Prop)
    (h7301 : p1215 ∨ p1223)
    (h7306 : p1216 ∨ p1223)
    (h7311 : p1217 ∨ p1223)
    (h7316 : p1218 ∨ p1223)
    (h7321 : p1219 ∨ p1223)
    (h7210 : p121 ∨ p1206 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : p1223 ∨ p121 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1223) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p121) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21133 (p121 p1206 p1215 p1216 p1217 p1218 p1219 p1220 p1221 p1222 p1223 p1224 : Prop)
    (h7235 : p121 ∨ p1206 ∨ (¬ p1220) ∨ (¬ p1221) ∨ (¬ p1222) ∨ (¬ p1223) ∨ (¬ p1224))
    (h7302 : p1215 ∨ p1224)
    (h7307 : p1216 ∨ p1224)
    (h7312 : p1217 ∨ p1224)
    (h7317 : p1218 ∨ p1224)
    (h7322 : p1219 ∨ p1224)
    (h7210 : p121 ∨ p1206 ∨ (¬ p1215) ∨ (¬ p1216) ∨ (¬ p1217) ∨ (¬ p1218) ∨ (¬ p1219)) : (¬ p1223) ∨ (¬ p1222) ∨ p1206 ∨ p121 ∨ (¬ p1220) ∨ (¬ p1221) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1223 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1222 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1206) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p121) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1220 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1221 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1224) := by
    rcases h7235 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1215 := by
    rcases h7302 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1216 := by
    rcases h7307 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1217 := by
    rcases h7312 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1218 := by
    rcases h7317 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1219 := by
    rcases h7322 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7210 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21134 (p121 p1206 p1220 p1221 p1222 p1223 : Prop)
    (h21129 : p1220 ∨ p121 ∨ p1206)
    (h21130 : p1221 ∨ p121 ∨ p1206)
    (h21131 : p1222 ∨ p121 ∨ p1206)
    (h21132 : p1223 ∨ p121 ∨ p1206)
    (h21133 : (¬ p1223) ∨ (¬ p1222) ∨ p1206 ∨ p121 ∨ (¬ p1220) ∨ (¬ p1221)) : p121 ∨ p1206 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p121) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1206) := fun hu => hn (Or.inr hu)
  have u2 : p1220 := by
    rcases h21129 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1221 := by
    rcases h21130 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1222 := by
    rcases h21131 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1223 := by
    rcases h21132 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21133 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21135 (p258 p286 p291 p292 p293 p294 p295 p296 : Prop)
    (h1546 : p291 ∨ p296)
    (h1551 : p292 ∨ p296)
    (h1556 : p293 ∨ p296)
    (h1561 : p294 ∨ p296)
    (h1566 : p295 ∨ p296)
    (h1456 : p258 ∨ p286 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p296 ∨ p286 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p296) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1546 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1551 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1556 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1561 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1566 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1456 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21136 (p258 p286 p291 p292 p293 p294 p295 p297 : Prop)
    (h1547 : p291 ∨ p297)
    (h1552 : p292 ∨ p297)
    (h1557 : p293 ∨ p297)
    (h1562 : p294 ∨ p297)
    (h1567 : p295 ∨ p297)
    (h1456 : p258 ∨ p286 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p297 ∨ p286 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p297) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1547 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1552 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1557 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1562 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1567 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1456 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21137 (p258 p286 p291 p292 p293 p294 p295 p298 : Prop)
    (h1548 : p291 ∨ p298)
    (h1553 : p292 ∨ p298)
    (h1558 : p293 ∨ p298)
    (h1563 : p294 ∨ p298)
    (h1568 : p295 ∨ p298)
    (h1456 : p258 ∨ p286 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p298 ∨ p286 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p298) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1548 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1553 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1558 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1563 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1568 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1456 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21138 (p258 p286 p291 p292 p293 p294 p295 p299 : Prop)
    (h1549 : p291 ∨ p299)
    (h1554 : p292 ∨ p299)
    (h1559 : p293 ∨ p299)
    (h1564 : p294 ∨ p299)
    (h1569 : p295 ∨ p299)
    (h1456 : p258 ∨ p286 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p299 ∨ p286 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p299) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p286) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1456 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21139 (p258 p286 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h1481 : p258 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300))
    (h1550 : p291 ∨ p300)
    (h1555 : p292 ∨ p300)
    (h1560 : p293 ∨ p300)
    (h1565 : p294 ∨ p300)
    (h1570 : p295 ∨ p300)
    (h1456 : p258 ∨ p286 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : (¬ p299) ∨ (¬ p298) ∨ p258 ∨ p286 ∨ (¬ p296) ∨ (¬ p297) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p299 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p298 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p286) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p296 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p297 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p300) := by
    rcases h1481 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p291 := by
    rcases h1550 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p292 := by
    rcases h1555 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p293 := by
    rcases h1560 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p294 := by
    rcases h1565 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p295 := by
    rcases h1570 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1456 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21140 (p258 p286 p296 p297 p298 p299 : Prop)
    (h21135 : p296 ∨ p286 ∨ p258)
    (h21136 : p297 ∨ p286 ∨ p258)
    (h21137 : p298 ∨ p286 ∨ p258)
    (h21138 : p299 ∨ p286 ∨ p258)
    (h21139 : (¬ p299) ∨ (¬ p298) ∨ p258 ∨ p286 ∨ (¬ p296) ∨ (¬ p297)) : p286 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p286) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p258) := fun hu => hn (Or.inr hu)
  have u2 : p296 := by
    rcases h21135 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p297 := by
    rcases h21136 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p298 := by
    rcases h21137 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p299 := by
    rcases h21138 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21139 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21141 (p258 p289 p291 p292 p293 p294 p295 p300 : Prop)
    (h1550 : p291 ∨ p300)
    (h1555 : p292 ∨ p300)
    (h1560 : p293 ∨ p300)
    (h1565 : p294 ∨ p300)
    (h1570 : p295 ∨ p300)
    (h1459 : p258 ∨ p289 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p300 ∨ p289 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p300) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1550 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1555 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1560 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1565 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1570 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21142 (p258 p289 p291 p292 p293 p294 p295 p296 : Prop)
    (h1546 : p291 ∨ p296)
    (h1551 : p292 ∨ p296)
    (h1556 : p293 ∨ p296)
    (h1561 : p294 ∨ p296)
    (h1566 : p295 ∨ p296)
    (h1459 : p258 ∨ p289 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p296 ∨ p289 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p296) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1546 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1551 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1556 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1561 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1566 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21143 (p258 p289 p291 p292 p293 p294 p295 p297 : Prop)
    (h1547 : p291 ∨ p297)
    (h1552 : p292 ∨ p297)
    (h1557 : p293 ∨ p297)
    (h1562 : p294 ∨ p297)
    (h1567 : p295 ∨ p297)
    (h1459 : p258 ∨ p289 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p297 ∨ p289 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p297) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1547 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1552 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1557 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1562 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1567 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21144 (p258 p289 p291 p292 p293 p294 p295 p298 : Prop)
    (h1548 : p291 ∨ p298)
    (h1553 : p292 ∨ p298)
    (h1558 : p293 ∨ p298)
    (h1563 : p294 ∨ p298)
    (h1568 : p295 ∨ p298)
    (h1459 : p258 ∨ p289 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p298 ∨ p289 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p298) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p289) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p291 := by
    rcases h1548 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p292 := by
    rcases h1553 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p293 := by
    rcases h1558 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p294 := by
    rcases h1563 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p295 := by
    rcases h1568 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21145 (p258 p283 p289 p291 p292 p293 p294 p295 p296 p297 p298 p299 p300 : Prop)
    (h21141 : p300 ∨ p289 ∨ p258)
    (h21142 : p296 ∨ p289 ∨ p258)
    (h21143 : p297 ∨ p289 ∨ p258)
    (h21144 : p298 ∨ p289 ∨ p258)
    (h1474 : p283 ∨ p289 ∨ (¬ p296) ∨ (¬ p297) ∨ (¬ p298) ∨ (¬ p299) ∨ (¬ p300))
    (h1549 : p291 ∨ p299)
    (h1554 : p292 ∨ p299)
    (h1559 : p293 ∨ p299)
    (h1564 : p294 ∨ p299)
    (h1569 : p295 ∨ p299)
    (h1459 : p258 ∨ p289 ∨ (¬ p291) ∨ (¬ p292) ∨ (¬ p293) ∨ (¬ p294) ∨ (¬ p295)) : p289 ∨ p283 ∨ p258 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p289) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p283) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p258) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p300 := by
    rcases h21141 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u4 : p296 := by
    rcases h21142 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u5 : p297 := by
    rcases h21143 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u6 : p298 := by
    rcases h21144 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u2 q2)
  have u7 : (¬ p299) := by
    rcases h1474 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u1 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p291 := by
    rcases h1549 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p292 := by
    rcases h1554 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p293 := by
    rcases h1559 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p294 := by
    rcases h1564 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p295 := by
    rcases h1569 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h1459 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21146 (p17 p265 p269 p270 p271 p272 p273 p274 : Prop)
    (h1413 : p269 ∨ p274)
    (h1418 : p270 ∨ p274)
    (h1423 : p271 ∨ p274)
    (h1428 : p272 ∨ p274)
    (h1433 : p273 ∨ p274)
    (h1323 : p17 ∨ p265 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p274 ∨ p17 ∨ p265 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p274) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p265) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21147 (p17 p265 p269 p270 p271 p272 p273 p275 : Prop)
    (h1414 : p269 ∨ p275)
    (h1419 : p270 ∨ p275)
    (h1424 : p271 ∨ p275)
    (h1429 : p272 ∨ p275)
    (h1434 : p273 ∨ p275)
    (h1323 : p17 ∨ p265 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p275 ∨ p17 ∨ p265 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p275) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p265) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21148 (p17 p265 p269 p270 p271 p272 p273 p276 : Prop)
    (h1415 : p269 ∨ p276)
    (h1420 : p270 ∨ p276)
    (h1425 : p271 ∨ p276)
    (h1430 : p272 ∨ p276)
    (h1435 : p273 ∨ p276)
    (h1323 : p17 ∨ p265 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p276 ∨ p17 ∨ p265 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p265) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21149 (p17 p265 p269 p270 p271 p272 p273 p277 : Prop)
    (h1416 : p269 ∨ p277)
    (h1421 : p270 ∨ p277)
    (h1426 : p271 ∨ p277)
    (h1431 : p272 ∨ p277)
    (h1436 : p273 ∨ p277)
    (h1323 : p17 ∨ p265 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p277 ∨ p17 ∨ p265 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p277) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p265) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21150 (p17 p265 p269 p270 p271 p272 p273 p278 : Prop)
    (h1417 : p269 ∨ p278)
    (h1422 : p270 ∨ p278)
    (h1427 : p271 ∨ p278)
    (h1432 : p272 ∨ p278)
    (h1437 : p273 ∨ p278)
    (h1323 : p17 ∨ p265 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p278 ∨ p17 ∨ p265 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p265) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1323 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21151 (p17 p265 p274 p275 p276 p277 p278 : Prop)
    (h21146 : p274 ∨ p17 ∨ p265)
    (h21147 : p275 ∨ p17 ∨ p265)
    (h21148 : p276 ∨ p17 ∨ p265)
    (h21149 : p277 ∨ p17 ∨ p265)
    (h21150 : p278 ∨ p17 ∨ p265)
    (h1348 : p17 ∨ p265 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278)) : p17 ∨ p265 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p17) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p265) := fun hu => hn (Or.inr hu)
  have u2 : p274 := by
    rcases h21146 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p275 := by
    rcases h21147 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p276 := by
    rcases h21148 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p277 := by
    rcases h21149 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p278 := by
    rcases h21150 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h1348 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u5)
  · exact False.elim (q6 u6)

theorem step21152 (p1349 p1353 p1356 p1357 p1358 p1359 p1360 p1361 : Prop)
    (h8198 : p1356 ∨ p1361)
    (h8203 : p1357 ∨ p1361)
    (h8208 : p1358 ∨ p1361)
    (h8213 : p1359 ∨ p1361)
    (h8218 : p1360 ∨ p1361)
    (h8109 : p1349 ∨ p1353 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1361 ∨ p1353 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1361) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1353) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8203 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8208 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8109 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21153 (p1349 p1353 p1356 p1357 p1358 p1359 p1360 p1362 : Prop)
    (h8199 : p1356 ∨ p1362)
    (h8204 : p1357 ∨ p1362)
    (h8209 : p1358 ∨ p1362)
    (h8214 : p1359 ∨ p1362)
    (h8219 : p1360 ∨ p1362)
    (h8109 : p1349 ∨ p1353 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1362 ∨ p1353 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1362) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1353) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8209 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8109 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21154 (p1349 p1353 p1356 p1357 p1358 p1359 p1360 p1363 : Prop)
    (h8200 : p1356 ∨ p1363)
    (h8205 : p1357 ∨ p1363)
    (h8210 : p1358 ∨ p1363)
    (h8215 : p1359 ∨ p1363)
    (h8220 : p1360 ∨ p1363)
    (h8109 : p1349 ∨ p1353 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1363 ∨ p1353 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1363) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1353) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h8109 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21155 (p1349 p1353 p1356 p1357 p1358 p1359 p1360 p1364 : Prop)
    (h8201 : p1356 ∨ p1364)
    (h8206 : p1357 ∨ p1364)
    (h8211 : p1358 ∨ p1364)
    (h8216 : p1359 ∨ p1364)
    (h8221 : p1360 ∨ p1364)
    (h8109 : p1349 ∨ p1353 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1364 ∨ p1353 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1364) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1353) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8201 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8206 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8211 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8216 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8221 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8109 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21156 (p1349 p1353 p1356 p1357 p1358 p1359 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8134 : p1349 ∨ p1353 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365))
    (h8202 : p1356 ∨ p1365)
    (h8207 : p1357 ∨ p1365)
    (h8212 : p1358 ∨ p1365)
    (h8217 : p1359 ∨ p1365)
    (h8222 : p1360 ∨ p1365)
    (h8109 : p1349 ∨ p1353 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : (¬ p1364) ∨ (¬ p1363) ∨ p1349 ∨ p1353 ∨ (¬ p1361) ∨ (¬ p1362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1364 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1353) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1365) := by
    rcases h8134 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1356 := by
    rcases h8202 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1357 := by
    rcases h8207 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1358 := by
    rcases h8212 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1359 := by
    rcases h8217 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1360 := by
    rcases h8222 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8109 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21157 (p1349 p1353 p1361 p1362 p1363 p1364 : Prop)
    (h21152 : p1361 ∨ p1353 ∨ p1349)
    (h21153 : p1362 ∨ p1353 ∨ p1349)
    (h21154 : p1363 ∨ p1353 ∨ p1349)
    (h21155 : p1364 ∨ p1353 ∨ p1349)
    (h21156 : (¬ p1364) ∨ (¬ p1363) ∨ p1349 ∨ p1353 ∨ (¬ p1361) ∨ (¬ p1362)) : p1353 ∨ p1349 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1353) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1349) := fun hu => hn (Or.inr hu)
  have u2 : p1361 := by
    rcases h21152 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1362 := by
    rcases h21153 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1363 := by
    rcases h21154 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1364 := by
    rcases h21155 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21156 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21158 (p256 p264 p269 p270 p271 p272 p273 p274 : Prop)
    (h1413 : p269 ∨ p274)
    (h1418 : p270 ∨ p274)
    (h1423 : p271 ∨ p274)
    (h1428 : p272 ∨ p274)
    (h1433 : p273 ∨ p274)
    (h1335 : p256 ∨ p264 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p274 ∨ p264 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p274) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p264) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1335 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21159 (p256 p264 p269 p270 p271 p272 p273 p275 : Prop)
    (h1414 : p269 ∨ p275)
    (h1419 : p270 ∨ p275)
    (h1424 : p271 ∨ p275)
    (h1429 : p272 ∨ p275)
    (h1434 : p273 ∨ p275)
    (h1335 : p256 ∨ p264 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p275 ∨ p264 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p275) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p264) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1335 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21160 (p256 p264 p269 p270 p271 p272 p273 p276 : Prop)
    (h1415 : p269 ∨ p276)
    (h1420 : p270 ∨ p276)
    (h1425 : p271 ∨ p276)
    (h1430 : p272 ∨ p276)
    (h1435 : p273 ∨ p276)
    (h1335 : p256 ∨ p264 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p276 ∨ p264 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p264) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1335 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21161 (p256 p264 p269 p270 p271 p272 p273 p277 : Prop)
    (h1416 : p269 ∨ p277)
    (h1421 : p270 ∨ p277)
    (h1426 : p271 ∨ p277)
    (h1431 : p272 ∨ p277)
    (h1436 : p273 ∨ p277)
    (h1335 : p256 ∨ p264 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p277 ∨ p264 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p277) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p264) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1335 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21162 (p256 p264 p269 p270 p271 p272 p273 p274 p275 p276 p277 p278 : Prop)
    (h1360 : p256 ∨ p264 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278))
    (h1417 : p269 ∨ p278)
    (h1422 : p270 ∨ p278)
    (h1427 : p271 ∨ p278)
    (h1432 : p272 ∨ p278)
    (h1437 : p273 ∨ p278)
    (h1335 : p256 ∨ p264 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : (¬ p277) ∨ (¬ p276) ∨ p264 ∨ p256 ∨ (¬ p275) ∨ (¬ p274) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p277 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p276 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p264) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p256) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p275 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p278) := by
    rcases h1360 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p269 := by
    rcases h1417 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p270 := by
    rcases h1422 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p271 := by
    rcases h1427 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p272 := by
    rcases h1432 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p273 := by
    rcases h1437 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1335 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21163 (p256 p264 p274 p275 p276 p277 : Prop)
    (h21158 : p274 ∨ p264 ∨ p256)
    (h21159 : p275 ∨ p264 ∨ p256)
    (h21160 : p276 ∨ p264 ∨ p256)
    (h21161 : p277 ∨ p264 ∨ p256)
    (h21162 : (¬ p277) ∨ (¬ p276) ∨ p264 ∨ p256 ∨ (¬ p275) ∨ (¬ p274)) : p264 ∨ p256 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p264) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr hu)
  have u2 : p274 := by
    rcases h21158 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p275 := by
    rcases h21159 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p276 := by
    rcases h21160 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p277 := by
    rcases h21161 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21162 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step21164 (p576 p580 p584 p585 p586 p587 p588 p589 p590 p591 p592 p593 : Prop)
    (h3274 : p576 ∨ p580 ∨ (¬ p589) ∨ (¬ p590) ∨ (¬ p591) ∨ (¬ p592) ∨ (¬ p593))
    (h3341 : p584 ∨ p592)
    (h3346 : p585 ∨ p592)
    (h3351 : p586 ∨ p592)
    (h3356 : p587 ∨ p592)
    (h3361 : p588 ∨ p592)
    (h3249 : p576 ∨ p580 ∨ (¬ p584) ∨ (¬ p585) ∨ (¬ p586) ∨ (¬ p587) ∨ (¬ p588)) : (¬ p590) ∨ p580 ∨ (¬ p591) ∨ (¬ p593) ∨ p576 ∨ (¬ p589) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p590 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p580) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : p591 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p593 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p576) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p589 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p592) := by
    rcases h3274 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u5)
    · exact False.elim (q3 u0)
    · exact False.elim (q4 u2)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p584 := by
    rcases h3341 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p585 := by
    rcases h3346 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p586 := by
    rcases h3351 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p587 := by
    rcases h3356 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p588 := by
    rcases h3361 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h3249 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21165 (p576 p580 p589 p590 p591 p593 : Prop)
    (h20960 : p591 ∨ p576 ∨ p580)
    (h20957 : p593 ∨ p576 ∨ p580)
    (h20958 : p589 ∨ p576 ∨ p580)
    (h20959 : p590 ∨ p576 ∨ p580)
    (h21164 : (¬ p590) ∨ p580 ∨ (¬ p591) ∨ (¬ p593) ∨ p576 ∨ (¬ p589)) : p576 ∨ p580 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p576) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p580) := fun hu => hn (Or.inr hu)
  have u2 : p591 := by
    rcases h20960 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p593 := by
    rcases h20957 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p589 := by
    rcases h20958 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p590 := by
    rcases h20959 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21164 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u2)
  · exact False.elim (q3 u3)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step21167 (p11 p1495 p1498 p1499 p1500 p1501 p1502 p1503 : Prop)
    (h9153 : p1498 ∨ p1503)
    (h9158 : p1499 ∨ p1503)
    (h9163 : p1500 ∨ p1503)
    (h9168 : p1501 ∨ p1503)
    (h9173 : p1502 ∨ p1503)
    (h9063 : p11 ∨ p1495 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1503 ∨ p1495 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1503) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9153 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9158 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9163 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9168 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9173 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21168 (p11 p1495 p1498 p1499 p1500 p1501 p1502 p1504 : Prop)
    (h9154 : p1498 ∨ p1504)
    (h9159 : p1499 ∨ p1504)
    (h9164 : p1500 ∨ p1504)
    (h9169 : p1501 ∨ p1504)
    (h9174 : p1502 ∨ p1504)
    (h9063 : p11 ∨ p1495 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1504 ∨ p1495 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1504) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9154 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9159 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9164 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9169 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9174 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21169 (p11 p1495 p1498 p1499 p1500 p1501 p1502 p1505 : Prop)
    (h9155 : p1498 ∨ p1505)
    (h9160 : p1499 ∨ p1505)
    (h9165 : p1500 ∨ p1505)
    (h9170 : p1501 ∨ p1505)
    (h9175 : p1502 ∨ p1505)
    (h9063 : p11 ∨ p1495 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1505 ∨ p1495 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1505) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9155 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9160 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9165 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9170 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9175 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21170 (p11 p1495 p1498 p1499 p1500 p1501 p1502 p1506 : Prop)
    (h9156 : p1498 ∨ p1506)
    (h9161 : p1499 ∨ p1506)
    (h9166 : p1500 ∨ p1506)
    (h9171 : p1501 ∨ p1506)
    (h9176 : p1502 ∨ p1506)
    (h9063 : p11 ∨ p1495 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : p1506 ∨ p1495 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1506) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1495) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1498 := by
    rcases h9156 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1499 := by
    rcases h9161 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1500 := by
    rcases h9166 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1501 := by
    rcases h9171 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1502 := by
    rcases h9176 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21171 (p11 p17 p581 p1346 p1452 p1492 p1495 p1498 p1499 p1500 p1501 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h11775 : (¬ p17) ∨ (¬ p1346) ∨ (¬ p1492))
    (h19938 : (¬ p17) ∨ (¬ p581) ∨ (¬ p1346) ∨ (¬ p1452) ∨ (¬ p1495))
    (h21167 : p1503 ∨ p1495 ∨ p11)
    (h21168 : p1504 ∨ p1495 ∨ p11)
    (h21169 : p1505 ∨ p1495 ∨ p11)
    (h21170 : p1506 ∨ p1495 ∨ p11)
    (h9078 : p1492 ∨ p1495 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507))
    (h9157 : p1498 ∨ p1507)
    (h9162 : p1499 ∨ p1507)
    (h9167 : p1500 ∨ p1507)
    (h9172 : p1501 ∨ p1507)
    (h9177 : p1502 ∨ p1507)
    (h9063 : p11 ∨ p1495 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502)) : (¬ p1346) ∨ (¬ p581) ∨ p11 ∨ (¬ p17) ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1346 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p581 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p17 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p1492) := by
    rcases h11775 with q0 | q1 | q2
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u0)
    · exact q2
  have u6 : (¬ p1495) := by
    rcases h19938 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u3)
    · exact False.elim (q1 u1)
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u4)
    · exact q4
  have u7 : p1503 := by
    rcases h21167 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u2 q2)
  have u8 : p1504 := by
    rcases h21168 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u2 q2)
  have u9 : p1505 := by
    rcases h21169 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u2 q2)
  have u10 : p1506 := by
    rcases h21170 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u6 q1)
    · exact False.elim (u2 q2)
  have u11 : (¬ p1507) := by
    rcases h9078 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u5 q0)
    · exact False.elim (u6 q1)
    · exact False.elim (q2 u7)
    · exact False.elim (q3 u8)
    · exact False.elim (q4 u9)
    · exact False.elim (q5 u10)
    · exact q6
  have u12 : p1498 := by
    rcases h9157 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u13 : p1499 := by
    rcases h9162 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u14 : p1500 := by
    rcases h9167 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u15 : p1501 := by
    rcases h9172 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  have u16 : p1502 := by
    rcases h9177 with q0 | q1
    · exact q0
    · exact False.elim (u11 q1)
  rcases h9063 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u6 q1)
  · exact False.elim (q2 u12)
  · exact False.elim (q3 u13)
  · exact False.elim (q4 u14)
  · exact False.elim (q5 u15)
  · exact False.elim (q6 u16)

theorem step21172 (p1346 p1349 p1356 p1357 p1358 p1359 p1360 p1365 : Prop)
    (h8202 : p1356 ∨ p1365)
    (h8207 : p1357 ∨ p1365)
    (h8212 : p1358 ∨ p1365)
    (h8217 : p1359 ∨ p1365)
    (h8222 : p1360 ∨ p1365)
    (h8110 : p1346 ∨ p1349 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1365 ∨ p1349 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1365) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8202 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8207 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8212 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8217 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8222 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21173 (p1346 p1349 p1356 p1357 p1358 p1359 p1360 p1361 : Prop)
    (h8198 : p1356 ∨ p1361)
    (h8203 : p1357 ∨ p1361)
    (h8208 : p1358 ∨ p1361)
    (h8213 : p1359 ∨ p1361)
    (h8218 : p1360 ∨ p1361)
    (h8110 : p1346 ∨ p1349 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1361 ∨ p1349 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1361) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8198 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8203 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8208 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8213 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8218 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21174 (p1346 p1349 p1356 p1357 p1358 p1359 p1360 p1362 : Prop)
    (h8199 : p1356 ∨ p1362)
    (h8204 : p1357 ∨ p1362)
    (h8209 : p1358 ∨ p1362)
    (h8214 : p1359 ∨ p1362)
    (h8219 : p1360 ∨ p1362)
    (h8110 : p1346 ∨ p1349 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1362 ∨ p1349 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1362) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1356 := by
    rcases h8199 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1357 := by
    rcases h8204 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1358 := by
    rcases h8209 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1359 := by
    rcases h8214 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1360 := by
    rcases h8219 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21175 (p1346 p1349 p1356 p1357 p1358 p1359 p1360 p1363 : Prop)
    (h8200 : p1356 ∨ p1363)
    (h8205 : p1357 ∨ p1363)
    (h8210 : p1358 ∨ p1363)
    (h8215 : p1359 ∨ p1363)
    (h8220 : p1360 ∨ p1363)
    (h8110 : p1346 ∨ p1349 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : p1363 ∨ p1349 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1363) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1349) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h8110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21176 (p1346 p1349 p1356 p1357 p1358 p1359 p1360 p1361 p1362 p1363 p1364 p1365 : Prop)
    (h8135 : p1346 ∨ p1349 ∨ (¬ p1361) ∨ (¬ p1362) ∨ (¬ p1363) ∨ (¬ p1364) ∨ (¬ p1365))
    (h8201 : p1356 ∨ p1364)
    (h8206 : p1357 ∨ p1364)
    (h8211 : p1358 ∨ p1364)
    (h8216 : p1359 ∨ p1364)
    (h8221 : p1360 ∨ p1364)
    (h8110 : p1346 ∨ p1349 ∨ (¬ p1356) ∨ (¬ p1357) ∨ (¬ p1358) ∨ (¬ p1359) ∨ (¬ p1360)) : (¬ p1363) ∨ (¬ p1361) ∨ p1349 ∨ (¬ p1365) ∨ p1346 ∨ (¬ p1362) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1363 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1361 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1349) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p1365 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p1346) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1362 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1364) := by
    rcases h8135 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p1356 := by
    rcases h8201 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1357 := by
    rcases h8206 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1358 := by
    rcases h8211 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1359 := by
    rcases h8216 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1360 := by
    rcases h8221 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8110 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21177 (p1346 p1349 p1361 p1362 p1363 p1365 : Prop)
    (h21172 : p1365 ∨ p1349 ∨ p1346)
    (h21173 : p1361 ∨ p1349 ∨ p1346)
    (h21174 : p1362 ∨ p1349 ∨ p1346)
    (h21175 : p1363 ∨ p1349 ∨ p1346)
    (h21176 : (¬ p1363) ∨ (¬ p1361) ∨ p1349 ∨ (¬ p1365) ∨ p1346 ∨ (¬ p1362)) : p1349 ∨ p1346 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1349) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1346) := fun hu => hn (Or.inr hu)
  have u2 : p1365 := by
    rcases h21172 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1361 := by
    rcases h21173 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1362 := by
    rcases h21174 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1363 := by
    rcases h21175 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21176 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u1 q4)
  · exact False.elim (q5 u4)

theorem step21178 (p160 p1226 p1414 p1415 p1416 p1417 p1418 p1419 : Prop)
    (h8574 : p1414 ∨ p1419)
    (h8579 : p1415 ∨ p1419)
    (h8584 : p1416 ∨ p1419)
    (h8589 : p1417 ∨ p1419)
    (h8594 : p1418 ∨ p1419)
    (h8486 : p160 ∨ p1226 ∨ (¬ p1414) ∨ (¬ p1415) ∨ (¬ p1416) ∨ (¬ p1417) ∨ (¬ p1418)) : p1419 ∨ p1226 ∨ p160 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1419) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p160) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1414 := by
    rcases h8574 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1415 := by
    rcases h8579 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1416 := by
    rcases h8584 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1417 := by
    rcases h8589 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1418 := by
    rcases h8594 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21179 (p160 p1226 p1414 p1415 p1416 p1417 p1418 p1420 : Prop)
    (h8575 : p1414 ∨ p1420)
    (h8580 : p1415 ∨ p1420)
    (h8585 : p1416 ∨ p1420)
    (h8590 : p1417 ∨ p1420)
    (h8595 : p1418 ∨ p1420)
    (h8486 : p160 ∨ p1226 ∨ (¬ p1414) ∨ (¬ p1415) ∨ (¬ p1416) ∨ (¬ p1417) ∨ (¬ p1418)) : p1420 ∨ p1226 ∨ p160 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1420) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p160) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1414 := by
    rcases h8575 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1415 := by
    rcases h8580 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1416 := by
    rcases h8585 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1417 := by
    rcases h8590 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1418 := by
    rcases h8595 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21180 (p160 p1226 p1414 p1415 p1416 p1417 p1418 p1421 : Prop)
    (h8576 : p1414 ∨ p1421)
    (h8581 : p1415 ∨ p1421)
    (h8586 : p1416 ∨ p1421)
    (h8591 : p1417 ∨ p1421)
    (h8596 : p1418 ∨ p1421)
    (h8486 : p160 ∨ p1226 ∨ (¬ p1414) ∨ (¬ p1415) ∨ (¬ p1416) ∨ (¬ p1417) ∨ (¬ p1418)) : p1421 ∨ p1226 ∨ p160 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1421) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p160) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1414 := by
    rcases h8576 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1415 := by
    rcases h8581 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1416 := by
    rcases h8586 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1417 := by
    rcases h8591 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1418 := by
    rcases h8596 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21181 (p160 p1226 p1414 p1415 p1416 p1417 p1418 p1422 : Prop)
    (h8577 : p1414 ∨ p1422)
    (h8582 : p1415 ∨ p1422)
    (h8587 : p1416 ∨ p1422)
    (h8592 : p1417 ∨ p1422)
    (h8597 : p1418 ∨ p1422)
    (h8486 : p160 ∨ p1226 ∨ (¬ p1414) ∨ (¬ p1415) ∨ (¬ p1416) ∨ (¬ p1417) ∨ (¬ p1418)) : p1422 ∨ p1226 ∨ p160 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1422) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1226) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p160) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1414 := by
    rcases h8577 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1415 := by
    rcases h8582 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1416 := by
    rcases h8587 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1417 := by
    rcases h8592 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1418 := by
    rcases h8597 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21182 (p160 p1226 p1414 p1415 p1416 p1417 p1418 p1419 p1420 p1421 p1422 p1423 : Prop)
    (h8511 : p160 ∨ p1226 ∨ (¬ p1419) ∨ (¬ p1420) ∨ (¬ p1421) ∨ (¬ p1422) ∨ (¬ p1423))
    (h8578 : p1414 ∨ p1423)
    (h8583 : p1415 ∨ p1423)
    (h8588 : p1416 ∨ p1423)
    (h8593 : p1417 ∨ p1423)
    (h8598 : p1418 ∨ p1423)
    (h8486 : p160 ∨ p1226 ∨ (¬ p1414) ∨ (¬ p1415) ∨ (¬ p1416) ∨ (¬ p1417) ∨ (¬ p1418)) : (¬ p1422) ∨ (¬ p1421) ∨ p1226 ∨ p160 ∨ (¬ p1419) ∨ (¬ p1420) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1422 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1421 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1226) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p160) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1419 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1420 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1423) := by
    rcases h8511 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1414 := by
    rcases h8578 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1415 := by
    rcases h8583 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1416 := by
    rcases h8588 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1417 := by
    rcases h8593 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1418 := by
    rcases h8598 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8486 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21183 (p160 p1226 p1419 p1420 p1421 p1422 : Prop)
    (h21178 : p1419 ∨ p1226 ∨ p160)
    (h21179 : p1420 ∨ p1226 ∨ p160)
    (h21180 : p1421 ∨ p1226 ∨ p160)
    (h21181 : p1422 ∨ p1226 ∨ p160)
    (h21182 : (¬ p1422) ∨ (¬ p1421) ∨ p1226 ∨ p160 ∨ (¬ p1419) ∨ (¬ p1420)) : p1226 ∨ p160 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1226) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p160) := fun hu => hn (Or.inr hu)
  have u2 : p1419 := by
    rcases h21178 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1420 := by
    rcases h21179 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1421 := by
    rcases h21180 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1422 := by
    rcases h21181 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21182 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21184 (p959 p964 p967 p968 p969 p970 p971 p975 : Prop)
    (h5689 : p967 ∨ p975)
    (h5694 : p968 ∨ p975)
    (h5699 : p969 ∨ p975)
    (h5704 : p970 ∨ p975)
    (h5709 : p971 ∨ p975)
    (h5586 : p959 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p975 ∨ p964 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p975) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21185 (p959 p964 p967 p968 p969 p970 p971 p976 : Prop)
    (h5690 : p967 ∨ p976)
    (h5695 : p968 ∨ p976)
    (h5700 : p969 ∨ p976)
    (h5705 : p970 ∨ p976)
    (h5710 : p971 ∨ p976)
    (h5586 : p959 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p976 ∨ p964 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p976) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21186 (p959 p964 p967 p968 p969 p970 p971 p972 : Prop)
    (h5686 : p967 ∨ p972)
    (h5691 : p968 ∨ p972)
    (h5696 : p969 ∨ p972)
    (h5701 : p970 ∨ p972)
    (h5706 : p971 ∨ p972)
    (h5586 : p959 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p972 ∨ p964 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p972) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5686 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5691 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5696 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5701 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21187 (p959 p964 p967 p968 p969 p970 p971 p973 : Prop)
    (h5687 : p967 ∨ p973)
    (h5692 : p968 ∨ p973)
    (h5697 : p969 ∨ p973)
    (h5702 : p970 ∨ p973)
    (h5707 : p971 ∨ p973)
    (h5586 : p959 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p973 ∨ p964 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p973) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h5586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21188 (p959 p964 p967 p968 p969 p970 p971 p972 p973 p974 p975 p976 : Prop)
    (h5611 : p959 ∨ p964 ∨ (¬ p972) ∨ (¬ p973) ∨ (¬ p974) ∨ (¬ p975) ∨ (¬ p976))
    (h5688 : p967 ∨ p974)
    (h5693 : p968 ∨ p974)
    (h5698 : p969 ∨ p974)
    (h5703 : p970 ∨ p974)
    (h5708 : p971 ∨ p974)
    (h5586 : p959 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : (¬ p973) ∨ (¬ p972) ∨ p959 ∨ (¬ p975) ∨ (¬ p976) ∨ p964 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p973 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p972 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p959) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p975 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p976 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : (¬ p964) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p974) := by
    rcases h5611 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u5 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u0)
    · exact q4
    · exact False.elim (q5 u3)
    · exact False.elim (q6 u4)
  have u7 : p967 := by
    rcases h5688 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p968 := by
    rcases h5693 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p969 := by
    rcases h5698 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p970 := by
    rcases h5703 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p971 := by
    rcases h5708 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5586 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u5 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21189 (p959 p964 p972 p973 p975 p976 : Prop)
    (h21184 : p975 ∨ p964 ∨ p959)
    (h21185 : p976 ∨ p964 ∨ p959)
    (h21186 : p972 ∨ p964 ∨ p959)
    (h21187 : p973 ∨ p964 ∨ p959)
    (h21188 : (¬ p973) ∨ (¬ p972) ∨ p959 ∨ (¬ p975) ∨ (¬ p976) ∨ p964) : p964 ∨ p959 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p964) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p959) := fun hu => hn (Or.inr hu)
  have u2 : p975 := by
    rcases h21184 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p976 := by
    rcases h21185 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p972 := by
    rcases h21186 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p973 := by
    rcases h21187 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21188 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (q4 u3)
  · exact False.elim (u0 q5)

theorem step21190 (p1230 p1235 p1239 p1240 p1241 p1242 p1243 p1248 : Prop)
    (h7432 : p1239 ∨ p1248)
    (h7437 : p1240 ∨ p1248)
    (h7442 : p1241 ∨ p1248)
    (h7447 : p1242 ∨ p1248)
    (h7452 : p1243 ∨ p1248)
    (h7328 : p1230 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1248 ∨ p1230 ∨ p1235 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1248) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1230) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1235) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7432 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7437 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7442 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7447 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7452 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21191 (p1230 p1235 p1239 p1240 p1241 p1242 p1243 p1244 : Prop)
    (h7428 : p1239 ∨ p1244)
    (h7433 : p1240 ∨ p1244)
    (h7438 : p1241 ∨ p1244)
    (h7443 : p1242 ∨ p1244)
    (h7448 : p1243 ∨ p1244)
    (h7328 : p1230 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1244 ∨ p1230 ∨ p1235 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1244) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1230) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1235) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7428 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7433 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7438 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7443 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7448 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21192 (p1230 p1235 p1239 p1240 p1241 p1242 p1243 p1245 : Prop)
    (h7429 : p1239 ∨ p1245)
    (h7434 : p1240 ∨ p1245)
    (h7439 : p1241 ∨ p1245)
    (h7444 : p1242 ∨ p1245)
    (h7449 : p1243 ∨ p1245)
    (h7328 : p1230 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1245 ∨ p1230 ∨ p1235 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1245) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1230) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1235) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7429 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7434 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7439 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7444 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7449 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21193 (p1230 p1235 p1239 p1240 p1241 p1242 p1243 p1246 : Prop)
    (h7430 : p1239 ∨ p1246)
    (h7435 : p1240 ∨ p1246)
    (h7440 : p1241 ∨ p1246)
    (h7445 : p1242 ∨ p1246)
    (h7450 : p1243 ∨ p1246)
    (h7328 : p1230 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1246 ∨ p1230 ∨ p1235 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1246) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1230) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1235) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1239 := by
    rcases h7430 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1240 := by
    rcases h7435 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1241 := by
    rcases h7440 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1242 := by
    rcases h7445 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1243 := by
    rcases h7450 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h7328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21194 (p1229 p1230 p1235 p1239 p1240 p1241 p1242 p1243 p1244 p1245 p1246 p1247 p1248 : Prop)
    (h21190 : p1248 ∨ p1230 ∨ p1235)
    (h21191 : p1244 ∨ p1230 ∨ p1235)
    (h21192 : p1245 ∨ p1230 ∨ p1235)
    (h21193 : p1246 ∨ p1230 ∨ p1235)
    (h7355 : p1229 ∨ p1230 ∨ (¬ p1244) ∨ (¬ p1245) ∨ (¬ p1246) ∨ (¬ p1247) ∨ (¬ p1248))
    (h7431 : p1239 ∨ p1247)
    (h7436 : p1240 ∨ p1247)
    (h7441 : p1241 ∨ p1247)
    (h7446 : p1242 ∨ p1247)
    (h7451 : p1243 ∨ p1247)
    (h7328 : p1230 ∨ p1235 ∨ (¬ p1239) ∨ (¬ p1240) ∨ (¬ p1241) ∨ (¬ p1242) ∨ (¬ p1243)) : p1230 ∨ p1235 ∨ p1229 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1230) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1235) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1229) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1248 := by
    rcases h21190 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1244 := by
    rcases h21191 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1245 := by
    rcases h21192 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p1246 := by
    rcases h21193 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p1247) := by
    rcases h7355 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u6)
    · exact q5
    · exact False.elim (q6 u3)
  have u8 : p1239 := by
    rcases h7431 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p1240 := by
    rcases h7436 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p1241 := by
    rcases h7441 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p1242 := by
    rcases h7446 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p1243 := by
    rcases h7451 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h7328 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21195 (p1328 p1331 p1336 p1337 p1338 p1339 p1340 p1341 : Prop)
    (h8072 : p1336 ∨ p1341)
    (h8077 : p1337 ∨ p1341)
    (h8082 : p1338 ∨ p1341)
    (h8087 : p1339 ∨ p1341)
    (h8092 : p1340 ∨ p1341)
    (h7972 : p1328 ∨ p1331 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1341 ∨ p1331 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1341) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1331) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21196 (p1328 p1331 p1336 p1337 p1338 p1339 p1340 p1342 : Prop)
    (h8073 : p1336 ∨ p1342)
    (h8078 : p1337 ∨ p1342)
    (h8083 : p1338 ∨ p1342)
    (h8088 : p1339 ∨ p1342)
    (h8093 : p1340 ∨ p1342)
    (h7972 : p1328 ∨ p1331 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1342 ∨ p1331 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1342) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1331) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21197 (p1328 p1331 p1336 p1337 p1338 p1339 p1340 p1343 : Prop)
    (h8074 : p1336 ∨ p1343)
    (h8079 : p1337 ∨ p1343)
    (h8084 : p1338 ∨ p1343)
    (h8089 : p1339 ∨ p1343)
    (h8094 : p1340 ∨ p1343)
    (h7972 : p1328 ∨ p1331 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1343 ∨ p1331 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1343) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1331) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h7972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21198 (p1328 p1331 p1336 p1337 p1338 p1339 p1340 p1344 : Prop)
    (h8075 : p1336 ∨ p1344)
    (h8080 : p1337 ∨ p1344)
    (h8085 : p1338 ∨ p1344)
    (h8090 : p1339 ∨ p1344)
    (h8095 : p1340 ∨ p1344)
    (h7972 : p1328 ∨ p1331 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : p1344 ∨ p1331 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1344) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1331) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h7972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21199 (p1328 p1331 p1336 p1337 p1338 p1339 p1340 p1341 p1342 p1343 p1344 p1345 : Prop)
    (h7997 : p1328 ∨ p1331 ∨ (¬ p1341) ∨ (¬ p1342) ∨ (¬ p1343) ∨ (¬ p1344) ∨ (¬ p1345))
    (h8076 : p1336 ∨ p1345)
    (h8081 : p1337 ∨ p1345)
    (h8086 : p1338 ∨ p1345)
    (h8091 : p1339 ∨ p1345)
    (h8096 : p1340 ∨ p1345)
    (h7972 : p1328 ∨ p1331 ∨ (¬ p1336) ∨ (¬ p1337) ∨ (¬ p1338) ∨ (¬ p1339) ∨ (¬ p1340)) : (¬ p1344) ∨ (¬ p1343) ∨ p1328 ∨ p1331 ∨ (¬ p1341) ∨ (¬ p1342) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1344 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1343 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1328) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1331) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1341 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1342 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1345) := by
    rcases h7997 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1336 := by
    rcases h8076 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1337 := by
    rcases h8081 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1338 := by
    rcases h8086 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1339 := by
    rcases h8091 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1340 := by
    rcases h8096 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h7972 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21200 (p1328 p1331 p1341 p1342 p1343 p1344 : Prop)
    (h21195 : p1341 ∨ p1331 ∨ p1328)
    (h21196 : p1342 ∨ p1331 ∨ p1328)
    (h21197 : p1343 ∨ p1331 ∨ p1328)
    (h21198 : p1344 ∨ p1331 ∨ p1328)
    (h21199 : (¬ p1344) ∨ (¬ p1343) ∨ p1328 ∨ p1331 ∨ (¬ p1341) ∨ (¬ p1342)) : p1331 ∨ p1328 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1331) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1328) := fun hu => hn (Or.inr hu)
  have u2 : p1341 := by
    rcases h21195 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1342 := by
    rcases h21196 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1343 := by
    rcases h21197 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1344 := by
    rcases h21198 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21199 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21201 (p228 p383 p390 p395 p396 p397 p398 p399 : Prop)
    (h2181 : p390 ∨ p395)
    (h2182 : p390 ∨ p396)
    (h2183 : p390 ∨ p397)
    (h2185 : p390 ∨ p399)
    (h2126 : p228 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p390 ∨ (¬ p398) ∨ p228 ∨ p383 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p390) := fun hu => hn (Or.inl hu)
  have u1 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p228) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p383) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21202 (p228 p383 p391 p395 p396 p397 p398 p399 : Prop)
    (h2186 : p391 ∨ p395)
    (h2187 : p391 ∨ p396)
    (h2188 : p391 ∨ p397)
    (h2190 : p391 ∨ p399)
    (h2126 : p228 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p391 ∨ (¬ p398) ∨ p228 ∨ p383 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p391) := fun hu => hn (Or.inl hu)
  have u1 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p228) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p383) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21203 (p228 p383 p392 p395 p396 p397 p398 p399 : Prop)
    (h2191 : p392 ∨ p395)
    (h2192 : p392 ∨ p396)
    (h2193 : p392 ∨ p397)
    (h2195 : p392 ∨ p399)
    (h2126 : p228 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p392 ∨ (¬ p398) ∨ p228 ∨ p383 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p392) := fun hu => hn (Or.inl hu)
  have u1 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p228) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p383) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21204 (p228 p383 p393 p395 p396 p397 p398 p399 : Prop)
    (h2196 : p393 ∨ p395)
    (h2197 : p393 ∨ p396)
    (h2198 : p393 ∨ p397)
    (h2200 : p393 ∨ p399)
    (h2126 : p228 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p393 ∨ (¬ p398) ∨ p228 ∨ p383 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p393) := fun hu => hn (Or.inl hu)
  have u1 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p228) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p383) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u1)
  · exact False.elim (q6 u7)

theorem step21205 (p228 p383 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h21201 : p390 ∨ (¬ p398) ∨ p228 ∨ p383)
    (h21202 : p391 ∨ (¬ p398) ∨ p228 ∨ p383)
    (h21203 : p392 ∨ (¬ p398) ∨ p228 ∨ p383)
    (h21204 : p393 ∨ (¬ p398) ∨ p228 ∨ p383)
    (h2101 : p228 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394))
    (h2201 : p394 ∨ p395)
    (h2202 : p394 ∨ p396)
    (h2203 : p394 ∨ p397)
    (h2205 : p394 ∨ p399)
    (h2126 : p228 ∨ p383 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : (¬ p398) ∨ p383 ∨ p228 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p398 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p383) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p228) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p390 := by
    rcases h21201 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u4 : p391 := by
    rcases h21202 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u5 : p392 := by
    rcases h21203 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u6 : p393 := by
    rcases h21204 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u2 q2)
    · exact False.elim (u1 q3)
  have u7 : (¬ p394) := by
    rcases h2101 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
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
  rcases h2126 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u0)
  · exact False.elim (q6 u11)

theorem step21206 (p228 p383 p390 p391 p392 p393 p394 p398 : Prop)
    (h21205 : (¬ p398) ∨ p383 ∨ p228)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2101 : p228 ∨ p383 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p383 ∨ p228 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p383) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p398) := by
    rcases h21205 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p390 := by
    rcases h2184 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p391 := by
    rcases h2189 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p392 := by
    rcases h2194 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p393 := by
    rcases h2199 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p394 := by
    rcases h2204 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h2101 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21208 (p264 p532 p959 p964 p1226 p1443 p1452 : Prop)
    (h20457 : (¬ p264) ∨ (¬ p959) ∨ (¬ p1226) ∨ (¬ p1443) ∨ (¬ p1452))
    (h10737 : p532 ∨ (¬ p964) ∨ (¬ p1226))
    (h21189 : p964 ∨ p959) : (¬ p1226) ∨ (¬ p1443) ∨ (¬ p264) ∨ p532 ∨ (¬ p1452) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1226 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1443 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : p264 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p532) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1452 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr hu))))
  have u5 : (¬ p959) := by
    rcases h20457 with q0 | q1 | q2 | q3 | q4
    · exact False.elim (q0 u2)
    · exact q1
    · exact False.elim (q2 u0)
    · exact False.elim (q3 u1)
    · exact False.elim (q4 u4)
  have u6 : (¬ p964) := by
    rcases h10737 with q0 | q1 | q2
    · exact False.elim (u3 q0)
    · exact q1
    · exact False.elim (q2 u0)
  rcases h21189 with q0 | q1
  · exact False.elim (u6 q0)
  · exact False.elim (u5 q1)

theorem step21209 (p228 p387 p390 p391 p392 p393 p394 p398 : Prop)
    (h2184 : p390 ∨ p398)
    (h2189 : p391 ∨ p398)
    (h2194 : p392 ∨ p398)
    (h2199 : p393 ∨ p398)
    (h2204 : p394 ∨ p398)
    (h2103 : p228 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394)) : p398 ∨ p228 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p398) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h2103 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21210 (p228 p387 p390 p395 p396 p397 p398 p399 : Prop)
    (h21209 : p398 ∨ p228 ∨ p387)
    (h2181 : p390 ∨ p395)
    (h2182 : p390 ∨ p396)
    (h2183 : p390 ∨ p397)
    (h2185 : p390 ∨ p399)
    (h2128 : p228 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p390 ∨ p228 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p390) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21209 with q0 | q1 | q2
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
  rcases h2128 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21211 (p228 p387 p391 p395 p396 p397 p398 p399 : Prop)
    (h21209 : p398 ∨ p228 ∨ p387)
    (h2186 : p391 ∨ p395)
    (h2187 : p391 ∨ p396)
    (h2188 : p391 ∨ p397)
    (h2190 : p391 ∨ p399)
    (h2128 : p228 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p391 ∨ p228 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p391) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21209 with q0 | q1 | q2
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
  rcases h2128 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21212 (p228 p387 p392 p395 p396 p397 p398 p399 : Prop)
    (h21209 : p398 ∨ p228 ∨ p387)
    (h2191 : p392 ∨ p395)
    (h2192 : p392 ∨ p396)
    (h2193 : p392 ∨ p397)
    (h2195 : p392 ∨ p399)
    (h2128 : p228 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p392 ∨ p228 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p392) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21209 with q0 | q1 | q2
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
  rcases h2128 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21213 (p228 p387 p393 p395 p396 p397 p398 p399 : Prop)
    (h21209 : p398 ∨ p228 ∨ p387)
    (h2196 : p393 ∨ p395)
    (h2197 : p393 ∨ p396)
    (h2198 : p393 ∨ p397)
    (h2200 : p393 ∨ p399)
    (h2128 : p228 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p393 ∨ p228 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p393) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p228) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p387) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p398 := by
    rcases h21209 with q0 | q1 | q2
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
  rcases h2128 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u3)
  · exact False.elim (q6 u7)

theorem step21214 (p228 p387 p390 p391 p392 p393 p394 p395 p396 p397 p398 p399 : Prop)
    (h21209 : p398 ∨ p228 ∨ p387)
    (h21210 : p390 ∨ p228 ∨ p387)
    (h21211 : p391 ∨ p228 ∨ p387)
    (h21212 : p392 ∨ p228 ∨ p387)
    (h21213 : p393 ∨ p228 ∨ p387)
    (h2103 : p228 ∨ p387 ∨ (¬ p390) ∨ (¬ p391) ∨ (¬ p392) ∨ (¬ p393) ∨ (¬ p394))
    (h2201 : p394 ∨ p395)
    (h2202 : p394 ∨ p396)
    (h2203 : p394 ∨ p397)
    (h2205 : p394 ∨ p399)
    (h2128 : p228 ∨ p387 ∨ (¬ p395) ∨ (¬ p396) ∨ (¬ p397) ∨ (¬ p398) ∨ (¬ p399)) : p228 ∨ p387 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p228) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p387) := fun hu => hn (Or.inr hu)
  have u2 : p398 := by
    rcases h21209 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p390 := by
    rcases h21210 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p391 := by
    rcases h21211 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p392 := by
    rcases h21212 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p393 := by
    rcases h21213 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p394) := by
    rcases h2103 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
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
  rcases h2128 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u2)
  · exact False.elim (q6 u11)

theorem step21216 (p301 p520 p522 p527 p528 p529 p530 p531 : Prop)
    (h2959 : p522 ∨ p527)
    (h2960 : p522 ∨ p528)
    (h2961 : p522 ∨ p529)
    (h2962 : p522 ∨ p530)
    (h2897 : p301 ∨ p520 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p522 ∨ (¬ p531) ∨ p520 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p522) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p520) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  rcases h2897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21217 (p301 p520 p523 p527 p528 p529 p530 p531 : Prop)
    (h2964 : p523 ∨ p527)
    (h2965 : p523 ∨ p528)
    (h2966 : p523 ∨ p529)
    (h2967 : p523 ∨ p530)
    (h2897 : p301 ∨ p520 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p523 ∨ (¬ p531) ∨ p520 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p523) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p520) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
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
  rcases h2897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21218 (p301 p520 p524 p527 p528 p529 p530 p531 : Prop)
    (h2969 : p524 ∨ p527)
    (h2970 : p524 ∨ p528)
    (h2971 : p524 ∨ p529)
    (h2972 : p524 ∨ p530)
    (h2897 : p301 ∨ p520 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p524 ∨ (¬ p531) ∨ p520 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p524) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p520) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
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
  rcases h2897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21219 (p301 p520 p525 p527 p528 p529 p530 p531 : Prop)
    (h2974 : p525 ∨ p527)
    (h2975 : p525 ∨ p528)
    (h2976 : p525 ∨ p529)
    (h2977 : p525 ∨ p530)
    (h2897 : p301 ∨ p520 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : p525 ∨ (¬ p531) ∨ p520 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p525) := fun hu => hn (Or.inl hu)
  have u1 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p520) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p301) := fun hu => hn (Or.inr (Or.inr (Or.inr hu)))
  have u4 : p527 := by
    rcases h2974 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p528 := by
    rcases h2975 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p529 := by
    rcases h2976 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p530 := by
    rcases h2977 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h2897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u1)

theorem step21220 (p301 p520 p522 p523 p524 p525 p526 p527 p528 p529 p530 p531 : Prop)
    (h21216 : p522 ∨ (¬ p531) ∨ p520 ∨ p301)
    (h21217 : p523 ∨ (¬ p531) ∨ p520 ∨ p301)
    (h21218 : p524 ∨ (¬ p531) ∨ p520 ∨ p301)
    (h21219 : p525 ∨ (¬ p531) ∨ p520 ∨ p301)
    (h2872 : p301 ∨ p520 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526))
    (h2979 : p526 ∨ p527)
    (h2980 : p526 ∨ p528)
    (h2981 : p526 ∨ p529)
    (h2982 : p526 ∨ p530)
    (h2897 : p301 ∨ p520 ∨ (¬ p527) ∨ (¬ p528) ∨ (¬ p529) ∨ (¬ p530) ∨ (¬ p531)) : (¬ p531) ∨ p520 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p531 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p520) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p301) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p522 := by
    rcases h21216 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u4 : p523 := by
    rcases h21217 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u5 : p524 := by
    rcases h21218 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u6 : p525 := by
    rcases h21219 with q0 | q1 | q2 | q3
    · exact q0
    · exact False.elim (q1 u0)
    · exact False.elim (u1 q2)
    · exact False.elim (u2 q3)
  have u7 : (¬ p526) := by
    rcases h2872 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p527 := by
    rcases h2979 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p528 := by
    rcases h2980 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p529 := by
    rcases h2981 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p530 := by
    rcases h2982 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h2897 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u0)

theorem step21222 (p11 p1443 p1498 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9153 : p1498 ∨ p1503)
    (h9154 : p1498 ∨ p1504)
    (h9155 : p1498 ∨ p1505)
    (h9156 : p1498 ∨ p1506)
    (h9157 : p1498 ∨ p1507)
    (h9090 : p11 ∨ p1443 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1498 ∨ p1443 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1498) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1443) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h9090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21223 (p11 p1443 p1499 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9158 : p1499 ∨ p1503)
    (h9159 : p1499 ∨ p1504)
    (h9160 : p1499 ∨ p1505)
    (h9161 : p1499 ∨ p1506)
    (h9162 : p1499 ∨ p1507)
    (h9090 : p11 ∨ p1443 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1499 ∨ p1443 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1499) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1443) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h9090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21224 (p11 p1443 p1500 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9163 : p1500 ∨ p1503)
    (h9164 : p1500 ∨ p1504)
    (h9165 : p1500 ∨ p1505)
    (h9166 : p1500 ∨ p1506)
    (h9167 : p1500 ∨ p1507)
    (h9090 : p11 ∨ p1443 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1500 ∨ p1443 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1500) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1443) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h9090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21225 (p11 p1443 p1501 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9168 : p1501 ∨ p1503)
    (h9169 : p1501 ∨ p1504)
    (h9170 : p1501 ∨ p1505)
    (h9171 : p1501 ∨ p1506)
    (h9172 : p1501 ∨ p1507)
    (h9090 : p11 ∨ p1443 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : p1501 ∨ p1443 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1501) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1443) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p11) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1503 := by
    rcases h9168 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u4 : p1504 := by
    rcases h9169 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p1505 := by
    rcases h9170 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p1506 := by
    rcases h9171 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p1507 := by
    rcases h9172 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h9090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21226 (p11 p1443 p1498 p1499 p1500 p1501 p1502 p1503 p1504 p1505 p1506 p1507 : Prop)
    (h9065 : p11 ∨ p1443 ∨ (¬ p1498) ∨ (¬ p1499) ∨ (¬ p1500) ∨ (¬ p1501) ∨ (¬ p1502))
    (h9173 : p1502 ∨ p1503)
    (h9174 : p1502 ∨ p1504)
    (h9175 : p1502 ∨ p1505)
    (h9176 : p1502 ∨ p1506)
    (h9177 : p1502 ∨ p1507)
    (h9090 : p11 ∨ p1443 ∨ (¬ p1503) ∨ (¬ p1504) ∨ (¬ p1505) ∨ (¬ p1506) ∨ (¬ p1507)) : (¬ p1501) ∨ (¬ p1500) ∨ p1443 ∨ p11 ∨ (¬ p1498) ∨ (¬ p1499) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1501 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1500 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1443) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p11) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1498 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1499 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1502) := by
    rcases h9065 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1503 := by
    rcases h9173 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u8 : p1504 := by
    rcases h9174 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u9 : p1505 := by
    rcases h9175 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u10 : p1506 := by
    rcases h9176 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  have u11 : p1507 := by
    rcases h9177 with q0 | q1
    · exact False.elim (u6 q0)
    · exact q1
  rcases h9090 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21227 (p11 p1443 p1498 p1499 p1500 p1501 : Prop)
    (h21222 : p1498 ∨ p1443 ∨ p11)
    (h21223 : p1499 ∨ p1443 ∨ p11)
    (h21224 : p1500 ∨ p1443 ∨ p11)
    (h21225 : p1501 ∨ p1443 ∨ p11)
    (h21226 : (¬ p1501) ∨ (¬ p1500) ∨ p1443 ∨ p11 ∨ (¬ p1498) ∨ (¬ p1499)) : p1443 ∨ p11 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1443) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p11) := fun hu => hn (Or.inr hu)
  have u2 : p1498 := by
    rcases h21222 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1499 := by
    rcases h21223 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1500 := by
    rcases h21224 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1501 := by
    rcases h21225 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21226 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21228 (p185 p237 p245 p246 p247 p248 p249 p250 : Prop)
    (h1280 : p245 ∨ p250)
    (h1285 : p246 ∨ p250)
    (h1290 : p247 ∨ p250)
    (h1295 : p248 ∨ p250)
    (h1300 : p249 ∨ p250)
    (h1192 : p185 ∨ p237 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p250 ∨ p237 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p250) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p245 := by
    rcases h1280 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p246 := by
    rcases h1285 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p247 := by
    rcases h1290 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p248 := by
    rcases h1295 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p249 := by
    rcases h1300 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21229 (p185 p237 p245 p246 p247 p248 p249 p251 : Prop)
    (h1281 : p245 ∨ p251)
    (h1286 : p246 ∨ p251)
    (h1291 : p247 ∨ p251)
    (h1296 : p248 ∨ p251)
    (h1301 : p249 ∨ p251)
    (h1192 : p185 ∨ p237 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p251 ∨ p237 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p251) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p245 := by
    rcases h1281 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p246 := by
    rcases h1286 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p247 := by
    rcases h1291 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p248 := by
    rcases h1296 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p249 := by
    rcases h1301 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21230 (p185 p237 p245 p246 p247 p248 p249 p252 : Prop)
    (h1282 : p245 ∨ p252)
    (h1287 : p246 ∨ p252)
    (h1292 : p247 ∨ p252)
    (h1297 : p248 ∨ p252)
    (h1302 : p249 ∨ p252)
    (h1192 : p185 ∨ p237 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p252 ∨ p237 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p252) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p245 := by
    rcases h1282 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p246 := by
    rcases h1287 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p247 := by
    rcases h1292 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p248 := by
    rcases h1297 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p249 := by
    rcases h1302 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h1192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21231 (p185 p237 p245 p246 p247 p248 p249 p253 : Prop)
    (h1283 : p245 ∨ p253)
    (h1288 : p246 ∨ p253)
    (h1293 : p247 ∨ p253)
    (h1298 : p248 ∨ p253)
    (h1303 : p249 ∨ p253)
    (h1192 : p185 ∨ p237 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : p253 ∨ p237 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p253) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p237) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p185) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h1192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21232 (p185 p237 p245 p246 p247 p248 p249 p250 p251 p252 p253 p254 : Prop)
    (h1217 : p185 ∨ p237 ∨ (¬ p250) ∨ (¬ p251) ∨ (¬ p252) ∨ (¬ p253) ∨ (¬ p254))
    (h1284 : p245 ∨ p254)
    (h1289 : p246 ∨ p254)
    (h1294 : p247 ∨ p254)
    (h1299 : p248 ∨ p254)
    (h1304 : p249 ∨ p254)
    (h1192 : p185 ∨ p237 ∨ (¬ p245) ∨ (¬ p246) ∨ (¬ p247) ∨ (¬ p248) ∨ (¬ p249)) : (¬ p253) ∨ (¬ p252) ∨ p237 ∨ p185 ∨ (¬ p250) ∨ (¬ p251) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p253 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p252 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p237) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p185) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p250 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p251 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p254) := by
    rcases h1217 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p245 := by
    rcases h1284 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p246 := by
    rcases h1289 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p247 := by
    rcases h1294 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p248 := by
    rcases h1299 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p249 := by
    rcases h1304 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1192 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21233 (p185 p237 p250 p251 p252 p253 : Prop)
    (h21228 : p250 ∨ p237 ∨ p185)
    (h21229 : p251 ∨ p237 ∨ p185)
    (h21230 : p252 ∨ p237 ∨ p185)
    (h21231 : p253 ∨ p237 ∨ p185)
    (h21232 : (¬ p253) ∨ (¬ p252) ∨ p237 ∨ p185 ∨ (¬ p250) ∨ (¬ p251)) : p237 ∨ p185 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p237) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p185) := fun hu => hn (Or.inr hu)
  have u2 : p250 := by
    rcases h21228 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p251 := by
    rcases h21229 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p252 := by
    rcases h21230 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p253 := by
    rcases h21231 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21232 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21234 (p961 p964 p967 p968 p969 p970 p971 p974 : Prop)
    (h5688 : p967 ∨ p974)
    (h5693 : p968 ∨ p974)
    (h5698 : p969 ∨ p974)
    (h5703 : p970 ∨ p974)
    (h5708 : p971 ∨ p974)
    (h5596 : p961 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p974 ∨ p964 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p974) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h5596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21235 (p961 p964 p967 p968 p969 p970 p971 p975 : Prop)
    (h5689 : p967 ∨ p975)
    (h5694 : p968 ∨ p975)
    (h5699 : p969 ∨ p975)
    (h5704 : p970 ∨ p975)
    (h5709 : p971 ∨ p975)
    (h5596 : p961 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p975 ∨ p964 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p975) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h5596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21236 (p961 p964 p967 p968 p969 p970 p971 p976 : Prop)
    (h5690 : p967 ∨ p976)
    (h5695 : p968 ∨ p976)
    (h5700 : p969 ∨ p976)
    (h5705 : p970 ∨ p976)
    (h5710 : p971 ∨ p976)
    (h5596 : p961 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p976 ∨ p964 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p976) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h5596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21237 (p961 p964 p967 p968 p969 p970 p971 p972 : Prop)
    (h5686 : p967 ∨ p972)
    (h5691 : p968 ∨ p972)
    (h5696 : p969 ∨ p972)
    (h5701 : p970 ∨ p972)
    (h5706 : p971 ∨ p972)
    (h5596 : p961 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : p972 ∨ p964 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p972) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p967 := by
    rcases h5686 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p968 := by
    rcases h5691 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p969 := by
    rcases h5696 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p970 := by
    rcases h5701 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p971 := by
    rcases h5706 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h5596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21238 (p961 p964 p967 p968 p969 p970 p971 p972 p973 p974 p975 p976 : Prop)
    (h5621 : p961 ∨ p964 ∨ (¬ p972) ∨ (¬ p973) ∨ (¬ p974) ∨ (¬ p975) ∨ (¬ p976))
    (h5687 : p967 ∨ p973)
    (h5692 : p968 ∨ p973)
    (h5697 : p969 ∨ p973)
    (h5702 : p970 ∨ p973)
    (h5707 : p971 ∨ p973)
    (h5596 : p961 ∨ p964 ∨ (¬ p967) ∨ (¬ p968) ∨ (¬ p969) ∨ (¬ p970) ∨ (¬ p971)) : (¬ p972) ∨ p964 ∨ p961 ∨ (¬ p976) ∨ (¬ p975) ∨ (¬ p974) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p972 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : (¬ p964) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p961) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p976 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p975 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p974 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p973) := by
    rcases h5621 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u0)
    · exact q3
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u4)
    · exact False.elim (q6 u3)
  have u7 : p967 := by
    rcases h5687 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p968 := by
    rcases h5692 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p969 := by
    rcases h5697 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p970 := by
    rcases h5702 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p971 := by
    rcases h5707 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h5596 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21239 (p961 p964 p972 p974 p975 p976 : Prop)
    (h21234 : p974 ∨ p964 ∨ p961)
    (h21235 : p975 ∨ p964 ∨ p961)
    (h21236 : p976 ∨ p964 ∨ p961)
    (h21237 : p972 ∨ p964 ∨ p961)
    (h21238 : (¬ p972) ∨ p964 ∨ p961 ∨ (¬ p976) ∨ (¬ p975) ∨ (¬ p974)) : p964 ∨ p961 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p964) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p961) := fun hu => hn (Or.inr hu)
  have u2 : p974 := by
    rcases h21234 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p975 := by
    rcases h21235 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p976 := by
    rcases h21236 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p972 := by
    rcases h21237 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21238 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (u0 q1)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u3)
  · exact False.elim (q5 u2)

theorem step21240 (p532 p1451 p1455 p1456 p1457 p1458 p1459 p1460 : Prop)
    (h8883 : p1455 ∨ p1460)
    (h8888 : p1456 ∨ p1460)
    (h8893 : p1457 ∨ p1460)
    (h8898 : p1458 ∨ p1460)
    (h8903 : p1459 ∨ p1460)
    (h8794 : p532 ∨ p1451 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1460 ∨ p1451 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1460) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1451) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h8794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21241 (p532 p1451 p1455 p1456 p1457 p1458 p1459 p1461 : Prop)
    (h8884 : p1455 ∨ p1461)
    (h8889 : p1456 ∨ p1461)
    (h8894 : p1457 ∨ p1461)
    (h8899 : p1458 ∨ p1461)
    (h8904 : p1459 ∨ p1461)
    (h8794 : p532 ∨ p1451 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1461 ∨ p1451 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1461) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1451) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h8794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21242 (p532 p1451 p1455 p1456 p1457 p1458 p1459 p1462 : Prop)
    (h8885 : p1455 ∨ p1462)
    (h8890 : p1456 ∨ p1462)
    (h8895 : p1457 ∨ p1462)
    (h8900 : p1458 ∨ p1462)
    (h8905 : p1459 ∨ p1462)
    (h8794 : p532 ∨ p1451 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1462 ∨ p1451 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1462) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1451) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h8794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21243 (p532 p1451 p1455 p1456 p1457 p1458 p1459 p1463 : Prop)
    (h8886 : p1455 ∨ p1463)
    (h8891 : p1456 ∨ p1463)
    (h8896 : p1457 ∨ p1463)
    (h8901 : p1458 ∨ p1463)
    (h8906 : p1459 ∨ p1463)
    (h8794 : p532 ∨ p1451 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : p1463 ∨ p1451 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1463) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1451) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1455 := by
    rcases h8886 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1456 := by
    rcases h8891 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1457 := by
    rcases h8896 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1458 := by
    rcases h8901 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1459 := by
    rcases h8906 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h8794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21244 (p532 p1451 p1455 p1456 p1457 p1458 p1459 p1460 p1461 p1462 p1463 p1464 : Prop)
    (h8819 : p532 ∨ p1451 ∨ (¬ p1460) ∨ (¬ p1461) ∨ (¬ p1462) ∨ (¬ p1463) ∨ (¬ p1464))
    (h8887 : p1455 ∨ p1464)
    (h8892 : p1456 ∨ p1464)
    (h8897 : p1457 ∨ p1464)
    (h8902 : p1458 ∨ p1464)
    (h8907 : p1459 ∨ p1464)
    (h8794 : p532 ∨ p1451 ∨ (¬ p1455) ∨ (¬ p1456) ∨ (¬ p1457) ∨ (¬ p1458) ∨ (¬ p1459)) : (¬ p1463) ∨ (¬ p1462) ∨ p532 ∨ p1451 ∨ (¬ p1460) ∨ (¬ p1461) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1463 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1462 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p532) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1451) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1460 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1461 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1464) := by
    rcases h8819 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1455 := by
    rcases h8887 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1456 := by
    rcases h8892 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1457 := by
    rcases h8897 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1458 := by
    rcases h8902 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1459 := by
    rcases h8907 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h8794 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21245 (p532 p1451 p1460 p1461 p1462 p1463 : Prop)
    (h21240 : p1460 ∨ p1451 ∨ p532)
    (h21241 : p1461 ∨ p1451 ∨ p532)
    (h21242 : p1462 ∨ p1451 ∨ p532)
    (h21243 : p1463 ∨ p1451 ∨ p532)
    (h21244 : (¬ p1463) ∨ (¬ p1462) ∨ p532 ∨ p1451 ∨ (¬ p1460) ∨ (¬ p1461)) : p1451 ∨ p532 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1451) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p532) := fun hu => hn (Or.inr hu)
  have u2 : p1460 := by
    rcases h21240 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1461 := by
    rcases h21241 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1462 := by
    rcases h21242 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1463 := by
    rcases h21243 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21244 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21246 (p1624 p1631 p1634 p1635 p1636 p1637 p1638 p1639 : Prop)
    (h10075 : p1634 ∨ p1639)
    (h10080 : p1635 ∨ p1639)
    (h10085 : p1636 ∨ p1639)
    (h10090 : p1637 ∨ p1639)
    (h10095 : p1638 ∨ p1639)
    (h9987 : p1624 ∨ p1631 ∨ (¬ p1634) ∨ (¬ p1635) ∨ (¬ p1636) ∨ (¬ p1637) ∨ (¬ p1638)) : p1639 ∨ p1631 ∨ p1624 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1639) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1631) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1624) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1634 := by
    rcases h10075 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1635 := by
    rcases h10080 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1636 := by
    rcases h10085 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1637 := by
    rcases h10090 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1638 := by
    rcases h10095 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9987 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21247 (p1624 p1631 p1634 p1635 p1636 p1637 p1638 p1640 : Prop)
    (h10076 : p1634 ∨ p1640)
    (h10081 : p1635 ∨ p1640)
    (h10086 : p1636 ∨ p1640)
    (h10091 : p1637 ∨ p1640)
    (h10096 : p1638 ∨ p1640)
    (h9987 : p1624 ∨ p1631 ∨ (¬ p1634) ∨ (¬ p1635) ∨ (¬ p1636) ∨ (¬ p1637) ∨ (¬ p1638)) : p1640 ∨ p1631 ∨ p1624 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1640) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1631) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1624) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1634 := by
    rcases h10076 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1635 := by
    rcases h10081 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1636 := by
    rcases h10086 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1637 := by
    rcases h10091 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1638 := by
    rcases h10096 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9987 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21248 (p1624 p1631 p1634 p1635 p1636 p1637 p1638 p1641 : Prop)
    (h10077 : p1634 ∨ p1641)
    (h10082 : p1635 ∨ p1641)
    (h10087 : p1636 ∨ p1641)
    (h10092 : p1637 ∨ p1641)
    (h10097 : p1638 ∨ p1641)
    (h9987 : p1624 ∨ p1631 ∨ (¬ p1634) ∨ (¬ p1635) ∨ (¬ p1636) ∨ (¬ p1637) ∨ (¬ p1638)) : p1641 ∨ p1631 ∨ p1624 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1641) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1631) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1624) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1634 := by
    rcases h10077 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1635 := by
    rcases h10082 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1636 := by
    rcases h10087 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1637 := by
    rcases h10092 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1638 := by
    rcases h10097 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9987 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21249 (p1624 p1631 p1634 p1635 p1636 p1637 p1638 p1642 : Prop)
    (h10078 : p1634 ∨ p1642)
    (h10083 : p1635 ∨ p1642)
    (h10088 : p1636 ∨ p1642)
    (h10093 : p1637 ∨ p1642)
    (h10098 : p1638 ∨ p1642)
    (h9987 : p1624 ∨ p1631 ∨ (¬ p1634) ∨ (¬ p1635) ∨ (¬ p1636) ∨ (¬ p1637) ∨ (¬ p1638)) : p1642 ∨ p1631 ∨ p1624 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1642) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1631) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1624) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p1634 := by
    rcases h10078 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p1635 := by
    rcases h10083 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p1636 := by
    rcases h10088 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p1637 := by
    rcases h10093 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p1638 := by
    rcases h10098 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h9987 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21250 (p1624 p1631 p1634 p1635 p1636 p1637 p1638 p1639 p1640 p1641 p1642 p1643 : Prop)
    (h10012 : p1624 ∨ p1631 ∨ (¬ p1639) ∨ (¬ p1640) ∨ (¬ p1641) ∨ (¬ p1642) ∨ (¬ p1643))
    (h10079 : p1634 ∨ p1643)
    (h10084 : p1635 ∨ p1643)
    (h10089 : p1636 ∨ p1643)
    (h10094 : p1637 ∨ p1643)
    (h10099 : p1638 ∨ p1643)
    (h9987 : p1624 ∨ p1631 ∨ (¬ p1634) ∨ (¬ p1635) ∨ (¬ p1636) ∨ (¬ p1637) ∨ (¬ p1638)) : (¬ p1642) ∨ (¬ p1641) ∨ p1631 ∨ p1624 ∨ (¬ p1639) ∨ (¬ p1640) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1642 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1641 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1631) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1624) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1639 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1640 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1643) := by
    rcases h10012 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p1634 := by
    rcases h10079 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p1635 := by
    rcases h10084 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p1636 := by
    rcases h10089 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p1637 := by
    rcases h10094 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p1638 := by
    rcases h10099 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h9987 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21251 (p1624 p1631 p1639 p1640 p1641 p1642 : Prop)
    (h21246 : p1639 ∨ p1631 ∨ p1624)
    (h21247 : p1640 ∨ p1631 ∨ p1624)
    (h21248 : p1641 ∨ p1631 ∨ p1624)
    (h21249 : p1642 ∨ p1631 ∨ p1624)
    (h21250 : (¬ p1642) ∨ (¬ p1641) ∨ p1631 ∨ p1624 ∨ (¬ p1639) ∨ (¬ p1640)) : p1631 ∨ p1624 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1631) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1624) := fun hu => hn (Or.inr hu)
  have u2 : p1639 := by
    rcases h21246 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1640 := by
    rcases h21247 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1641 := by
    rcases h21248 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1642 := by
    rcases h21249 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21250 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21252 (p186 p189 p196 p197 p198 p199 p200 p201 : Prop)
    (h1022 : p196 ∨ p201)
    (h1027 : p197 ∨ p201)
    (h1032 : p198 ∨ p201)
    (h1037 : p199 ∨ p201)
    (h1042 : p200 ∨ p201)
    (h933 : p186 ∨ p189 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p201 ∨ p186 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p201) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p186) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h933 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21253 (p186 p189 p196 p197 p198 p199 p200 p202 : Prop)
    (h1023 : p196 ∨ p202)
    (h1028 : p197 ∨ p202)
    (h1033 : p198 ∨ p202)
    (h1038 : p199 ∨ p202)
    (h1043 : p200 ∨ p202)
    (h933 : p186 ∨ p189 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p202 ∨ p186 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p202) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p186) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h933 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21254 (p186 p189 p196 p197 p198 p199 p200 p203 : Prop)
    (h1024 : p196 ∨ p203)
    (h1029 : p197 ∨ p203)
    (h1034 : p198 ∨ p203)
    (h1039 : p199 ∨ p203)
    (h1044 : p200 ∨ p203)
    (h933 : p186 ∨ p189 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p203 ∨ p186 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p203) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p186) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h933 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21255 (p186 p189 p196 p197 p198 p199 p200 p204 : Prop)
    (h1025 : p196 ∨ p204)
    (h1030 : p197 ∨ p204)
    (h1035 : p198 ∨ p204)
    (h1040 : p199 ∨ p204)
    (h1045 : p200 ∨ p204)
    (h933 : p186 ∨ p189 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p204 ∨ p186 ∨ p189 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p204) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p186) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p189) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p196 := by
    rcases h1025 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p197 := by
    rcases h1030 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p198 := by
    rcases h1035 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p199 := by
    rcases h1040 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p200 := by
    rcases h1045 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h933 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21257 (p189 p193 p196 p197 p198 p199 p200 p205 : Prop)
    (h1026 : p196 ∨ p205)
    (h1031 : p197 ∨ p205)
    (h1036 : p198 ∨ p205)
    (h1041 : p199 ∨ p205)
    (h1046 : p200 ∨ p205)
    (h934 : p189 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200)) : p205 ∨ p189 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p205) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h934 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21258 (p189 p193 p196 p201 p202 p203 p204 p205 : Prop)
    (h21257 : p205 ∨ p189 ∨ p193)
    (h1022 : p196 ∨ p201)
    (h1023 : p196 ∨ p202)
    (h1024 : p196 ∨ p203)
    (h1025 : p196 ∨ p204)
    (h959 : p189 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p196 ∨ p189 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p196) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p205 := by
    rcases h21257 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p201 := by
    rcases h1022 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p202 := by
    rcases h1023 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p203 := by
    rcases h1024 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p204 := by
    rcases h1025 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h959 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21259 (p189 p193 p197 p201 p202 p203 p204 p205 : Prop)
    (h21257 : p205 ∨ p189 ∨ p193)
    (h1027 : p197 ∨ p201)
    (h1028 : p197 ∨ p202)
    (h1029 : p197 ∨ p203)
    (h1030 : p197 ∨ p204)
    (h959 : p189 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p197 ∨ p189 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p197) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p205 := by
    rcases h21257 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p201 := by
    rcases h1027 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p202 := by
    rcases h1028 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p203 := by
    rcases h1029 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p204 := by
    rcases h1030 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h959 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21260 (p189 p193 p198 p201 p202 p203 p204 p205 : Prop)
    (h21257 : p205 ∨ p189 ∨ p193)
    (h1032 : p198 ∨ p201)
    (h1033 : p198 ∨ p202)
    (h1034 : p198 ∨ p203)
    (h1035 : p198 ∨ p204)
    (h959 : p189 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p198 ∨ p189 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p198) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p205 := by
    rcases h21257 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p201 := by
    rcases h1032 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p202 := by
    rcases h1033 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p203 := by
    rcases h1034 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p204 := by
    rcases h1035 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h959 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21261 (p189 p193 p199 p201 p202 p203 p204 p205 : Prop)
    (h21257 : p205 ∨ p189 ∨ p193)
    (h1037 : p199 ∨ p201)
    (h1038 : p199 ∨ p202)
    (h1039 : p199 ∨ p203)
    (h1040 : p199 ∨ p204)
    (h959 : p189 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p199 ∨ p189 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p199) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p189) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p193) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p205 := by
    rcases h21257 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u1 q1)
    · exact False.elim (u2 q2)
  have u4 : p201 := by
    rcases h1037 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u5 : p202 := by
    rcases h1038 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u6 : p203 := by
    rcases h1039 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  have u7 : p204 := by
    rcases h1040 with q0 | q1
    · exact False.elim (u0 q0)
    · exact q1
  rcases h959 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u4)
  · exact False.elim (q3 u5)
  · exact False.elim (q4 u6)
  · exact False.elim (q5 u7)
  · exact False.elim (q6 u3)

theorem step21262 (p189 p193 p196 p197 p198 p199 p200 p201 p202 p203 p204 p205 : Prop)
    (h21257 : p205 ∨ p189 ∨ p193)
    (h21258 : p196 ∨ p189 ∨ p193)
    (h21259 : p197 ∨ p189 ∨ p193)
    (h21260 : p198 ∨ p189 ∨ p193)
    (h21261 : p199 ∨ p189 ∨ p193)
    (h934 : p189 ∨ p193 ∨ (¬ p196) ∨ (¬ p197) ∨ (¬ p198) ∨ (¬ p199) ∨ (¬ p200))
    (h1042 : p200 ∨ p201)
    (h1043 : p200 ∨ p202)
    (h1044 : p200 ∨ p203)
    (h1045 : p200 ∨ p204)
    (h959 : p189 ∨ p193 ∨ (¬ p201) ∨ (¬ p202) ∨ (¬ p203) ∨ (¬ p204) ∨ (¬ p205)) : p189 ∨ p193 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p189) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p193) := fun hu => hn (Or.inr hu)
  have u2 : p205 := by
    rcases h21257 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p196 := by
    rcases h21258 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p197 := by
    rcases h21259 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p198 := by
    rcases h21260 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p199 := by
    rcases h21261 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p200) := by
    rcases h934 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u0 q0)
    · exact False.elim (u1 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p201 := by
    rcases h1042 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u9 : p202 := by
    rcases h1043 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u10 : p203 := by
    rcases h1044 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  have u11 : p204 := by
    rcases h1045 with q0 | q1
    · exact False.elim (u7 q0)
    · exact q1
  rcases h959 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u0 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u2)

theorem step21263 (p797 p801 p804 p805 p806 p807 p808 p813 : Prop)
    (h4647 : p804 ∨ p813)
    (h4652 : p805 ∨ p813)
    (h4657 : p806 ∨ p813)
    (h4662 : p807 ∨ p813)
    (h4667 : p808 ∨ p813)
    (h4543 : p797 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p813 ∨ p797 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p813) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4647 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4652 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4657 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4662 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4667 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4543 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21264 (p797 p801 p804 p805 p806 p807 p808 p809 : Prop)
    (h4643 : p804 ∨ p809)
    (h4648 : p805 ∨ p809)
    (h4653 : p806 ∨ p809)
    (h4658 : p807 ∨ p809)
    (h4663 : p808 ∨ p809)
    (h4543 : p797 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p809 ∨ p797 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p809) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4643 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4648 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4653 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4658 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4663 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4543 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21265 (p797 p801 p804 p805 p806 p807 p808 p810 : Prop)
    (h4644 : p804 ∨ p810)
    (h4649 : p805 ∨ p810)
    (h4654 : p806 ∨ p810)
    (h4659 : p807 ∨ p810)
    (h4664 : p808 ∨ p810)
    (h4543 : p797 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p810 ∨ p797 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p810) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p804 := by
    rcases h4644 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p805 := by
    rcases h4649 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p806 := by
    rcases h4654 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p807 := by
    rcases h4659 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p808 := by
    rcases h4664 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h4543 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21266 (p797 p801 p804 p805 p806 p807 p808 p811 : Prop)
    (h4645 : p804 ∨ p811)
    (h4650 : p805 ∨ p811)
    (h4655 : p806 ∨ p811)
    (h4660 : p807 ∨ p811)
    (h4665 : p808 ∨ p811)
    (h4543 : p797 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : p811 ∨ p797 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p811) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p797) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h4543 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21267 (p797 p801 p804 p805 p806 p807 p808 p809 p810 p811 p812 p813 : Prop)
    (h4568 : p797 ∨ p801 ∨ (¬ p809) ∨ (¬ p810) ∨ (¬ p811) ∨ (¬ p812) ∨ (¬ p813))
    (h4646 : p804 ∨ p812)
    (h4651 : p805 ∨ p812)
    (h4656 : p806 ∨ p812)
    (h4661 : p807 ∨ p812)
    (h4666 : p808 ∨ p812)
    (h4543 : p797 ∨ p801 ∨ (¬ p804) ∨ (¬ p805) ∨ (¬ p806) ∨ (¬ p807) ∨ (¬ p808)) : (¬ p811) ∨ (¬ p809) ∨ p801 ∨ (¬ p813) ∨ p797 ∨ (¬ p810) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p811 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p809 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p801) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : p813 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : (¬ p797) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p810 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p812) := by
    rcases h4568 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u4 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u3)
  have u7 : p804 := by
    rcases h4646 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p805 := by
    rcases h4651 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p806 := by
    rcases h4656 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p807 := by
    rcases h4661 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p808 := by
    rcases h4666 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h4543 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u4 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21268 (p797 p801 p809 p810 p811 p813 : Prop)
    (h21263 : p813 ∨ p797 ∨ p801)
    (h21264 : p809 ∨ p797 ∨ p801)
    (h21265 : p810 ∨ p797 ∨ p801)
    (h21266 : p811 ∨ p797 ∨ p801)
    (h21267 : (¬ p811) ∨ (¬ p809) ∨ p801 ∨ (¬ p813) ∨ p797 ∨ (¬ p810)) : p797 ∨ p801 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p797) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p801) := fun hu => hn (Or.inr hu)
  have u2 : p813 := by
    rcases h21263 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p809 := by
    rcases h21264 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p810 := by
    rcases h21265 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p811 := by
    rcases h21266 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21267 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u1 q2)
  · exact False.elim (q3 u2)
  · exact False.elim (u0 q4)
  · exact False.elim (q5 u4)

theorem step21270 (p301 p520 p522 p523 p524 p525 p526 p531 : Prop)
    (h21220 : (¬ p531) ∨ p520 ∨ p301)
    (h2963 : p522 ∨ p531)
    (h2968 : p523 ∨ p531)
    (h2973 : p524 ∨ p531)
    (h2978 : p525 ∨ p531)
    (h2983 : p526 ∨ p531)
    (h2872 : p301 ∨ p520 ∨ (¬ p522) ∨ (¬ p523) ∨ (¬ p524) ∨ (¬ p525) ∨ (¬ p526)) : p520 ∨ p301 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p520) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p301) := fun hu => hn (Or.inr hu)
  have u2 : (¬ p531) := by
    rcases h21220 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p522 := by
    rcases h2963 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u4 : p523 := by
    rcases h2968 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u5 : p524 := by
    rcases h2973 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u6 : p525 := by
    rcases h2978 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  have u7 : p526 := by
    rcases h2983 with q0 | q1
    · exact q0
    · exact False.elim (u2 q1)
  rcases h2872 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21271 (p17 p256 p269 p270 p271 p272 p273 p278 : Prop)
    (h1417 : p269 ∨ p278)
    (h1422 : p270 ∨ p278)
    (h1427 : p271 ∨ p278)
    (h1432 : p272 ∨ p278)
    (h1437 : p273 ∨ p278)
    (h1325 : p17 ∨ p256 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p278 ∨ p256 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p278) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h1325 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21272 (p17 p256 p269 p270 p271 p272 p273 p274 : Prop)
    (h1413 : p269 ∨ p274)
    (h1418 : p270 ∨ p274)
    (h1423 : p271 ∨ p274)
    (h1428 : p272 ∨ p274)
    (h1433 : p273 ∨ p274)
    (h1325 : p17 ∨ p256 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p274 ∨ p256 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p274) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h1325 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21273 (p17 p256 p269 p270 p271 p272 p273 p275 : Prop)
    (h1414 : p269 ∨ p275)
    (h1419 : p270 ∨ p275)
    (h1424 : p271 ∨ p275)
    (h1429 : p272 ∨ p275)
    (h1434 : p273 ∨ p275)
    (h1325 : p17 ∨ p256 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p275 ∨ p256 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p275) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h1325 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21274 (p17 p256 p269 p270 p271 p272 p273 p276 : Prop)
    (h1415 : p269 ∨ p276)
    (h1420 : p270 ∨ p276)
    (h1425 : p271 ∨ p276)
    (h1430 : p272 ∨ p276)
    (h1435 : p273 ∨ p276)
    (h1325 : p17 ∨ p256 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : p276 ∨ p256 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p276) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p256) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h1325 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21275 (p17 p256 p269 p270 p271 p272 p273 p274 p275 p276 p277 p278 : Prop)
    (h1350 : p17 ∨ p256 ∨ (¬ p274) ∨ (¬ p275) ∨ (¬ p276) ∨ (¬ p277) ∨ (¬ p278))
    (h1416 : p269 ∨ p277)
    (h1421 : p270 ∨ p277)
    (h1426 : p271 ∨ p277)
    (h1431 : p272 ∨ p277)
    (h1436 : p273 ∨ p277)
    (h1325 : p17 ∨ p256 ∨ (¬ p269) ∨ (¬ p270) ∨ (¬ p271) ∨ (¬ p272) ∨ (¬ p273)) : (¬ p276) ∨ (¬ p274) ∨ p256 ∨ p17 ∨ (¬ p275) ∨ (¬ p278) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p276 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p274 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p256) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p17) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p275 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p278 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p277) := by
    rcases h1350 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u1)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u0)
    · exact q5
    · exact False.elim (q6 u5)
  have u7 : p269 := by
    rcases h1416 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p270 := by
    rcases h1421 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p271 := by
    rcases h1426 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p272 := by
    rcases h1431 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p273 := by
    rcases h1436 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h1325 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21276 (p17 p256 p274 p275 p276 p278 : Prop)
    (h21271 : p278 ∨ p256 ∨ p17)
    (h21272 : p274 ∨ p256 ∨ p17)
    (h21273 : p275 ∨ p256 ∨ p17)
    (h21274 : p276 ∨ p256 ∨ p17)
    (h21275 : (¬ p276) ∨ (¬ p274) ∨ p256 ∨ p17 ∨ (¬ p275) ∨ (¬ p278)) : p256 ∨ p17 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p256) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p17) := fun hu => hn (Or.inr hu)
  have u2 : p278 := by
    rcases h21271 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p274 := by
    rcases h21272 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p275 := by
    rcases h21273 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p276 := by
    rcases h21274 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21275 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u3)
  · exact False.elim (u0 q2)
  · exact False.elim (u1 q3)
  · exact False.elim (q4 u4)
  · exact False.elim (q5 u2)

theorem step21277 (p163 p167 p173 p174 p175 p176 p177 p178 : Prop)
    (h890 : p173 ∨ p178)
    (h895 : p174 ∨ p178)
    (h900 : p175 ∨ p178)
    (h905 : p176 ∨ p178)
    (h910 : p177 ∨ p178)
    (h802 : p163 ∨ p167 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p178 ∨ p163 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p178) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21278 (p163 p167 p173 p174 p175 p176 p177 p179 : Prop)
    (h891 : p173 ∨ p179)
    (h896 : p174 ∨ p179)
    (h901 : p175 ∨ p179)
    (h906 : p176 ∨ p179)
    (h911 : p177 ∨ p179)
    (h802 : p163 ∨ p167 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p179 ∨ p163 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p179) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21279 (p163 p167 p173 p174 p175 p176 p177 p180 : Prop)
    (h892 : p173 ∨ p180)
    (h897 : p174 ∨ p180)
    (h902 : p175 ∨ p180)
    (h907 : p176 ∨ p180)
    (h912 : p177 ∨ p180)
    (h802 : p163 ∨ p167 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p180 ∨ p163 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p180) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21280 (p163 p167 p173 p174 p175 p176 p177 p181 : Prop)
    (h893 : p173 ∨ p181)
    (h898 : p174 ∨ p181)
    (h903 : p175 ∨ p181)
    (h908 : p176 ∨ p181)
    (h913 : p177 ∨ p181)
    (h802 : p163 ∨ p167 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : p181 ∨ p163 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p181) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p163) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21281 (p163 p167 p173 p174 p175 p176 p177 p178 p179 p180 p181 p182 : Prop)
    (h827 : p163 ∨ p167 ∨ (¬ p178) ∨ (¬ p179) ∨ (¬ p180) ∨ (¬ p181) ∨ (¬ p182))
    (h894 : p173 ∨ p182)
    (h899 : p174 ∨ p182)
    (h904 : p175 ∨ p182)
    (h909 : p176 ∨ p182)
    (h914 : p177 ∨ p182)
    (h802 : p163 ∨ p167 ∨ (¬ p173) ∨ (¬ p174) ∨ (¬ p175) ∨ (¬ p176) ∨ (¬ p177)) : (¬ p181) ∨ (¬ p180) ∨ p167 ∨ p163 ∨ (¬ p178) ∨ (¬ p179) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p181 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p180 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p167) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p163) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p178 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p179 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p182) := by
    rcases h827 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u3 q0)
    · exact False.elim (u2 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p173 := by
    rcases h894 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p174 := by
    rcases h899 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p175 := by
    rcases h904 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p176 := by
    rcases h909 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p177 := by
    rcases h914 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h802 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u3 q0)
  · exact False.elim (u2 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21282 (p163 p167 p178 p179 p180 p181 : Prop)
    (h21277 : p178 ∨ p163 ∨ p167)
    (h21278 : p179 ∨ p163 ∨ p167)
    (h21279 : p180 ∨ p163 ∨ p167)
    (h21280 : p181 ∨ p163 ∨ p167)
    (h21281 : (¬ p181) ∨ (¬ p180) ∨ p167 ∨ p163 ∨ (¬ p178) ∨ (¬ p179)) : p163 ∨ p167 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p163) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p167) := fun hu => hn (Or.inr hu)
  have u2 : p178 := by
    rcases h21277 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p179 := by
    rcases h21278 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p180 := by
    rcases h21279 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p181 := by
    rcases h21280 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21281 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21283 (p103 p107 p111 p112 p113 p114 p115 p116 : Prop)
    (h620 : p111 ∨ p116)
    (h625 : p112 ∨ p116)
    (h630 : p113 ∨ p116)
    (h635 : p114 ∨ p116)
    (h640 : p115 ∨ p116)
    (h520 : p103 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p116 ∨ p107 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p116) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p111 := by
    rcases h620 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p112 := by
    rcases h625 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p113 := by
    rcases h630 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p114 := by
    rcases h635 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h640 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21284 (p103 p107 p111 p112 p113 p114 p115 p117 : Prop)
    (h621 : p111 ∨ p117)
    (h626 : p112 ∨ p117)
    (h631 : p113 ∨ p117)
    (h636 : p114 ∨ p117)
    (h641 : p115 ∨ p117)
    (h520 : p103 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p117 ∨ p107 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p117) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p111 := by
    rcases h621 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p112 := by
    rcases h626 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p113 := by
    rcases h631 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p114 := by
    rcases h636 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h641 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21285 (p103 p107 p111 p112 p113 p114 p115 p118 : Prop)
    (h622 : p111 ∨ p118)
    (h627 : p112 ∨ p118)
    (h632 : p113 ∨ p118)
    (h637 : p114 ∨ p118)
    (h642 : p115 ∨ p118)
    (h520 : p103 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p118 ∨ p107 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p118) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p111 := by
    rcases h622 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p112 := by
    rcases h627 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p113 := by
    rcases h632 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p114 := by
    rcases h637 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h642 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21286 (p103 p107 p111 p112 p113 p114 p115 p119 : Prop)
    (h623 : p111 ∨ p119)
    (h628 : p112 ∨ p119)
    (h633 : p113 ∨ p119)
    (h638 : p114 ∨ p119)
    (h643 : p115 ∨ p119)
    (h520 : p103 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p119 ∨ p107 ∨ p103 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p119) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p107) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p103) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p111 := by
    rcases h623 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u4 : p112 := by
    rcases h628 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u5 : p113 := by
    rcases h633 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u6 : p114 := by
    rcases h638 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  have u7 : p115 := by
    rcases h643 with q0 | q1
    · exact q0
    · exact False.elim (u0 q1)
  rcases h520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21287 (p101 p103 p107 p111 p112 p113 p114 p115 p116 p117 p118 p119 p120 : Prop)
    (h21283 : p116 ∨ p107 ∨ p103)
    (h21284 : p117 ∨ p107 ∨ p103)
    (h21285 : p118 ∨ p107 ∨ p103)
    (h21286 : p119 ∨ p107 ∨ p103)
    (h555 : p101 ∨ p107 ∨ (¬ p116) ∨ (¬ p117) ∨ (¬ p118) ∨ (¬ p119) ∨ (¬ p120))
    (h624 : p111 ∨ p120)
    (h629 : p112 ∨ p120)
    (h634 : p113 ∨ p120)
    (h639 : p114 ∨ p120)
    (h644 : p115 ∨ p120)
    (h520 : p103 ∨ p107 ∨ (¬ p111) ∨ (¬ p112) ∨ (¬ p113) ∨ (¬ p114) ∨ (¬ p115)) : p107 ∨ p103 ∨ p101 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p107) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p103) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p101) := fun hu => hn (Or.inr (Or.inr hu))
  have u3 : p116 := by
    rcases h21283 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p117 := by
    rcases h21284 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p118 := by
    rcases h21285 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u6 : p119 := by
    rcases h21286 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u7 : (¬ p120) := by
    rcases h555 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u0 q1)
    · exact False.elim (q2 u3)
    · exact False.elim (q3 u4)
    · exact False.elim (q4 u5)
    · exact False.elim (q5 u6)
    · exact q6
  have u8 : p111 := by
    rcases h624 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u9 : p112 := by
    rcases h629 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u10 : p113 := by
    rcases h634 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u11 : p114 := by
    rcases h639 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  have u12 : p115 := by
    rcases h644 with q0 | q1
    · exact q0
    · exact False.elim (u7 q1)
  rcases h520 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u1 q0)
  · exact False.elim (u0 q1)
  · exact False.elim (q2 u8)
  · exact False.elim (q3 u9)
  · exact False.elim (q4 u10)
  · exact False.elim (q5 u11)
  · exact False.elim (q6 u12)

theorem step21288 (p1099 p1102 p1105 p1106 p1107 p1108 p1109 p1110 : Prop)
    (h6579 : p1105 ∨ p1110)
    (h6584 : p1106 ∨ p1110)
    (h6589 : p1107 ∨ p1110)
    (h6594 : p1108 ∨ p1110)
    (h6599 : p1109 ∨ p1110)
    (h6489 : p1099 ∨ p1102 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1110 ∨ p1102 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1110) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1102) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21289 (p1099 p1102 p1105 p1106 p1107 p1108 p1109 p1111 : Prop)
    (h6580 : p1105 ∨ p1111)
    (h6585 : p1106 ∨ p1111)
    (h6590 : p1107 ∨ p1111)
    (h6595 : p1108 ∨ p1111)
    (h6600 : p1109 ∨ p1111)
    (h6489 : p1099 ∨ p1102 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1111 ∨ p1102 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1111) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1102) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21290 (p1099 p1102 p1105 p1106 p1107 p1108 p1109 p1112 : Prop)
    (h6581 : p1105 ∨ p1112)
    (h6586 : p1106 ∨ p1112)
    (h6591 : p1107 ∨ p1112)
    (h6596 : p1108 ∨ p1112)
    (h6601 : p1109 ∨ p1112)
    (h6489 : p1099 ∨ p1102 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1112 ∨ p1102 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1112) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1102) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1099) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h6489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21291 (p1099 p1102 p1105 p1106 p1107 p1108 p1109 p1113 : Prop)
    (h6582 : p1105 ∨ p1113)
    (h6587 : p1106 ∨ p1113)
    (h6592 : p1107 ∨ p1113)
    (h6597 : p1108 ∨ p1113)
    (h6602 : p1109 ∨ p1113)
    (h6489 : p1099 ∨ p1102 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : p1113 ∨ p1102 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1113) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1102) := fun hu => hn (Or.inr (Or.inl hu))
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
  rcases h6489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21292 (p1099 p1102 p1105 p1106 p1107 p1108 p1109 p1110 p1111 p1112 p1113 p1114 : Prop)
    (h6514 : p1099 ∨ p1102 ∨ (¬ p1110) ∨ (¬ p1111) ∨ (¬ p1112) ∨ (¬ p1113) ∨ (¬ p1114))
    (h6583 : p1105 ∨ p1114)
    (h6588 : p1106 ∨ p1114)
    (h6593 : p1107 ∨ p1114)
    (h6598 : p1108 ∨ p1114)
    (h6603 : p1109 ∨ p1114)
    (h6489 : p1099 ∨ p1102 ∨ (¬ p1105) ∨ (¬ p1106) ∨ (¬ p1107) ∨ (¬ p1108) ∨ (¬ p1109)) : (¬ p1113) ∨ (¬ p1112) ∨ p1099 ∨ p1102 ∨ (¬ p1110) ∨ (¬ p1111) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p1113 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p1112 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p1099) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p1102) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p1110 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p1111 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p1114) := by
    rcases h6514 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
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
  rcases h6489 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

theorem step21293 (p1099 p1102 p1110 p1111 p1112 p1113 : Prop)
    (h21288 : p1110 ∨ p1102 ∨ p1099)
    (h21289 : p1111 ∨ p1102 ∨ p1099)
    (h21290 : p1112 ∨ p1102 ∨ p1099)
    (h21291 : p1113 ∨ p1102 ∨ p1099)
    (h21292 : (¬ p1113) ∨ (¬ p1112) ∨ p1099 ∨ p1102 ∨ (¬ p1110) ∨ (¬ p1111)) : p1102 ∨ p1099 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p1102) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p1099) := fun hu => hn (Or.inr hu)
  have u2 : p1110 := by
    rcases h21288 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u3 : p1111 := by
    rcases h21289 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u4 : p1112 := by
    rcases h21290 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  have u5 : p1113 := by
    rcases h21291 with q0 | q1 | q2
    · exact q0
    · exact False.elim (u0 q1)
    · exact False.elim (u1 q2)
  rcases h21292 with q0 | q1 | q2 | q3 | q4 | q5
  · exact False.elim (q0 u5)
  · exact False.elim (q1 u4)
  · exact False.elim (u1 q2)
  · exact False.elim (u0 q3)
  · exact False.elim (q4 u2)
  · exact False.elim (q5 u3)

theorem step21294 (p38 p67 p73 p74 p75 p76 p77 p78 : Prop)
    (h369 : p73 ∨ p78)
    (h374 : p74 ∨ p78)
    (h379 : p75 ∨ p78)
    (h384 : p76 ∨ p78)
    (h389 : p77 ∨ p78)
    (h289 : p38 ∨ p67 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p78 ∨ p67 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p78) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p67) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21295 (p38 p67 p73 p74 p75 p76 p77 p79 : Prop)
    (h370 : p73 ∨ p79)
    (h375 : p74 ∨ p79)
    (h380 : p75 ∨ p79)
    (h385 : p76 ∨ p79)
    (h390 : p77 ∨ p79)
    (h289 : p38 ∨ p67 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p79 ∨ p67 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p79) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p67) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21296 (p38 p67 p73 p74 p75 p76 p77 p80 : Prop)
    (h371 : p73 ∨ p80)
    (h376 : p74 ∨ p80)
    (h381 : p75 ∨ p80)
    (h386 : p76 ∨ p80)
    (h391 : p77 ∨ p80)
    (h289 : p38 ∨ p67 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p80 ∨ p67 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p80) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p67) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21297 (p38 p67 p73 p74 p75 p76 p77 p81 : Prop)
    (h372 : p73 ∨ p81)
    (h377 : p74 ∨ p81)
    (h382 : p75 ∨ p81)
    (h387 : p76 ∨ p81)
    (h392 : p77 ∨ p81)
    (h289 : p38 ∨ p67 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : p81 ∨ p67 ∨ p38 := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : (¬ p81) := fun hu => hn (Or.inl hu)
  have u1 : (¬ p67) := fun hu => hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr hu))
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
  rcases h289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u1 q1)
  · exact False.elim (q2 u3)
  · exact False.elim (q3 u4)
  · exact False.elim (q4 u5)
  · exact False.elim (q5 u6)
  · exact False.elim (q6 u7)

theorem step21298 (p38 p67 p73 p74 p75 p76 p77 p78 p79 p80 p81 p82 : Prop)
    (h314 : p38 ∨ p67 ∨ (¬ p78) ∨ (¬ p79) ∨ (¬ p80) ∨ (¬ p81) ∨ (¬ p82))
    (h373 : p73 ∨ p82)
    (h378 : p74 ∨ p82)
    (h383 : p75 ∨ p82)
    (h388 : p76 ∨ p82)
    (h393 : p77 ∨ p82)
    (h289 : p38 ∨ p67 ∨ (¬ p73) ∨ (¬ p74) ∨ (¬ p75) ∨ (¬ p76) ∨ (¬ p77)) : (¬ p81) ∨ (¬ p80) ∨ p38 ∨ p67 ∨ (¬ p78) ∨ (¬ p79) := by
  classical
  apply Classical.byContradiction
  intro hn
  have u0 : p81 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inl hu)
  have u1 : p80 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inl hu))
  have u2 : (¬ p38) := fun hu => hn (Or.inr (Or.inr (Or.inl hu)))
  have u3 : (¬ p67) := fun hu => hn (Or.inr (Or.inr (Or.inr (Or.inl hu))))
  have u4 : p78 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hu)))))
  have u5 : p79 := by
    apply Classical.byContradiction
    intro hu
    exact hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu)))))
  have u6 : (¬ p82) := by
    rcases h314 with q0 | q1 | q2 | q3 | q4 | q5 | q6
    · exact False.elim (u2 q0)
    · exact False.elim (u3 q1)
    · exact False.elim (q2 u4)
    · exact False.elim (q3 u5)
    · exact False.elim (q4 u1)
    · exact False.elim (q5 u0)
    · exact q6
  have u7 : p73 := by
    rcases h373 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u8 : p74 := by
    rcases h378 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u9 : p75 := by
    rcases h383 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u10 : p76 := by
    rcases h388 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  have u11 : p77 := by
    rcases h393 with q0 | q1
    · exact q0
    · exact False.elim (u6 q1)
  rcases h289 with q0 | q1 | q2 | q3 | q4 | q5 | q6
  · exact False.elim (u2 q0)
  · exact False.elim (u3 q1)
  · exact False.elim (q2 u7)
  · exact False.elim (q3 u8)
  · exact False.elim (q4 u9)
  · exact False.elim (q5 u10)
  · exact False.elim (q6 u11)

#print axioms step21298

end NineRUPTrial
