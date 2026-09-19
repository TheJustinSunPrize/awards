import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory006
import SunPrize.Certificate.Theory007
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule9766 (p2027 p2307 p2584 p2630 p2656 p2745 p3549 p4245 : Prop) (h : (¬ p2584) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p4245) ∨ (¬ p2307) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p2630)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3549) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial9766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory1584 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 6 7)
  exact rule9766 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2630) (meaning t m 2656) (meaning t m 2745) (meaning t m 3549) (meaning t m 4245) source

theorem rule9769 (p2027 p2307 p2373 p2588 p2590 p3743 p4509 : Prop) (h : p2027 ∨ (¬ p2588) ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2590) ∨ (¬ p4509) ∨ (¬ p3743)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p3743) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial9769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory1587 t (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule9769 (meaning t m 2027) (meaning t m 2307) (meaning t m 2373) (meaning t m 2588) (meaning t m 2590) (meaning t m 3743) (meaning t m 4509) source

theorem rule9771 (p2027 p3097 p3309 p4110 p4338 p4632 : Prop) (h : (¬ p4338) ∨ (¬ p4632) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p4110)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4110) ∨ (¬ p4338) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial9771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory1589 t (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule9771 (meaning t m 2027) (meaning t m 3097) (meaning t m 3309) (meaning t m 4110) (meaning t m 4338) (meaning t m 4632) source

theorem rule9772 (p2210 p3555 : Prop) (h : (¬ p3555) ∨ (¬ p2210)) : (¬ p2210) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial9772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory1590 (m.theta 0 1) (m.theta 1 5)
  exact rule9772 (meaning t m 2210) (meaning t m 3555) source

theorem rule9773 (p2027 p2507 p2588 p3399 p3547 p3591 : Prop) (h : (¬ p3547) ∨ (¬ p3591) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2507) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial9773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory1591 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7)
  exact rule9773 (meaning t m 2027) (meaning t m 2507) (meaning t m 2588) (meaning t m 3399) (meaning t m 3547) (meaning t m 3591) source

theorem rule9774 (p2192 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p2192)) : (¬ p2192) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial9774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory1592 (m.theta 1 5) (m.theta 5 6)
  exact rule9774 (meaning t m 2192) (meaning t m 4173) source

theorem rule9775 (p2027 p2928 p3389 p3954 p4079 p5216 : Prop) (h : (¬ p2928) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3954) ∨ (¬ p4079)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial9775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory1593 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 7)
  exact rule9775 (meaning t m 2027) (meaning t m 2928) (meaning t m 3389) (meaning t m 3954) (meaning t m 4079) (meaning t m 5216) source

theorem rule9776 (p2027 p2166 p3956 p3958 p4173 p4441 : Prop) (h : (¬ p3956) ∨ (¬ p4441) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3958) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4173) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial9776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory1594 t (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule9776 (meaning t m 2027) (meaning t m 2166) (meaning t m 3956) (meaning t m 3958) (meaning t m 4173) (meaning t m 4441) source

theorem rule9778 (p2027 p2588 p2891 p3958 p4140 p4173 : Prop) (h : p2027 ∨ (¬ p3958) ∨ (¬ p2588) ∨ (¬ p4173) ∨ (¬ p4140) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2588) ∨ (¬ p2891) ∨ (¬ p3958) ∨ (¬ p4140) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial9778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory1596 t (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule9778 (meaning t m 2027) (meaning t m 2588) (meaning t m 2891) (meaning t m 3958) (meaning t m 4140) (meaning t m 4173) source

theorem rule9779 (p3564 p4137 : Prop) (h : (¬ p4137) ∨ (¬ p3564)) : (¬ p3564) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial9779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory1597 (m.theta 4 6) (m.theta 6 9)
  exact rule9779 (meaning t m 3564) (meaning t m 4137) source

theorem rule9780 (p2027 p2963 p3166 p3956 p4417 p4976 : Prop) (h : (¬ p2963) ∨ (¬ p4417) ∨ (¬ p3956) ∨ (¬ p4976) ∨ p2027 ∨ (¬ p3166)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3956) ∨ (¬ p4417) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial9780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory1598 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule9780 (meaning t m 2027) (meaning t m 2963) (meaning t m 3166) (meaning t m 3956) (meaning t m 4417) (meaning t m 4976) source

theorem rule9781 (p2027 p2387 p3654 p3692 p4345 p4433 : Prop) (h : (¬ p3654) ∨ (¬ p4345) ∨ (¬ p3692) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial9781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory1599 t (m.theta 0 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule9781 (meaning t m 2027) (meaning t m 2387) (meaning t m 3654) (meaning t m 3692) (meaning t m 4345) (meaning t m 4433) source

theorem rule9783 (p2027 p2383 p2901 p3324 p3743 p4153 p4558 : Prop) (h : (¬ p3324) ∨ (¬ p4153) ∨ (¬ p4558) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p3743)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2901) ∨ (¬ p3324) ∨ (¬ p3743) ∨ (¬ p4153) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial9783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory1601 t (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule9783 (meaning t m 2027) (meaning t m 2383) (meaning t m 2901) (meaning t m 3324) (meaning t m 3743) (meaning t m 4153) (meaning t m 4558) source

theorem rule9785 (p2383 p2387 : Prop) (h : (¬ p2387) ∨ (¬ p2383)) : (¬ p2383) ∨ (¬ p2387) := by
  classical
  tauto

theorem initial9785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2387)) := by
  have source := ElevenTheory.theory1603 (m.theta 0 6) (m.theta 6 8)
  exact rule9785 (meaning t m 2383) (meaning t m 2387) source

theorem rule9786 (p2027 p2946 p3146 p3156 p3201 p3540 p3905 p4697 p4786 p5160 : Prop) (h : (¬ p3540) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p4786) ∨ (¬ p3201) ∨ (¬ p3905) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial9786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory1604 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule9786 (meaning t m 2027) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3201) (meaning t m 3540) (meaning t m 3905) (meaning t m 4697) (meaning t m 4786) (meaning t m 5160) source

theorem rule9787 (p2027 p2933 p3399 p3452 p3742 p4814 : Prop) (h : (¬ p4814) ∨ (¬ p3452) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p2933)) : (p2027) ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3742) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial9787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory1605 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7)
  exact rule9787 (meaning t m 2027) (meaning t m 2933) (meaning t m 3399) (meaning t m 3452) (meaning t m 3742) (meaning t m 4814) source

theorem rule9788 (p2027 p2247 p2744 p2928 p3389 p4079 p4257 : Prop) (h : (¬ p2247) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p2928) ∨ (¬ p4079) ∨ (¬ p4257)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial9788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory1606 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 7)
  exact rule9788 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 2928) (meaning t m 3389) (meaning t m 4079) (meaning t m 4257) source

theorem rule9790 (p4199 p4201 p5568 p5569 p5570 : Prop) : (p4199) ∨ (¬ (p4201 ∧ p4199 ∧ p5568 ∧ p5569 ∧ p5570)) := by
  classical
  tauto

theorem initial9790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4199) ∨ (¬ (meaning t m 5567)) := by
  exact rule9790 (meaning t m 4199) (meaning t m 4201) (meaning t m 5568) (meaning t m 5569) (meaning t m 5570)

theorem rule9791 (p4199 p4201 p5568 p5569 p5570 : Prop) : (¬ (p4201 ∧ p4199 ∧ p5568 ∧ p5569 ∧ p5570)) ∨ (p5568) := by
  classical
  tauto

theorem initial9791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5567)) ∨ (meaning t m 5568) := by
  exact rule9791 (meaning t m 4199) (meaning t m 4201) (meaning t m 5568) (meaning t m 5569) (meaning t m 5570)

theorem rule9792 (p4199 p4201 p5568 p5569 p5570 : Prop) : (¬ (p4201 ∧ p4199 ∧ p5568 ∧ p5569 ∧ p5570)) ∨ (p5569) := by
  classical
  tauto

theorem initial9792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5567)) ∨ (meaning t m 5569) := by
  exact rule9792 (meaning t m 4199) (meaning t m 4201) (meaning t m 5568) (meaning t m 5569) (meaning t m 5570)

theorem rule9797 (p3969 p5572 p5573 p5574 p5575 : Prop) : (p3969) ∨ (¬ (p5572 ∧ p5573 ∧ p3969 ∧ p5574 ∧ p5575)) := by
  classical
  tauto

theorem initial9797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3969) ∨ (¬ (meaning t m 5571)) := by
  exact rule9797 (meaning t m 3969) (meaning t m 5572) (meaning t m 5573) (meaning t m 5574) (meaning t m 5575)

theorem rule9803 (p5567 p5571 : Prop) : (¬ (p5567 ∨ p5571)) ∨ (p5567) ∨ (p5571) := by
  classical
  tauto

theorem initial9803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5566)) ∨ (meaning t m 5567) ∨ (meaning t m 5571) := by
  exact rule9803 (meaning t m 5567) (meaning t m 5571)

theorem rule9804 (p3963 p5566 : Prop) (h : (p3963 ↔ p5566)) : (¬ p3963) ∨ (p5566) := by
  classical
  tauto

theorem initial9804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3963)) ∨ (meaning t m 5566) := by
  have source := ElevenTheory.theory1607 t (m.theta 5 10) (m.theta 5 8) (m.theta 8 10)
  exact rule9804 (meaning t m 3963) (meaning t m 5566) source

theorem rule9807 (p5578 p5579 p5580 p5581 p5582 : Prop) : (¬ (p5578 ∧ p5579 ∧ p5580 ∧ p5581 ∧ p5582)) ∨ (p5579) := by
  classical
  tauto

theorem initial9807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5577)) ∨ (meaning t m 5579) := by
  exact rule9807 (meaning t m 5578) (meaning t m 5579) (meaning t m 5580) (meaning t m 5581) (meaning t m 5582)

theorem rule9808 (p5578 p5579 p5580 p5581 p5582 : Prop) : (¬ (p5578 ∧ p5579 ∧ p5580 ∧ p5581 ∧ p5582)) ∨ (p5580) := by
  classical
  tauto

theorem initial9808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5577)) ∨ (meaning t m 5580) := by
  exact rule9808 (meaning t m 5578) (meaning t m 5579) (meaning t m 5580) (meaning t m 5581) (meaning t m 5582)

theorem rule9810 (p5578 p5579 p5580 p5581 p5582 : Prop) : (¬ (p5578 ∧ p5579 ∧ p5580 ∧ p5581 ∧ p5582)) ∨ (p5582) := by
  classical
  tauto

theorem initial9810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5577)) ∨ (meaning t m 5582) := by
  exact rule9810 (meaning t m 5578) (meaning t m 5579) (meaning t m 5580) (meaning t m 5581) (meaning t m 5582)

theorem rule9812 (p3979 p5584 p5585 p5586 p5587 : Prop) : (¬ (p5584 ∧ p5585 ∧ p3979 ∧ p5586 ∧ p5587)) ∨ (p5584) := by
  classical
  tauto

theorem initial9812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5583)) ∨ (meaning t m 5584) := by
  exact rule9812 (meaning t m 3979) (meaning t m 5584) (meaning t m 5585) (meaning t m 5586) (meaning t m 5587)

theorem rule9814 (p3979 p5584 p5585 p5586 p5587 : Prop) : (p3979) ∨ (¬ (p5584 ∧ p5585 ∧ p3979 ∧ p5586 ∧ p5587)) := by
  classical
  tauto

theorem initial9814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3979) ∨ (¬ (meaning t m 5583)) := by
  exact rule9814 (meaning t m 3979) (meaning t m 5584) (meaning t m 5585) (meaning t m 5586) (meaning t m 5587)

theorem rule9815 (p3979 p5584 p5585 p5586 p5587 : Prop) : (¬ (p5584 ∧ p5585 ∧ p3979 ∧ p5586 ∧ p5587)) ∨ (p5586) := by
  classical
  tauto

theorem initial9815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5583)) ∨ (meaning t m 5586) := by
  exact rule9815 (meaning t m 3979) (meaning t m 5584) (meaning t m 5585) (meaning t m 5586) (meaning t m 5587)

theorem rule9820 (p5577 p5583 : Prop) : (¬ (p5577 ∨ p5583)) ∨ (p5577) ∨ (p5583) := by
  classical
  tauto

theorem initial9820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5576)) ∨ (meaning t m 5577) ∨ (meaning t m 5583) := by
  exact rule9820 (meaning t m 5577) (meaning t m 5583)

theorem rule9821 (p3973 p5576 : Prop) (h : (p3973 ↔ p5576)) : (¬ p3973) ∨ (p5576) := by
  classical
  tauto

theorem initial9821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3973)) ∨ (meaning t m 5576) := by
  have source := ElevenTheory.theory1608 t (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule9821 (meaning t m 3973) (meaning t m 5576) source

theorem rule9823 (p2027 p2946 p3055 p3146 p3156 p3876 p4278 p4669 p4786 : Prop) (h : (¬ p4278) ∨ (¬ p3876) ∨ (¬ p3146) ∨ (¬ p4669) ∨ (¬ p4786) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial9823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory1609 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule9823 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 3146) (meaning t m 3156) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) (meaning t m 4786) source

theorem rule9824 (p2295 p3568 : Prop) (h : (¬ p3568) ∨ (¬ p2295)) : (¬ p2295) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial9824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory1610 (m.theta 3 6) (m.theta 6 7)
  exact rule9824 (meaning t m 2295) (meaning t m 3568) source

theorem rule9825 (p2027 p3471 p3555 p3588 p3589 p4377 : Prop) (h : p2027 ∨ (¬ p3588) ∨ (¬ p3471) ∨ (¬ p3589) ∨ (¬ p4377) ∨ (¬ p3555)) : (p2027) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p3588) ∨ (¬ p3589) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial9825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory1611 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 7)
  exact rule9825 (meaning t m 2027) (meaning t m 3471) (meaning t m 3555) (meaning t m 3588) (meaning t m 3589) (meaning t m 4377) source

theorem rule9826 (p2027 p2922 p3541 p3583 p3876 p4881 : Prop) (h : (¬ p3583) ∨ (¬ p4881) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p3541) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3876) ∨ (¬ p4881) := by
  classical
  tauto

theorem initial9826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4881)) := by
  have source := ElevenTheory.theory1612 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7)
  exact rule9826 (meaning t m 2027) (meaning t m 2922) (meaning t m 3541) (meaning t m 3583) (meaning t m 3876) (meaning t m 4881) source

theorem rule9827 (p2027 p3379 p3583 p3954 p4030 p4881 : Prop) (h : (¬ p3583) ∨ (¬ p4881) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4030)) : (p2027) ∨ (¬ p3379) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4881) := by
  classical
  tauto

theorem initial9827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4881)) := by
  have source := ElevenTheory.theory1613 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5)
  exact rule9827 (meaning t m 2027) (meaning t m 3379) (meaning t m 3583) (meaning t m 3954) (meaning t m 4030) (meaning t m 4881) source

theorem rule9828 (p2027 p2743 p3631 p3687 p4324 p4782 : Prop) (h : (¬ p3687) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p4782) ∨ (¬ p2743) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p4324) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial9828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory1614 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule9828 (meaning t m 2027) (meaning t m 2743) (meaning t m 3631) (meaning t m 3687) (meaning t m 4324) (meaning t m 4782) source

theorem rule9829 (p2922 p2928 : Prop) (h : (¬ p2928) ∨ (¬ p2922)) : (¬ p2922) ∨ (¬ p2928) := by
  classical
  tauto

theorem initial9829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2928)) := by
  have source := ElevenTheory.theory1615 (m.theta 1 4) (m.theta 4 7)
  exact rule9829 (meaning t m 2922) (meaning t m 2928) source

theorem rule9830 (p2027 p2761 p3434 p4025 p4191 p4477 : Prop) (h : (¬ p3434) ∨ (¬ p4025) ∨ (¬ p4477) ∨ (¬ p4191) ∨ (¬ p2761) ∨ p2027) : (p2027) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial9830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory1616 t (m.theta 2 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9830 (meaning t m 2027) (meaning t m 2761) (meaning t m 3434) (meaning t m 4025) (meaning t m 4191) (meaning t m 4477) source

theorem rule9832 (p2027 p2383 p2437 p2962 p3324 p4109 p4194 p4646 : Prop) (h : (¬ p2383) ∨ (¬ p2437) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p4194) ∨ (¬ p2962) ∨ (¬ p3324) ∨ (¬ p4109)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2437) ∨ (¬ p2962) ∨ (¬ p3324) ∨ (¬ p4109) ∨ (¬ p4194) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial9832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1618 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 7) (m.theta 6 8)
  exact rule9832 (meaning t m 2027) (meaning t m 2383) (meaning t m 2437) (meaning t m 2962) (meaning t m 3324) (meaning t m 4109) (meaning t m 4194) (meaning t m 4646) source

theorem rule9833 (p2027 p2246 p2744 p2761 p2946 p3146 p3156 p3366 p3425 p4669 p5228 p5387 : Prop) (h : (¬ p5228) ∨ (¬ p2946) ∨ (¬ p2744) ∨ (¬ p5387) ∨ (¬ p3366) ∨ (¬ p3156) ∨ (¬ p3425) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p3146) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4669) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial9833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory1619 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 2 9) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule9833 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2761) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3366) (meaning t m 3425) (meaning t m 4669) (meaning t m 5228) (meaning t m 5387) source

theorem rule9834 (p2027 p2664 p2946 p3156 p3540 p3658 p3969 p4324 p4381 p5119 : Prop) (h : p2027 ∨ (¬ p2664) ∨ (¬ p4324) ∨ (¬ p3540) ∨ (¬ p3969) ∨ (¬ p5119) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p4381) ∨ (¬ p3658)) : (p2027) ∨ (¬ p2664) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3658) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial9834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2664)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory1620 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule9834 (meaning t m 2027) (meaning t m 2664) (meaning t m 2946) (meaning t m 3156) (meaning t m 3540) (meaning t m 3658) (meaning t m 3969) (meaning t m 4324) (meaning t m 4381) (meaning t m 5119) source

theorem rule9835 (p2417 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p2417)) : (¬ p2417) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial9835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory1621 (m.theta 4 7) (m.theta 7 9)
  exact rule9835 (meaning t m 2417) (meaning t m 4278) source

theorem rule9836 (p4309 p4310 p5590 p5591 p5592 : Prop) : (p4309) ∨ (¬ (p4309 ∧ p4310 ∧ p5590 ∧ p5591 ∧ p5592)) := by
  classical
  tauto

theorem initial9836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4309) ∨ (¬ (meaning t m 5589)) := by
  exact rule9836 (meaning t m 4309) (meaning t m 4310) (meaning t m 5590) (meaning t m 5591) (meaning t m 5592)

theorem rule9837 (p4309 p4310 p5590 p5591 p5592 : Prop) : (p4310) ∨ (¬ (p4309 ∧ p4310 ∧ p5590 ∧ p5591 ∧ p5592)) := by
  classical
  tauto

theorem initial9837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4310) ∨ (¬ (meaning t m 5589)) := by
  exact rule9837 (meaning t m 4309) (meaning t m 4310) (meaning t m 5590) (meaning t m 5591) (meaning t m 5592)

theorem rule9838 (p4309 p4310 p5590 p5591 p5592 : Prop) : (¬ (p4309 ∧ p4310 ∧ p5590 ∧ p5591 ∧ p5592)) ∨ (p5590) := by
  classical
  tauto

theorem initial9838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5589)) ∨ (meaning t m 5590) := by
  exact rule9838 (meaning t m 4309) (meaning t m 4310) (meaning t m 5590) (meaning t m 5591) (meaning t m 5592)

theorem rule9844 (p3998 p4284 p4285 p5594 p5595 : Prop) : (p3998) ∨ (¬ (p4285 ∧ p4284 ∧ p3998 ∧ p5594 ∧ p5595)) := by
  classical
  tauto

theorem initial9844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3998) ∨ (¬ (meaning t m 5593)) := by
  exact rule9844 (meaning t m 3998) (meaning t m 4284) (meaning t m 4285) (meaning t m 5594) (meaning t m 5595)

theorem rule9850 (p5589 p5593 : Prop) : (¬ (p5589 ∨ p5593)) ∨ (p5589) ∨ (p5593) := by
  classical
  tauto

theorem initial9850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5588)) ∨ (meaning t m 5589) ∨ (meaning t m 5593) := by
  exact rule9850 (meaning t m 5589) (meaning t m 5593)

theorem rule9851 (p3992 p5588 : Prop) (h : (p3992 ↔ p5588)) : (¬ p3992) ∨ (p5588) := by
  classical
  tauto

theorem initial9851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3992)) ∨ (meaning t m 5588) := by
  have source := ElevenTheory.theory1622 t (m.theta 0 10) (m.theta 0 8) (m.theta 8 10)
  exact rule9851 (meaning t m 3992) (meaning t m 5588) source

theorem rule9853 (p3125 p3744 : Prop) (h : (¬ p3744) ∨ (¬ p3125)) : (¬ p3125) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial9853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory1623 (m.theta 5 6) (m.theta 6 9)
  exact rule9853 (meaning t m 3125) (meaning t m 3744) source

theorem rule9854 (p2027 p2274 p3461 p4205 p4322 p4620 : Prop) (h : (¬ p4205) ∨ (¬ p3461) ∨ (¬ p4620) ∨ (¬ p4322) ∨ (¬ p2274) ∨ p2027) : (p2027) ∨ (¬ p2274) ∨ (¬ p3461) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial9854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4205)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1624 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule9854 (meaning t m 2027) (meaning t m 2274) (meaning t m 3461) (meaning t m 4205) (meaning t m 4322) (meaning t m 4620) source

theorem rule9855 (p2027 p2246 p2608 p2744 p2946 p3146 p3156 p3817 p4366 p4669 : Prop) (h : (¬ p4366) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p2744) ∨ (¬ p3817) ∨ (¬ p4669) ∨ (¬ p2608) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial9855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory1625 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule9855 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) source

theorem rule9856 (p2027 p2098 p2247 p2744 p3589 p4242 : Prop) (h : p2027 ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3589) ∨ (¬ p2098) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3589) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial9856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory1626 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 8)
  exact rule9856 (meaning t m 2027) (meaning t m 2098) (meaning t m 2247) (meaning t m 2744) (meaning t m 3589) (meaning t m 4242) source

theorem rule9857 (p2027 p2743 p3399 p3576 p3954 p4782 : Prop) (h : (¬ p2743) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4782) ∨ (¬ p3399) ∨ (¬ p3576)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3954) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial9857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory1627 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7)
  exact rule9857 (meaning t m 2027) (meaning t m 2743) (meaning t m 3399) (meaning t m 3576) (meaning t m 3954) (meaning t m 4782) source

theorem rule9858 (p2027 p2743 p3093 p3954 p4024 p4845 : Prop) (h : (¬ p3954) ∨ (¬ p4845) ∨ (¬ p2743) ∨ (¬ p4024) ∨ (¬ p3093) ∨ p2027) : (p2027) ∨ (¬ p2743) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial9858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory1628 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6)
  exact rule9858 (meaning t m 2027) (meaning t m 2743) (meaning t m 3093) (meaning t m 3954) (meaning t m 4024) (meaning t m 4845) source

theorem rule9859 (p2027 p2946 p3156 p3425 p3969 p4324 p4381 p4786 p5119 : Prop) (h : (¬ p3969) ∨ (¬ p3425) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3156) ∨ (¬ p4324) ∨ (¬ p4786) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4786) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial9859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory1629 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule9859 (meaning t m 2027) (meaning t m 2946) (meaning t m 3156) (meaning t m 3425) (meaning t m 3969) (meaning t m 4324) (meaning t m 4381) (meaning t m 4786) (meaning t m 5119) source

theorem rule9860 (p2274 p3097 : Prop) (h : (¬ p3097) ∨ (¬ p2274)) : (¬ p2274) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial9860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory1630 (m.theta 5 6) (m.theta 6 7)
  exact rule9860 (meaning t m 2274) (meaning t m 3097) source

theorem rule9861 (p3276 p4425 : Prop) (h : (¬ p4425) ∨ (¬ p3276)) : (¬ p3276) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial9861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory1631 (m.theta 4 9) (m.theta 9 10)
  exact rule9861 (meaning t m 3276) (meaning t m 4425) source

theorem rule9862 (p5598 p5599 p5600 p5601 p5602 : Prop) : (¬ (p5598 ∧ p5599 ∧ p5600 ∧ p5601 ∧ p5602)) ∨ (p5598) := by
  classical
  tauto

theorem initial9862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5597)) ∨ (meaning t m 5598) := by
  exact rule9862 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule9863 (p5598 p5599 p5600 p5601 p5602 : Prop) : (¬ (p5598 ∧ p5599 ∧ p5600 ∧ p5601 ∧ p5602)) ∨ (p5599) := by
  classical
  tauto

theorem initial9863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5597)) ∨ (meaning t m 5599) := by
  exact rule9863 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule9864 (p5598 p5599 p5600 p5601 p5602 : Prop) : (¬ (p5598 ∧ p5599 ∧ p5600 ∧ p5601 ∧ p5602)) ∨ (p5600) := by
  classical
  tauto

theorem initial9864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5597)) ∨ (meaning t m 5600) := by
  exact rule9864 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule9865 (p5598 p5599 p5600 p5601 p5602 : Prop) : (¬ (p5598 ∧ p5599 ∧ p5600 ∧ p5601 ∧ p5602)) ∨ (p5601) := by
  classical
  tauto

theorem initial9865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5597)) ∨ (meaning t m 5601) := by
  exact rule9865 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule9866 (p5598 p5599 p5600 p5601 p5602 : Prop) : (¬ (p5598 ∧ p5599 ∧ p5600 ∧ p5601 ∧ p5602)) ∨ (p5602) := by
  classical
  tauto

theorem initial9866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5597)) ∨ (meaning t m 5602) := by
  exact rule9866 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule9867 (p5598 p5599 p5600 p5601 p5602 : Prop) : ((p5598 ∧ p5599 ∧ p5600 ∧ p5601 ∧ p5602)) ∨ (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5600) ∨ (¬ p5601) ∨ (¬ p5602) := by
  classical
  tauto

theorem initial9867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5597) ∨ (¬ (meaning t m 5598)) ∨ (¬ (meaning t m 5599)) ∨ (¬ (meaning t m 5600)) ∨ (¬ (meaning t m 5601)) ∨ (¬ (meaning t m 5602)) := by
  exact rule9867 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule9870 (p4009 p5604 p5605 p5606 p5607 : Prop) : (p4009) ∨ (¬ (p5604 ∧ p5605 ∧ p4009 ∧ p5606 ∧ p5607)) := by
  classical
  tauto

theorem initial9870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4009) ∨ (¬ (meaning t m 5603)) := by
  exact rule9870 (meaning t m 4009) (meaning t m 5604) (meaning t m 5605) (meaning t m 5606) (meaning t m 5607)

theorem rule9876 (p5597 p5603 : Prop) : (¬ (p5597 ∨ p5603)) ∨ (p5597) ∨ (p5603) := by
  classical
  tauto

theorem initial9876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5596)) ∨ (meaning t m 5597) ∨ (meaning t m 5603) := by
  exact rule9876 (meaning t m 5597) (meaning t m 5603)

theorem rule9877 (p4003 p5596 : Prop) (h : (p4003 ↔ p5596)) : (¬ p4003) ∨ (p5596) := by
  classical
  tauto

theorem initial9877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4003)) ∨ (meaning t m 5596) := by
  have source := ElevenTheory.theory1632 t (m.theta 3 10) (m.theta 3 8) (m.theta 8 10)
  exact rule9877 (meaning t m 4003) (meaning t m 5596) source

theorem rule9881 (p5610 p5611 p5612 p5613 p5614 : Prop) : (¬ (p5610 ∧ p5611 ∧ p5612 ∧ p5613 ∧ p5614)) ∨ (p5612) := by
  classical
  tauto

theorem initial9881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5609)) ∨ (meaning t m 5612) := by
  exact rule9881 (meaning t m 5610) (meaning t m 5611) (meaning t m 5612) (meaning t m 5613) (meaning t m 5614)

theorem rule9885 (p4019 p5616 p5617 p5618 p5619 : Prop) : (¬ (p5616 ∧ p5617 ∧ p4019 ∧ p5618 ∧ p5619)) ∨ (p5616) := by
  classical
  tauto

theorem initial9885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5615)) ∨ (meaning t m 5616) := by
  exact rule9885 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule9886 (p4019 p5616 p5617 p5618 p5619 : Prop) : (¬ (p5616 ∧ p5617 ∧ p4019 ∧ p5618 ∧ p5619)) ∨ (p5617) := by
  classical
  tauto

theorem initial9886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5615)) ∨ (meaning t m 5617) := by
  exact rule9886 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule9887 (p4019 p5616 p5617 p5618 p5619 : Prop) : (p4019) ∨ (¬ (p5616 ∧ p5617 ∧ p4019 ∧ p5618 ∧ p5619)) := by
  classical
  tauto

theorem initial9887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4019) ∨ (¬ (meaning t m 5615)) := by
  exact rule9887 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule9888 (p4019 p5616 p5617 p5618 p5619 : Prop) : (¬ (p5616 ∧ p5617 ∧ p4019 ∧ p5618 ∧ p5619)) ∨ (p5618) := by
  classical
  tauto

theorem initial9888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5615)) ∨ (meaning t m 5618) := by
  exact rule9888 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule9889 (p4019 p5616 p5617 p5618 p5619 : Prop) : (¬ (p5616 ∧ p5617 ∧ p4019 ∧ p5618 ∧ p5619)) ∨ (p5619) := by
  classical
  tauto

theorem initial9889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5615)) ∨ (meaning t m 5619) := by
  exact rule9889 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule9890 (p4019 p5616 p5617 p5618 p5619 : Prop) : (¬ p4019) ∨ ((p5616 ∧ p5617 ∧ p4019 ∧ p5618 ∧ p5619)) ∨ (¬ p5616) ∨ (¬ p5617) ∨ (¬ p5618) ∨ (¬ p5619) := by
  classical
  tauto

theorem initial9890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4019)) ∨ (meaning t m 5615) ∨ (¬ (meaning t m 5616)) ∨ (¬ (meaning t m 5617)) ∨ (¬ (meaning t m 5618)) ∨ (¬ (meaning t m 5619)) := by
  exact rule9890 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule9893 (p5609 p5615 : Prop) : (¬ (p5609 ∨ p5615)) ∨ (p5609) ∨ (p5615) := by
  classical
  tauto

theorem initial9893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5608)) ∨ (meaning t m 5609) ∨ (meaning t m 5615) := by
  exact rule9893 (meaning t m 5609) (meaning t m 5615)

theorem rule9894 (p4013 p5608 : Prop) (h : (p4013 ↔ p5608)) : (¬ p4013) ∨ (p5608) := by
  classical
  tauto

theorem initial9894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4013)) ∨ (meaning t m 5608) := by
  have source := ElevenTheory.theory1633 t (m.theta 2 10) (m.theta 2 8) (m.theta 8 10)
  exact rule9894 (meaning t m 4013) (meaning t m 5608) source

theorem rule9896 (p2668 p3324 : Prop) (h : (¬ p3324) ∨ (¬ p2668)) : (¬ p2668) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial9896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory1634 (m.theta 3 6) (m.theta 6 8)
  exact rule9896 (meaning t m 2668) (meaning t m 3324) source

theorem rule9897 (p2027 p2911 p3362 p3389 p3551 p5260 : Prop) (h : (¬ p3389) ∨ (¬ p3362) ∨ (¬ p5260) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3551) ∨ (¬ p5260) := by
  classical
  tauto

theorem initial9897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 5260)) := by
  have source := ElevenTheory.theory1635 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule9897 (meaning t m 2027) (meaning t m 2911) (meaning t m 3362) (meaning t m 3389) (meaning t m 3551) (meaning t m 5260) source

theorem rule9898 (p2027 p2534 p3516 p3551 p4420 p4443 : Prop) (h : (¬ p3516) ∨ (¬ p4420) ∨ (¬ p3551) ∨ (¬ p4443) ∨ (¬ p2534) ∨ p2027) : (p2027) ∨ (¬ p2534) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4420) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial9898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory1636 t (m.theta 0 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule9898 (meaning t m 2027) (meaning t m 2534) (meaning t m 3516) (meaning t m 3551) (meaning t m 4420) (meaning t m 4443) source

theorem rule9899 (p2881 p3570 : Prop) (h : (¬ p3570) ∨ (¬ p2881)) : (¬ p2881) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial9899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory1637 (m.theta 5 7) (m.theta 7 8)
  exact rule9899 (meaning t m 2881) (meaning t m 3570) source

theorem rule9900 (p2027 p2387 p3654 p4118 p4345 p4771 : Prop) (h : (¬ p2387) ∨ (¬ p4345) ∨ (¬ p4771) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p4118)) : (p2027) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4118) ∨ (¬ p4345) ∨ (¬ p4771) := by
  classical
  tauto

theorem initial9900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4771)) := by
  have source := ElevenTheory.theory1638 t (m.theta 0 6) (m.theta 3 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule9900 (meaning t m 2027) (meaning t m 2387) (meaning t m 3654) (meaning t m 4118) (meaning t m 4345) (meaning t m 4771) source

theorem rule9902 (p3589 p3905 p4108 : Prop) (h : p3905 ∨ (¬ p3589) ∨ (¬ p4108)) : (¬ p3589) ∨ (p3905) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial9902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3589)) ∨ (meaning t m 3905) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory1640 (m.theta 0 1) (m.theta 0 2) (m.theta 0 4)
  exact rule9902 (meaning t m 3589) (meaning t m 3905) (meaning t m 4108) source

theorem rule9904 (p2027 p2584 p2589 p2667 p3027 p3579 p4154 p4646 : Prop) (h : (¬ p2667) ∨ (¬ p2584) ∨ (¬ p4154) ∨ (¬ p3027) ∨ (¬ p3579) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p3027) ∨ (¬ p3579) ∨ (¬ p4154) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial9904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1642 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule9904 (meaning t m 2027) (meaning t m 2584) (meaning t m 2589) (meaning t m 2667) (meaning t m 3027) (meaning t m 3579) (meaning t m 4154) (meaning t m 4646) source

theorem rule9905 (p2027 p2589 p2707 p3363 p3585 p3658 p4646 : Prop) (h : (¬ p2589) ∨ (¬ p4646) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2707) ∨ (¬ p3658)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2707) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial9905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1643 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7)
  exact rule9905 (meaning t m 2027) (meaning t m 2589) (meaning t m 2707) (meaning t m 3363) (meaning t m 3585) (meaning t m 3658) (meaning t m 4646) source

theorem rule9906 (p3146 p3692 : Prop) (h : (¬ p3692) ∨ (¬ p3146)) : (¬ p3146) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial9906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory1644 (m.theta 5 8) (m.theta 8 9)
  exact rule9906 (meaning t m 3146) (meaning t m 3692) source

theorem rule9907 (p2027 p3670 p3692 p4444 p4746 p5344 : Prop) (h : (¬ p4746) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3670) ∨ (¬ p5344)) : (p2027) ∨ (¬ p3670) ∨ (¬ p3692) ∨ (¬ p4444) ∨ (¬ p4746) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial9907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4746)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory1645 t (m.theta 2 8) (m.theta 2 9) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule9907 (meaning t m 2027) (meaning t m 3670) (meaning t m 3692) (meaning t m 4444) (meaning t m 4746) (meaning t m 5344) source

theorem rule9908 (p2027 p2363 p2373 p3949 p4433 p4948 : Prop) (h : (¬ p2373) ∨ (¬ p3949) ∨ (¬ p2363) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p4948)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p3949) ∨ (¬ p4433) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial9908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory1646 t (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule9908 (meaning t m 2027) (meaning t m 2363) (meaning t m 2373) (meaning t m 3949) (meaning t m 4433) (meaning t m 4948) source

theorem rule9909 (p2027 p3599 p3692 p4242 p4746 p5343 : Prop) (h : (¬ p3599) ∨ (¬ p4242) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4746) ∨ (¬ p5343)) : (p2027) ∨ (¬ p3599) ∨ (¬ p3692) ∨ (¬ p4242) ∨ (¬ p4746) ∨ (¬ p5343) := by
  classical
  tauto

theorem initial9909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4746)) ∨ (¬ (meaning t m 5343)) := by
  have source := ElevenTheory.theory1647 t (m.theta 1 2) (m.theta 2 8) (m.theta 2 9) (m.theta 5 8) (m.theta 8 9)
  exact rule9909 (meaning t m 2027) (meaning t m 3599) (meaning t m 3692) (meaning t m 4242) (meaning t m 4746) (meaning t m 5343) source

theorem rule9910 (p2027 p2132 p3583 p3589 p4366 p4793 : Prop) (h : (¬ p3589) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p4793) ∨ (¬ p3583) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial9910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory1648 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 5)
  exact rule9910 (meaning t m 2027) (meaning t m 2132) (meaning t m 3583) (meaning t m 3589) (meaning t m 4366) (meaning t m 4793) source

theorem rule9911 (p2027 p2088 p2112 p3537 p4379 p5339 : Prop) (h : (¬ p2112) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p5339) ∨ (¬ p4379)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2112) ∨ (¬ p3537) ∨ (¬ p4379) ∨ (¬ p5339) := by
  classical
  tauto

theorem initial9911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2112)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5339)) := by
  have source := ElevenTheory.theory1649 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 8) (m.theta 2 9) (m.theta 8 9)
  exact rule9911 (meaning t m 2027) (meaning t m 2088) (meaning t m 2112) (meaning t m 3537) (meaning t m 4379) (meaning t m 5339) source

theorem rule9913 (p2027 p2313 p3654 p4276 p4278 p4623 : Prop) (h : (¬ p4276) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p4623)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial9913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory1651 t (m.theta 0 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule9913 (meaning t m 2027) (meaning t m 2313) (meaning t m 3654) (meaning t m 4276) (meaning t m 4278) (meaning t m 4623) source

theorem rule9914 (p3389 p3540 : Prop) (h : (¬ p3540) ∨ (¬ p3389)) : (¬ p3389) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial9914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory1652 (m.theta 0 4) (m.theta 4 7)
  exact rule9914 (meaning t m 3389) (meaning t m 3540) source

theorem rule9915 (p2027 p2972 p3958 p4137 p4173 p5045 : Prop) (h : (¬ p4173) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p2972) ∨ p2027 ∨ (¬ p5045)) : (p2027) ∨ (¬ p2972) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p4173) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial9915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory1653 t (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule9915 (meaning t m 2027) (meaning t m 2972) (meaning t m 3958) (meaning t m 4137) (meaning t m 4173) (meaning t m 5045) source

theorem rule9916 (p2027 p2230 p2563 p3369 p3646 p5190 : Prop) (h : (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3369) ∨ (¬ p2230) ∨ (¬ p5190) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial9916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory1654 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule9916 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 3369) (meaning t m 3646) (meaning t m 5190) source

theorem rule9917 (p2027 p2307 p2588 p2962 p4032 p4203 p5043 : Prop) (h : (¬ p4203) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4032) ∨ (¬ p2962) ∨ (¬ p5043)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2962) ∨ (¬ p4032) ∨ (¬ p4203) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial9917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory1655 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule9917 (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 2962) (meaning t m 4032) (meaning t m 4203) (meaning t m 5043) source

theorem rule9918 (p2307 p3946 p4187 : Prop) (h : (¬ p3946) ∨ (¬ p2307) ∨ (¬ p4187)) : (¬ p2307) ∨ (¬ p3946) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial9918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory1656 (m.theta 0 6) (m.theta 6 7) (m.theta 6 9)
  exact rule9918 (meaning t m 2307) (meaning t m 3946) (meaning t m 4187) source

theorem rule9919 (p2027 p2318 p2507 p2588 p3527 p3551 p4452 : Prop) (h : (¬ p2588) ∨ (¬ p2507) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2318) ∨ (¬ p4452)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial9919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory1657 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule9919 (meaning t m 2027) (meaning t m 2318) (meaning t m 2507) (meaning t m 2588) (meaning t m 3527) (meaning t m 3551) (meaning t m 4452) source

theorem rule9920 (p2027 p2619 p2810 p2957 p4120 p4313 p4704 : Prop) (h : (¬ p4120) ∨ p2027 ∨ (¬ p4313) ∨ (¬ p2810) ∨ (¬ p4704) ∨ (¬ p2957) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p2810) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4313) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial9920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory1658 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule9920 (meaning t m 2027) (meaning t m 2619) (meaning t m 2810) (meaning t m 2957) (meaning t m 4120) (meaning t m 4313) (meaning t m 4704) source

theorem rule9921 (p2220 p4120 : Prop) (h : (¬ p4120) ∨ (¬ p2220)) : (¬ p2220) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial9921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory1659 (m.theta 0 5) (m.theta 5 8)
  exact rule9921 (meaning t m 2220) (meaning t m 4120) source

theorem rule9922 (p3309 p3549 : Prop) (h : (¬ p3549) ∨ (¬ p3309)) : (¬ p3309) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial9922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory1660 (m.theta 1 6) (m.theta 6 7)
  exact rule9922 (meaning t m 3309) (meaning t m 3549) source

theorem rule9925 (p2027 p2191 p2563 p2668 p4210 p4506 p4560 : Prop) (h : (¬ p4560) ∨ (¬ p2668) ∨ (¬ p4506) ∨ (¬ p2191) ∨ (¬ p4210) ∨ p2027 ∨ (¬ p2563)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p4210) ∨ (¬ p4506) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial9925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory1663 t (m.theta 1 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule9925 (meaning t m 2027) (meaning t m 2191) (meaning t m 2563) (meaning t m 2668) (meaning t m 4210) (meaning t m 4506) (meaning t m 4560) source

theorem rule9929 (p2027 p2743 p3707 p5333 p5387 p5460 : Prop) (h : (¬ p2743) ∨ (¬ p5460) ∨ p2027 ∨ (¬ p3707) ∨ (¬ p5333) ∨ (¬ p5387)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3707) ∨ (¬ p5333) ∨ (¬ p5387) ∨ (¬ p5460) := by
  classical
  tauto

theorem initial9929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 5333)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5460)) := by
  have source := ElevenTheory.theory1667 t (m.theta 1 2) (m.theta 1 9) (m.theta 2 3) (m.theta 2 9) (m.theta 9 10)
  exact rule9929 (meaning t m 2027) (meaning t m 2743) (meaning t m 3707) (meaning t m 5333) (meaning t m 5387) (meaning t m 5460) source

theorem rule9930 (p2027 p2641 p3497 p3662 p3984 p4203 p4507 : Prop) (h : (¬ p3984) ∨ (¬ p3662) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p4203) ∨ (¬ p4507)) : (p2027) ∨ (¬ p2641) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3984) ∨ (¬ p4203) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial9930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory1668 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule9930 (meaning t m 2027) (meaning t m 2641) (meaning t m 3497) (meaning t m 3662) (meaning t m 3984) (meaning t m 4203) (meaning t m 4507) source

theorem rule9931 (p2027 p2191 p2373 p2922 p4202 p4646 : Prop) (h : (¬ p2922) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p4202) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2373) ∨ (¬ p2922) ∨ (¬ p4202) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial9931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1669 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8)
  exact rule9931 (meaning t m 2027) (meaning t m 2191) (meaning t m 2373) (meaning t m 2922) (meaning t m 4202) (meaning t m 4646) source

theorem rule9932 (p2027 p3609 p3857 p3923 p4113 p4861 p4867 : Prop) (h : (¬ p4867) ∨ p2027 ∨ (¬ p4861) ∨ (¬ p3857) ∨ (¬ p3609) ∨ (¬ p4113) ∨ (¬ p3923)) : (p2027) ∨ (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3923) ∨ (¬ p4113) ∨ (¬ p4861) ∨ (¬ p4867) := by
  classical
  tauto

theorem initial9932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4861)) ∨ (¬ (meaning t m 4867)) := by
  have source := ElevenTheory.theory1670 t (m.theta 0 8) (m.theta 1 6) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule9932 (meaning t m 2027) (meaning t m 3609) (meaning t m 3857) (meaning t m 3923) (meaning t m 4113) (meaning t m 4861) (meaning t m 4867) source

theorem rule9933 (p2619 p3694 : Prop) (h : (¬ p3694) ∨ (¬ p2619)) : (¬ p2619) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial9933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory1671 (m.theta 2 5) (m.theta 5 8)
  exact rule9933 (meaning t m 2619) (meaning t m 3694) source

theorem rule9934 (p2027 p2191 p2220 p2745 p2951 p3136 p3368 : Prop) (h : (¬ p3136) ∨ (¬ p2191) ∨ (¬ p3368) ∨ (¬ p2951) ∨ (¬ p2745) ∨ p2027 ∨ (¬ p2220)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3368) := by
  classical
  tauto

theorem initial9934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3368)) := by
  have source := ElevenTheory.theory1672 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8)
  exact rule9934 (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 2745) (meaning t m 2951) (meaning t m 3136) (meaning t m 3368) source

theorem rule9935 (p2166 p2191 : Prop) (h : (¬ p2191) ∨ (¬ p2166)) : (¬ p2166) ∨ (¬ p2191) := by
  classical
  tauto

theorem initial9935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2191)) := by
  have source := ElevenTheory.theory1673 (m.theta 1 5) (m.theta 5 8)
  exact rule9935 (meaning t m 2166) (meaning t m 2191) source

theorem rule9936 (p2352 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p2352)) : (¬ p2352) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial9936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory1674 (m.theta 4 6) (m.theta 6 8)
  exact rule9936 (meaning t m 2352) (meaning t m 3956) source

theorem rule9937 (p2156 p3646 : Prop) (h : (¬ p3646) ∨ (¬ p2156)) : (¬ p2156) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial9937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory1675 (m.theta 0 5) (m.theta 5 6)
  exact rule9937 (meaning t m 2156) (meaning t m 3646) source

theorem rule9939 (p3319 p4026 : Prop) (h : (¬ p4026) ∨ (¬ p3319)) : (¬ p3319) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial9939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory1677 (m.theta 1 6) (m.theta 6 9)
  exact rule9939 (meaning t m 3319) (meaning t m 4026) source

theorem rule9940 (p2027 p3063 p3146 p4026 p4134 p4171 : Prop) (h : (¬ p4134) ∨ (¬ p4171) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p3063) ∨ (¬ p3146)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3146) ∨ (¬ p4026) ∨ (¬ p4134) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial9940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory1678 t (m.theta 1 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule9940 (meaning t m 2027) (meaning t m 3063) (meaning t m 3146) (meaning t m 4026) (meaning t m 4134) (meaning t m 4171) source

theorem rule9945 (p2027 p2241 p2254 p3027 p3172 p4044 : Prop) (h : p2027 ∨ (¬ p2254) ∨ (¬ p4044) ∨ (¬ p3172) ∨ (¬ p2241) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3172) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial9945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory1683 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule9945 (meaning t m 2027) (meaning t m 2241) (meaning t m 2254) (meaning t m 3027) (meaning t m 3172) (meaning t m 4044) source

theorem rule9946 (p2027 p2230 p2656 p3027 p3238 p3402 p4652 : Prop) (h : (¬ p3027) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p4652) ∨ (¬ p2656) ∨ (¬ p3402)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3027) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial9946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory1684 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule9946 (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 3027) (meaning t m 3238) (meaning t m 3402) (meaning t m 4652) source

theorem rule9947 (p2027 p2138 p2331 p4117 p4195 p5049 : Prop) (h : (¬ p4195) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p5049) ∨ (¬ p4117)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial9947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory1685 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6)
  exact rule9947 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 4117) (meaning t m 4195) (meaning t m 5049) source

theorem rule9948 (p2027 p2696 p2797 p3055 p4343 p4975 : Prop) (h : (¬ p3055) ∨ (¬ p4343) ∨ (¬ p2696) ∨ (¬ p4975) ∨ (¬ p2797) ∨ p2027) : (p2027) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3055) ∨ (¬ p4343) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial9948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory1686 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6)
  exact rule9948 (meaning t m 2027) (meaning t m 2696) (meaning t m 2797) (meaning t m 3055) (meaning t m 4343) (meaning t m 4975) source

theorem rule9949 (p2027 p2254 p2459 p2952 p3399 p3527 p3744 p3952 p4604 : Prop) (h : (¬ p2952) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p4604) ∨ (¬ p2254) ∨ (¬ p3952) ∨ (¬ p3744) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial9949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory1687 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule9949 (meaning t m 2027) (meaning t m 2254) (meaning t m 2459) (meaning t m 2952) (meaning t m 3399) (meaning t m 3527) (meaning t m 3744) (meaning t m 3952) (meaning t m 4604) source

theorem rule9950 (p2027 p2470 p3540 p3570 p4370 p4647 p5307 : Prop) (h : (¬ p3540) ∨ (¬ p5307) ∨ (¬ p4647) ∨ (¬ p4370) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4370) ∨ (¬ p4647) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial9950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory1688 t (m.theta 0 4) (m.theta 1 8) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule9950 (meaning t m 2027) (meaning t m 2470) (meaning t m 3540) (meaning t m 3570) (meaning t m 4370) (meaning t m 4647) (meaning t m 5307) source

theorem rule9951 (p2027 p2274 p2312 p3516 p3947 p4067 p4564 : Prop) (h : (¬ p3516) ∨ (¬ p4564) ∨ p2027 ∨ (¬ p2312) ∨ (¬ p2274) ∨ (¬ p3947) ∨ (¬ p4067)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial9951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory1689 t (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule9951 (meaning t m 2027) (meaning t m 2274) (meaning t m 2312) (meaning t m 3516) (meaning t m 3947) (meaning t m 4067) (meaning t m 4564) source

theorem rule9952 (p2027 p2299 p2319 p3527 p3546 p3946 p4620 : Prop) (h : (¬ p3527) ∨ (¬ p2319) ∨ (¬ p3946) ∨ (¬ p3546) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p4620)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3946) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial9952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1690 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule9952 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 3527) (meaning t m 3546) (meaning t m 3946) (meaning t m 4620) source

theorem rule9953 (p2027 p2619 p3690 p4042 p4244 p4666 : Prop) (h : (¬ p4042) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p3690) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3690) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial9953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory1691 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule9953 (meaning t m 2027) (meaning t m 2619) (meaning t m 3690) (meaning t m 4042) (meaning t m 4244) (meaning t m 4666) source

theorem rule9954 (p2656 p3759 p4343 : Prop) (h : (¬ p4343) ∨ p2656 ∨ (¬ p3759)) : (p2656) ∨ (¬ p3759) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial9954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2656) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory1692 (m.theta 0 4) (m.theta 2 4) (m.theta 3 4)
  exact rule9954 (meaning t m 2656) (meaning t m 3759) (meaning t m 4343) source

theorem rule9957 (p4435 p5622 p5623 p5624 p5625 : Prop) : (p4435) ∨ (¬ (p5622 ∧ p5623 ∧ p4435 ∧ p5624 ∧ p5625)) := by
  classical
  tauto

theorem initial9957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4435) ∨ (¬ (meaning t m 5621)) := by
  exact rule9957 (meaning t m 4435) (meaning t m 5622) (meaning t m 5623) (meaning t m 5624) (meaning t m 5625)

theorem rule9963 (p4053 p5627 p5628 p5629 p5630 : Prop) : (p4053) ∨ (¬ (p5627 ∧ p5628 ∧ p4053 ∧ p5629 ∧ p5630)) := by
  classical
  tauto

theorem initial9963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4053) ∨ (¬ (meaning t m 5626)) := by
  exact rule9963 (meaning t m 4053) (meaning t m 5627) (meaning t m 5628) (meaning t m 5629) (meaning t m 5630)

theorem rule9969 (p5621 p5626 : Prop) : (¬ (p5621 ∨ p5626)) ∨ (p5621) ∨ (p5626) := by
  classical
  tauto

theorem initial9969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5620)) ∨ (meaning t m 5621) ∨ (meaning t m 5626) := by
  exact rule9969 (meaning t m 5621) (meaning t m 5626)

theorem rule9970 (p4047 p5620 : Prop) (h : (p4047 ↔ p5620)) : (¬ p4047) ∨ (p5620) := by
  classical
  tauto

theorem initial9970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4047)) ∨ (meaning t m 5620) := by
  have source := ElevenTheory.theory1693 t (m.theta 1 10) (m.theta 1 6) (m.theta 6 10)
  exact rule9970 (meaning t m 4047) (meaning t m 5620) source

theorem rule9974 (p4372 p5633 p5634 p5635 p5636 : Prop) : (p4372) ∨ (¬ (p5633 ∧ p5634 ∧ p4372 ∧ p5635 ∧ p5636)) := by
  classical
  tauto

theorem initial9974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4372) ∨ (¬ (meaning t m 5632)) := by
  exact rule9974 (meaning t m 4372) (meaning t m 5633) (meaning t m 5634) (meaning t m 5635) (meaning t m 5636)

theorem rule9980 (p4063 p5638 p5639 p5640 p5641 : Prop) : (p4063) ∨ (¬ (p5638 ∧ p5639 ∧ p4063 ∧ p5640 ∧ p5641)) := by
  classical
  tauto

theorem initial9980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4063) ∨ (¬ (meaning t m 5637)) := by
  exact rule9980 (meaning t m 4063) (meaning t m 5638) (meaning t m 5639) (meaning t m 5640) (meaning t m 5641)

theorem rule9986 (p5632 p5637 : Prop) : (¬ (p5632 ∨ p5637)) ∨ (p5632) ∨ (p5637) := by
  classical
  tauto

theorem initial9986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5631)) ∨ (meaning t m 5632) ∨ (meaning t m 5637) := by
  exact rule9986 (meaning t m 5632) (meaning t m 5637)

theorem rule9987 (p4057 p5631 : Prop) (h : (p4057 ↔ p5631)) : (¬ p4057) ∨ (p5631) := by
  classical
  tauto

theorem initial9987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4057)) ∨ (meaning t m 5631) := by
  have source := ElevenTheory.theory1694 t (m.theta 0 10) (m.theta 0 7) (m.theta 7 10)
  exact rule9987 (meaning t m 4057) (meaning t m 5631) source

theorem rule9989 (p2307 p3549 p5016 : Prop) (h : (¬ p3549) ∨ (¬ p2307) ∨ (¬ p5016)) : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial9989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory1695 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule9989 (meaning t m 2307) (meaning t m 3549) (meaning t m 5016) source

theorem rule9990 (p2027 p2449 p3097 p3547 p3817 p4156 p4560 : Prop) (h : (¬ p3097) ∨ (¬ p3817) ∨ (¬ p3547) ∨ (¬ p4560) ∨ p2027 ∨ (¬ p4156) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3097) ∨ (¬ p3547) ∨ (¬ p3817) ∨ (¬ p4156) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial9990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory1696 t (m.theta 1 7) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule9990 (meaning t m 2027) (meaning t m 2449) (meaning t m 3097) (meaning t m 3547) (meaning t m 3817) (meaning t m 4156) (meaning t m 4560) source

theorem rule9991 (p2027 p2386 p2499 p2797 p2810 p3567 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p3567) ∨ (¬ p2386) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1697 t (m.theta 0 6) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule9991 (meaning t m 2027) (meaning t m 2386) (meaning t m 2499) (meaning t m 2797) (meaning t m 2810) (meaning t m 3567) (meaning t m 4811) source

theorem rule9992 (p2573 p2579 : Prop) (h : (¬ p2579) ∨ (¬ p2573)) : (¬ p2573) ∨ (¬ p2579) := by
  classical
  tauto

theorem initial9992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2579)) := by
  have source := ElevenTheory.theory1698 (m.theta 0 4) (m.theta 4 6)
  exact rule9992 (meaning t m 2573) (meaning t m 2579) source

theorem rule9993 (p2027 p2807 p2963 p3097 p3552 p4560 : Prop) (h : (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ p2027 ∨ (¬ p4560) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial9993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory1699 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule9993 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3097) (meaning t m 3552) (meaning t m 4560) source

theorem rule9994 (p2027 p2254 p2952 p3073 p3449 p3952 p3989 p4348 p4503 : Prop) (h : (¬ p3449) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4348) ∨ (¬ p3989) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial9994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory1700 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9994 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3073) (meaning t m 3449) (meaning t m 3952) (meaning t m 3989) (meaning t m 4348) (meaning t m 4503) source

theorem rule9995 (p2027 p3367 p3609 p4261 p4436 p5370 : Prop) (h : (¬ p4261) ∨ (¬ p3367) ∨ (¬ p4436) ∨ (¬ p3609) ∨ (¬ p5370) ∨ p2027) : (p2027) ∨ (¬ p3367) ∨ (¬ p3609) ∨ (¬ p4261) ∨ (¬ p4436) ∨ (¬ p5370) := by
  classical
  tauto

theorem initial9995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 5370)) := by
  have source := ElevenTheory.theory1701 t (m.theta 1 2) (m.theta 1 8) (m.theta 2 4) (m.theta 2 8) (m.theta 8 9)
  exact rule9995 (meaning t m 2027) (meaning t m 3367) (meaning t m 3609) (meaning t m 4261) (meaning t m 4436) (meaning t m 5370) source

theorem rule9996 (p2027 p2363 p3325 p3553 p4348 p4570 : Prop) (h : (¬ p3553) ∨ (¬ p3325) ∨ p2027 ∨ (¬ p4570) ∨ (¬ p4348) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial9996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory1702 t (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9996 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3553) (meaning t m 4348) (meaning t m 4570) source

theorem rule10001 (p4442 p5644 p5645 p5646 p5647 : Prop) : (p4442) ∨ (¬ (p5644 ∧ p5645 ∧ p4442 ∧ p5646 ∧ p5647)) := by
  classical
  tauto

theorem initial10001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4442) ∨ (¬ (meaning t m 5643)) := by
  exact rule10001 (meaning t m 4442) (meaning t m 5644) (meaning t m 5645) (meaning t m 5646) (meaning t m 5647)

theorem rule10005 (p4075 p5649 p5650 p5651 p5652 : Prop) : (¬ (p5649 ∧ p5650 ∧ p4075 ∧ p5651 ∧ p5652)) ∨ (p5649) := by
  classical
  tauto

theorem initial10005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5648)) ∨ (meaning t m 5649) := by
  exact rule10005 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule10006 (p4075 p5649 p5650 p5651 p5652 : Prop) : (¬ (p5649 ∧ p5650 ∧ p4075 ∧ p5651 ∧ p5652)) ∨ (p5650) := by
  classical
  tauto

theorem initial10006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5648)) ∨ (meaning t m 5650) := by
  exact rule10006 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule10007 (p4075 p5649 p5650 p5651 p5652 : Prop) : (p4075) ∨ (¬ (p5649 ∧ p5650 ∧ p4075 ∧ p5651 ∧ p5652)) := by
  classical
  tauto

theorem initial10007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4075) ∨ (¬ (meaning t m 5648)) := by
  exact rule10007 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule10008 (p4075 p5649 p5650 p5651 p5652 : Prop) : (¬ (p5649 ∧ p5650 ∧ p4075 ∧ p5651 ∧ p5652)) ∨ (p5651) := by
  classical
  tauto

theorem initial10008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5648)) ∨ (meaning t m 5651) := by
  exact rule10008 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule10009 (p4075 p5649 p5650 p5651 p5652 : Prop) : (¬ (p5649 ∧ p5650 ∧ p4075 ∧ p5651 ∧ p5652)) ∨ (p5652) := by
  classical
  tauto

theorem initial10009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5648)) ∨ (meaning t m 5652) := by
  exact rule10009 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule10010 (p4075 p5649 p5650 p5651 p5652 : Prop) : (¬ p4075) ∨ ((p5649 ∧ p5650 ∧ p4075 ∧ p5651 ∧ p5652)) ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5651) ∨ (¬ p5652) := by
  classical
  tauto

theorem initial10010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4075)) ∨ (meaning t m 5648) ∨ (¬ (meaning t m 5649)) ∨ (¬ (meaning t m 5650)) ∨ (¬ (meaning t m 5651)) ∨ (¬ (meaning t m 5652)) := by
  exact rule10010 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule10013 (p5643 p5648 : Prop) : (¬ (p5643 ∨ p5648)) ∨ (p5643) ∨ (p5648) := by
  classical
  tauto

theorem initial10013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5642)) ∨ (meaning t m 5643) ∨ (meaning t m 5648) := by
  exact rule10013 (meaning t m 5643) (meaning t m 5648)

theorem rule10014 (p4069 p5642 : Prop) (h : (p4069 ↔ p5642)) : (¬ p4069) ∨ (p5642) := by
  classical
  tauto

theorem initial10014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4069)) ∨ (meaning t m 5642) := by
  have source := ElevenTheory.theory1705 t (m.theta 1 10) (m.theta 1 7) (m.theta 7 10)
  exact rule10014 (meaning t m 4069) (meaning t m 5642) source

theorem rule10016 (p2027 p3063 p3791 p4105 p4405 p4442 : Prop) (h : (¬ p4405) ∨ (¬ p3063) ∨ (¬ p4442) ∨ p2027 ∨ (¬ p4105) ∨ (¬ p3791)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3791) ∨ (¬ p4105) ∨ (¬ p4405) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial10016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory1706 t (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule10016 (meaning t m 2027) (meaning t m 3063) (meaning t m 3791) (meaning t m 4105) (meaning t m 4405) (meaning t m 4442) source

theorem rule10018 (p2027 p2860 p3246 p3576 p3817 p4136 p4555 : Prop) (h : (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4555) ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4136) ∨ p2027) : (p2027) ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4136) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1708 t (m.theta 1 7) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule10018 (meaning t m 2027) (meaning t m 2860) (meaning t m 3246) (meaning t m 3576) (meaning t m 3817) (meaning t m 4136) (meaning t m 4555) source

theorem rule10019 (p2027 p2881 p3051 p4032 p4382 p4666 : Prop) (h : (¬ p3051) ∨ (¬ p4382) ∨ (¬ p4032) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4666)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4382) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial10019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory1709 t (m.theta 0 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule10019 (meaning t m 2027) (meaning t m 2881) (meaning t m 3051) (meaning t m 4032) (meaning t m 4382) (meaning t m 4666) source

theorem rule10020 (p2027 p2498 p3063 p3660 p3989 p4235 p4555 : Prop) (h : (¬ p2498) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p3660) ∨ (¬ p4555) ∨ (¬ p4235) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2498) ∨ (¬ p3063) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4235) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1710 t (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule10020 (meaning t m 2027) (meaning t m 2498) (meaning t m 3063) (meaning t m 3660) (meaning t m 3989) (meaning t m 4235) (meaning t m 4555) source

theorem rule10023 (p2027 p2122 p2313 p2386 p2499 p4375 p5214 : Prop) (h : (¬ p5214) ∨ (¬ p2122) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p2386) ∨ (¬ p4375) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p4375) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial10023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory1713 t (m.theta 0 6) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule10023 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2386) (meaning t m 2499) (meaning t m 4375) (meaning t m 5214) source

theorem rule10024 (p2027 p2284 p3246 p3947 p4386 p4555 : Prop) (h : (¬ p3246) ∨ (¬ p4555) ∨ (¬ p3947) ∨ (¬ p2284) ∨ (¬ p4386) ∨ p2027) : (p2027) ∨ (¬ p2284) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1714 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule10024 (meaning t m 2027) (meaning t m 2284) (meaning t m 3246) (meaning t m 3947) (meaning t m 4386) (meaning t m 4555) source

theorem rule10025 (p2027 p2727 p2996 p3201 p3740 p4753 : Prop) (h : (¬ p2727) ∨ (¬ p3201) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p4753) ∨ (¬ p3740)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3201) ∨ (¬ p3740) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial10025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory1715 t (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule10025 (meaning t m 2027) (meaning t m 2727) (meaning t m 2996) (meaning t m 3201) (meaning t m 3740) (meaning t m 4753) source

theorem rule10026 (p2027 p3005 p3568 p4195 p4405 p4417 : Prop) (h : (¬ p4405) ∨ p2027 ∨ (¬ p4417) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p3005)) : (p2027) ∨ (¬ p3005) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial10026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory1716 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule10026 (meaning t m 2027) (meaning t m 3005) (meaning t m 3568) (meaning t m 4195) (meaning t m 4405) (meaning t m 4417) source

theorem rule10029 (p2027 p2797 p3323 p3946 p3983 p4787 : Prop) (h : (¬ p3946) ∨ (¬ p4787) ∨ p2027 ∨ (¬ p3983) ∨ (¬ p2797) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p3983) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial10029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory1719 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9)
  exact rule10029 (meaning t m 2027) (meaning t m 2797) (meaning t m 3323) (meaning t m 3946) (meaning t m 3983) (meaning t m 4787) source

theorem rule10030 (p2088 p3857 : Prop) (h : (¬ p3857) ∨ (¬ p2088)) : (¬ p2088) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial10030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory1720 (m.theta 0 8) (m.theta 8 9)
  exact rule10030 (meaning t m 2088) (meaning t m 3857) source

theorem rule10031 (p2737 p2743 : Prop) (h : (¬ p2743) ∨ (¬ p2737)) : (¬ p2737) ∨ (¬ p2743) := by
  classical
  tauto

theorem initial10031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2743)) := by
  have source := ElevenTheory.theory1721 (m.theta 1 2) (m.theta 2 3)
  exact rule10031 (meaning t m 2737) (meaning t m 2743) source

theorem rule10032 (p2027 p2295 p2312 p2493 p2928 p4279 p4976 : Prop) (h : (¬ p4976) ∨ (¬ p2312) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4279) ∨ (¬ p2493) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p4279) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial10032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory1722 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule10032 (meaning t m 2027) (meaning t m 2295) (meaning t m 2312) (meaning t m 2493) (meaning t m 2928) (meaning t m 4279) (meaning t m 4976) source

theorem rule10033 (p2027 p2387 p2667 p2745 p2819 p4154 p4426 : Prop) (h : p2027 ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2819) ∨ (¬ p2387) ∨ (¬ p4154) ∨ (¬ p4426)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2819) ∨ (¬ p4154) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial10033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory1723 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule10033 (meaning t m 2027) (meaning t m 2387) (meaning t m 2667) (meaning t m 2745) (meaning t m 2819) (meaning t m 4154) (meaning t m 4426) source

theorem rule10036 (p4091 p4098 : Prop) : (p4091) ∨ (p4098) ∨ (¬ (p4091 ∨ p4098)) := by
  classical
  tauto

theorem initial10036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4091) ∨ (meaning t m 4098) ∨ (¬ (meaning t m 5653)) := by
  exact rule10036 (meaning t m 4091) (meaning t m 4098)

theorem rule10037 (p4082 p5653 : Prop) (h : (p4082 ↔ p5653)) : (¬ p4082) ∨ (p5653) := by
  classical
  tauto

theorem initial10037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4082)) ∨ (meaning t m 5653) := by
  have source := ElevenTheory.theory1724 t (m.theta 0 10) (m.theta 0 6) (m.theta 6 10)
  exact rule10037 (meaning t m 4082) (meaning t m 5653) source

theorem rule10055 (p2027 p2534 p3256 p3574 p4121 p4598 : Prop) (h : (¬ p4598) ∨ (¬ p2534) ∨ (¬ p3256) ∨ (¬ p4121) ∨ (¬ p3574) ∨ p2027) : (p2027) ∨ (¬ p2534) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4121) ∨ (¬ p4598) := by
  classical
  tauto

theorem initial10055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4598)) := by
  have source := ElevenTheory.theory1727 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule10055 (meaning t m 2027) (meaning t m 2534) (meaning t m 3256) (meaning t m 3574) (meaning t m 4121) (meaning t m 4598) source

theorem rule10057 (p2027 p2396 p2819 p3689 p4324 p4405 : Prop) (h : (¬ p4405) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p3689) ∨ (¬ p4324) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2819) ∨ (¬ p3689) ∨ (¬ p4324) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory1729 t (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule10057 (meaning t m 2027) (meaning t m 2396) (meaning t m 2819) (meaning t m 3689) (meaning t m 4324) (meaning t m 4405) source

theorem rule10059 (p2027 p2992 p3574 p4111 p4241 p4715 : Prop) (h : (¬ p4715) ∨ p2027 ∨ (¬ p4241) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2992) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial10059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory1731 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule10059 (meaning t m 2027) (meaning t m 2992) (meaning t m 3574) (meaning t m 4111) (meaning t m 4241) (meaning t m 4715) source

theorem rule10060 (p2027 p2098 p3425 p3570 p4804 p4898 : Prop) (h : (¬ p4804) ∨ (¬ p3425) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p4898) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4804) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial10060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4804)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory1732 t (m.theta 0 2) (m.theta 2 7) (m.theta 2 8) (m.theta 5 7) (m.theta 7 8)
  exact rule10060 (meaning t m 2027) (meaning t m 2098) (meaning t m 3425) (meaning t m 3570) (meaning t m 4804) (meaning t m 4898) source

theorem rule10063 (p2027 p2299 p3166 p3414 p4361 p4378 : Prop) (h : (¬ p4361) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p4378) ∨ (¬ p3414) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p4361) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial10063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory1735 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule10063 (meaning t m 2027) (meaning t m 2299) (meaning t m 3166) (meaning t m 3414) (meaning t m 4361) (meaning t m 4378) source

theorem rule10064 (p2027 p2946 p3055 p4117 p4315 p4749 : Prop) (h : (¬ p4315) ∨ (¬ p3055) ∨ (¬ p4749) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4117)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial10064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory1736 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule10064 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 4117) (meaning t m 4315) (meaning t m 4749) source

theorem rule10065 (p2027 p2299 p3166 p3414 p3699 p4378 p4559 : Prop) (h : (¬ p2299) ∨ (¬ p3699) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p3414) ∨ (¬ p3166) ∨ (¬ p4378)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4378) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory1737 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10065 (meaning t m 2027) (meaning t m 2299) (meaning t m 3166) (meaning t m 3414) (meaning t m 3699) (meaning t m 4378) (meaning t m 4559) source

theorem rule10066 (p2027 p2696 p2727 p2742 p2780 p4337 p4972 : Prop) (h : (¬ p2742) ∨ (¬ p4972) ∨ (¬ p4337) ∨ (¬ p2780) ∨ (¬ p2727) ∨ (¬ p2696) ∨ p2027) : (p2027) ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2780) ∨ (¬ p4337) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial10066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1738 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6)
  exact rule10066 (meaning t m 2027) (meaning t m 2696) (meaning t m 2727) (meaning t m 2742) (meaning t m 2780) (meaning t m 4337) (meaning t m 4972) source

theorem rule10067 (p2027 p2132 p2745 p3365 p3662 p5051 : Prop) (h : (¬ p3662) ∨ (¬ p3365) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p2745) ∨ (¬ p5051)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial10067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory1739 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule10067 (meaning t m 2027) (meaning t m 2132) (meaning t m 2745) (meaning t m 3365) (meaning t m 3662) (meaning t m 5051) source

theorem rule10068 (p2252 p2748 p3361 : Prop) (h : (¬ p2252) ∨ (¬ p2748) ∨ p3361) : (¬ p2252) ∨ (¬ p2748) ∨ (p3361) := by
  classical
  tauto

theorem initial10068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (meaning t m 3361) := by
  have source := ElevenTheory.theory1740 (m.theta 0 3) (m.theta 1 3) (m.theta 2 3)
  exact rule10068 (meaning t m 2252) (meaning t m 2748) (meaning t m 3361) source

theorem rule10069 (p3379 p3452 : Prop) (h : (¬ p3452) ∨ (¬ p3379)) : (¬ p3379) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial10069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory1741 (m.theta 0 1) (m.theta 1 4)
  exact rule10069 (meaning t m 3379) (meaning t m 3452) source

theorem rule10070 (p2641 p4154 : Prop) (h : (¬ p4154) ∨ (¬ p2641)) : (¬ p2641) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial10070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory1742 (m.theta 1 3) (m.theta 3 6)
  exact rule10070 (meaning t m 2641) (meaning t m 4154) source

theorem rule10072 (p2027 p2982 p4040 p4107 p4235 p4559 p4660 : Prop) (h : (¬ p4040) ∨ (¬ p4660) ∨ (¬ p4107) ∨ (¬ p2982) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4559)) : (p2027) ∨ (¬ p2982) ∨ (¬ p4040) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial10072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory1744 t (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10072 (meaning t m 2027) (meaning t m 2982) (meaning t m 4040) (meaning t m 4107) (meaning t m 4235) (meaning t m 4559) (meaning t m 4660) source

theorem rule10073 (p2027 p3588 p3599 p4107 p4477 p5233 : Prop) (h : (¬ p3588) ∨ (¬ p3599) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p5233) ∨ (¬ p4477)) : (p2027) ∨ (¬ p3588) ∨ (¬ p3599) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p5233) := by
  classical
  tauto

theorem initial10073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 5233)) := by
  have source := ElevenTheory.theory1745 t (m.theta 1 2) (m.theta 2 7) (m.theta 2 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10073 (meaning t m 2027) (meaning t m 3588) (meaning t m 3599) (meaning t m 4107) (meaning t m 4477) (meaning t m 5233) source

theorem rule10074 (p2027 p2098 p2299 p3425 p4169 p4559 p4804 : Prop) (h : (¬ p2299) ∨ (¬ p4804) ∨ p2027 ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p3425) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p4804) := by
  classical
  tauto

theorem initial10074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4804)) := by
  have source := ElevenTheory.theory1746 t (m.theta 0 2) (m.theta 2 7) (m.theta 2 8) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10074 (meaning t m 2027) (meaning t m 2098) (meaning t m 2299) (meaning t m 3425) (meaning t m 4169) (meaning t m 4559) (meaning t m 4804) source

theorem rule10075 (p3434 p4324 : Prop) (h : (¬ p4324) ∨ (¬ p3434)) : (¬ p3434) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial10075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory1747 (m.theta 2 7) (m.theta 7 9)
  exact rule10075 (meaning t m 3434) (meaning t m 4324) source

theorem rule10076 (p2027 p2589 p2891 p3948 p4235 p5191 : Prop) (h : (¬ p5191) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2891) ∨ (¬ p4235) ∨ (¬ p3948)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial10076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory1748 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule10076 (meaning t m 2027) (meaning t m 2589) (meaning t m 2891) (meaning t m 3948) (meaning t m 4235) (meaning t m 5191) source

theorem rule10077 (p2027 p2406 p2589 p2662 p2996 p4281 p4650 : Prop) (h : (¬ p4281) ∨ (¬ p4650) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2996)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p4281) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial10077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory1749 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule10077 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2662) (meaning t m 2996) (meaning t m 4281) (meaning t m 4650) source

theorem rule10078 (p2027 p2406 p2589 p2743 p3363 p3541 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3541) ∨ (¬ p2589) ∨ (¬ p2406) ∨ (¬ p3363)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2743) ∨ (¬ p3363) ∨ (¬ p3541) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial10078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1750 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule10078 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2743) (meaning t m 3363) (meaning t m 3541) (meaning t m 4752) source

theorem rule10079 (p2027 p2253 p2651 p2741 p3591 p4111 p4866 : Prop) (h : (¬ p4866) ∨ (¬ p3591) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2253)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p3591) ∨ (¬ p4111) ∨ (¬ p4866) := by
  classical
  tauto

theorem initial10079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4866)) := by
  have source := ElevenTheory.theory1751 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4)
  exact rule10079 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2741) (meaning t m 3591) (meaning t m 4111) (meaning t m 4866) source

theorem rule10080 (p2027 p2528 p3266 p3657 p4381 p4438 : Prop) (h : (¬ p3266) ∨ (¬ p4438) ∨ (¬ p3657) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial10080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory1752 t (m.theta 4 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10080 (meaning t m 2027) (meaning t m 2528) (meaning t m 3266) (meaning t m 3657) (meaning t m 4381) (meaning t m 4438) source

theorem rule10081 (p2528 p4340 p5373 : Prop) (h : (¬ p4340) ∨ (¬ p2528) ∨ (¬ p5373)) : (¬ p2528) ∨ (¬ p4340) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial10081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory1753 (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule10081 (meaning t m 2528) (meaning t m 4340) (meaning t m 5373) source

theorem rule10083 (p2027 p2737 p2850 p3238 p4257 p4749 : Prop) (h : (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p4749)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial10083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory1755 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule10083 (meaning t m 2027) (meaning t m 2737) (meaning t m 2850) (meaning t m 3238) (meaning t m 4257) (meaning t m 4749) source

theorem rule10086 (p2027 p2501 p3276 p4026 p4191 p4422 : Prop) (h : (¬ p2501) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p3276) ∨ (¬ p4026)) : (p2027) ∨ (¬ p2501) ∨ (¬ p3276) ∨ (¬ p4026) ∨ (¬ p4191) ∨ (¬ p4422) := by
  classical
  tauto

theorem initial10086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) := by
  have source := ElevenTheory.theory1758 t (m.theta 1 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule10086 (meaning t m 2027) (meaning t m 2501) (meaning t m 3276) (meaning t m 4026) (meaning t m 4191) (meaning t m 4422) source

theorem rule10087 (p2027 p2352 p2406 p2497 p3923 p4715 : Prop) (h : (¬ p3923) ∨ (¬ p2497) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p4715)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p3923) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial10087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory1759 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule10087 (meaning t m 2027) (meaning t m 2352) (meaning t m 2406) (meaning t m 2497) (meaning t m 3923) (meaning t m 4715) source

theorem rule10088 (p2027 p2427 p2946 p3414 p3699 p4702 : Prop) (h : (¬ p2946) ∨ (¬ p3699) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p4702) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory1760 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule10088 (meaning t m 2027) (meaning t m 2427) (meaning t m 2946) (meaning t m 3414) (meaning t m 3699) (meaning t m 4702) source

theorem rule10089 (p2027 p2807 p2963 p3549 p3552 p4757 : Prop) (h : (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ p2027 ∨ (¬ p4757) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3552) ∨ (¬ p4757) := by
  classical
  tauto

theorem initial10089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4757)) := by
  have source := ElevenTheory.theory1761 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule10089 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3549) (meaning t m 3552) (meaning t m 4757) source

theorem rule10090 (p2027 p2192 p3136 p3745 p4195 p4960 : Prop) (h : (¬ p3136) ∨ (¬ p4960) ∨ (¬ p4195) ∨ (¬ p3745) ∨ (¬ p2192) ∨ p2027) : (p2027) ∨ (¬ p2192) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory1762 t (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule10090 (meaning t m 2027) (meaning t m 2192) (meaning t m 3136) (meaning t m 3745) (meaning t m 4195) (meaning t m 4960) source

theorem rule10091 (p2027 p2717 p2745 p2996 p3551 p4155 p4781 : Prop) (h : (¬ p2745) ∨ (¬ p3551) ∨ (¬ p4781) ∨ (¬ p4155) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p2996)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial10091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory1763 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule10091 (meaning t m 2027) (meaning t m 2717) (meaning t m 2745) (meaning t m 2996) (meaning t m 3551) (meaning t m 4155) (meaning t m 4781) source

theorem rule10092 (p2027 p2191 p2952 p3166 p4311 p4957 : Prop) (h : p2027 ∨ (¬ p4957) ∨ (¬ p4311) ∨ (¬ p2191) ∨ (¬ p2952) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial10092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory1764 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule10092 (meaning t m 2027) (meaning t m 2191) (meaning t m 2952) (meaning t m 3166) (meaning t m 4311) (meaning t m 4957) source

theorem rule10093 (p2891 p3486 : Prop) (h : (¬ p3486) ∨ (¬ p2891)) : (¬ p2891) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial10093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory1765 (m.theta 1 5) (m.theta 5 7)
  exact rule10093 (meaning t m 2891) (meaning t m 3486) source

theorem rule10094 (p2807 p3172 p4044 : Prop) (h : (¬ p3172) ∨ (¬ p2807) ∨ (¬ p4044)) : (¬ p2807) ∨ (¬ p3172) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial10094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory1766 (m.theta 0 3) (m.theta 3 7) (m.theta 3 8)
  exact rule10094 (meaning t m 2807) (meaning t m 3172) (meaning t m 4044) source

theorem rule10095 (p2027 p2662 p2745 p3201 p3475 p3540 p4111 : Prop) (h : (¬ p3475) ∨ (¬ p2745) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p2662)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3201) ∨ (¬ p3475) ∨ (¬ p3540) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial10095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory1767 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule10095 (meaning t m 2027) (meaning t m 2662) (meaning t m 2745) (meaning t m 3201) (meaning t m 3475) (meaning t m 3540) (meaning t m 4111) source

theorem rule10097 (p2027 p2963 p3166 p3989 p4318 p4560 p5074 : Prop) (h : (¬ p5074) ∨ (¬ p2963) ∨ (¬ p3989) ∨ (¬ p3166) ∨ (¬ p4318) ∨ p2027 ∨ (¬ p4560)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3989) ∨ (¬ p4318) ∨ (¬ p4560) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial10097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4560)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory1769 t (m.theta 0 3) (m.theta 1 8) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule10097 (meaning t m 2027) (meaning t m 2963) (meaning t m 3166) (meaning t m 3989) (meaning t m 4318) (meaning t m 4560) (meaning t m 5074) source

theorem rule10098 (p2027 p3276 p3917 p4191 p4422 p5222 : Prop) (h : (¬ p3276) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p5222) ∨ (¬ p4422) ∨ (¬ p4191)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial10098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory1770 t (m.theta 2 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule10098 (meaning t m 2027) (meaning t m 3276) (meaning t m 3917) (meaning t m 4191) (meaning t m 4422) (meaning t m 5222) source

theorem rule10099 (p2027 p2088 p3266 p3322 p4191 p4617 : Prop) (h : p2027 ∨ (¬ p4617) ∨ (¬ p2088) ∨ (¬ p3266) ∨ (¬ p4191) ∨ (¬ p3322)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4617) := by
  classical
  tauto

theorem initial10099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4617)) := by
  have source := ElevenTheory.theory1771 t (m.theta 0 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10099 (meaning t m 2027) (meaning t m 2088) (meaning t m 3266) (meaning t m 3322) (meaning t m 4191) (meaning t m 4617) source

theorem rule10100 (p2027 p2459 p3266 p4802 p5338 p5387 : Prop) (h : (¬ p2459) ∨ (¬ p5387) ∨ (¬ p5338) ∨ (¬ p3266) ∨ (¬ p4802) ∨ p2027) : (p2027) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4802) ∨ (¬ p5338) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial10100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4802)) ∨ (¬ (meaning t m 5338)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory1772 t (m.theta 2 8) (m.theta 2 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule10100 (meaning t m 2027) (meaning t m 2459) (meaning t m 3266) (meaning t m 4802) (meaning t m 5338) (meaning t m 5387) source

theorem rule10101 (p2027 p2417 p3644 p4133 p4347 p4443 : Prop) (h : (¬ p4347) ∨ (¬ p2417) ∨ (¬ p4443) ∨ (¬ p3644) ∨ (¬ p4133) ∨ p2027) : (p2027) ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial10101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory1773 t (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10101 (meaning t m 2027) (meaning t m 2417) (meaning t m 3644) (meaning t m 4133) (meaning t m 4347) (meaning t m 4443) source

end SunPrize.SMT
