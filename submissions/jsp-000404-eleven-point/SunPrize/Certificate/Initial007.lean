import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory002
import SunPrize.Certificate.Theory003
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule6541 (p2104 p3425 p3685 : Prop) (h : (¬ p3425) ∨ (¬ p3685) ∨ p2104) : (p2104) ∨ (¬ p3425) ∨ (¬ p3685) := by
  classical
  tauto

theorem initial6541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2104) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) := by
  have source := ElevenTheory.theory708 (m.theta 0 2) (m.theta 2 7) (m.theta 2 8)
  exact rule6541 (meaning t m 2104) (meaning t m 3425) (meaning t m 3685) source

theorem rule6542 (p3506 p3853 p4321 : Prop) (h : (¬ p3853) ∨ (¬ p3506) ∨ (¬ p4321)) : (¬ p3506) ∨ (¬ p3853) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial6542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory709 (m.theta 1 9) (m.theta 3 9) (m.theta 9 10)
  exact rule6542 (meaning t m 3506) (meaning t m 3853) (meaning t m 4321) source

theorem rule6543 (p2192 p2284 p4282 : Prop) (h : (¬ p4282) ∨ (¬ p2284) ∨ p2192) : (p2192) ∨ (¬ p2284) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial6543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2192) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory710 (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule6543 (meaning t m 2192) (meaning t m 2284) (meaning t m 4282) source

theorem rule6545 (p3698 p4235 p4244 : Prop) (h : (¬ p3698) ∨ (¬ p4235) ∨ p4244) : (¬ p3698) ∨ (¬ p4235) ∨ (p4244) := by
  classical
  tauto

theorem initial6545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4235)) ∨ (meaning t m 4244) := by
  have source := ElevenTheory.theory712 (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6545 (meaning t m 3698) (meaning t m 4235) (meaning t m 4244) source

theorem rule6546 (p2274 p2295 p3745 : Prop) (h : (¬ p2295) ∨ (¬ p3745) ∨ p2274) : (p2274) ∨ (¬ p2295) ∨ (¬ p3745) := by
  classical
  tauto

theorem initial6546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2274) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3745)) := by
  have source := ElevenTheory.theory713 (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule6546 (meaning t m 2274) (meaning t m 2295) (meaning t m 3745) source

theorem rule6548 (p2505 p3093 p3379 : Prop) (h : (¬ p3379) ∨ (¬ p2505) ∨ p3093) : (¬ p2505) ∨ (p3093) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial6548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2505)) ∨ (meaning t m 3093) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory715 (m.theta 0 1) (m.theta 1 4) (m.theta 1 6)
  exact rule6548 (meaning t m 2505) (meaning t m 3093) (meaning t m 3379) source

theorem rule6549 (p2934 p3379 p3399 : Prop) (h : (¬ p2934) ∨ (¬ p3379) ∨ p3399) : (¬ p2934) ∨ (¬ p3379) ∨ (p3399) := by
  classical
  tauto

theorem initial6549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 3399) := by
  have source := ElevenTheory.theory716 (m.theta 0 1) (m.theta 1 4) (m.theta 1 7)
  exact rule6549 (meaning t m 2934) (meaning t m 3379) (meaning t m 3399) source

theorem rule6550 (p2449 p4324 p4325 : Prop) (h : (¬ p4324) ∨ (¬ p2449) ∨ (¬ p4325)) : (¬ p2449) ∨ (¬ p4324) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial6550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory717 (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule6550 (meaning t m 2449) (meaning t m 4324) (meaning t m 4325) source

theorem rule6551 (p3758 p3872 p4244 : Prop) (h : (¬ p3872) ∨ (¬ p4244) ∨ p3758) : (p3758) ∨ (¬ p3872) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial6551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3758) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory718 (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6551 (meaning t m 3758) (meaning t m 3872) (meaning t m 4244) source

theorem rule6552 (p2579 p3363 p3584 : Prop) (h : (¬ p3363) ∨ (¬ p2579) ∨ p3584) : (¬ p2579) ∨ (¬ p3363) ∨ (p3584) := by
  classical
  tauto

theorem initial6552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3363)) ∨ (meaning t m 3584) := by
  have source := ElevenTheory.theory719 (m.theta 0 4) (m.theta 2 4) (m.theta 4 6)
  exact rule6552 (meaning t m 2579) (meaning t m 3363) (meaning t m 3584) source

theorem rule6553 (p2331 p2651 p4194 : Prop) (h : (¬ p4194) ∨ (¬ p2331) ∨ p2651) : (¬ p2331) ∨ (p2651) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial6553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (meaning t m 2651) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory720 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule6553 (meaning t m 2331) (meaning t m 2651) (meaning t m 4194) source

theorem rule6554 (p3097 p3309 p3957 : Prop) (h : (¬ p3097) ∨ (¬ p3957) ∨ (¬ p3309)) : (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3957) := by
  classical
  tauto

theorem initial6554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3957)) := by
  have source := ElevenTheory.theory721 (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule6554 (meaning t m 3097) (meaning t m 3309) (meaning t m 3957) source

theorem rule6555 (p2246 p2807 p3027 : Prop) (h : (¬ p2246) ∨ (¬ p2807) ∨ p3027) : (¬ p2246) ∨ (¬ p2807) ∨ (p3027) := by
  classical
  tauto

theorem initial6555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2807)) ∨ (meaning t m 3027) := by
  have source := ElevenTheory.theory722 (m.theta 0 3) (m.theta 1 3) (m.theta 3 7)
  exact rule6555 (meaning t m 2246) (meaning t m 2807) (meaning t m 3027) source

theorem rule6558 (p4228 p4328 p4329 : Prop) (h : (¬ p4328) ∨ (¬ p4329) ∨ (¬ p4228)) : (¬ p4228) ∨ (¬ p4328) ∨ (¬ p4329) := by
  classical
  tauto

theorem initial6558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4329)) := by
  have source := ElevenTheory.theory725 (m.theta 2 6) (m.theta 3 6) (m.theta 6 10)
  exact rule6558 (meaning t m 4228) (meaning t m 4328) (meaning t m 4329) source

theorem rule6560 (p2779 p3483 p3654 : Prop) (h : (¬ p2779) ∨ (¬ p3654) ∨ p3483) : (¬ p2779) ∨ (p3483) ∨ (¬ p3654) := by
  classical
  tauto

theorem initial6560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2779)) ∨ (meaning t m 3483) ∨ (¬ (meaning t m 3654)) := by
  have source := ElevenTheory.theory727 (m.theta 0 6) (m.theta 2 6) (m.theta 6 9)
  exact rule6560 (meaning t m 2779) (meaning t m 3483) (meaning t m 3654) source

theorem rule6561 (p2493 p3422 p3590 : Prop) (h : (¬ p2493) ∨ (¬ p3590) ∨ p3422) : (¬ p2493) ∨ (p3422) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial6561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (meaning t m 3422) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory728 (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule6561 (meaning t m 2493) (meaning t m 3422) (meaning t m 3590) source

theorem rule6564 (p2651 p2807 p3580 : Prop) (h : (¬ p2651) ∨ (¬ p3580) ∨ p2807) : (¬ p2651) ∨ (p2807) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial6564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (meaning t m 2807) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory731 (m.theta 0 3) (m.theta 3 4) (m.theta 3 7)
  exact rule6564 (meaning t m 2651) (meaning t m 2807) (meaning t m 3580) source

theorem rule6565 (p3246 p3947 p4333 : Prop) (h : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4333)) : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial6565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory732 (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule6565 (meaning t m 3246) (meaning t m 3947) (meaning t m 4333) source

theorem rule6567 (p3879 p4235 p4320 : Prop) (h : (¬ p3879) ∨ (¬ p4235) ∨ p4320) : (¬ p3879) ∨ (¬ p4235) ∨ (p4320) := by
  classical
  tauto

theorem initial6567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) ∨ (meaning t m 4320) := by
  have source := ElevenTheory.theory734 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6567 (meaning t m 3879) (meaning t m 4235) (meaning t m 4320) source

theorem rule6568 (p2437 p3083 p3875 : Prop) (h : (¬ p2437) ∨ (¬ p3875) ∨ p3083) : (¬ p2437) ∨ (p3083) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial6568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (meaning t m 3083) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory735 (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6568 (meaning t m 2437) (meaning t m 3083) (meaning t m 3875) source

theorem rule6569 (p3556 p4109 p4235 : Prop) (h : (¬ p4109) ∨ (¬ p4235) ∨ p3556) : (p3556) ∨ (¬ p4109) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial6569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3556) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory736 (m.theta 0 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6569 (meaning t m 3556) (meaning t m 4109) (meaning t m 4235) source

theorem rule6570 (p3486 p4034 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p4034) ∨ p3486) : (p3486) ∨ (¬ p4034) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial6570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3486) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory737 (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6570 (meaning t m 3486) (meaning t m 4034) (meaning t m 4235) source

theorem rule6572 (p2951 p3556 p4320 : Prop) (h : (¬ p2951) ∨ (¬ p4320) ∨ p3556) : (¬ p2951) ∨ (p3556) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial6572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (meaning t m 3556) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory739 (m.theta 0 5) (m.theta 3 5) (m.theta 5 7)
  exact rule6572 (meaning t m 2951) (meaning t m 3556) (meaning t m 4320) source

theorem rule6574 (p2797 p3136 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p3136) ∨ p2797) : (p2797) ∨ (¬ p3136) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial6574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2797) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory741 (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule6574 (meaning t m 2797) (meaning t m 3136) (meaning t m 4336) source

theorem rule6575 (p3550 p4138 : Prop) (h : p3550 ∨ p4138) : (p3550) ∨ (p4138) := by
  classical
  tauto

theorem initial6575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3550) ∨ (meaning t m 4138) := by
  have source := ElevenTheory.theory742 (m.theta 6 8) (m.theta 7 8)
  exact rule6575 (meaning t m 3550) (meaning t m 4138) source

theorem rule6576 (p4328 p4337 : Prop) (h : p4328 ∨ p4337) : (p4328) ∨ (p4337) := by
  classical
  tauto

theorem initial6576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4328) ∨ (meaning t m 4337) := by
  have source := ElevenTheory.theory743 (m.theta 2 6) (m.theta 3 6)
  exact rule6576 (meaning t m 4328) (meaning t m 4337) source

theorem rule6577 (p3572 p4156 p4195 : Prop) (h : (¬ p4156) ∨ (¬ p3572) ∨ p4195) : (¬ p3572) ∨ (¬ p4156) ∨ (p4195) := by
  classical
  tauto

theorem initial6577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4156)) ∨ (meaning t m 4195) := by
  have source := ElevenTheory.theory744 (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule6577 (meaning t m 3572) (meaning t m 4156) (meaning t m 4195) source

theorem rule6578 (p2210 p3591 p4338 : Prop) (h : (¬ p2210) ∨ (¬ p4338) ∨ (¬ p3591)) : (¬ p2210) ∨ (¬ p3591) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial6578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory745 (m.theta 0 1) (m.theta 1 5) (m.theta 1 6)
  exact rule6578 (meaning t m 2210) (meaning t m 3591) (meaning t m 4338) source

theorem rule6579 (p2079 p4339 : Prop) (h : ((¬ p2079) ↔ (¬ p4339))) : (p2079) ∨ (¬ p4339) := by
  classical
  tauto

theorem initial6579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2079) ∨ (¬ (meaning t m 4339)) := by
  have source := ElevenTheory.theory746 t (m.theta 2 10)
  exact rule6579 (meaning t m 2079) (meaning t m 4339) source

theorem rule6582 (p2103 p3857 p4340 : Prop) (h : (¬ p2103) ∨ (¬ p4340) ∨ p3857) : (¬ p2103) ∨ (p3857) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial6582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2103)) ∨ (meaning t m 3857) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory748 (m.theta 0 8) (m.theta 2 8) (m.theta 8 9)
  exact rule6582 (meaning t m 2103) (meaning t m 3857) (meaning t m 4340) source

theorem rule6583 (p2156 p3051 p3872 : Prop) (h : (¬ p2156) ∨ (¬ p3872) ∨ p3051) : (¬ p2156) ∨ (p3051) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial6583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 3051) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory749 (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6583 (meaning t m 2156) (meaning t m 3051) (meaning t m 3872) source

theorem rule6584 (p3570 p3690 p3945 : Prop) (h : (¬ p3945) ∨ (¬ p3690) ∨ p3570) : (p3570) ∨ (¬ p3690) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial6584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3570) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory750 (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6584 (meaning t m 3570) (meaning t m 3690) (meaning t m 3945) source

theorem rule6587 (p2963 p3172 p4341 : Prop) (h : (¬ p3172) ∨ (¬ p4341) ∨ p2963) : (p2963) ∨ (¬ p3172) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial6587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2963) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory753 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8)
  exact rule6587 (meaning t m 2963) (meaning t m 3172) (meaning t m 4341) source

theorem rule6589 (p2588 p3822 p4342 : Prop) (h : (¬ p2588) ∨ (¬ p4342) ∨ p3822) : (¬ p2588) ∨ (p3822) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial6589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2588)) ∨ (meaning t m 3822) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory755 (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule6589 (meaning t m 2588) (meaning t m 3822) (meaning t m 4342) source

theorem rule6590 (p3333 p3355 p3363 : Prop) (h : (¬ p3333) ∨ (¬ p3363) ∨ p3355) : (¬ p3333) ∨ (p3355) ∨ (¬ p3363) := by
  classical
  tauto

theorem initial6590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3333)) ∨ (meaning t m 3355) ∨ (¬ (meaning t m 3363)) := by
  have source := ElevenTheory.theory756 (m.theta 0 4) (m.theta 2 4) (m.theta 4 9)
  exact rule6590 (meaning t m 3333) (meaning t m 3355) (meaning t m 3363) source

theorem rule6591 (p3146 p3609 p4188 : Prop) (h : (¬ p4188) ∨ (¬ p3146) ∨ p3609) : (¬ p3146) ∨ (p3609) ∨ (¬ p4188) := by
  classical
  tauto

theorem initial6591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (meaning t m 3609) ∨ (¬ (meaning t m 4188)) := by
  have source := ElevenTheory.theory757 (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule6591 (meaning t m 3146) (meaning t m 3609) (meaning t m 4188) source

theorem rule6592 (p3553 p3644 p3740 : Prop) (h : (¬ p3644) ∨ (¬ p3740) ∨ p3553) : (p3553) ∨ (¬ p3644) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial6592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3553) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory758 (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule6592 (meaning t m 3553) (meaning t m 3644) (meaning t m 3740) source

theorem rule6594 (p2440 p3684 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p2440) ∨ p3684) : (¬ p2440) ∨ (p3684) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial6594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (meaning t m 3684) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory760 (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule6594 (meaning t m 2440) (meaning t m 3684) (meaning t m 4343) source

theorem rule6595 (p3572 p3877 p4044 : Prop) (h : (¬ p3877) ∨ (¬ p4044) ∨ p3572) : (p3572) ∨ (¬ p3877) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial6595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3572) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory761 (m.theta 2 3) (m.theta 3 7) (m.theta 3 8)
  exact rule6595 (meaning t m 3572) (meaning t m 3877) (meaning t m 4044) source

theorem rule6597 (p2951 p3051 p3156 p3747 : Prop) (h : (¬ p3051) ∨ (¬ p2951) ∨ (¬ p3747) ∨ p3156) : (¬ p2951) ∨ (¬ p3051) ∨ (p3156) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial6597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (meaning t m 3156) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory763 (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6597 (meaning t m 2951) (meaning t m 3051) (meaning t m 3156) (meaning t m 3747) source

theorem rule6598 (p3322 p3955 p4025 : Prop) (h : (¬ p3955) ∨ (¬ p3322) ∨ p4025) : (¬ p3322) ∨ (¬ p3955) ∨ (p4025) := by
  classical
  tauto

theorem initial6598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3955)) ∨ (meaning t m 4025) := by
  have source := ElevenTheory.theory764 (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule6598 (meaning t m 3322) (meaning t m 3955) (meaning t m 4025) source

theorem rule6599 (p4129 p4253 p4344 : Prop) (h : (¬ p4129) ∨ (¬ p4344) ∨ p4253) : (¬ p4129) ∨ (p4253) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial6599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4129)) ∨ (meaning t m 4253) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory765 (m.theta 2 7) (m.theta 5 7) (m.theta 7 10)
  exact rule6599 (meaning t m 4129) (meaning t m 4253) (meaning t m 4344) source

theorem rule6600 (p3990 p4118 p4157 p4345 p4346 : Prop) (h : (¬ p4157) ∨ (¬ p4118) ∨ (¬ p4345) ∨ (¬ p4346) ∨ (¬ p3990)) : (¬ p3990) ∨ (¬ p4118) ∨ (¬ p4157) ∨ (¬ p4345) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial6600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory766 (m.theta 3 8) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule6600 (meaning t m 3990) (meaning t m 4118) (meaning t m 4157) (meaning t m 4345) (meaning t m 4346) source

theorem rule6601 (p2137 p3370 p4243 : Prop) (h : (¬ p4243) ∨ (¬ p2137) ∨ p3370) : (¬ p2137) ∨ (p3370) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (meaning t m 3370) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory767 (m.theta 0 5) (m.theta 1 5) (m.theta 2 5)
  exact rule6601 (meaning t m 2137) (meaning t m 3370) (meaning t m 4243) source

theorem rule6602 (p2187 p2274 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p2274) ∨ p2187) : (p2187) ∨ (¬ p2274) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial6602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory768 (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6602 (meaning t m 2187) (meaning t m 2274) (meaning t m 3325) source

theorem rule6603 (p2373 p4119 p4235 : Prop) (h : (¬ p4119) ∨ (¬ p4235) ∨ (¬ p2373)) : (¬ p2373) ∨ (¬ p4119) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial6603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory769 (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6603 (meaning t m 2373) (meaning t m 4119) (meaning t m 4235) source

theorem rule6604 (p2109 p3609 p3857 : Prop) (h : (¬ p2109) ∨ (¬ p3609) ∨ (¬ p3857)) : (¬ p2109) ∨ (¬ p3609) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial6604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2109)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory770 (m.theta 0 8) (m.theta 2 8) (m.theta 8 9)
  exact rule6604 (meaning t m 2109) (meaning t m 3609) (meaning t m 3857) source

theorem rule6605 (p3550 p4347 p4348 : Prop) (h : (¬ p4347) ∨ (¬ p3550) ∨ p4348) : (¬ p3550) ∨ (¬ p4347) ∨ (p4348) := by
  classical
  tauto

theorem initial6605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4347)) ∨ (meaning t m 4348) := by
  have source := ElevenTheory.theory771 (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule6605 (meaning t m 3550) (meaning t m 4347) (meaning t m 4348) source

theorem rule6606 (p3758 p4173 p4243 : Prop) (h : (¬ p4243) ∨ (¬ p4173) ∨ p3758) : (p3758) ∨ (¬ p4173) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3758) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory772 (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule6606 (meaning t m 3758) (meaning t m 4173) (meaning t m 4243) source

theorem rule6607 (p2619 p2901 p4119 p4316 : Prop) (h : (¬ p2619) ∨ (¬ p4316) ∨ (¬ p4119) ∨ p2901) : (¬ p2619) ∨ (p2901) ∨ (¬ p4119) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial6607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (meaning t m 2901) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory773 (m.theta 2 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6607 (meaning t m 2619) (meaning t m 2901) (meaning t m 4119) (meaning t m 4316) source

theorem rule6608 (p2619 p2870 p4119 : Prop) (h : (¬ p2619) ∨ (¬ p4119) ∨ p2870) : (¬ p2619) ∨ (p2870) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial6608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (meaning t m 2870) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory774 (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6608 (meaning t m 2619) (meaning t m 2870) (meaning t m 4119) source

theorem rule6610 (p3172 p3292 p4349 : Prop) (h : (¬ p4349) ∨ (¬ p3172) ∨ p3292) : (¬ p3172) ∨ (p3292) ∨ (¬ p4349) := by
  classical
  tauto

theorem initial6610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3172)) ∨ (meaning t m 3292) ∨ (¬ (meaning t m 4349)) := by
  have source := ElevenTheory.theory776 (m.theta 0 3) (m.theta 3 8) (m.theta 3 9)
  exact rule6610 (meaning t m 3172) (meaning t m 3292) (meaning t m 4349) source

theorem rule6613 (p3692 p4042 p4348 : Prop) (h : (¬ p4042) ∨ (¬ p3692) ∨ p4348) : (¬ p3692) ∨ (¬ p4042) ∨ (p4348) := by
  classical
  tauto

theorem initial6613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4042)) ∨ (meaning t m 4348) := by
  have source := ElevenTheory.theory779 (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule6613 (meaning t m 3692) (meaning t m 4042) (meaning t m 4348) source

theorem rule6614 (p4340 p4351 p4352 p4353 : Prop) (h : (¬ p4351) ∨ (¬ p4352) ∨ (¬ p4340) ∨ (¬ p4353)) : (¬ p4340) ∨ (¬ p4351) ∨ (¬ p4352) ∨ (¬ p4353) := by
  classical
  tauto

theorem initial6614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 4352)) ∨ (¬ (meaning t m 4353)) := by
  have source := ElevenTheory.theory780 (m.theta 1 8) (m.theta 1 9) (m.theta 2 8) (m.theta 8 9)
  exact rule6614 (meaning t m 4340) (meaning t m 4351) (meaning t m 4352) (meaning t m 4353) source

theorem rule6616 (p2104 p2598 p4354 : Prop) (h : (¬ p4354) ∨ (¬ p2598) ∨ (¬ p2104)) : (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4354) := by
  classical
  tauto

theorem initial6616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 4354)) := by
  have source := ElevenTheory.theory782 (m.theta 0 2) (m.theta 2 4) (m.theta 2 8)
  exact rule6616 (meaning t m 2104) (meaning t m 2598) (meaning t m 4354) source

theorem rule6617 (p2191 p3694 p4243 : Prop) (h : (¬ p4243) ∨ (¬ p2191) ∨ p3694) : (¬ p2191) ∨ (p3694) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (meaning t m 3694) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory783 (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule6617 (meaning t m 2191) (meaning t m 3694) (meaning t m 4243) source

theorem rule6618 (p3568 p4025 p4037 : Prop) (h : (¬ p4025) ∨ (¬ p3568) ∨ p4037) : (¬ p3568) ∨ (¬ p4025) ∨ (p4037) := by
  classical
  tauto

theorem initial6618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4025)) ∨ (meaning t m 4037) := by
  have source := ElevenTheory.theory784 (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule6618 (meaning t m 3568) (meaning t m 4025) (meaning t m 4037) source

theorem rule6620 (p2177 p2881 p4140 : Prop) (h : (¬ p2177) ∨ (¬ p4140) ∨ p2881) : (¬ p2177) ∨ (p2881) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial6620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (meaning t m 2881) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory786 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule6620 (meaning t m 2177) (meaning t m 2881) (meaning t m 4140) source

theorem rule6621 (p2542 p3016 p3660 : Prop) (h : (¬ p3660) ∨ (¬ p2542) ∨ p3016) : (¬ p2542) ∨ (p3016) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial6621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (meaning t m 3016) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory787 (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule6621 (meaning t m 2542) (meaning t m 3016) (meaning t m 3660) source

theorem rule6622 (p2230 p2509 p3519 p4355 : Prop) (h : (¬ p3519) ∨ (¬ p2509) ∨ (¬ p2230) ∨ (¬ p4355)) : (¬ p2230) ∨ (¬ p2509) ∨ (¬ p3519) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial6622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory788 (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8)
  exact rule6622 (meaning t m 2230) (meaning t m 2509) (meaning t m 3519) (meaning t m 4355) source

theorem rule6623 (p3201 p3389 p3759 : Prop) (h : (¬ p3759) ∨ (¬ p3389) ∨ p3201) : (p3201) ∨ (¬ p3389) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial6623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3201) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory789 (m.theta 0 4) (m.theta 2 4) (m.theta 4 7)
  exact rule6623 (meaning t m 3201) (meaning t m 3389) (meaning t m 3759) source

theorem rule6625 (p2737 p3364 p3367 : Prop) (h : (¬ p3367) ∨ (¬ p3364) ∨ p2737) : (p2737) ∨ (¬ p3364) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial6625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2737) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory791 (m.theta 1 2) (m.theta 2 3) (m.theta 2 4)
  exact rule6625 (meaning t m 2737) (meaning t m 3364) (meaning t m 3367) source

theorem rule6627 (p2230 p2406 p3519 : Prop) (h : (¬ p2230) ∨ (¬ p3519) ∨ p2406) : (¬ p2230) ∨ (p2406) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial6627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (meaning t m 2406) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory793 (m.theta 0 4) (m.theta 1 4) (m.theta 4 5)
  exact rule6627 (meaning t m 2230) (meaning t m 2406) (meaning t m 3519) source

theorem rule6628 (p2187 p2383 p4356 : Prop) (h : (¬ p2187) ∨ (¬ p4356) ∨ p2383) : (¬ p2187) ∨ (p2383) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial6628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (meaning t m 2383) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory794 (m.theta 0 6) (m.theta 5 6) (m.theta 6 8)
  exact rule6628 (meaning t m 2187) (meaning t m 2383) (meaning t m 4356) source

theorem rule6629 (p3097 p3955 p3989 : Prop) (h : (¬ p3097) ∨ (¬ p3955) ∨ p3989) : (¬ p3097) ∨ (¬ p3955) ∨ (p3989) := by
  classical
  tauto

theorem initial6629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3955)) ∨ (meaning t m 3989) := by
  have source := ElevenTheory.theory795 (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6629 (meaning t m 3097) (meaning t m 3955) (meaning t m 3989) source

theorem rule6630 (p3549 p3568 p4319 : Prop) (h : (¬ p3568) ∨ (¬ p4319) ∨ p3549) : (p3549) ∨ (¬ p3568) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial6630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3549) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory796 (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule6630 (meaning t m 3549) (meaning t m 3568) (meaning t m 4319) source

theorem rule6631 (p3365 p3425 p4357 : Prop) (h : (¬ p3365) ∨ (¬ p4357) ∨ p3425) : (¬ p3365) ∨ (p3425) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial6631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3365)) ∨ (meaning t m 3425) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory797 (m.theta 0 2) (m.theta 2 3) (m.theta 2 7)
  exact rule6631 (meaning t m 3365) (meaning t m 3425) (meaning t m 4357) source

theorem rule6633 (p2934 p3541 p3687 : Prop) (h : (¬ p2934) ∨ (¬ p3541) ∨ p3687) : (¬ p2934) ∨ (¬ p3541) ∨ (p3687) := by
  classical
  tauto

theorem initial6633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3541)) ∨ (meaning t m 3687) := by
  have source := ElevenTheory.theory799 (m.theta 1 2) (m.theta 1 4) (m.theta 1 7)
  exact rule6633 (meaning t m 2934) (meaning t m 3541) (meaning t m 3687) source

theorem rule6636 (p2748 p2996 p3572 : Prop) (h : (¬ p2748) ∨ (¬ p2996) ∨ p3572) : (¬ p2748) ∨ (¬ p2996) ∨ (p3572) := by
  classical
  tauto

theorem initial6636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 3572) := by
  have source := ElevenTheory.theory802 (m.theta 1 3) (m.theta 2 3) (m.theta 3 7)
  exact rule6636 (meaning t m 2748) (meaning t m 2996) (meaning t m 3572) source

theorem rule6637 (p2104 p2138 p4359 : Prop) (h : (¬ p4359) ∨ (¬ p2138) ∨ p2104) : (p2104) ∨ (¬ p2138) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial6637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2104) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory803 (m.theta 0 2) (m.theta 2 5) (m.theta 2 8)
  exact rule6637 (meaning t m 2104) (meaning t m 2138) (meaning t m 4359) source

theorem rule6638 (p2996 p4044 p4360 : Prop) (h : (¬ p4044) ∨ (¬ p4360) ∨ p2996) : (p2996) ∨ (¬ p4044) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial6638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2996) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory804 (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule6638 (meaning t m 2996) (meaning t m 4044) (meaning t m 4360) source

theorem rule6640 (p2143 p2156 p2860 : Prop) (h : (¬ p2860) ∨ (¬ p2143) ∨ p2156) : (¬ p2143) ∨ (p2156) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial6640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (meaning t m 2156) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory806 (m.theta 0 5) (m.theta 2 5) (m.theta 5 6)
  exact rule6640 (meaning t m 2143) (meaning t m 2156) (meaning t m 2860) source

theorem rule6641 (p4140 p4361 p4362 : Prop) (h : (¬ p4140) ∨ (¬ p4361) ∨ p4362) : (¬ p4140) ∨ (¬ p4361) ∨ (p4362) := by
  classical
  tauto

theorem initial6641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4361)) ∨ (meaning t m 4362) := by
  have source := ElevenTheory.theory807 t (m.theta 3 7) (m.theta 5 7) (m.theta 6 7)
  exact rule6641 (meaning t m 4140) (meaning t m 4361) (meaning t m 4362) source

theorem rule6642 (p2441 p3644 p3880 p4042 : Prop) (h : (¬ p4042) ∨ (¬ p2441) ∨ (¬ p3644) ∨ p3880) : (¬ p2441) ∨ (¬ p3644) ∨ (p3880) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial6642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3644)) ∨ (meaning t m 3880) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory808 (m.theta 4 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8)
  exact rule6642 (meaning t m 2441) (meaning t m 3644) (meaning t m 3880) (meaning t m 4042) source

theorem rule6643 (p3212 p3370 p4363 : Prop) (h : (¬ p3370) ∨ (¬ p3212) ∨ (¬ p4363)) : (¬ p3212) ∨ (¬ p3370) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial6643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory809 (m.theta 0 5) (m.theta 1 5) (m.theta 5 9)
  exact rule6643 (meaning t m 3212) (meaning t m 3370) (meaning t m 4363) source

theorem rule6644 (p2104 p3365 p4364 : Prop) (h : (¬ p3365) ∨ (¬ p4364) ∨ p2104) : (p2104) ∨ (¬ p3365) ∨ (¬ p4364) := by
  classical
  tauto

theorem initial6644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2104) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4364)) := by
  have source := ElevenTheory.theory810 (m.theta 0 2) (m.theta 2 3) (m.theta 2 8)
  exact rule6644 (meaning t m 2104) (meaning t m 3365) (meaning t m 4364) source

theorem rule6648 (p2534 p4118 p4346 : Prop) (h : (¬ p4118) ∨ (¬ p4346) ∨ p2534) : (p2534) ∨ (¬ p4118) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial6648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2534) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory814 (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule6648 (meaning t m 2534) (meaning t m 4118) (meaning t m 4346) source

theorem rule6649 (p2481 p2534 p3857 : Prop) (h : (¬ p2481) ∨ (¬ p3857) ∨ p2534) : (¬ p2481) ∨ (p2534) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial6649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2481)) ∨ (meaning t m 2534) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory815 (m.theta 0 8) (m.theta 4 8) (m.theta 8 9)
  exact rule6649 (meaning t m 2481) (meaning t m 2534) (meaning t m 3857) source

theorem rule6651 (p3848 p4349 p4360 : Prop) (h : (¬ p4349) ∨ (¬ p4360) ∨ p3848) : (p3848) ∨ (¬ p4349) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial6651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3848) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory817 (m.theta 1 3) (m.theta 3 8) (m.theta 3 9)
  exact rule6651 (meaning t m 3848) (meaning t m 4349) (meaning t m 4360) source

theorem rule6652 (p2247 p3031 p4366 : Prop) (h : (¬ p3031) ∨ (¬ p2247) ∨ p4366) : (¬ p2247) ∨ (¬ p3031) ∨ (p4366) := by
  classical
  tauto

theorem initial6652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3031)) ∨ (meaning t m 4366) := by
  have source := ElevenTheory.theory818 (m.theta 0 1) (m.theta 1 3) (m.theta 1 7)
  exact rule6652 (meaning t m 2247) (meaning t m 3031) (meaning t m 4366) source

theorem rule6656 (p2528 p3073 p4370 : Prop) (h : (¬ p4370) ∨ (¬ p3073) ∨ p2528) : (p2528) ∨ (¬ p3073) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial6656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2528) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory822 (m.theta 1 8) (m.theta 4 8) (m.theta 8 9)
  exact rule6656 (meaning t m 2528) (meaning t m 3073) (meaning t m 4370) source

theorem rule6657 (p2630 p4194 p4195 : Prop) (h : (¬ p4195) ∨ (¬ p2630) ∨ p4194) : (¬ p2630) ∨ (p4194) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial6657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (meaning t m 4194) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory823 (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule6657 (meaning t m 2630) (meaning t m 4194) (meaning t m 4195) source

theorem rule6662 (p3556 p3645 p3694 p4119 p4243 : Prop) (h : (¬ p4119) ∨ (¬ p3556) ∨ (¬ p4243) ∨ (¬ p3645) ∨ p3694) : (¬ p3556) ∨ (¬ p3645) ∨ (p3694) ∨ (¬ p4119) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (meaning t m 3694) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory828 (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6662 (meaning t m 3556) (meaning t m 3645) (meaning t m 3694) (meaning t m 4119) (meaning t m 4243) source

theorem rule6663 (p2493 p3422 p4030 : Prop) (h : (¬ p3422) ∨ (¬ p4030) ∨ p2493) : (p2493) ∨ (¬ p3422) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial6663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2493) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory829 (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule6663 (meaning t m 2493) (meaning t m 3422) (meaning t m 4030) source

theorem rule6664 (p4244 p4316 p4320 : Prop) (h : (¬ p4316) ∨ (¬ p4320) ∨ p4244) : (p4244) ∨ (¬ p4316) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial6664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4244) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory830 (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule6664 (meaning t m 4244) (meaning t m 4316) (meaning t m 4320) source

theorem rule6666 (p2417 p2933 p3631 : Prop) (h : (¬ p2933) ∨ (¬ p2417) ∨ p3631) : (¬ p2417) ∨ (¬ p2933) ∨ (p3631) := by
  classical
  tauto

theorem initial6666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2933)) ∨ (meaning t m 3631) := by
  have source := ElevenTheory.theory832 (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule6666 (meaning t m 2417) (meaning t m 2933) (meaning t m 3631) source

theorem rule6667 (p2963 p3172 p4196 : Prop) (h : (¬ p4196) ∨ (¬ p2963) ∨ p3172) : (¬ p2963) ∨ (p3172) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial6667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2963)) ∨ (meaning t m 3172) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory833 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8)
  exact rule6667 (meaning t m 2963) (meaning t m 3172) (meaning t m 4196) source

theorem rule6668 (p2406 p2850 p4030 : Prop) (h : (¬ p2850) ∨ (¬ p4030) ∨ p2406) : (p2406) ∨ (¬ p2850) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial6668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2406) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory834 (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule6668 (meaning t m 2406) (meaning t m 2850) (meaning t m 4030) source

theorem rule6669 (p2427 p4110 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p4110) ∨ (¬ p2427)) : (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial6669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory835 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6669 (meaning t m 2427) (meaning t m 4110) (meaning t m 4204) source

theorem rule6670 (p2427 p2891 p4210 : Prop) (h : (¬ p2427) ∨ (¬ p4210) ∨ p2891) : (¬ p2427) ∨ (p2891) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial6670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (meaning t m 2891) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory836 (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6670 (meaning t m 2427) (meaning t m 2891) (meaning t m 4210) source

theorem rule6671 (p3051 p4109 p4235 : Prop) (h : (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4235)) : (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial6671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory837 (m.theta 0 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6671 (meaning t m 3051) (meaning t m 4109) (meaning t m 4235) source

theorem rule6673 (p2957 p4032 p4208 : Prop) (h : (¬ p2957) ∨ (¬ p4032) ∨ p4208) : (¬ p2957) ∨ (¬ p4032) ∨ (p4208) := by
  classical
  tauto

theorem initial6673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 4032)) ∨ (meaning t m 4208) := by
  have source := ElevenTheory.theory839 (m.theta 0 5) (m.theta 3 5) (m.theta 5 9)
  exact rule6673 (meaning t m 2957) (meaning t m 4032) (meaning t m 4208) source

theorem rule6674 (p2137 p2220 p3694 : Prop) (h : (¬ p3694) ∨ (¬ p2137) ∨ (¬ p2220)) : (¬ p2137) ∨ (¬ p2220) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial6674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory840 (m.theta 0 5) (m.theta 2 5) (m.theta 5 8)
  exact rule6674 (meaning t m 2137) (meaning t m 2220) (meaning t m 3694) source

theorem rule6675 (p2598 p2774 p4375 : Prop) (h : (¬ p2598) ∨ (¬ p4375) ∨ p2774) : (¬ p2598) ∨ (p2774) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial6675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (meaning t m 2774) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory841 (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule6675 (meaning t m 2598) (meaning t m 2774) (meaning t m 4375) source

theorem rule6676 (p3692 p4118 p4312 : Prop) (h : (¬ p4312) ∨ (¬ p3692) ∨ p4118) : (¬ p3692) ∨ (p4118) ∨ (¬ p4312) := by
  classical
  tauto

theorem initial6676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3692)) ∨ (meaning t m 4118) ∨ (¬ (meaning t m 4312)) := by
  have source := ElevenTheory.theory842 (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule6676 (meaning t m 3692) (meaning t m 4118) (meaning t m 4312) source

theorem rule6677 (p2963 p3414 p4156 : Prop) (h : (¬ p4156) ∨ (¬ p3414) ∨ p2963) : (p2963) ∨ (¬ p3414) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial6677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2963) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory843 (m.theta 0 3) (m.theta 3 6) (m.theta 3 7)
  exact rule6677 (meaning t m 2963) (meaning t m 3414) (meaning t m 4156) source

theorem rule6680 (p2274 p2588 p4203 : Prop) (h : (¬ p4203) ∨ (¬ p2588) ∨ (¬ p2274)) : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial6680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory846 (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule6680 (meaning t m 2274) (meaning t m 2588) (meaning t m 4203) source

theorem rule6682 (p2191 p3486 p4119 : Prop) (h : (¬ p3486) ∨ (¬ p4119) ∨ p2191) : (p2191) ∨ (¬ p3486) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial6682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2191) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory848 (m.theta 1 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6682 (meaning t m 2191) (meaning t m 3486) (meaning t m 4119) source

theorem rule6683 (p2137 p2870 p3051 : Prop) (h : (¬ p2137) ∨ (¬ p3051) ∨ p2870) : (¬ p2137) ∨ (p2870) ∨ (¬ p3051) := by
  classical
  tauto

theorem initial6683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (meaning t m 2870) ∨ (¬ (meaning t m 3051)) := by
  have source := ElevenTheory.theory849 (m.theta 0 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6683 (meaning t m 2137) (meaning t m 2870) (meaning t m 3051) source

theorem rule6684 (p2668 p3323 p3990 : Prop) (h : (¬ p3990) ∨ (¬ p2668) ∨ p3323) : (¬ p2668) ∨ (p3323) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial6684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (meaning t m 3323) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory850 (m.theta 3 6) (m.theta 6 8) (m.theta 6 9)
  exact rule6684 (meaning t m 2668) (meaning t m 3323) (meaning t m 3990) source

theorem rule6685 (p3948 p4376 p4377 : Prop) (h : (¬ p3948) ∨ (¬ p4376) ∨ p4377) : (¬ p3948) ∨ (¬ p4376) ∨ (p4377) := by
  classical
  tauto

theorem initial6685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4376)) ∨ (meaning t m 4377) := by
  have source := ElevenTheory.theory851 t (m.theta 1 2) (m.theta 1 4) (m.theta 1 5)
  exact rule6685 (meaning t m 3948) (meaning t m 4376) (meaning t m 4377) source

theorem rule6687 (p2662 p3363 p3487 p3590 : Prop) (h : (¬ p3590) ∨ (¬ p3363) ∨ (¬ p3487) ∨ p2662) : (p2662) ∨ (¬ p3363) ∨ (¬ p3487) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial6687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2662) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory853 (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 3 4)
  exact rule6687 (meaning t m 2662) (meaning t m 3363) (meaning t m 3487) (meaning t m 3590) source

theorem rule6688 (p3347 p3363 p3590 : Prop) (h : (¬ p3590) ∨ (¬ p3363) ∨ p3347) : (p3347) ∨ (¬ p3363) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial6688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3347) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory854 (m.theta 0 4) (m.theta 1 4) (m.theta 2 4)
  exact rule6688 (meaning t m 3347) (meaning t m 3363) (meaning t m 3590) source

theorem rule6690 (p3519 p3759 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p3759) ∨ p3519) : (p3519) ∨ (¬ p3759) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial6690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3519) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory856 (m.theta 0 4) (m.theta 1 4) (m.theta 2 4)
  exact rule6690 (meaning t m 3519) (meaning t m 3759) (meaning t m 4030) source

theorem rule6692 (p2192 p2563 p4210 : Prop) (h : (¬ p2563) ∨ (¬ p4210) ∨ p2192) : (p2192) ∨ (¬ p2563) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial6692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2192) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory858 (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6692 (meaning t m 2192) (meaning t m 2563) (meaning t m 4210) source

theorem rule6693 (p2563 p2860 p3695 : Prop) (h : (¬ p3695) ∨ (¬ p2563) ∨ p2860) : (¬ p2563) ∨ (p2860) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial6693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (meaning t m 2860) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory859 (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6693 (meaning t m 2563) (meaning t m 2860) (meaning t m 3695) source

theorem rule6694 (p2881 p2911 p4001 : Prop) (h : (¬ p4001) ∨ (¬ p2911) ∨ p2881) : (p2881) ∨ (¬ p2911) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial6694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2881) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory860 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule6694 (meaning t m 2881) (meaning t m 2911) (meaning t m 4001) source

theorem rule6695 (p4129 p4283 p4372 : Prop) (h : (¬ p4372) ∨ (¬ p4129) ∨ (¬ p4283)) : (¬ p4129) ∨ (¬ p4283) ∨ (¬ p4372) := by
  classical
  tauto

theorem initial6695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4372)) := by
  have source := ElevenTheory.theory861 (m.theta 0 7) (m.theta 5 7) (m.theta 7 10)
  exact rule6695 (meaning t m 4129) (meaning t m 4283) (meaning t m 4372) source

theorem rule6697 (p2470 p2656 p3083 : Prop) (h : (¬ p2656) ∨ (¬ p2470) ∨ p3083) : (¬ p2470) ∨ (¬ p2656) ∨ (p3083) := by
  classical
  tauto

theorem initial6697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 3083) := by
  have source := ElevenTheory.theory863 (m.theta 0 4) (m.theta 3 4) (m.theta 4 8)
  exact rule6697 (meaning t m 2470) (meaning t m 2656) (meaning t m 3083) source

theorem rule6698 (p3680 p4381 p4382 : Prop) (h : (¬ p3680) ∨ (¬ p4381) ∨ (¬ p4382)) : (¬ p3680) ∨ (¬ p4381) ∨ (¬ p4382) := by
  classical
  tauto

theorem initial6698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4382)) := by
  have source := ElevenTheory.theory864 (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule6698 (meaning t m 3680) (meaning t m 4381) (meaning t m 4382) source

theorem rule6699 (p3758 p3952 p4316 : Prop) (h : (¬ p4316) ∨ (¬ p3952) ∨ p3758) : (p3758) ∨ (¬ p3952) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial6699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3758) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory865 (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule6699 (meaning t m 3758) (meaning t m 3952) (meaning t m 4316) source

theorem rule6700 (p2928 p3238 p3741 : Prop) (h : (¬ p3741) ∨ (¬ p2928) ∨ p3238) : (¬ p2928) ∨ (p3238) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial6700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2928)) ∨ (meaning t m 3238) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory866 (m.theta 1 4) (m.theta 4 5) (m.theta 4 7)
  exact rule6700 (meaning t m 2928) (meaning t m 3238) (meaning t m 3741) source

theorem rule6701 (p3363 p3540 p3876 : Prop) (h : (¬ p3540) ∨ (¬ p3363) ∨ p3876) : (¬ p3363) ∨ (¬ p3540) ∨ (p3876) := by
  classical
  tauto

theorem initial6701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (meaning t m 3876) := by
  have source := ElevenTheory.theory867 (m.theta 0 4) (m.theta 2 4) (m.theta 4 7)
  exact rule6701 (meaning t m 3363) (meaning t m 3540) (meaning t m 3876) source

theorem rule6703 (p2143 p3646 p3758 : Prop) (h : (¬ p2143) ∨ (¬ p3646) ∨ p3758) : (¬ p2143) ∨ (¬ p3646) ∨ (p3758) := by
  classical
  tauto

theorem initial6703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 3646)) ∨ (meaning t m 3758) := by
  have source := ElevenTheory.theory869 (m.theta 0 5) (m.theta 2 5) (m.theta 5 6)
  exact rule6703 (meaning t m 2143) (meaning t m 3646) (meaning t m 3758) source

theorem rule6704 (p2143 p2220 p2619 : Prop) (h : (¬ p2143) ∨ (¬ p2619) ∨ p2220) : (¬ p2143) ∨ (p2220) ∨ (¬ p2619) := by
  classical
  tauto

theorem initial6704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (meaning t m 2220) ∨ (¬ (meaning t m 2619)) := by
  have source := ElevenTheory.theory870 (m.theta 0 5) (m.theta 2 5) (m.theta 5 8)
  exact rule6704 (meaning t m 2143) (meaning t m 2220) (meaning t m 2619) source

theorem rule6705 (p4133 p4383 p4384 : Prop) (h : (¬ p4383) ∨ (¬ p4133) ∨ p4384) : (¬ p4133) ∨ (¬ p4383) ∨ (p4384) := by
  classical
  tauto

theorem initial6705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4383)) ∨ (meaning t m 4384) := by
  have source := ElevenTheory.theory871 t (m.theta 4 8) (m.theta 6 8) (m.theta 7 8)
  exact rule6705 (meaning t m 4133) (meaning t m 4383) (meaning t m 4384) source

theorem rule6706 (p2476 p2656 p4256 : Prop) (h : (¬ p2656) ∨ (¬ p4256) ∨ p2476) : (p2476) ∨ (¬ p2656) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial6706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory872 (m.theta 0 4) (m.theta 3 4) (m.theta 4 8)
  exact rule6706 (meaning t m 2476) (meaning t m 2656) (meaning t m 4256) source

theorem rule6707 (p3742 p3875 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p3875) ∨ p3742) : (p3742) ∨ (¬ p3875) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial6707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3742) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory873 (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6707 (meaning t m 3742) (meaning t m 3875) (meaning t m 4256) source

theorem rule6708 (p2470 p2510 p2573 : Prop) (h : (¬ p2573) ∨ (¬ p2510) ∨ p2470) : (p2470) ∨ (¬ p2510) ∨ (¬ p2573) := by
  classical
  tauto

theorem initial6708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2470) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2573)) := by
  have source := ElevenTheory.theory874 (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule6708 (meaning t m 2470) (meaning t m 2510) (meaning t m 2573) source

theorem rule6709 (p2143 p4032 p4385 : Prop) (h : (¬ p2143) ∨ (¬ p4032) ∨ p4385) : (¬ p2143) ∨ (¬ p4032) ∨ (p4385) := by
  classical
  tauto

theorem initial6709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 4032)) ∨ (meaning t m 4385) := by
  have source := ElevenTheory.theory875 (m.theta 0 5) (m.theta 2 5) (m.theta 5 9)
  exact rule6709 (meaning t m 2143) (meaning t m 4032) (meaning t m 4385) source

theorem rule6710 (p2509 p2928 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p2928) ∨ p2509) : (p2509) ∨ (¬ p2928) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial6710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory876 (m.theta 1 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6710 (meaning t m 2509) (meaning t m 2928) (meaning t m 4186) source

theorem rule6711 (p2440 p3574 p3660 : Prop) (h : (¬ p3574) ∨ (¬ p3660) ∨ p2440) : (p2440) ∨ (¬ p3574) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial6711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2440) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory877 (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule6711 (meaning t m 2440) (meaning t m 3574) (meaning t m 3660) source

theorem rule6712 (p2132 p2774 p3985 : Prop) (h : (¬ p3985) ∨ (¬ p2132) ∨ p2774) : (¬ p2132) ∨ (p2774) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial6712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (meaning t m 2774) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory878 (m.theta 0 2) (m.theta 2 5) (m.theta 2 6)
  exact rule6712 (meaning t m 2132) (meaning t m 2774) (meaning t m 3985) source

theorem rule6713 (p2952 p3414 p4386 : Prop) (h : (¬ p4386) ∨ (¬ p2952) ∨ p3414) : (¬ p2952) ∨ (p3414) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial6713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2952)) ∨ (meaning t m 3414) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory879 (m.theta 0 3) (m.theta 3 5) (m.theta 3 7)
  exact rule6713 (meaning t m 2952) (meaning t m 3414) (meaning t m 4386) source

theorem rule6714 (p3822 p3872 p4140 p4185 : Prop) (h : (¬ p4140) ∨ (¬ p3822) ∨ (¬ p4185) ∨ (¬ p3872)) : (¬ p3822) ∨ (¬ p3872) ∨ (¬ p4140) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial6714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory880 (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule6714 (meaning t m 3822) (meaning t m 3872) (meaning t m 4140) (meaning t m 4185) source

theorem rule6716 (p2143 p2870 p3051 : Prop) (h : (¬ p2143) ∨ (¬ p2870) ∨ p3051) : (¬ p2143) ∨ (¬ p2870) ∨ (p3051) := by
  classical
  tauto

theorem initial6716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2870)) ∨ (meaning t m 3051) := by
  have source := ElevenTheory.theory882 (m.theta 0 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6716 (meaning t m 2143) (meaning t m 2870) (meaning t m 3051) source

theorem rule6717 (p2499 p3584 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p2499) ∨ p3584) : (¬ p2499) ∨ (p3584) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial6717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (meaning t m 3584) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory883 (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule6717 (meaning t m 2499) (meaning t m 3584) (meaning t m 4030) source

theorem rule6718 (p2166 p2619 p4243 : Prop) (h : (¬ p2619) ∨ (¬ p4243) ∨ p2166) : (p2166) ∨ (¬ p2619) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory884 (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule6718 (meaning t m 2166) (meaning t m 2619) (meaning t m 4243) source

theorem rule6720 (p2870 p2891 p4243 : Prop) (h : (¬ p4243) ∨ (¬ p2870) ∨ p2891) : (¬ p2870) ∨ (p2891) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (meaning t m 2891) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory886 (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6720 (meaning t m 2870) (meaning t m 2891) (meaning t m 4243) source

theorem rule6721 (p3323 p3564 p4389 : Prop) (h : (¬ p3323) ∨ (¬ p4389) ∨ p3564) : (¬ p3323) ∨ (p3564) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial6721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3323)) ∨ (meaning t m 3564) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory887 (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule6721 (meaning t m 3323) (meaning t m 3564) (meaning t m 4389) source

theorem rule6723 (p2797 p3005 p4341 : Prop) (h : (¬ p4341) ∨ (¬ p2797) ∨ p3005) : (¬ p2797) ∨ (p3005) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial6723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (meaning t m 3005) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory889 (m.theta 2 3) (m.theta 3 6) (m.theta 3 8)
  exact rule6723 (meaning t m 2797) (meaning t m 3005) (meaning t m 4341) source

theorem rule6724 (p2510 p2573 p2656 p3083 : Prop) (h : (¬ p2656) ∨ (¬ p2510) ∨ (¬ p2573) ∨ p3083) : (¬ p2510) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p3083) := by
  classical
  tauto

theorem initial6724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 3083) := by
  have source := ElevenTheory.theory890 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule6724 (meaning t m 2510) (meaning t m 2573) (meaning t m 2656) (meaning t m 3083) source

theorem rule6725 (p3661 p3877 p4315 : Prop) (h : (¬ p3661) ∨ (¬ p4315) ∨ p3877) : (¬ p3661) ∨ (p3877) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial6725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3661)) ∨ (meaning t m 3877) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory891 (m.theta 2 3) (m.theta 3 5) (m.theta 3 8)
  exact rule6725 (meaning t m 3661) (meaning t m 3877) (meaning t m 4315) source

theorem rule6726 (p2284 p4208 p4334 : Prop) (h : (¬ p2284) ∨ (¬ p4334) ∨ (¬ p4208)) : (¬ p2284) ∨ (¬ p4208) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial6726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory892 (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule6726 (meaning t m 2284) (meaning t m 4208) (meaning t m 4334) source

theorem rule6728 (p4063 p4066 p4391 : Prop) (h : (¬ p4066) ∨ (¬ p4391) ∨ (¬ p4063)) : (¬ p4063) ∨ (¬ p4066) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial6728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory894 (m.theta 0 7) (m.theta 3 7) (m.theta 7 10)
  exact rule6728 (meaning t m 4063) (meaning t m 4066) (meaning t m 4391) source

theorem rule6729 (p2630 p3413 p4316 p4392 : Prop) (h : (¬ p4392) ∨ (¬ p4316) ∨ (¬ p3413) ∨ (¬ p2630)) : (¬ p2630) ∨ (¬ p3413) ∨ (¬ p4316) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial6729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory895 (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule6729 (meaning t m 2630) (meaning t m 3413) (meaning t m 4316) (meaning t m 4392) source

theorem rule6730 (p4195 p4315 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p4195) ∨ p4315) : (¬ p4195) ∨ (p4315) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial6730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4195)) ∨ (meaning t m 4315) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory896 (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule6730 (meaning t m 4195) (meaning t m 4315) (meaning t m 4336) source

theorem rule6731 (p2284 p2901 p3872 : Prop) (h : (¬ p3872) ∨ (¬ p2284) ∨ p2901) : (¬ p2284) ∨ (p2901) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial6731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (meaning t m 2901) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory897 (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6731 (meaning t m 2284) (meaning t m 2901) (meaning t m 3872) source

theorem rule6732 (p3744 p4393 p4394 : Prop) (h : (¬ p4393) ∨ (¬ p4394) ∨ p3744) : (p3744) ∨ (¬ p4393) ∨ (¬ p4394) := by
  classical
  tauto

theorem initial6732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3744) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4394)) := by
  have source := ElevenTheory.theory898 (m.theta 5 6) (m.theta 6 10) (m.theta 6 9)
  exact rule6732 (meaning t m 3744) (meaning t m 4393) (meaning t m 4394) source

theorem rule6733 (p3556 p4031 p4235 : Prop) (h : (¬ p3556) ∨ (¬ p4031) ∨ p4235) : (¬ p3556) ∨ (¬ p4031) ∨ (p4235) := by
  classical
  tauto

theorem initial6733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4031)) ∨ (meaning t m 4235) := by
  have source := ElevenTheory.theory899 (m.theta 0 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6733 (meaning t m 3556) (meaning t m 4031) (meaning t m 4235) source

theorem rule6734 (p3556 p3646 p3872 : Prop) (h : (¬ p3556) ∨ (¬ p3872) ∨ p3646) : (¬ p3556) ∨ (p3646) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial6734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (meaning t m 3646) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory900 (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6734 (meaning t m 3556) (meaning t m 3646) (meaning t m 3872) source

theorem rule6735 (p4395 p4396 p4397 : Prop) (h : (¬ p4395) ∨ (¬ p4396) ∨ p4397) : (¬ p4395) ∨ (¬ p4396) ∨ (p4397) := by
  classical
  tauto

theorem initial6735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4396)) ∨ (meaning t m 4397) := by
  have source := ElevenTheory.theory901 t (m.theta 5 9) (m.theta 6 9) (m.theta 7 9)
  exact rule6735 (meaning t m 4395) (meaning t m 4396) (meaning t m 4397) source

theorem rule6736 (p2737 p2839 p4392 : Prop) (h : (¬ p4392) ∨ (¬ p2839) ∨ p2737) : (p2737) ∨ (¬ p2839) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial6736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2737) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory902 (m.theta 1 2) (m.theta 2 3) (m.theta 2 5)
  exact rule6736 (meaning t m 2737) (meaning t m 2839) (meaning t m 4392) source

theorem rule6739 (p2396 p2449 p3552 : Prop) (h : (¬ p2396) ∨ (¬ p3552) ∨ p2449) : (¬ p2396) ∨ (p2449) ∨ (¬ p3552) := by
  classical
  tauto

theorem initial6739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (meaning t m 2449) ∨ (¬ (meaning t m 3552)) := by
  have source := ElevenTheory.theory905 (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule6739 (meaning t m 2396) (meaning t m 2449) (meaning t m 3552) source

theorem rule6741 (p2274 p2295 p3986 : Prop) (h : (¬ p2274) ∨ (¬ p3986) ∨ p2295) : (¬ p2274) ∨ (p2295) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial6741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (meaning t m 2295) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory907 (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule6741 (meaning t m 2274) (meaning t m 2295) (meaning t m 3986) source

theorem rule6743 (p2482 p4238 p4399 : Prop) (h : (¬ p4399) ∨ (¬ p4238) ∨ p2482) : (p2482) ∨ (¬ p4238) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial6743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2482) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory909 (m.theta 0 4) (m.theta 0 5) (m.theta 0 8)
  exact rule6743 (meaning t m 2482) (meaning t m 4238) (meaning t m 4399) source

theorem rule6744 (p2230 p2470 p4355 : Prop) (h : (¬ p2230) ∨ (¬ p4355) ∨ p2470) : (¬ p2230) ∨ (p2470) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial6744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (meaning t m 2470) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory910 (m.theta 0 4) (m.theta 4 5) (m.theta 4 8)
  exact rule6744 (meaning t m 2230) (meaning t m 2470) (meaning t m 4355) source

theorem rule6747 (p3238 p3590 p3684 : Prop) (h : (¬ p3590) ∨ (¬ p3684) ∨ p3238) : (p3238) ∨ (¬ p3590) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial6747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3238) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory913 (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule6747 (meaning t m 3238) (meaning t m 3590) (meaning t m 3684) source

theorem rule6748 (p2406 p2518 p4355 : Prop) (h : (¬ p4355) ∨ (¬ p2406) ∨ p2518) : (¬ p2406) ∨ (p2518) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial6748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (meaning t m 2518) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory914 (m.theta 1 4) (m.theta 4 5) (m.theta 4 8)
  exact rule6748 (meaning t m 2406) (meaning t m 2518) (meaning t m 4355) source

theorem rule6749 (p2782 p4356 p4401 : Prop) (h : (¬ p4356) ∨ (¬ p4401) ∨ p2782) : (p2782) ∨ (¬ p4356) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial6749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2782) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory915 t (m.theta 0 6) (m.theta 2 6) (m.theta 5 6)
  exact rule6749 (meaning t m 2782) (meaning t m 4356) (meaning t m 4401) source

theorem rule6750 (p3692 p4118 p4311 : Prop) (h : (¬ p4311) ∨ (¬ p4118) ∨ p3692) : (p3692) ∨ (¬ p4118) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial6750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory916 (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule6750 (meaning t m 3692) (meaning t m 4118) (meaning t m 4311) source

theorem rule6752 (p2742 p2810 p4111 : Prop) (h : (¬ p2810) ∨ (¬ p2742) ∨ p4111) : (¬ p2742) ∨ (¬ p2810) ∨ (p4111) := by
  classical
  tauto

theorem initial6752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 4111) := by
  have source := ElevenTheory.theory918 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule6752 (meaning t m 2742) (meaning t m 2810) (meaning t m 4111) source

theorem rule6755 (p2850 p3422 p3660 : Prop) (h : (¬ p3660) ∨ (¬ p2850) ∨ p3422) : (¬ p2850) ∨ (p3422) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial6755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (meaning t m 3422) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory921 (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule6755 (meaning t m 2850) (meaning t m 3422) (meaning t m 3660) source

theorem rule6756 (p3201 p3641 p3875 : Prop) (h : (¬ p3875) ∨ (¬ p3201) ∨ p3641) : (¬ p3201) ∨ (p3641) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial6756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (meaning t m 3641) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory922 (m.theta 2 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6756 (meaning t m 3201) (meaning t m 3641) (meaning t m 3875) source

theorem rule6757 (p4208 p4320 p4402 : Prop) (h : (¬ p4320) ∨ (¬ p4402) ∨ p4208) : (p4208) ∨ (¬ p4320) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial6757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4208) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory923 (m.theta 3 5) (m.theta 5 7) (m.theta 5 9)
  exact rule6757 (meaning t m 4208) (meaning t m 4320) (meaning t m 4402) source

theorem rule6758 (p2510 p3875 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3875) ∨ p2510) : (p2510) ∨ (¬ p3875) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2510) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory924 (m.theta 4 6) (m.theta 4 7) (m.theta 4 8)
  exact rule6758 (meaning t m 2510) (meaning t m 3875) (meaning t m 3920) source

theorem rule6760 (p2579 p3540 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3540) ∨ p2579) : (p2579) ∨ (¬ p3540) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2579) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory926 (m.theta 0 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6760 (meaning t m 2579) (meaning t m 3540) (meaning t m 3920) source

theorem rule6761 (p2299 p4133 p4405 : Prop) (h : (¬ p4133) ∨ (¬ p2299) ∨ p4405) : (¬ p2299) ∨ (¬ p4133) ∨ (p4405) := by
  classical
  tauto

theorem initial6761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 4133)) ∨ (meaning t m 4405) := by
  have source := ElevenTheory.theory927 t (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule6761 (meaning t m 2299) (meaning t m 4133) (meaning t m 4405) source

theorem rule6762 (p3584 p3660 p3684 : Prop) (h : (¬ p3660) ∨ (¬ p3584) ∨ p3684) : (¬ p3584) ∨ (¬ p3660) ∨ (p3684) := by
  classical
  tauto

theorem initial6762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3660)) ∨ (meaning t m 3684) := by
  have source := ElevenTheory.theory928 (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule6762 (meaning t m 3584) (meaning t m 3660) (meaning t m 3684) source

theorem rule6764 (p3125 p3564 p4203 : Prop) (h : (¬ p3125) ∨ (¬ p4203) ∨ p3564) : (¬ p3125) ∨ (p3564) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial6764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (meaning t m 3564) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory930 (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule6764 (meaning t m 3125) (meaning t m 3564) (meaning t m 4203) source

theorem rule6785 (p2264 p2449 p3945 : Prop) (h : (¬ p2264) ∨ (¬ p3945) ∨ p2449) : (¬ p2264) ∨ (p2449) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial6785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (meaning t m 2449) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory932 (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6785 (meaning t m 2264) (meaning t m 2449) (meaning t m 3945) source

theorem rule6789 (p2192 p2891 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p2891) ∨ p2192) : (p2192) ∨ (¬ p2891) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial6789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2192) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory936 (m.theta 1 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6789 (meaning t m 2192) (meaning t m 2891) (meaning t m 4204) source

theorem rule6790 (p2210 p3379 p4202 : Prop) (h : (¬ p4202) ∨ (¬ p2210) ∨ p3379) : (¬ p2210) ∨ (p3379) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial6790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (meaning t m 3379) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory937 (m.theta 0 1) (m.theta 1 4) (m.theta 1 5)
  exact rule6790 (meaning t m 2210) (meaning t m 3379) (meaning t m 4202) source

theorem rule6791 (p2995 p3572 p4315 : Prop) (h : (¬ p3572) ∨ (¬ p2995) ∨ p4315) : (¬ p2995) ∨ (¬ p3572) ∨ (p4315) := by
  classical
  tauto

theorem initial6791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3572)) ∨ (meaning t m 4315) := by
  have source := ElevenTheory.theory938 (m.theta 2 3) (m.theta 3 5) (m.theta 3 7)
  exact rule6791 (meaning t m 2995) (meaning t m 3572) (meaning t m 4315) source

theorem rule6792 (p2166 p2533 p2972 : Prop) (h : (¬ p2533) ∨ (¬ p2166) ∨ p2972) : (¬ p2166) ∨ (¬ p2533) ∨ (p2972) := by
  classical
  tauto

theorem initial6792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2533)) ∨ (meaning t m 2972) := by
  have source := ElevenTheory.theory939 (m.theta 1 5) (m.theta 5 8) (m.theta 5 9)
  exact rule6792 (meaning t m 2166) (meaning t m 2533) (meaning t m 2972) source

theorem rule6793 (p2630 p2685 p3580 : Prop) (h : (¬ p2630) ∨ (¬ p3580) ∨ p2685) : (¬ p2630) ∨ (p2685) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial6793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (meaning t m 2685) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory940 (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule6793 (meaning t m 2630) (meaning t m 2685) (meaning t m 3580) source

theorem rule6794 (p3370 p4034 p4109 : Prop) (h : (¬ p3370) ∨ (¬ p4034) ∨ p4109) : (¬ p3370) ∨ (¬ p4034) ∨ (p4109) := by
  classical
  tauto

theorem initial6794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4034)) ∨ (meaning t m 4109) := by
  have source := ElevenTheory.theory941 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5)
  exact rule6794 (meaning t m 3370) (meaning t m 4034) (meaning t m 4109) source

theorem rule6795 (p3413 p4121 p4237 : Prop) (h : (¬ p3413) ∨ (¬ p4237) ∨ p4121) : (¬ p3413) ∨ (p4121) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial6795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3413)) ∨ (meaning t m 4121) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory942 (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule6795 (meaning t m 3413) (meaning t m 4121) (meaning t m 4237) source

theorem rule6797 (p2191 p3880 p4210 : Prop) (h : (¬ p4210) ∨ (¬ p2191) ∨ p3880) : (¬ p2191) ∨ (p3880) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial6797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (meaning t m 3880) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory944 (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule6797 (meaning t m 2191) (meaning t m 3880) (meaning t m 4210) source

theorem rule6798 (p2166 p2891 p4119 : Prop) (h : (¬ p4119) ∨ (¬ p2166) ∨ p2891) : (¬ p2166) ∨ (p2891) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial6798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (meaning t m 2891) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory945 (m.theta 1 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6798 (meaning t m 2166) (meaning t m 2891) (meaning t m 4119) source

theorem rule6799 (p2972 p3212 p3645 : Prop) (h : (¬ p3645) ∨ (¬ p2972) ∨ p3212) : (¬ p2972) ∨ (p3212) ∨ (¬ p3645) := by
  classical
  tauto

theorem initial6799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (meaning t m 3212) ∨ (¬ (meaning t m 3645)) := by
  have source := ElevenTheory.theory946 (m.theta 0 5) (m.theta 1 5) (m.theta 5 9)
  exact rule6799 (meaning t m 2972) (meaning t m 3212) (meaning t m 3645) source

theorem rule6801 (p2901 p3486 p4282 : Prop) (h : (¬ p4282) ∨ (¬ p2901) ∨ (¬ p3486)) : (¬ p2901) ∨ (¬ p3486) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial6801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory948 (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule6801 (meaning t m 2901) (meaning t m 3486) (meaning t m 4282) source

theorem rule6803 (p2850 p3201 p3741 : Prop) (h : (¬ p2850) ∨ (¬ p3741) ∨ p3201) : (¬ p2850) ∨ (p3201) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial6803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (meaning t m 3201) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory950 (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule6803 (meaning t m 2850) (meaning t m 3201) (meaning t m 3741) source

theorem rule6804 (p2363 p3256 p4417 : Prop) (h : (¬ p4417) ∨ (¬ p2363) ∨ p3256) : (¬ p2363) ∨ (p3256) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial6804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (meaning t m 3256) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory951 (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule6804 (meaning t m 2363) (meaning t m 3256) (meaning t m 4417) source

theorem rule6805 (p2386 p3564 p3654 : Prop) (h : (¬ p3564) ∨ (¬ p2386) ∨ p3654) : (¬ p2386) ∨ (¬ p3564) ∨ (p3654) := by
  classical
  tauto

theorem initial6805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3564)) ∨ (meaning t m 3654) := by
  have source := ElevenTheory.theory952 (m.theta 0 6) (m.theta 4 6) (m.theta 6 9)
  exact rule6805 (meaning t m 2386) (meaning t m 3564) (meaning t m 3654) source

theorem rule6807 (p2313 p2387 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p2387) ∨ p2313) : (p2313) ∨ (¬ p2387) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial6807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2313) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory954 (m.theta 0 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6807 (meaning t m 2313) (meaning t m 2387) (meaning t m 3325) source

theorem rule6809 (p3584 p3876 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3876) ∨ p3584) : (p3584) ∨ (¬ p3876) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3584) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory956 (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6809 (meaning t m 3584) (meaning t m 3876) (meaning t m 3920) source

theorem rule6810 (p2946 p3166 p4237 : Prop) (h : (¬ p4237) ∨ (¬ p2946) ∨ p3166) : (¬ p2946) ∨ (p3166) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial6810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2946)) ∨ (meaning t m 3166) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory957 (m.theta 0 3) (m.theta 3 5) (m.theta 3 8)
  exact rule6810 (meaning t m 2946) (meaning t m 3166) (meaning t m 4237) source

theorem rule6813 (p2166 p2891 p3747 : Prop) (h : (¬ p2891) ∨ (¬ p3747) ∨ p2166) : (p2166) ∨ (¬ p2891) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial6813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory960 (m.theta 1 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6813 (meaning t m 2166) (meaning t m 2891) (meaning t m 3747) source

theorem rule6814 (p2870 p2891 p4418 : Prop) (h : (¬ p2891) ∨ (¬ p4418) ∨ p2870) : (p2870) ∨ (¬ p2891) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial6814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2870) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory961 (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6814 (meaning t m 2870) (meaning t m 2891) (meaning t m 4418) source

theorem rule6815 (p2264 p2341 p4066 : Prop) (h : (¬ p4066) ∨ (¬ p2341) ∨ p2264) : (p2264) ∨ (¬ p2341) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial6815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2264) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory962 (m.theta 0 7) (m.theta 3 7) (m.theta 7 8)
  exact rule6815 (meaning t m 2264) (meaning t m 2341) (meaning t m 4066) source

theorem rule6816 (p2441 p2589 p3540 : Prop) (h : (¬ p2589) ∨ (¬ p2441) ∨ p3540) : (¬ p2441) ∨ (¬ p2589) ∨ (p3540) := by
  classical
  tauto

theorem initial6816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 3540) := by
  have source := ElevenTheory.theory963 (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule6816 (meaning t m 2441) (meaning t m 2589) (meaning t m 3540) source

theorem rule6818 (p2383 p3654 p3990 : Prop) (h : (¬ p3990) ∨ (¬ p2383) ∨ p3654) : (¬ p2383) ∨ (p3654) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial6818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (meaning t m 3654) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory965 (m.theta 0 6) (m.theta 6 8) (m.theta 6 9)
  exact rule6818 (meaning t m 2383) (meaning t m 3654) (meaning t m 3990) source

theorem rule6819 (p3324 p3990 p4037 : Prop) (h : (¬ p4037) ∨ (¬ p3990) ∨ p3324) : (p3324) ∨ (¬ p3990) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial6819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory966 (m.theta 3 6) (m.theta 6 8) (m.theta 6 9)
  exact rule6819 (meaning t m 3324) (meaning t m 3990) (meaning t m 4037) source

theorem rule6821 (p4133 p4157 p4420 : Prop) (h : (¬ p4133) ∨ (¬ p4157) ∨ p4420) : (¬ p4133) ∨ (¬ p4157) ∨ (p4420) := by
  classical
  tauto

theorem initial6821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4157)) ∨ (meaning t m 4420) := by
  have source := ElevenTheory.theory968 t (m.theta 4 8) (m.theta 6 8) (m.theta 7 8)
  exact rule6821 (meaning t m 4133) (meaning t m 4157) (meaning t m 4420) source

theorem rule6825 (p2437 p3083 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p3083) ∨ p2437) : (p2437) ∨ (¬ p3083) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial6825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2437) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory972 (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6825 (meaning t m 2437) (meaning t m 3083) (meaning t m 4186) source

theorem rule6827 (p2387 p2578 p3956 : Prop) (h : (¬ p2578) ∨ (¬ p3956) ∨ p2387) : (p2387) ∨ (¬ p2578) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial6827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2387) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory974 (m.theta 0 6) (m.theta 4 6) (m.theta 6 8)
  exact rule6827 (meaning t m 2387) (meaning t m 2578) (meaning t m 3956) source

theorem rule6828 (p3324 p3956 p4389 : Prop) (h : (¬ p4389) ∨ (¬ p3956) ∨ p3324) : (p3324) ∨ (¬ p3956) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial6828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory975 (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule6828 (meaning t m 3324) (meaning t m 3956) (meaning t m 4389) source

theorem rule6829 (p3698 p3758 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p3698) ∨ p3758) : (¬ p3698) ∨ (p3758) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial6829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3698)) ∨ (meaning t m 3758) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory976 (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6829 (meaning t m 3698) (meaning t m 3758) (meaning t m 4110) source

theorem rule6830 (p2437 p3201 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p3201) ∨ p2437) : (p2437) ∨ (¬ p3201) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial6830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2437) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory977 (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule6830 (meaning t m 2437) (meaning t m 3201) (meaning t m 4343) source

theorem rule6831 (p3055 p3425 p3686 : Prop) (h : (¬ p3055) ∨ (¬ p3686) ∨ p3425) : (¬ p3055) ∨ (p3425) ∨ (¬ p3686) := by
  classical
  tauto

theorem initial6831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3055)) ∨ (meaning t m 3425) ∨ (¬ (meaning t m 3686)) := by
  have source := ElevenTheory.theory978 (m.theta 0 2) (m.theta 2 4) (m.theta 2 7)
  exact rule6831 (meaning t m 3055) (meaning t m 3425) (meaning t m 3686) source

theorem rule6832 (p3646 p4032 p4205 : Prop) (h : (¬ p3646) ∨ (¬ p4205) ∨ p4032) : (¬ p3646) ∨ (p4032) ∨ (¬ p4205) := by
  classical
  tauto

theorem initial6832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3646)) ∨ (meaning t m 4032) ∨ (¬ (meaning t m 4205)) := by
  have source := ElevenTheory.theory979 (m.theta 0 5) (m.theta 5 6) (m.theta 5 9)
  exact rule6832 (meaning t m 3646) (meaning t m 4032) (meaning t m 4205) source

theorem rule6833 (p4022 p4191 p4425 : Prop) (h : (¬ p4191) ∨ (¬ p4022) ∨ p4425) : (¬ p4022) ∨ (¬ p4191) ∨ (p4425) := by
  classical
  tauto

theorem initial6833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4191)) ∨ (meaning t m 4425) := by
  have source := ElevenTheory.theory980 (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule6833 (meaning t m 4022) (meaning t m 4191) (meaning t m 4425) source

theorem rule6834 (p3201 p3641 p4186 : Prop) (h : (¬ p3641) ∨ (¬ p4186) ∨ p3201) : (p3201) ∨ (¬ p3641) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial6834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3201) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory981 (m.theta 2 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6834 (meaning t m 3201) (meaning t m 3641) (meaning t m 4186) source

theorem rule6835 (p2737 p2829 p4426 : Prop) (h : (¬ p2737) ∨ (¬ p4426) ∨ p2829) : (¬ p2737) ∨ (p2829) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial6835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (meaning t m 2829) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory982 (m.theta 1 2) (m.theta 2 3) (m.theta 2 6)
  exact rule6835 (meaning t m 2737) (meaning t m 2829) (meaning t m 4426) source

theorem rule6837 (p3954 p4366 p4400 : Prop) (h : (¬ p3954) ∨ (¬ p4400) ∨ p4366) : (¬ p3954) ∨ (p4366) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial6837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3954)) ∨ (meaning t m 4366) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory984 (m.theta 0 1) (m.theta 1 2) (m.theta 1 7)
  exact rule6837 (meaning t m 3954) (meaning t m 4366) (meaning t m 4400) source

theorem rule6838 (p2177 p2881 p4275 : Prop) (h : (¬ p2881) ∨ (¬ p4275) ∨ p2177) : (p2177) ∨ (¬ p2881) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial6838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2177) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory985 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule6838 (meaning t m 2177) (meaning t m 2881) (meaning t m 4275) source

theorem rule6839 (p2470 p2662 p3083 : Prop) (h : (¬ p2662) ∨ (¬ p3083) ∨ p2470) : (p2470) ∨ (¬ p2662) ∨ (¬ p3083) := by
  classical
  tauto

theorem initial6839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2470) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3083)) := by
  have source := ElevenTheory.theory986 (m.theta 0 4) (m.theta 3 4) (m.theta 4 8)
  exact rule6839 (meaning t m 2470) (meaning t m 2662) (meaning t m 3083) source

theorem rule6840 (p3817 p4107 p4427 : Prop) (h : (¬ p4427) ∨ (¬ p4107) ∨ p3817) : (p3817) ∨ (¬ p4107) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial6840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3817) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory987 (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule6840 (meaning t m 3817) (meaning t m 4107) (meaning t m 4427) source

theorem rule6841 (p3644 p3657 p4278 : Prop) (h : (¬ p3644) ∨ (¬ p3657) ∨ p4278) : (¬ p3644) ∨ (¬ p3657) ∨ (p4278) := by
  classical
  tauto

theorem initial6841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 4278) := by
  have source := ElevenTheory.theory988 (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6841 (meaning t m 3644) (meaning t m 3657) (meaning t m 4278) source

end SunPrize.SMT
