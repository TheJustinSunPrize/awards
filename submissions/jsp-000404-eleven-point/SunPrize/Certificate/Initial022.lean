import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory011
import SunPrize.Certificate.Theory012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule11620 (p3641 p3874 : Prop) (h : (¬ p3874) ∨ (¬ p3641)) : (¬ p3641) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial11620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory3116 (m.theta 2 4) (m.theta 4 8)
  exact rule11620 (meaning t m 3641) (meaning t m 3874) source

theorem rule11621 (p2027 p2518 p3379 p3555 p4034 p4610 : Prop) (h : (¬ p3379) ∨ (¬ p4034) ∨ p2027 ∨ (¬ p4610) ∨ (¬ p3555) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial11621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory3117 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 8)
  exact rule11621 (meaning t m 2027) (meaning t m 2518) (meaning t m 3379) (meaning t m 3555) (meaning t m 4034) (meaning t m 4610) source

theorem rule11622 (p2027 p4075 p4320 p4338 p4452 p4960 p5660 : Prop) (h : (¬ p4338) ∨ (¬ p4320) ∨ (¬ p5660) ∨ (¬ p4452) ∨ (¬ p4960) ∨ (¬ p4075) ∨ p2027) : (p2027) ∨ (¬ p4075) ∨ (¬ p4320) ∨ (¬ p4338) ∨ (¬ p4452) ∨ (¬ p4960) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial11622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4960)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory3118 t (m.theta 1 5) (m.theta 1 6) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10)
  exact rule11622 (meaning t m 2027) (meaning t m 4075) (meaning t m 4320) (meaning t m 4338) (meaning t m 4452) (meaning t m 4960) (meaning t m 5660) source

theorem rule11623 (p2027 p2145 p2295 p2331 p2373 p2396 p3951 p4117 p4120 p4948 : Prop) (h : p2027 ∨ (¬ p2145) ∨ (¬ p3951) ∨ (¬ p4117) ∨ (¬ p2373) ∨ (¬ p2331) ∨ (¬ p2295) ∨ (¬ p4120) ∨ (¬ p4948) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2373) ∨ (¬ p2396) ∨ (¬ p3951) ∨ (¬ p4117) ∨ (¬ p4120) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory3119 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule11623 (meaning t m 2027) (meaning t m 2145) (meaning t m 2295) (meaning t m 2331) (meaning t m 2373) (meaning t m 2396) (meaning t m 3951) (meaning t m 4117) (meaning t m 4120) (meaning t m 4948) source

theorem rule11624 (p2027 p3568 p4075 p4260 p4452 p4761 : Prop) (h : (¬ p4761) ∨ (¬ p3568) ∨ (¬ p4075) ∨ (¬ p4452) ∨ p2027 ∨ (¬ p4260)) : (p2027) ∨ (¬ p3568) ∨ (¬ p4075) ∨ (¬ p4260) ∨ (¬ p4452) ∨ (¬ p4761) := by
  classical
  tauto

theorem initial11624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4761)) := by
  have source := ElevenTheory.theory3120 t (m.theta 1 6) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10)
  exact rule11624 (meaning t m 2027) (meaning t m 3568) (meaning t m 4075) (meaning t m 4260) (meaning t m 4452) (meaning t m 4761) source

theorem rule11625 (p2027 p3324 p3449 p3591 p4318 p4761 : Prop) (h : (¬ p4761) ∨ (¬ p3591) ∨ (¬ p4318) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p3449)) : (p2027) ∨ (¬ p3324) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4318) ∨ (¬ p4761) := by
  classical
  tauto

theorem initial11625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4761)) := by
  have source := ElevenTheory.theory3121 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8)
  exact rule11625 (meaning t m 2027) (meaning t m 3324) (meaning t m 3449) (meaning t m 3591) (meaning t m 4318) (meaning t m 4761) source

theorem rule11626 (p2027 p2145 p2307 p2373 p2786 p3323 p3568 p4120 p4368 p4948 : Prop) (h : (¬ p4120) ∨ (¬ p2145) ∨ (¬ p4368) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2373) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2786) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4120) ∨ (¬ p4368) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory3122 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule11626 (meaning t m 2027) (meaning t m 2145) (meaning t m 2307) (meaning t m 2373) (meaning t m 2786) (meaning t m 3323) (meaning t m 3568) (meaning t m 4120) (meaning t m 4368) (meaning t m 4948) source

theorem rule11627 (p2027 p3038 p3631 p3947 p4111 p4652 : Prop) (h : (¬ p4652) ∨ (¬ p4111) ∨ (¬ p3038) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3947)) : (p2027) ∨ (¬ p3038) ∨ (¬ p3631) ∨ (¬ p3947) ∨ (¬ p4111) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory3123 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule11627 (meaning t m 2027) (meaning t m 3038) (meaning t m 3631) (meaning t m 3947) (meaning t m 4111) (meaning t m 4652) source

theorem rule11629 (p2027 p2156 p2751 p2951 p2992 p3758 p4392 : Prop) (h : p2027 ∨ (¬ p2751) ∨ (¬ p2156) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3758) ∨ (¬ p4392)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3758) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial11629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory3125 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule11629 (meaning t m 2027) (meaning t m 2156) (meaning t m 2751) (meaning t m 2951) (meaning t m 2992) (meaning t m 3758) (meaning t m 4392) source

theorem rule11630 (p2027 p2138 p2696 p2751 p2992 p4316 : Prop) (h : p2027 ∨ (¬ p4316) ∨ (¬ p2992) ∨ (¬ p2138) ∨ (¬ p2751) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2992) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial11630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory3126 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule11630 (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2751) (meaning t m 2992) (meaning t m 4316) source

theorem rule11631 (p2027 p2383 p2641 p2751 p3567 p4358 p4841 : Prop) (h : (¬ p2641) ∨ (¬ p4841) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p2751) ∨ (¬ p2383) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2641) ∨ (¬ p2751) ∨ (¬ p3567) ∨ (¬ p4358) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial11631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory3127 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule11631 (meaning t m 2027) (meaning t m 2383) (meaning t m 2641) (meaning t m 2751) (meaning t m 3567) (meaning t m 4358) (meaning t m 4841) source

theorem rule11634 (p2027 p2505 p3238 p4053 p4717 p5514 : Prop) (h : (¬ p3238) ∨ (¬ p5514) ∨ p2027 ∨ (¬ p4053) ∨ (¬ p2505) ∨ (¬ p4717)) : (p2027) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p4053) ∨ (¬ p4717) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial11634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory3130 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 10)
  exact rule11634 (meaning t m 2027) (meaning t m 2505) (meaning t m 3238) (meaning t m 4053) (meaning t m 4717) (meaning t m 5514) source

theorem rule11635 (p2027 p2476 p3537 p3585 p4727 p5373 : Prop) (h : (¬ p4727) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p5373) ∨ (¬ p2476) ∨ p2027) : (p2027) ∨ (¬ p2476) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p4727) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial11635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4727)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory3131 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8)
  exact rule11635 (meaning t m 2027) (meaning t m 2476) (meaning t m 3537) (meaning t m 3585) (meaning t m 4727) (meaning t m 5373) source

theorem rule11636 (p2027 p2553 p3461 p3746 p4425 p4620 : Prop) (h : p2027 ∨ (¬ p3746) ∨ (¬ p4620) ∨ (¬ p3461) ∨ (¬ p4425) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial11636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory3132 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule11636 (meaning t m 2027) (meaning t m 2553) (meaning t m 3461) (meaning t m 3746) (meaning t m 4425) (meaning t m 4620) source

theorem rule11637 (p2027 p2103 p3537 p3688 p3989 p4113 p4401 : Prop) (h : (¬ p3537) ∨ (¬ p2103) ∨ p2027 ∨ (¬ p4113) ∨ (¬ p3989) ∨ (¬ p3688) ∨ (¬ p4401)) : (p2027) ∨ (¬ p2103) ∨ (¬ p3537) ∨ (¬ p3688) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial11637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2103)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory3133 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8)
  exact rule11637 (meaning t m 2027) (meaning t m 2103) (meaning t m 3537) (meaning t m 3688) (meaning t m 3989) (meaning t m 4113) (meaning t m 4401) source

theorem rule11638 (p2027 p3742 p4253 p4753 p5085 p5503 : Prop) (h : (¬ p4753) ∨ (¬ p5503) ∨ (¬ p5085) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p4253)) : (p2027) ∨ (¬ p3742) ∨ (¬ p4253) ∨ (¬ p4753) ∨ (¬ p5085) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial11638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4753)) ∨ (¬ (meaning t m 5085)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory3134 t (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10)
  exact rule11638 (meaning t m 2027) (meaning t m 3742) (meaning t m 4253) (meaning t m 4753) (meaning t m 5085) (meaning t m 5503) source

theorem rule11639 (p2027 p3105 p3237 p3680 p4425 p4885 : Prop) (h : p2027 ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p3105) ∨ (¬ p3237) ∨ (¬ p4885)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial11639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory3135 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule11639 (meaning t m 2027) (meaning t m 3105) (meaning t m 3237) (meaning t m 3680) (meaning t m 4425) (meaning t m 4885) source

theorem rule11641 (p3115 p4208 : Prop) (h : (¬ p4208) ∨ (¬ p3115)) : (¬ p3115) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial11641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory3137 (m.theta 3 5) (m.theta 5 9)
  exact rule11641 (meaning t m 3115) (meaning t m 4208) source

theorem rule11642 (p2027 p2298 p2641 p2668 p2996 p4405 : Prop) (h : p2027 ∨ (¬ p2668) ∨ (¬ p2641) ∨ (¬ p4405) ∨ (¬ p2298) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2996) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial11642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory3138 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8)
  exact rule11642 (meaning t m 2027) (meaning t m 2298) (meaning t m 2641) (meaning t m 2668) (meaning t m 2996) (meaning t m 4405) source

theorem rule11643 (p2027 p2307 p2363 p3325 p3585 p3874 p3954 p4348 p4438 p5017 : Prop) (h : (¬ p3325) ∨ (¬ p3585) ∨ (¬ p2307) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p5017) ∨ (¬ p4348) ∨ (¬ p3954) ∨ (¬ p3874) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial11643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory3139 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11643 (meaning t m 2027) (meaning t m 2307) (meaning t m 2363) (meaning t m 3325) (meaning t m 3585) (meaning t m 3874) (meaning t m 3954) (meaning t m 4348) (meaning t m 4438) (meaning t m 5017) source

theorem rule11645 (p2027 p2139 p2220 p2810 p3146 p3365 p4256 p4348 p4438 : Prop) (h : (¬ p4256) ∨ (¬ p4348) ∨ (¬ p3146) ∨ (¬ p2220) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p2139) ∨ (¬ p3365) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2810) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial11645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory3141 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11645 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 2810) (meaning t m 3146) (meaning t m 3365) (meaning t m 4256) (meaning t m 4348) (meaning t m 4438) source

theorem rule11646 (p2027 p2252 p2750 p3414 p3449 p3553 p3954 p4181 p4348 p5122 : Prop) (h : (¬ p4181) ∨ (¬ p4348) ∨ (¬ p2750) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p2252) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3414) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p4348) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial11646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory3142 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule11646 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 3414) (meaning t m 3449) (meaning t m 3553) (meaning t m 3954) (meaning t m 4181) (meaning t m 4348) (meaning t m 5122) source

theorem rule11647 (p2027 p2156 p2177 p2245 p2274 p2528 p3172 p4118 p4438 p4521 : Prop) (h : (¬ p4438) ∨ (¬ p3172) ∨ (¬ p2245) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p2528) ∨ (¬ p2274) ∨ (¬ p4521) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4438) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial11647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory3143 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11647 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2245) (meaning t m 2274) (meaning t m 2528) (meaning t m 3172) (meaning t m 4118) (meaning t m 4438) (meaning t m 4521) source

theorem rule11648 (p2027 p2156 p2177 p2274 p2608 p3370 p3817 p4366 p4377 p4666 : Prop) (h : (¬ p3817) ∨ (¬ p3370) ∨ (¬ p4366) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2608) ∨ (¬ p3370) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4377) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory3144 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11648 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2608) (meaning t m 3370) (meaning t m 3817) (meaning t m 4366) (meaning t m 4377) (meaning t m 4666) source

theorem rule11650 (p2027 p2132 p3105 p3414 p3553 p3680 p4789 p5123 p5558 : Prop) (h : (¬ p4789) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p5558) ∨ (¬ p5123) ∨ (¬ p3414) ∨ (¬ p3680) ∨ (¬ p3105) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3105) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3680) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial11650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory3146 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11650 (meaning t m 2027) (meaning t m 2132) (meaning t m 3105) (meaning t m 3414) (meaning t m 3553) (meaning t m 3680) (meaning t m 4789) (meaning t m 5123) (meaning t m 5558) source

theorem rule11651 (p2027 p2252 p2534 p2657 p2750 p3051 p3105 p3370 p3371 p4244 p4256 p4450 : Prop) (h : (¬ p3371) ∨ (¬ p3370) ∨ (¬ p4256) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p2534) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3051) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial11651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory3147 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule11651 (meaning t m 2027) (meaning t m 2252) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 3051) (meaning t m 3105) (meaning t m 3370) (meaning t m 3371) (meaning t m 4244) (meaning t m 4256) (meaning t m 4450) source

theorem rule11653 (p2027 p2761 p3051 p3246 p3365 p3366 p3370 p4195 p4377 p5254 p5717 : Prop) (h : p2027 ∨ (¬ p5254) ∨ (¬ p5717) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p2761) ∨ (¬ p3370) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial11653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory3149 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule11653 (meaning t m 2027) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 4195) (meaning t m 4377) (meaning t m 5254) (meaning t m 5717) source

theorem rule11654 (p2027 p2470 p2509 p3555 p4079 p4257 p4377 : Prop) (h : (¬ p4079) ∨ (¬ p2470) ∨ (¬ p3555) ∨ (¬ p2509) ∨ (¬ p4257) ∨ p2027 ∨ (¬ p4377)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p3555) ∨ (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial11654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory3150 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8)
  exact rule11654 (meaning t m 2027) (meaning t m 2470) (meaning t m 2509) (meaning t m 3555) (meaning t m 4079) (meaning t m 4257) (meaning t m 4377) source

theorem rule11656 (p2027 p2241 p2707 p2750 p3425 p3873 : Prop) (h : (¬ p2750) ∨ (¬ p3873) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2707) ∨ (¬ p2750) ∨ (¬ p3425) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial11656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory3152 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7)
  exact rule11656 (meaning t m 2027) (meaning t m 2241) (meaning t m 2707) (meaning t m 2750) (meaning t m 3425) (meaning t m 3873) source

theorem rule11657 (p2027 p2383 p3923 p3954 p4870 p5020 : Prop) (h : p2027 ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p2383) ∨ (¬ p4870) ∨ (¬ p5020)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4870) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial11657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory3153 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 8)
  exact rule11657 (meaning t m 2027) (meaning t m 2383) (meaning t m 3923) (meaning t m 3954) (meaning t m 4870) (meaning t m 5020) source

theorem rule11658 (p2027 p2510 p2588 p4149 p4405 p5580 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p4149) ∨ (¬ p5580) ∨ (¬ p2510)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2588) ∨ (¬ p4149) ∨ (¬ p4405) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial11658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory3154 t (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule11658 (meaning t m 2027) (meaning t m 2510) (meaning t m 2588) (meaning t m 4149) (meaning t m 4405) (meaning t m 5580) source

theorem rule11660 (p2027 p2241 p2717 p2750 p2753 p3471 p3860 p3941 p4261 p5122 : Prop) (h : (¬ p3860) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p3471) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p4261) ∨ (¬ p3941) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial11660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory3156 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule11660 (meaning t m 2027) (meaning t m 2241) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3860) (meaning t m 3941) (meaning t m 4261) (meaning t m 5122) source

theorem rule11662 (p2027 p2177 p2241 p2553 p2573 p2750 p2753 p3362 p3817 p4366 p4666 : Prop) (h : (¬ p2241) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p2753) ∨ (¬ p2573) ∨ (¬ p2553) ∨ (¬ p3817) ∨ (¬ p4666) ∨ (¬ p4366) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3362) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory3158 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11662 (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2553) (meaning t m 2573) (meaning t m 2750) (meaning t m 2753) (meaning t m 3362) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) source

theorem rule11663 (p2027 p2573 p3365 p3366 p3461 p3519 p3564 p3877 p4376 p5123 p5600 : Prop) (h : (¬ p4376) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p2573) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p5600) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3461) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p3877) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial11663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory3159 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11663 (meaning t m 2027) (meaning t m 2573) (meaning t m 3365) (meaning t m 3366) (meaning t m 3461) (meaning t m 3519) (meaning t m 3564) (meaning t m 3877) (meaning t m 4376) (meaning t m 5123) (meaning t m 5600) source

theorem rule11664 (p2027 p2230 p2982 p3365 p3366 p3519 p3680 p3877 p4376 p5123 p5600 : Prop) (h : (¬ p3680) ∨ (¬ p2982) ∨ (¬ p5123) ∨ (¬ p3366) ∨ (¬ p5600) ∨ (¬ p3365) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2230) ∨ (¬ p3877) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p3877) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial11664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory3160 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11664 (meaning t m 2027) (meaning t m 2230) (meaning t m 2982) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3680) (meaning t m 3877) (meaning t m 4376) (meaning t m 5123) (meaning t m 5600) source

theorem rule11665 (p2027 p2383 p3452 p3923 p3953 p4376 p5020 : Prop) (h : p2027 ∨ (¬ p4376) ∨ (¬ p3452) ∨ (¬ p2383) ∨ (¬ p3953) ∨ (¬ p3923) ∨ (¬ p5020)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3452) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4376) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial11665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory3161 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 6 8)
  exact rule11665 (meaning t m 2027) (meaning t m 2383) (meaning t m 3452) (meaning t m 3923) (meaning t m 3953) (meaning t m 4376) (meaning t m 5020) source

theorem rule11666 (p2027 p2780 p3366 p3452 p3707 p3830 p4358 p4376 p5123 p5580 : Prop) (h : p2027 ∨ (¬ p4358) ∨ (¬ p3452) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4376) ∨ (¬ p5580) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4358) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial11666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory3162 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11666 (meaning t m 2027) (meaning t m 2780) (meaning t m 3366) (meaning t m 3452) (meaning t m 3707) (meaning t m 3830) (meaning t m 4358) (meaning t m 4376) (meaning t m 5123) (meaning t m 5580) source

theorem rule11667 (p2027 p2230 p2427 p3246 p3292 p3670 p4236 p4419 p5236 p5284 : Prop) (h : (¬ p5236) ∨ (¬ p4236) ∨ (¬ p3246) ∨ (¬ p5284) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4419) ∨ (¬ p3670) ∨ p2027 ∨ (¬ p3292)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p3670) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p5236) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5236)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory3163 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 9) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule11667 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 3246) (meaning t m 3292) (meaning t m 3670) (meaning t m 4236) (meaning t m 4419) (meaning t m 5236) (meaning t m 5284) source

theorem rule11668 (p2027 p2230 p2427 p3005 p3172 p3246 p4035 p4236 p4419 p4663 : Prop) (h : (¬ p4236) ∨ (¬ p4663) ∨ (¬ p3246) ∨ (¬ p3172) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4419) ∨ p2027 ∨ (¬ p4035) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3246) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4663) := by
  classical
  tauto

theorem initial11668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4663)) := by
  have source := ElevenTheory.theory3164 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule11668 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 3005) (meaning t m 3172) (meaning t m 3246) (meaning t m 4035) (meaning t m 4236) (meaning t m 4419) (meaning t m 4663) source

theorem rule11669 (p2027 p2230 p2427 p2881 p3365 p3572 p3947 p4419 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p4419) ∨ (¬ p3947) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4419) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory3165 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11669 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2881) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4419) (meaning t m 4666) source

theorem rule11670 (p2027 p2230 p2427 p2963 p3246 p3366 p3519 p3950 p4236 p4328 p4347 p4358 p4376 : Prop) (h : (¬ p3519) ∨ (¬ p4236) ∨ (¬ p2427) ∨ (¬ p4376) ∨ (¬ p4328) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3950) ∨ (¬ p2963) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4328) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory3166 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule11670 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2963) (meaning t m 3246) (meaning t m 3366) (meaning t m 3519) (meaning t m 3950) (meaning t m 4236) (meaning t m 4328) (meaning t m 4347) (meaning t m 4358) (meaning t m 4376) source

theorem rule11671 (p2027 p2780 p2911 p2933 p3366 p3399 p3452 p3822 p4107 p4376 p4666 : Prop) (h : p2027 ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4666) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p4376) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p2933) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4376) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory3167 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11671 (meaning t m 2027) (meaning t m 2780) (meaning t m 2911) (meaning t m 2933) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3822) (meaning t m 4107) (meaning t m 4376) (meaning t m 4666) source

theorem rule11675 (p2027 p3201 p3584 p4137 p4620 p4710 : Prop) (h : (¬ p3584) ∨ (¬ p4710) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p4137)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial11675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory3171 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule11675 (meaning t m 2027) (meaning t m 3201) (meaning t m 3584) (meaning t m 4137) (meaning t m 4620) (meaning t m 4710) source

theorem rule11676 (p2027 p2132 p2860 p3172 p3737 p4118 p4444 p4789 p5250 : Prop) (h : (¬ p4444) ∨ (¬ p5250) ∨ (¬ p4789) ∨ (¬ p2132) ∨ (¬ p4118) ∨ (¬ p2860) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p3737)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3172) ∨ (¬ p3737) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial11676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory3172 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule11676 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3172) (meaning t m 3737) (meaning t m 4118) (meaning t m 4444) (meaning t m 4789) (meaning t m 5250) source

theorem rule11677 (p2027 p3201 p3569 p3584 p4140 p5472 p5514 : Prop) (h : (¬ p4140) ∨ (¬ p3584) ∨ (¬ p3569) ∨ (¬ p3201) ∨ (¬ p5472) ∨ p2027 ∨ (¬ p5514)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3569) ∨ (¬ p3584) ∨ (¬ p4140) ∨ (¬ p5472) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial11677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 5472)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory3173 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 10) (m.theta 6 7)
  exact rule11677 (meaning t m 2027) (meaning t m 3201) (meaning t m 3569) (meaning t m 3584) (meaning t m 4140) (meaning t m 5472) (meaning t m 5514) source

theorem rule11678 (p2027 p2132 p2241 p2750 p2753 p2860 p3125 p3860 p4261 p4330 : Prop) (h : (¬ p2132) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p2753) ∨ (¬ p4330) ∨ (¬ p3125) ∨ (¬ p4261) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial11678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory3174 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule11678 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2860) (meaning t m 3125) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) source

theorem rule11680 (p2027 p2449 p3034 p3399 p3834 p5358 : Prop) (h : (¬ p2449) ∨ (¬ p3034) ∨ p2027 ∨ (¬ p3834) ∨ (¬ p3399) ∨ (¬ p5358)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3034) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial11680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3034)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory3176 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 3 7) (m.theta 7 9)
  exact rule11680 (meaning t m 2027) (meaning t m 2449) (meaning t m 3034) (meaning t m 3399) (meaning t m 3834) (meaning t m 5358) source

theorem rule11681 (p2027 p2598 p3266 p3292 p3422 p3564 p4330 p4789 p5284 : Prop) (h : (¬ p3292) ∨ (¬ p4330) ∨ (¬ p3564) ∨ (¬ p3422) ∨ (¬ p3266) ∨ (¬ p5284) ∨ (¬ p4789) ∨ (¬ p2598) ∨ p2027) : (p2027) ∨ (¬ p2598) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory3177 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule11681 (meaning t m 2027) (meaning t m 2598) (meaning t m 3266) (meaning t m 3292) (meaning t m 3422) (meaning t m 3564) (meaning t m 4330) (meaning t m 4789) (meaning t m 5284) source

theorem rule11682 (p2027 p2253 p2750 p2807 p2996 p3954 : Prop) (h : (¬ p3954) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial11682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory3178 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 7)
  exact rule11682 (meaning t m 2027) (meaning t m 2253) (meaning t m 2750) (meaning t m 2807) (meaning t m 2996) (meaning t m 3954) source

theorem rule11683 (p2027 p2241 p3027 p3452 p4116 p4652 : Prop) (h : (¬ p4116) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p4652)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory3179 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7)
  exact rule11683 (meaning t m 2027) (meaning t m 2241) (meaning t m 3027) (meaning t m 3452) (meaning t m 4116) (meaning t m 4652) source

theorem rule11684 (p2027 p2241 p2750 p2891 p3369 p3371 p3556 : Prop) (h : (¬ p2241) ∨ (¬ p3556) ∨ (¬ p3369) ∨ (¬ p2891) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3371)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial11684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory3180 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 7)
  exact rule11684 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2891) (meaning t m 3369) (meaning t m 3371) (meaning t m 3556) source

theorem rule11685 (p2027 p2252 p2598 p2750 p2753 p3276 p3333 p3414 p3553 p5123 p5558 : Prop) (h : (¬ p5123) ∨ (¬ p3333) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p3414) ∨ (¬ p2252) ∨ (¬ p3553) ∨ (¬ p2753) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p5558)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial11685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory3181 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11685 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3276) (meaning t m 3333) (meaning t m 3414) (meaning t m 3553) (meaning t m 5123) (meaning t m 5558) source

theorem rule11686 (p2027 p2936 p3201 p3631 p4636 p5160 : Prop) (h : (¬ p2936) ∨ (¬ p3631) ∨ (¬ p3201) ∨ (¬ p5160) ∨ p2027 ∨ (¬ p4636)) : (p2027) ∨ (¬ p2936) ∨ (¬ p3201) ∨ (¬ p3631) ∨ (¬ p4636) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial11686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory3182 t (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule11686 (meaning t m 2027) (meaning t m 2936) (meaning t m 3201) (meaning t m 3631) (meaning t m 4636) (meaning t m 5160) source

theorem rule11688 (p2027 p2241 p2750 p2972 p3369 p3371 p4032 : Prop) (h : p2027 ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p3369) ∨ (¬ p2972) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2972) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial11688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory3184 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 9)
  exact rule11688 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2972) (meaning t m 3369) (meaning t m 3371) (meaning t m 4032) source

theorem rule11689 (p2027 p2252 p2598 p2750 p2753 p2850 p2963 p2982 p3324 p4347 p4450 : Prop) (h : (¬ p4450) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p4347) ∨ (¬ p3324) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p2750) ∨ (¬ p2850) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial11689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory3185 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule11689 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2850) (meaning t m 2963) (meaning t m 2982) (meaning t m 3324) (meaning t m 4347) (meaning t m 4450) source

theorem rule11690 (p2027 p2252 p2598 p2750 p2753 p2963 p3276 p3324 p3333 p5123 p5580 : Prop) (h : (¬ p2750) ∨ (¬ p5580) ∨ (¬ p3324) ∨ (¬ p2963) ∨ (¬ p5123) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p3333) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3324) ∨ (¬ p3333) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial11690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory3186 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11690 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2963) (meaning t m 3276) (meaning t m 3324) (meaning t m 3333) (meaning t m 5123) (meaning t m 5580) source

theorem rule11692 (p2027 p2352 p4009 p4774 p5514 p5579 : Prop) (h : (¬ p4774) ∨ (¬ p2352) ∨ (¬ p4009) ∨ p2027 ∨ (¬ p5514) ∨ (¬ p5579)) : (p2027) ∨ (¬ p2352) ∨ (¬ p4009) ∨ (¬ p4774) ∨ (¬ p5514) ∨ (¬ p5579) := by
  classical
  tauto

theorem initial11692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4774)) ∨ (¬ (meaning t m 5514)) ∨ (¬ (meaning t m 5579)) := by
  have source := ElevenTheory.theory3188 t (m.theta 3 8) (m.theta 4 6) (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule11692 (meaning t m 2027) (meaning t m 2352) (meaning t m 4009) (meaning t m 4774) (meaning t m 5514) (meaning t m 5579) source

theorem rule11693 (p2027 p2573 p3486 p3555 p3570 p3584 p3641 p4420 p5190 : Prop) (h : (¬ p3570) ∨ (¬ p4420) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3584) ∨ (¬ p3555) ∨ (¬ p5190) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4420) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory3189 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule11693 (meaning t m 2027) (meaning t m 2573) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 3584) (meaning t m 3641) (meaning t m 4420) (meaning t m 5190) source

theorem rule11694 (p2027 p2481 p2936 p3201 p3527 p3874 p3960 : Prop) (h : (¬ p2936) ∨ (¬ p3960) ∨ (¬ p2481) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2481) ∨ (¬ p2936) ∨ (¬ p3201) ∨ (¬ p3527) ∨ (¬ p3874) ∨ (¬ p3960) := by
  classical
  tauto

theorem initial11694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3960)) := by
  have source := ElevenTheory.theory3190 t (m.theta 0 8) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule11694 (meaning t m 2027) (meaning t m 2481) (meaning t m 2936) (meaning t m 3201) (meaning t m 3527) (meaning t m 3874) (meaning t m 3960) source

theorem rule11695 (p2027 p2657 p2946 p4241 p4256 p4608 : Prop) (h : (¬ p4241) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4256) ∨ (¬ p4608)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4241) ∨ (¬ p4256) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial11695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory3191 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8)
  exact rule11695 (meaning t m 2027) (meaning t m 2657) (meaning t m 2946) (meaning t m 4241) (meaning t m 4256) (meaning t m 4608) source

theorem rule11698 (p2027 p2220 p3684 p3880 p4399 p4730 : Prop) (h : (¬ p2220) ∨ (¬ p4399) ∨ (¬ p3880) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p4730)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial11698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory3194 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8)
  exact rule11698 (meaning t m 2027) (meaning t m 2220) (meaning t m 3684) (meaning t m 3880) (meaning t m 4399) (meaning t m 4730) source

theorem rule11699 (p2027 p3286 p3414 p3690 p4362 p5233 p5454 : Prop) (h : (¬ p5233) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p5454) ∨ (¬ p3286) ∨ p2027 ∨ (¬ p4362)) : (p2027) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4362) ∨ (¬ p5233) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial11699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 5233)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory3195 t (m.theta 0 3) (m.theta 2 9) (m.theta 3 7) (m.theta 3 9) (m.theta 5 7) (m.theta 7 9)
  exact rule11699 (meaning t m 2027) (meaning t m 3286) (meaning t m 3414) (meaning t m 3690) (meaning t m 4362) (meaning t m 5233) (meaning t m 5454) source

theorem rule11702 (p2027 p2192 p3246 p3554 p3817 p4555 : Prop) (h : (¬ p2192) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3246) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory3198 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule11702 (meaning t m 2027) (meaning t m 2192) (meaning t m 3246) (meaning t m 3554) (meaning t m 3817) (meaning t m 4555) source

theorem rule11703 (p2027 p2210 p2901 p4366 p4909 p4957 : Prop) (h : p2027 ∨ (¬ p4909) ∨ (¬ p2210) ∨ (¬ p4366) ∨ (¬ p4957) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2901) ∨ (¬ p4366) ∨ (¬ p4909) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial11703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4909)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory3199 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7)
  exact rule11703 (meaning t m 2027) (meaning t m 2210) (meaning t m 2901) (meaning t m 4366) (meaning t m 4909) (meaning t m 4957) source

theorem rule11705 (p2027 p2210 p3115 p3834 p4388 p4957 : Prop) (h : (¬ p3115) ∨ (¬ p2210) ∨ (¬ p4388) ∨ (¬ p4957) ∨ (¬ p3834) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p3115) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial11705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4388)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory3201 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 3 5) (m.theta 5 9)
  exact rule11705 (meaning t m 2027) (meaning t m 2210) (meaning t m 3115) (meaning t m 3834) (meaning t m 4388) (meaning t m 4957) source

theorem rule11707 (p2027 p2963 p3324 p3333 p3362 p3389 p3876 p4332 p4347 p4789 : Prop) (h : (¬ p3324) ∨ (¬ p3389) ∨ (¬ p3333) ∨ (¬ p4789) ∨ (¬ p4332) ∨ (¬ p2963) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial11707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory3203 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule11707 (meaning t m 2027) (meaning t m 2963) (meaning t m 3324) (meaning t m 3333) (meaning t m 3362) (meaning t m 3389) (meaning t m 3876) (meaning t m 4332) (meaning t m 4347) (meaning t m 4789) source

theorem rule11708 (p2584 p4079 p5020 : Prop) (h : p5020 ∨ (¬ p2584) ∨ (¬ p4079)) : (¬ p2584) ∨ (¬ p4079) ∨ (p5020) := by
  classical
  tauto

theorem initial11708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 4079)) ∨ (meaning t m 5020) := by
  have source := ElevenTheory.theory3204 (m.theta 0 1) (m.theta 0 4) (m.theta 0 6)
  exact rule11708 (meaning t m 2584) (meaning t m 4079) (meaning t m 5020) source

theorem rule11709 (p2027 p2132 p2619 p2657 p3146 p3574 p4137 p4604 p4789 : Prop) (h : (¬ p4604) ∨ (¬ p4137) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p4789) ∨ (¬ p3146) ∨ (¬ p2657) ∨ (¬ p2619) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial11709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory3205 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule11709 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2657) (meaning t m 3146) (meaning t m 3574) (meaning t m 4137) (meaning t m 4604) (meaning t m 4789) source

theorem rule11710 (p2027 p2901 p3497 p4129 p4132 p5564 : Prop) (h : (¬ p3497) ∨ (¬ p2901) ∨ (¬ p5564) ∨ (¬ p4129) ∨ p2027 ∨ (¬ p4132)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p4129) ∨ (¬ p4132) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory3206 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8)
  exact rule11710 (meaning t m 2027) (meaning t m 2901) (meaning t m 3497) (meaning t m 4129) (meaning t m 4132) (meaning t m 5564) source

theorem rule11711 (p2027 p3146 p3438 p3449 p3834 p4494 : Prop) (h : (¬ p3449) ∨ (¬ p3146) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p3438) ∨ (¬ p4494)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4494) := by
  classical
  tauto

theorem initial11711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4494)) := by
  have source := ElevenTheory.theory3207 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 5 8) (m.theta 8 9)
  exact rule11711 (meaning t m 2027) (meaning t m 3146) (meaning t m 3438) (meaning t m 3449) (meaning t m 3834) (meaning t m 4494) source

theorem rule11712 (p2027 p2936 p3830 p4278 p4366 p5362 : Prop) (h : (¬ p2936) ∨ (¬ p3830) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p5362) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2936) ∨ (¬ p3830) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial11712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory3208 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 4 7) (m.theta 7 9)
  exact rule11712 (meaning t m 2027) (meaning t m 2936) (meaning t m 3830) (meaning t m 4278) (meaning t m 4366) (meaning t m 5362) source

theorem rule11713 (p3857 p4455 p4456 p4457 p4458 : Prop) : (p3857) ∨ (((¬ p3857) ∨ (¬ p4456) ∨ (¬ p4455) ∨ (¬ p4458) ∨ (¬ p4457))) := by
  classical
  tauto

theorem initial11713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3857) ∨ (meaning t m 5785) := by
  exact rule11713 (meaning t m 3857) (meaning t m 4455) (meaning t m 4456) (meaning t m 4457) (meaning t m 4458)

theorem rule11714 (p3857 p4455 p4456 p4457 p4458 : Prop) : (p4456) ∨ (((¬ p3857) ∨ (¬ p4456) ∨ (¬ p4455) ∨ (¬ p4458) ∨ (¬ p4457))) := by
  classical
  tauto

theorem initial11714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4456) ∨ (meaning t m 5785) := by
  exact rule11714 (meaning t m 3857) (meaning t m 4455) (meaning t m 4456) (meaning t m 4457) (meaning t m 4458)

theorem rule11715 (p3857 p4455 p4456 p4457 p4458 : Prop) : (p4455) ∨ (((¬ p3857) ∨ (¬ p4456) ∨ (¬ p4455) ∨ (¬ p4458) ∨ (¬ p4457))) := by
  classical
  tauto

theorem initial11715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4455) ∨ (meaning t m 5785) := by
  exact rule11715 (meaning t m 3857) (meaning t m 4455) (meaning t m 4456) (meaning t m 4457) (meaning t m 4458)

theorem rule11719 (p2088 p4460 p4461 p4462 p4463 : Prop) : (p2088) ∨ (((¬ p2088) ∨ (¬ p4461) ∨ (¬ p4462) ∨ (¬ p4463) ∨ (¬ p4460))) := by
  classical
  tauto

theorem initial11719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2088) ∨ (meaning t m 5786) := by
  exact rule11719 (meaning t m 2088) (meaning t m 4460) (meaning t m 4461) (meaning t m 4462) (meaning t m 4463)

theorem rule11720 (p2088 p4460 p4461 p4462 p4463 : Prop) : (p4461) ∨ (((¬ p2088) ∨ (¬ p4461) ∨ (¬ p4462) ∨ (¬ p4463) ∨ (¬ p4460))) := by
  classical
  tauto

theorem initial11720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4461) ∨ (meaning t m 5786) := by
  exact rule11720 (meaning t m 2088) (meaning t m 4460) (meaning t m 4461) (meaning t m 4462) (meaning t m 4463)

theorem rule11723 (p2088 p4460 p4461 p4462 p4463 : Prop) : (p4460) ∨ (((¬ p2088) ∨ (¬ p4461) ∨ (¬ p4462) ∨ (¬ p4463) ∨ (¬ p4460))) := by
  classical
  tauto

theorem initial11723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4460) ∨ (meaning t m 5786) := by
  exact rule11723 (meaning t m 2088) (meaning t m 4460) (meaning t m 4461) (meaning t m 4462) (meaning t m 4463)

theorem rule11727 (p5785 p5786 : Prop) : (¬ ((¬ p5785) ∨ (¬ p5786))) ∨ (¬ p5785) ∨ (¬ p5786) := by
  classical
  tauto

theorem initial11727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5784)) ∨ (¬ (meaning t m 5785)) ∨ (¬ (meaning t m 5786)) := by
  exact rule11727 (meaning t m 5785) (meaning t m 5786)

theorem rule11728 (p4453 p5784 : Prop) (h : (p4453 ↔ p5784)) : (¬ p4453) ∨ (p5784) := by
  classical
  tauto

theorem initial11728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4453)) ∨ (meaning t m 5784) := by
  have source := ElevenTheory.theory3209 t (m.theta 0 8) (m.theta 0 9) (m.theta 8 9)
  exact rule11728 (meaning t m 4453) (meaning t m 5784) source

theorem rule11730 (p1975 p2027 p2104 p2114 p2122 p2774 p3537 : Prop) (h : (¬ p1975) ∨ (¬ p2774) ∨ (¬ p2104) ∨ (¬ p3537) ∨ p2027 ∨ p2114 ∨ (¬ p2122)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2104) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3537) := by
  classical
  tauto

theorem initial11730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3537)) := by
  have source := ElevenTheory.theory3210 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 6 7)
  exact rule11730 (meaning t m 1975) (meaning t m 2027) (meaning t m 2104) (meaning t m 2114) (meaning t m 2122) (meaning t m 2774) (meaning t m 3537) source

theorem rule11731 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p4471) ∨ (((¬ p4471) ∨ (¬ p3822) ∨ (¬ p3689) ∨ (¬ p4472) ∨ (¬ p4473))) := by
  classical
  tauto

theorem initial11731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4471) ∨ (meaning t m 5788) := by
  exact rule11731 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule11732 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p3822) ∨ (((¬ p4471) ∨ (¬ p3822) ∨ (¬ p3689) ∨ (¬ p4472) ∨ (¬ p4473))) := by
  classical
  tauto

theorem initial11732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3822) ∨ (meaning t m 5788) := by
  exact rule11732 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule11733 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p3689) ∨ (((¬ p4471) ∨ (¬ p3822) ∨ (¬ p3689) ∨ (¬ p4472) ∨ (¬ p4473))) := by
  classical
  tauto

theorem initial11733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3689) ∨ (meaning t m 5788) := by
  exact rule11733 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule11734 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p4472) ∨ (((¬ p4471) ∨ (¬ p3822) ∨ (¬ p3689) ∨ (¬ p4472) ∨ (¬ p4473))) := by
  classical
  tauto

theorem initial11734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4472) ∨ (meaning t m 5788) := by
  exact rule11734 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule11735 (p3689 p3822 p4471 p4472 p4473 : Prop) : (p4473) ∨ (((¬ p4471) ∨ (¬ p3822) ∨ (¬ p3689) ∨ (¬ p4472) ∨ (¬ p4473))) := by
  classical
  tauto

theorem initial11735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4473) ∨ (meaning t m 5788) := by
  exact rule11735 (meaning t m 3689) (meaning t m 3822) (meaning t m 4471) (meaning t m 4472) (meaning t m 4473)

theorem rule11737 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p4475) ∨ (((¬ p4475) ∨ (¬ p3426) ∨ (¬ p2122) ∨ (¬ p4476) ∨ (¬ p4477))) := by
  classical
  tauto

theorem initial11737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4475) ∨ (meaning t m 5789) := by
  exact rule11737 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule11738 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p3426) ∨ (((¬ p4475) ∨ (¬ p3426) ∨ (¬ p2122) ∨ (¬ p4476) ∨ (¬ p4477))) := by
  classical
  tauto

theorem initial11738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3426) ∨ (meaning t m 5789) := by
  exact rule11738 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule11739 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p2122) ∨ (((¬ p4475) ∨ (¬ p3426) ∨ (¬ p2122) ∨ (¬ p4476) ∨ (¬ p4477))) := by
  classical
  tauto

theorem initial11739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (meaning t m 5789) := by
  exact rule11739 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule11740 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p4476) ∨ (((¬ p4475) ∨ (¬ p3426) ∨ (¬ p2122) ∨ (¬ p4476) ∨ (¬ p4477))) := by
  classical
  tauto

theorem initial11740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4476) ∨ (meaning t m 5789) := by
  exact rule11740 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule11741 (p2122 p3426 p4475 p4476 p4477 : Prop) : (p4477) ∨ (((¬ p4475) ∨ (¬ p3426) ∨ (¬ p2122) ∨ (¬ p4476) ∨ (¬ p4477))) := by
  classical
  tauto

theorem initial11741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4477) ∨ (meaning t m 5789) := by
  exact rule11741 (meaning t m 2122) (meaning t m 3426) (meaning t m 4475) (meaning t m 4476) (meaning t m 4477)

theorem rule11745 (p5788 p5789 : Prop) : (¬ ((¬ p5788) ∨ (¬ p5789))) ∨ (¬ p5788) ∨ (¬ p5789) := by
  classical
  tauto

theorem initial11745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5787)) ∨ (¬ (meaning t m 5788)) ∨ (¬ (meaning t m 5789)) := by
  exact rule11745 (meaning t m 5788) (meaning t m 5789)

theorem rule11746 (p4469 p5787 : Prop) (h : (p4469 ↔ p5787)) : (¬ p4469) ∨ (p5787) := by
  classical
  tauto

theorem initial11746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4469)) ∨ (meaning t m 5787) := by
  have source := ElevenTheory.theory3211 t (m.theta 2 6) (m.theta 2 7) (m.theta 6 7)
  exact rule11746 (meaning t m 4469) (meaning t m 5787) source

theorem rule11748 (p1976 p2138 p2146 p2148 : Prop) (h : (¬ p1976) ∨ p2148 ∨ (¬ p2138) ∨ p2146) : (¬ p1976) ∨ (¬ p2138) ∨ (p2146) ∨ (p2148) := by
  classical
  tauto

theorem initial11748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2146) ∨ (meaning t m 2148) := by
  have source := ElevenTheory.theory3212 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule11748 (meaning t m 1976) (meaning t m 2138) (meaning t m 2146) (meaning t m 2148) source

theorem rule11749 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p4486) ∨ (((¬ p4486) ∨ (¬ p3646) ∨ (¬ p4485) ∨ (¬ p4198) ∨ (¬ p3743))) := by
  classical
  tauto

theorem initial11749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4486) ∨ (meaning t m 5791) := by
  exact rule11749 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule11750 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p3646) ∨ (((¬ p4486) ∨ (¬ p3646) ∨ (¬ p4485) ∨ (¬ p4198) ∨ (¬ p3743))) := by
  classical
  tauto

theorem initial11750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3646) ∨ (meaning t m 5791) := by
  exact rule11750 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule11752 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p4198) ∨ (((¬ p4486) ∨ (¬ p3646) ∨ (¬ p4485) ∨ (¬ p4198) ∨ (¬ p3743))) := by
  classical
  tauto

theorem initial11752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4198) ∨ (meaning t m 5791) := by
  exact rule11752 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule11753 (p3646 p3743 p4198 p4485 p4486 : Prop) : (p3743) ∨ (((¬ p4486) ∨ (¬ p3646) ∨ (¬ p4485) ∨ (¬ p4198) ∨ (¬ p3743))) := by
  classical
  tauto

theorem initial11753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3743) ∨ (meaning t m 5791) := by
  exact rule11753 (meaning t m 3646) (meaning t m 3743) (meaning t m 4198) (meaning t m 4485) (meaning t m 4486)

theorem rule11757 (p2156 p2962 p4356 p4488 p4489 : Prop) : (p2156) ∨ (((¬ p4489) ∨ (¬ p4488) ∨ (¬ p2156) ∨ (¬ p2962) ∨ (¬ p4356))) := by
  classical
  tauto

theorem initial11757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (meaning t m 5792) := by
  exact rule11757 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule11758 (p2156 p2962 p4356 p4488 p4489 : Prop) : (p2962) ∨ (((¬ p4489) ∨ (¬ p4488) ∨ (¬ p2156) ∨ (¬ p2962) ∨ (¬ p4356))) := by
  classical
  tauto

theorem initial11758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2962) ∨ (meaning t m 5792) := by
  exact rule11758 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule11759 (p2156 p2962 p4356 p4488 p4489 : Prop) : (p4356) ∨ (((¬ p4489) ∨ (¬ p4488) ∨ (¬ p2156) ∨ (¬ p2962) ∨ (¬ p4356))) := by
  classical
  tauto

theorem initial11759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4356) ∨ (meaning t m 5792) := by
  exact rule11759 (meaning t m 2156) (meaning t m 2962) (meaning t m 4356) (meaning t m 4488) (meaning t m 4489)

theorem rule11763 (p5791 p5792 : Prop) : (¬ ((¬ p5791) ∨ (¬ p5792))) ∨ (¬ p5791) ∨ (¬ p5792) := by
  classical
  tauto

theorem initial11763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5790)) ∨ (¬ (meaning t m 5791)) ∨ (¬ (meaning t m 5792)) := by
  exact rule11763 (meaning t m 5791) (meaning t m 5792)

theorem rule11764 (p4483 p5790 : Prop) (h : (p4483 ↔ p5790)) : (¬ p4483) ∨ (p5790) := by
  classical
  tauto

theorem initial11764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4483)) ∨ (meaning t m 5790) := by
  have source := ElevenTheory.theory3213 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6)
  exact rule11764 (meaning t m 4483) (meaning t m 5790) source

theorem rule11766 (p2191 p3906 p4492 p4493 p4494 : Prop) : (p3906) ∨ (((¬ p3906) ∨ (¬ p2191) ∨ (¬ p4492) ∨ (¬ p4493) ∨ (¬ p4494))) := by
  classical
  tauto

theorem initial11766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3906) ∨ (meaning t m 5794) := by
  exact rule11766 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule11767 (p2191 p3906 p4492 p4493 p4494 : Prop) : (p2191) ∨ (((¬ p3906) ∨ (¬ p2191) ∨ (¬ p4492) ∨ (¬ p4493) ∨ (¬ p4494))) := by
  classical
  tauto

theorem initial11767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2191) ∨ (meaning t m 5794) := by
  exact rule11767 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule11768 (p2191 p3906 p4492 p4493 p4494 : Prop) : (p4492) ∨ (((¬ p3906) ∨ (¬ p2191) ∨ (¬ p4492) ∨ (¬ p4493) ∨ (¬ p4494))) := by
  classical
  tauto

theorem initial11768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4492) ∨ (meaning t m 5794) := by
  exact rule11768 (meaning t m 2191) (meaning t m 3906) (meaning t m 4492) (meaning t m 4493) (meaning t m 4494)

theorem rule11772 (p2166 p4446 p4496 p4497 p4498 : Prop) : (p4446) ∨ (((¬ p4446) ∨ (¬ p4496) ∨ (¬ p2166) ∨ (¬ p4497) ∨ (¬ p4498))) := by
  classical
  tauto

theorem initial11772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4446) ∨ (meaning t m 5795) := by
  exact rule11772 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule11773 (p2166 p4446 p4496 p4497 p4498 : Prop) : (p4496) ∨ (((¬ p4446) ∨ (¬ p4496) ∨ (¬ p2166) ∨ (¬ p4497) ∨ (¬ p4498))) := by
  classical
  tauto

theorem initial11773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4496) ∨ (meaning t m 5795) := by
  exact rule11773 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule11774 (p2166 p4446 p4496 p4497 p4498 : Prop) : (p2166) ∨ (((¬ p4446) ∨ (¬ p4496) ∨ (¬ p2166) ∨ (¬ p4497) ∨ (¬ p4498))) := by
  classical
  tauto

theorem initial11774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (meaning t m 5795) := by
  exact rule11774 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule11776 (p2166 p4446 p4496 p4497 p4498 : Prop) : (p4498) ∨ (((¬ p4446) ∨ (¬ p4496) ∨ (¬ p2166) ∨ (¬ p4497) ∨ (¬ p4498))) := by
  classical
  tauto

theorem initial11776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4498) ∨ (meaning t m 5795) := by
  exact rule11776 (meaning t m 2166) (meaning t m 4446) (meaning t m 4496) (meaning t m 4497) (meaning t m 4498)

theorem rule11780 (p5794 p5795 : Prop) : (¬ ((¬ p5794) ∨ (¬ p5795))) ∨ (¬ p5794) ∨ (¬ p5795) := by
  classical
  tauto

theorem initial11780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5793)) ∨ (¬ (meaning t m 5794)) ∨ (¬ (meaning t m 5795)) := by
  exact rule11780 (meaning t m 5794) (meaning t m 5795)

theorem rule11781 (p4490 p5793 : Prop) (h : (p4490 ↔ p5793)) : (¬ p4490) ∨ (p5793) := by
  classical
  tauto

theorem initial11781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4490)) ∨ (meaning t m 5793) := by
  have source := ElevenTheory.theory3214 t (m.theta 1 5) (m.theta 1 8) (m.theta 5 8)
  exact rule11781 (meaning t m 4490) (meaning t m 5793) source

theorem rule11783 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p4138) ∨ (((¬ p4138) ∨ (¬ p2299) ∨ (¬ p3955) ∨ (¬ p4501) ∨ (¬ p4133))) := by
  classical
  tauto

theorem initial11783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4138) ∨ (meaning t m 5797) := by
  exact rule11783 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule11784 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p2299) ∨ (((¬ p4138) ∨ (¬ p2299) ∨ (¬ p3955) ∨ (¬ p4501) ∨ (¬ p4133))) := by
  classical
  tauto

theorem initial11784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2299) ∨ (meaning t m 5797) := by
  exact rule11784 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule11785 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p3955) ∨ (((¬ p4138) ∨ (¬ p2299) ∨ (¬ p3955) ∨ (¬ p4501) ∨ (¬ p4133))) := by
  classical
  tauto

theorem initial11785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3955) ∨ (meaning t m 5797) := by
  exact rule11785 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule11786 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p4501) ∨ (((¬ p4138) ∨ (¬ p2299) ∨ (¬ p3955) ∨ (¬ p4501) ∨ (¬ p4133))) := by
  classical
  tauto

theorem initial11786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4501) ∨ (meaning t m 5797) := by
  exact rule11786 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule11787 (p2299 p3955 p4133 p4138 p4501 : Prop) : (p4133) ∨ (((¬ p4138) ∨ (¬ p2299) ∨ (¬ p3955) ∨ (¬ p4501) ∨ (¬ p4133))) := by
  classical
  tauto

theorem initial11787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4133) ∨ (meaning t m 5797) := by
  exact rule11787 (meaning t m 2299) (meaning t m 3955) (meaning t m 4133) (meaning t m 4138) (meaning t m 4501)

theorem rule11789 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p3550) ∨ (((¬ p3550) ∨ (¬ p3325) ∨ (¬ p2177) ∨ (¬ p4405) ∨ (¬ p4503))) := by
  classical
  tauto

theorem initial11789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3550) ∨ (meaning t m 5798) := by
  exact rule11789 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule11790 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p3325) ∨ (((¬ p3550) ∨ (¬ p3325) ∨ (¬ p2177) ∨ (¬ p4405) ∨ (¬ p4503))) := by
  classical
  tauto

theorem initial11790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3325) ∨ (meaning t m 5798) := by
  exact rule11790 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule11791 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p2177) ∨ (((¬ p3550) ∨ (¬ p3325) ∨ (¬ p2177) ∨ (¬ p4405) ∨ (¬ p4503))) := by
  classical
  tauto

theorem initial11791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2177) ∨ (meaning t m 5798) := by
  exact rule11791 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule11793 (p2177 p3325 p3550 p4405 p4503 : Prop) : (p4503) ∨ (((¬ p3550) ∨ (¬ p3325) ∨ (¬ p2177) ∨ (¬ p4405) ∨ (¬ p4503))) := by
  classical
  tauto

theorem initial11793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4503) ∨ (meaning t m 5798) := by
  exact rule11793 (meaning t m 2177) (meaning t m 3325) (meaning t m 3550) (meaning t m 4405) (meaning t m 4503)

theorem rule11797 (p5797 p5798 : Prop) : (¬ ((¬ p5797) ∨ (¬ p5798))) ∨ (¬ p5797) ∨ (¬ p5798) := by
  classical
  tauto

theorem initial11797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5796)) ∨ (¬ (meaning t m 5797)) ∨ (¬ (meaning t m 5798)) := by
  exact rule11797 (meaning t m 5797) (meaning t m 5798)

theorem rule11798 (p4499 p5796 : Prop) (h : (p4499 ↔ p5796)) : (¬ p4499) ∨ (p5796) := by
  classical
  tauto

theorem initial11798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4499)) ∨ (meaning t m 5796) := by
  have source := ElevenTheory.theory3215 t (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule11798 (meaning t m 4499) (meaning t m 5796) source

theorem rule11800 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p4506) ∨ (((¬ p4506) ∨ (¬ p3989) ∨ (¬ p3988) ∨ (¬ p4507) ∨ (¬ p4433))) := by
  classical
  tauto

theorem initial11800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4506) ∨ (meaning t m 5800) := by
  exact rule11800 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule11801 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p3989) ∨ (((¬ p4506) ∨ (¬ p3989) ∨ (¬ p3988) ∨ (¬ p4507) ∨ (¬ p4433))) := by
  classical
  tauto

theorem initial11801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3989) ∨ (meaning t m 5800) := by
  exact rule11801 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule11802 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p3988) ∨ (((¬ p4506) ∨ (¬ p3989) ∨ (¬ p3988) ∨ (¬ p4507) ∨ (¬ p4433))) := by
  classical
  tauto

theorem initial11802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3988) ∨ (meaning t m 5800) := by
  exact rule11802 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule11803 (p3988 p3989 p4433 p4506 p4507 : Prop) : (p4507) ∨ (((¬ p4506) ∨ (¬ p3989) ∨ (¬ p3988) ∨ (¬ p4507) ∨ (¬ p4433))) := by
  classical
  tauto

theorem initial11803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4507) ∨ (meaning t m 5800) := by
  exact rule11803 (meaning t m 3988) (meaning t m 3989) (meaning t m 4433) (meaning t m 4506) (meaning t m 4507)

theorem rule11806 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p4441) ∨ (((¬ p4441) ∨ (¬ p2190) ∨ (¬ p2187) ∨ (¬ p4509) ∨ (¬ p4134))) := by
  classical
  tauto

theorem initial11806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4441) ∨ (meaning t m 5801) := by
  exact rule11806 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule11807 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p2190) ∨ (((¬ p4441) ∨ (¬ p2190) ∨ (¬ p2187) ∨ (¬ p4509) ∨ (¬ p4134))) := by
  classical
  tauto

theorem initial11807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2190) ∨ (meaning t m 5801) := by
  exact rule11807 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule11808 (p2187 p2190 p4134 p4441 p4509 : Prop) : (p2187) ∨ (((¬ p4441) ∨ (¬ p2190) ∨ (¬ p2187) ∨ (¬ p4509) ∨ (¬ p4134))) := by
  classical
  tauto

theorem initial11808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (meaning t m 5801) := by
  exact rule11808 (meaning t m 2187) (meaning t m 2190) (meaning t m 4134) (meaning t m 4441) (meaning t m 4509)

theorem rule11814 (p5800 p5801 : Prop) : (¬ ((¬ p5800) ∨ (¬ p5801))) ∨ (¬ p5800) ∨ (¬ p5801) := by
  classical
  tauto

theorem initial11814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5799)) ∨ (¬ (meaning t m 5800)) ∨ (¬ (meaning t m 5801)) := by
  exact rule11814 (meaning t m 5800) (meaning t m 5801)

theorem rule11815 (p4504 p5799 : Prop) (h : (p4504 ↔ p5799)) : (¬ p4504) ∨ (p5799) := by
  classical
  tauto

theorem initial11815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4504)) ∨ (meaning t m 5799) := by
  have source := ElevenTheory.theory3216 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule11815 (meaning t m 4504) (meaning t m 5799) source

theorem rule11817 (p3957 p4173 p4512 p4513 p4514 : Prop) : (p4512) ∨ (((¬ p4512) ∨ (¬ p3957) ∨ (¬ p4173) ∨ (¬ p4513) ∨ (¬ p4514))) := by
  classical
  tauto

theorem initial11817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4512) ∨ (meaning t m 5803) := by
  exact rule11817 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule11818 (p3957 p4173 p4512 p4513 p4514 : Prop) : (p3957) ∨ (((¬ p4512) ∨ (¬ p3957) ∨ (¬ p4173) ∨ (¬ p4513) ∨ (¬ p4514))) := by
  classical
  tauto

theorem initial11818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3957) ∨ (meaning t m 5803) := by
  exact rule11818 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule11819 (p3957 p4173 p4512 p4513 p4514 : Prop) : (p4173) ∨ (((¬ p4512) ∨ (¬ p3957) ∨ (¬ p4173) ∨ (¬ p4513) ∨ (¬ p4514))) := by
  classical
  tauto

theorem initial11819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4173) ∨ (meaning t m 5803) := by
  exact rule11819 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule11821 (p3957 p4173 p4512 p4513 p4514 : Prop) : (p4514) ∨ (((¬ p4512) ∨ (¬ p3957) ∨ (¬ p4173) ∨ (¬ p4513) ∨ (¬ p4514))) := by
  classical
  tauto

theorem initial11821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4514) ∨ (meaning t m 5803) := by
  exact rule11821 (meaning t m 3957) (meaning t m 4173) (meaning t m 4512) (meaning t m 4513) (meaning t m 4514)

theorem rule11823 (p2192 p4338 p4516 p4517 p4518 : Prop) : (p4516) ∨ (((¬ p4516) ∨ (¬ p4338) ∨ (¬ p2192) ∨ (¬ p4517) ∨ (¬ p4518))) := by
  classical
  tauto

theorem initial11823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4516) ∨ (meaning t m 5804) := by
  exact rule11823 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule11824 (p2192 p4338 p4516 p4517 p4518 : Prop) : (p4338) ∨ (((¬ p4516) ∨ (¬ p4338) ∨ (¬ p2192) ∨ (¬ p4517) ∨ (¬ p4518))) := by
  classical
  tauto

theorem initial11824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4338) ∨ (meaning t m 5804) := by
  exact rule11824 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule11825 (p2192 p4338 p4516 p4517 p4518 : Prop) : (p2192) ∨ (((¬ p4516) ∨ (¬ p4338) ∨ (¬ p2192) ∨ (¬ p4517) ∨ (¬ p4518))) := by
  classical
  tauto

theorem initial11825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2192) ∨ (meaning t m 5804) := by
  exact rule11825 (meaning t m 2192) (meaning t m 4338) (meaning t m 4516) (meaning t m 4517) (meaning t m 4518)

theorem rule11831 (p5803 p5804 : Prop) : (¬ ((¬ p5803) ∨ (¬ p5804))) ∨ (¬ p5803) ∨ (¬ p5804) := by
  classical
  tauto

theorem initial11831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5802)) ∨ (¬ (meaning t m 5803)) ∨ (¬ (meaning t m 5804)) := by
  exact rule11831 (meaning t m 5803) (meaning t m 5804)

theorem rule11832 (p4510 p5802 : Prop) (h : (p4510 ↔ p5802)) : (¬ p4510) ∨ (p5802) := by
  classical
  tauto

theorem initial11832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4510)) ∨ (meaning t m 5802) := by
  have source := ElevenTheory.theory3217 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6)
  exact rule11832 (meaning t m 4510) (meaning t m 5802) source

theorem rule11834 (p1977 p2027 p2202 p2241 p2563 p3555 p4173 : Prop) (h : (¬ p2241) ∨ p2202 ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2563) ∨ (¬ p3555) ∨ (¬ p4173)) : (¬ p1977) ∨ (p2027) ∨ (p2202) ∨ (¬ p2241) ∨ (¬ p2563) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial11834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory3218 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule11834 (meaning t m 1977) (meaning t m 2027) (meaning t m 2202) (meaning t m 2241) (meaning t m 2563) (meaning t m 3555) (meaning t m 4173) source

theorem rule11835 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p3369) ∨ (((¬ p3369) ∨ (¬ p3370) ∨ (¬ p3555) ∨ (¬ p4521) ∨ (¬ p4522))) := by
  classical
  tauto

theorem initial11835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3369) ∨ (meaning t m 5806) := by
  exact rule11835 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule11836 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p3370) ∨ (((¬ p3369) ∨ (¬ p3370) ∨ (¬ p3555) ∨ (¬ p4521) ∨ (¬ p4522))) := by
  classical
  tauto

theorem initial11836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3370) ∨ (meaning t m 5806) := by
  exact rule11836 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule11837 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p3555) ∨ (((¬ p3369) ∨ (¬ p3370) ∨ (¬ p3555) ∨ (¬ p4521) ∨ (¬ p4522))) := by
  classical
  tauto

theorem initial11837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3555) ∨ (meaning t m 5806) := by
  exact rule11837 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule11838 (p3369 p3370 p3555 p4521 p4522 : Prop) : (p4521) ∨ (((¬ p3369) ∨ (¬ p3370) ∨ (¬ p3555) ∨ (¬ p4521) ∨ (¬ p4522))) := by
  classical
  tauto

theorem initial11838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4521) ∨ (meaning t m 5806) := by
  exact rule11838 (meaning t m 3369) (meaning t m 3370) (meaning t m 3555) (meaning t m 4521) (meaning t m 4522)

theorem rule11841 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p2210) ∨ (((¬ p2210) ∨ (¬ p4524) ∨ (¬ p3645) ∨ (¬ p4172) ∨ (¬ p4525))) := by
  classical
  tauto

theorem initial11841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2210) ∨ (meaning t m 5807) := by
  exact rule11841 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule11843 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p3645) ∨ (((¬ p2210) ∨ (¬ p4524) ∨ (¬ p3645) ∨ (¬ p4172) ∨ (¬ p4525))) := by
  classical
  tauto

theorem initial11843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3645) ∨ (meaning t m 5807) := by
  exact rule11843 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule11844 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p4172) ∨ (((¬ p2210) ∨ (¬ p4524) ∨ (¬ p3645) ∨ (¬ p4172) ∨ (¬ p4525))) := by
  classical
  tauto

theorem initial11844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4172) ∨ (meaning t m 5807) := by
  exact rule11844 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule11845 (p2210 p3645 p4172 p4524 p4525 : Prop) : (p4525) ∨ (((¬ p2210) ∨ (¬ p4524) ∨ (¬ p3645) ∨ (¬ p4172) ∨ (¬ p4525))) := by
  classical
  tauto

theorem initial11845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4525) ∨ (meaning t m 5807) := by
  exact rule11845 (meaning t m 2210) (meaning t m 3645) (meaning t m 4172) (meaning t m 4524) (meaning t m 4525)

theorem rule11849 (p5806 p5807 : Prop) : (¬ ((¬ p5806) ∨ (¬ p5807))) ∨ (¬ p5806) ∨ (¬ p5807) := by
  classical
  tauto

theorem initial11849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5805)) ∨ (¬ (meaning t m 5806)) ∨ (¬ (meaning t m 5807)) := by
  exact rule11849 (meaning t m 5806) (meaning t m 5807)

theorem rule11850 (p4519 p5805 : Prop) (h : (p4519 ↔ p5805)) : (¬ p4519) ∨ (p5805) := by
  classical
  tauto

theorem initial11850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4519)) ∨ (meaning t m 5805) := by
  have source := ElevenTheory.theory3219 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5)
  exact rule11850 (meaning t m 4519) (meaning t m 5805) source

theorem rule11852 (p2166 p3645 p3696 p3697 : Prop) (h : (¬ p3645) ∨ (¬ p3697) ∨ (¬ p2166) ∨ (¬ p3696)) : (¬ p2166) ∨ (¬ p3645) ∨ (¬ p3696) ∨ (¬ p3697) := by
  classical
  tauto

theorem initial11852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3697)) := by
  have source := ElevenTheory.theory3220 (m.theta 0 5) (m.theta 0 8) (m.theta 1 5) (m.theta 5 8)
  exact rule11852 (meaning t m 2166) (meaning t m 3645) (meaning t m 3696) (meaning t m 3697) source

theorem rule11853 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p3697) ∨ (((¬ p3697) ∨ (¬ p3696) ∨ (¬ p4120) ∨ (¬ p4529) ∨ (¬ p4528))) := by
  classical
  tauto

theorem initial11853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3697) ∨ (meaning t m 5809) := by
  exact rule11853 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule11854 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p3696) ∨ (((¬ p3697) ∨ (¬ p3696) ∨ (¬ p4120) ∨ (¬ p4529) ∨ (¬ p4528))) := by
  classical
  tauto

theorem initial11854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3696) ∨ (meaning t m 5809) := by
  exact rule11854 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule11855 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p4120) ∨ (((¬ p3697) ∨ (¬ p3696) ∨ (¬ p4120) ∨ (¬ p4529) ∨ (¬ p4528))) := by
  classical
  tauto

theorem initial11855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4120) ∨ (meaning t m 5809) := by
  exact rule11855 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule11856 (p3696 p3697 p4120 p4528 p4529 : Prop) : (p4529) ∨ (((¬ p3697) ∨ (¬ p3696) ∨ (¬ p4120) ∨ (¬ p4529) ∨ (¬ p4528))) := by
  classical
  tauto

theorem initial11856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4529) ∨ (meaning t m 5809) := by
  exact rule11856 (meaning t m 3696) (meaning t m 3697) (meaning t m 4120) (meaning t m 4528) (meaning t m 4529)

theorem rule11861 (p2220 p4115 p4238 p4531 p4532 : Prop) : (p4238) ∨ (((¬ p4531) ∨ (¬ p4532) ∨ (¬ p4238) ∨ (¬ p2220) ∨ (¬ p4115))) := by
  classical
  tauto

theorem initial11861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4238) ∨ (meaning t m 5810) := by
  exact rule11861 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule11862 (p2220 p4115 p4238 p4531 p4532 : Prop) : (p2220) ∨ (((¬ p4531) ∨ (¬ p4532) ∨ (¬ p4238) ∨ (¬ p2220) ∨ (¬ p4115))) := by
  classical
  tauto

theorem initial11862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2220) ∨ (meaning t m 5810) := by
  exact rule11862 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule11863 (p2220 p4115 p4238 p4531 p4532 : Prop) : (p4115) ∨ (((¬ p4531) ∨ (¬ p4532) ∨ (¬ p4238) ∨ (¬ p2220) ∨ (¬ p4115))) := by
  classical
  tauto

theorem initial11863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4115) ∨ (meaning t m 5810) := by
  exact rule11863 (meaning t m 2220) (meaning t m 4115) (meaning t m 4238) (meaning t m 4531) (meaning t m 4532)

theorem rule11867 (p5809 p5810 : Prop) : (¬ ((¬ p5809) ∨ (¬ p5810))) ∨ (¬ p5809) ∨ (¬ p5810) := by
  classical
  tauto

theorem initial11867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5808)) ∨ (¬ (meaning t m 5809)) ∨ (¬ (meaning t m 5810)) := by
  exact rule11867 (meaning t m 5809) (meaning t m 5810)

theorem rule11868 (p4526 p5808 : Prop) (h : (p4526 ↔ p5808)) : (¬ p4526) ∨ (p5808) := by
  classical
  tauto

theorem initial11868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4526)) ∨ (meaning t m 5808) := by
  have source := ElevenTheory.theory3221 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 8)
  exact rule11868 (meaning t m 4526) (meaning t m 5808) source

theorem rule11870 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p4109) ∨ (((¬ p4109) ∨ (¬ p4536) ∨ (¬ p2589) ∨ (¬ p4533) ∨ (¬ p3904))) := by
  classical
  tauto

theorem initial11870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4109) ∨ (meaning t m 5812) := by
  exact rule11870 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule11872 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p2589) ∨ (((¬ p4109) ∨ (¬ p4536) ∨ (¬ p2589) ∨ (¬ p4533) ∨ (¬ p3904))) := by
  classical
  tauto

theorem initial11872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2589) ∨ (meaning t m 5812) := by
  exact rule11872 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule11874 (p2589 p3904 p4109 p4533 p4536 : Prop) : (p3904) ∨ (((¬ p4109) ∨ (¬ p4536) ∨ (¬ p2589) ∨ (¬ p4533) ∨ (¬ p3904))) := by
  classical
  tauto

theorem initial11874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3904) ∨ (meaning t m 5812) := by
  exact rule11874 (meaning t m 2589) (meaning t m 3904) (meaning t m 4109) (meaning t m 4533) (meaning t m 4536)

theorem rule11878 (p2230 p4031 p4399 p4538 p4539 : Prop) : (p4031) ∨ (((¬ p4538) ∨ (¬ p4539) ∨ (¬ p4031) ∨ (¬ p2230) ∨ (¬ p4399))) := by
  classical
  tauto

theorem initial11878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4031) ∨ (meaning t m 5813) := by
  exact rule11878 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule11879 (p2230 p4031 p4399 p4538 p4539 : Prop) : (p2230) ∨ (((¬ p4538) ∨ (¬ p4539) ∨ (¬ p4031) ∨ (¬ p2230) ∨ (¬ p4399))) := by
  classical
  tauto

theorem initial11879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2230) ∨ (meaning t m 5813) := by
  exact rule11879 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule11880 (p2230 p4031 p4399 p4538 p4539 : Prop) : (p4399) ∨ (((¬ p4538) ∨ (¬ p4539) ∨ (¬ p4031) ∨ (¬ p2230) ∨ (¬ p4399))) := by
  classical
  tauto

theorem initial11880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4399) ∨ (meaning t m 5813) := by
  exact rule11880 (meaning t m 2230) (meaning t m 4031) (meaning t m 4399) (meaning t m 4538) (meaning t m 4539)

theorem rule11884 (p5812 p5813 : Prop) : (¬ ((¬ p5812) ∨ (¬ p5813))) ∨ (¬ p5812) ∨ (¬ p5813) := by
  classical
  tauto

theorem initial11884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5811)) ∨ (¬ (meaning t m 5812)) ∨ (¬ (meaning t m 5813)) := by
  exact rule11884 (meaning t m 5812) (meaning t m 5813)

theorem rule11885 (p4534 p5811 : Prop) (h : (p4534 ↔ p5811)) : (¬ p4534) ∨ (p5811) := by
  classical
  tauto

theorem initial11885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4534)) ∨ (meaning t m 5811) := by
  have source := ElevenTheory.theory3222 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5)
  exact rule11885 (meaning t m 4534) (meaning t m 5811) source

theorem rule11887 (p1978 p2230 p2233 p4533 : Prop) (h : (¬ p1978) ∨ (¬ p2230) ∨ p2233 ∨ p4533) : (¬ p1978) ∨ (¬ p2230) ∨ (p2233) ∨ (p4533) := by
  classical
  tauto

theorem initial11887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (meaning t m 4533) := by
  have source := ElevenTheory.theory3223 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5)
  exact rule11887 (meaning t m 1978) (meaning t m 2230) (meaning t m 2233) (meaning t m 4533) source

theorem rule11888 (p3553 p3919 p4548 p4549 p4550 : Prop) : (p4548) ∨ (((¬ p4548) ∨ (¬ p3553) ∨ (¬ p3919) ∨ (¬ p4549) ∨ (¬ p4550))) := by
  classical
  tauto

theorem initial11888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4548) ∨ (meaning t m 5815) := by
  exact rule11888 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule11889 (p3553 p3919 p4548 p4549 p4550 : Prop) : (p3553) ∨ (((¬ p4548) ∨ (¬ p3553) ∨ (¬ p3919) ∨ (¬ p4549) ∨ (¬ p4550))) := by
  classical
  tauto

theorem initial11889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3553) ∨ (meaning t m 5815) := by
  exact rule11889 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule11890 (p3553 p3919 p4548 p4549 p4550 : Prop) : (p3919) ∨ (((¬ p4548) ∨ (¬ p3553) ∨ (¬ p3919) ∨ (¬ p4549) ∨ (¬ p4550))) := by
  classical
  tauto

theorem initial11890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3919) ∨ (meaning t m 5815) := by
  exact rule11890 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule11892 (p3553 p3919 p4548 p4549 p4550 : Prop) : (p4550) ∨ (((¬ p4548) ∨ (¬ p3553) ∨ (¬ p3919) ∨ (¬ p4549) ∨ (¬ p4550))) := by
  classical
  tauto

theorem initial11892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4550) ∨ (meaning t m 5815) := by
  exact rule11892 (meaning t m 3553) (meaning t m 3919) (meaning t m 4548) (meaning t m 4549) (meaning t m 4550)

theorem rule11894 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p4378) ∨ (((¬ p4378) ∨ (¬ p4044) ∨ (¬ p2264) ∨ (¬ p4552) ∨ (¬ p4041))) := by
  classical
  tauto

theorem initial11894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4378) ∨ (meaning t m 5816) := by
  exact rule11894 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule11895 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p4044) ∨ (((¬ p4378) ∨ (¬ p4044) ∨ (¬ p2264) ∨ (¬ p4552) ∨ (¬ p4041))) := by
  classical
  tauto

theorem initial11895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4044) ∨ (meaning t m 5816) := by
  exact rule11895 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule11896 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p2264) ∨ (((¬ p4378) ∨ (¬ p4044) ∨ (¬ p2264) ∨ (¬ p4552) ∨ (¬ p4041))) := by
  classical
  tauto

theorem initial11896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2264) ∨ (meaning t m 5816) := by
  exact rule11896 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule11898 (p2264 p4041 p4044 p4378 p4552 : Prop) : (p4041) ∨ (((¬ p4378) ∨ (¬ p4044) ∨ (¬ p2264) ∨ (¬ p4552) ∨ (¬ p4041))) := by
  classical
  tauto

theorem initial11898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4041) ∨ (meaning t m 5816) := by
  exact rule11898 (meaning t m 2264) (meaning t m 4041) (meaning t m 4044) (meaning t m 4378) (meaning t m 4552)

theorem rule11902 (p5815 p5816 : Prop) : (¬ ((¬ p5815) ∨ (¬ p5816))) ∨ (¬ p5815) ∨ (¬ p5816) := by
  classical
  tauto

theorem initial11902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5814)) ∨ (¬ (meaning t m 5815)) ∨ (¬ (meaning t m 5816)) := by
  exact rule11902 (meaning t m 5815) (meaning t m 5816)

theorem rule11903 (p4546 p5814 : Prop) (h : (p4546 ↔ p5814)) : (¬ p4546) ∨ (p5814) := by
  classical
  tauto

theorem initial11903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4546)) ∨ (meaning t m 5814) := by
  have source := ElevenTheory.theory3224 t (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule11903 (meaning t m 4546) (meaning t m 5814) source

theorem rule11905 (p3097 p4204 p4275 p4555 p4556 : Prop) : (p4275) ∨ (((¬ p4275) ∨ (¬ p3097) ∨ (¬ p4204) ∨ (¬ p4555) ∨ (¬ p4556))) := by
  classical
  tauto

theorem initial11905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4275) ∨ (meaning t m 5818) := by
  exact rule11905 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule11906 (p3097 p4204 p4275 p4555 p4556 : Prop) : (p3097) ∨ (((¬ p4275) ∨ (¬ p3097) ∨ (¬ p4204) ∨ (¬ p4555) ∨ (¬ p4556))) := by
  classical
  tauto

theorem initial11906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3097) ∨ (meaning t m 5818) := by
  exact rule11906 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule11907 (p3097 p4204 p4275 p4555 p4556 : Prop) : (p4204) ∨ (((¬ p4275) ∨ (¬ p3097) ∨ (¬ p4204) ∨ (¬ p4555) ∨ (¬ p4556))) := by
  classical
  tauto

theorem initial11907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4204) ∨ (meaning t m 5818) := by
  exact rule11907 (meaning t m 3097) (meaning t m 4204) (meaning t m 4275) (meaning t m 4555) (meaning t m 4556)

theorem rule11911 (p2274 p3872 p4140 p4558 p4559 : Prop) : (p4140) ∨ (((¬ p4140) ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p4558) ∨ (¬ p4559))) := by
  classical
  tauto

theorem initial11911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4140) ∨ (meaning t m 5819) := by
  exact rule11911 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule11912 (p2274 p3872 p4140 p4558 p4559 : Prop) : (p3872) ∨ (((¬ p4140) ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p4558) ∨ (¬ p4559))) := by
  classical
  tauto

theorem initial11912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3872) ∨ (meaning t m 5819) := by
  exact rule11912 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule11913 (p2274 p3872 p4140 p4558 p4559 : Prop) : (p2274) ∨ (((¬ p4140) ∨ (¬ p3872) ∨ (¬ p2274) ∨ (¬ p4558) ∨ (¬ p4559))) := by
  classical
  tauto

theorem initial11913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2274) ∨ (meaning t m 5819) := by
  exact rule11913 (meaning t m 2274) (meaning t m 3872) (meaning t m 4140) (meaning t m 4558) (meaning t m 4559)

theorem rule11919 (p5818 p5819 : Prop) : (¬ ((¬ p5818) ∨ (¬ p5819))) ∨ (¬ p5818) ∨ (¬ p5819) := by
  classical
  tauto

theorem initial11919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5817)) ∨ (¬ (meaning t m 5818)) ∨ (¬ (meaning t m 5819)) := by
  exact rule11919 (meaning t m 5818) (meaning t m 5819)

theorem rule11920 (p4553 p5817 : Prop) (h : (p4553 ↔ p5817)) : (¬ p4553) ∨ (p5817) := by
  classical
  tauto

theorem initial11920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4553)) ∨ (meaning t m 5817) := by
  have source := ElevenTheory.theory3225 t (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule11920 (meaning t m 4553) (meaning t m 5817) source

theorem rule11922 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p3745) ∨ (((¬ p3745) ∨ (¬ p3952) ∨ (¬ p4153) ∨ (¬ p4563) ∨ (¬ p4564))) := by
  classical
  tauto

theorem initial11922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3745) ∨ (meaning t m 5821) := by
  exact rule11922 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule11923 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p3952) ∨ (((¬ p3745) ∨ (¬ p3952) ∨ (¬ p4153) ∨ (¬ p4563) ∨ (¬ p4564))) := by
  classical
  tauto

theorem initial11923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3952) ∨ (meaning t m 5821) := by
  exact rule11923 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule11924 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p4153) ∨ (((¬ p3745) ∨ (¬ p3952) ∨ (¬ p4153) ∨ (¬ p4563) ∨ (¬ p4564))) := by
  classical
  tauto

theorem initial11924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4153) ∨ (meaning t m 5821) := by
  exact rule11924 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule11925 (p3745 p3952 p4153 p4563 p4564 : Prop) : (p4563) ∨ (((¬ p3745) ∨ (¬ p3952) ∨ (¬ p4153) ∨ (¬ p4563) ∨ (¬ p4564))) := by
  classical
  tauto

theorem initial11925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4563) ∨ (meaning t m 5821) := by
  exact rule11925 (meaning t m 3745) (meaning t m 3952) (meaning t m 4153) (meaning t m 4563) (meaning t m 4564)

theorem rule11928 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p3986) ∨ (((¬ p3986) ∨ (¬ p4336) ∨ (¬ p2284) ∨ (¬ p4566) ∨ (¬ p4560))) := by
  classical
  tauto

theorem initial11928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3986) ∨ (meaning t m 5822) := by
  exact rule11928 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule11929 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p4336) ∨ (((¬ p3986) ∨ (¬ p4336) ∨ (¬ p2284) ∨ (¬ p4566) ∨ (¬ p4560))) := by
  classical
  tauto

theorem initial11929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4336) ∨ (meaning t m 5822) := by
  exact rule11929 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule11930 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p2284) ∨ (((¬ p3986) ∨ (¬ p4336) ∨ (¬ p2284) ∨ (¬ p4566) ∨ (¬ p4560))) := by
  classical
  tauto

theorem initial11930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2284) ∨ (meaning t m 5822) := by
  exact rule11930 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule11932 (p2284 p3986 p4336 p4560 p4566 : Prop) : (p4560) ∨ (((¬ p3986) ∨ (¬ p4336) ∨ (¬ p2284) ∨ (¬ p4566) ∨ (¬ p4560))) := by
  classical
  tauto

theorem initial11932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4560) ∨ (meaning t m 5822) := by
  exact rule11932 (meaning t m 2284) (meaning t m 3986) (meaning t m 4336) (meaning t m 4560) (meaning t m 4566)

theorem rule11936 (p5821 p5822 : Prop) : (¬ ((¬ p5821) ∨ (¬ p5822))) ∨ (¬ p5821) ∨ (¬ p5822) := by
  classical
  tauto

theorem initial11936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5820)) ∨ (¬ (meaning t m 5821)) ∨ (¬ (meaning t m 5822)) := by
  exact rule11936 (meaning t m 5821) (meaning t m 5822)

theorem rule11937 (p4561 p5820 : Prop) (h : (p4561 ↔ p5820)) : (¬ p4561) ∨ (p5820) := by
  classical
  tauto

theorem initial11937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4561)) ∨ (meaning t m 5820) := by
  have source := ElevenTheory.theory3226 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule11937 (meaning t m 4561) (meaning t m 5820) source

theorem rule11939 (p1979 p2287 p3952 p4560 : Prop) (h : (¬ p1979) ∨ p2287 ∨ (¬ p3952) ∨ p4560) : (¬ p1979) ∨ (p2287) ∨ (¬ p3952) ∨ (p4560) := by
  classical
  tauto

theorem initial11939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 3952)) ∨ (meaning t m 4560) := by
  have source := ElevenTheory.theory3227 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule11939 (meaning t m 1979) (meaning t m 2287) (meaning t m 3952) (meaning t m 4560) source

theorem rule11940 (p2298 p3568 p4067 p4569 p4570 : Prop) : (p2298) ∨ (((¬ p2298) ∨ (¬ p3568) ∨ (¬ p4067) ∨ (¬ p4569) ∨ (¬ p4570))) := by
  classical
  tauto

theorem initial11940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2298) ∨ (meaning t m 5824) := by
  exact rule11940 (meaning t m 2298) (meaning t m 3568) (meaning t m 4067) (meaning t m 4569) (meaning t m 4570)

end SunPrize.SMT
