import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory058
import SunPrize.Certificate.Theory059
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule33323 (p2027 p2230 p2373 p3365 p3366 p3519 p3969 p4035 p4376 p5119 p5284 : Prop) (h : (¬ p5119) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p3365) ∨ (¬ p5284) ∨ (¬ p4376) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3366) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial33323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory22579 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule33323 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3969) (meaning t m 4035) (meaning t m 4376) (meaning t m 5119) (meaning t m 5284) source

theorem rule33335 (p3324 p3922 p3923 : Prop) (h : (¬ p3923) ∨ (¬ p3922) ∨ p3324) : (p3324) ∨ (¬ p3922) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial33335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory22591 (m.theta 1 6) (m.theta 3 6) (m.theta 6 8)
  exact rule33335 (meaning t m 3324) (meaning t m 3922) (meaning t m 3923) source

theorem rule33336 (p1977 p2027 p2417 p2633 p3644 p3947 p4111 p4112 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p4112) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p2417) ∨ (¬ p4111) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial33336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory22592 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33336 (meaning t m 1977) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 3644) (meaning t m 3947) (meaning t m 4111) (meaning t m 4112) source

theorem rule33343 (p2027 p2284 p2950 p3286 p3646 p5039 : Prop) (h : (¬ p2284) ∨ (¬ p3646) ∨ (¬ p2950) ∨ (¬ p5039) ∨ p2027 ∨ (¬ p3286)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p3286) ∨ (¬ p3646) ∨ (¬ p5039) := by
  classical
  tauto

theorem initial33343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 5039)) := by
  have source := ElevenTheory.theory22599 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 3 9) (m.theta 5 6)
  exact rule33343 (meaning t m 2027) (meaning t m 2284) (meaning t m 2950) (meaning t m 3286) (meaning t m 3646) (meaning t m 5039) source

theorem rule33348 (p2027 p2470 p2509 p2542 p2589 p4811 : Prop) (h : (¬ p2542) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p2470) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial33348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory22604 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule33348 (meaning t m 2027) (meaning t m 2470) (meaning t m 2509) (meaning t m 2542) (meaning t m 2589) (meaning t m 4811) source

theorem rule33349 (p2027 p2098 p2928 p3055 p3658 p3685 p5214 : Prop) (h : (¬ p3055) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3658) ∨ (¬ p5214) ∨ (¬ p3685)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p3658) ∨ (¬ p3685) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial33349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory22605 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 2 8) (m.theta 4 7)
  exact rule33349 (meaning t m 2027) (meaning t m 2098) (meaning t m 2928) (meaning t m 3055) (meaning t m 3658) (meaning t m 3685) (meaning t m 5214) source

theorem rule33351 (p2027 p2753 p3097 p3471 p3688 p4401 p4475 : Prop) (h : (¬ p3471) ∨ p2027 ∨ (¬ p4401) ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p4475) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3471) ∨ (¬ p3688) ∨ (¬ p4401) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial33351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory22607 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7)
  exact rule33351 (meaning t m 2027) (meaning t m 2753) (meaning t m 3097) (meaning t m 3471) (meaning t m 3688) (meaning t m 4401) (meaning t m 4475) source

theorem rule33352 (p2027 p2246 p2579 p2749 p2946 p3347 p3506 p3956 p4322 p4347 p4450 p5038 p5216 : Prop) (h : (¬ p3347) ∨ (¬ p5216) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3506) ∨ (¬ p2246) ∨ (¬ p3956) ∨ (¬ p5038) ∨ (¬ p4347) ∨ (¬ p4450)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3506) ∨ (¬ p3956) ∨ (¬ p4322) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p5038) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial33352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5038)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory22608 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 3 9) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule33352 (meaning t m 2027) (meaning t m 2246) (meaning t m 2579) (meaning t m 2749) (meaning t m 2946) (meaning t m 3347) (meaning t m 3506) (meaning t m 3956) (meaning t m 4322) (meaning t m 4347) (meaning t m 4450) (meaning t m 5038) (meaning t m 5216) source

theorem rule33355 (p1982 p2027 p2187 p2363 p2563 p2842 p2850 : Prop) (h : p2842 ∨ (¬ p2850) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2187) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (p2842) ∨ (¬ p2850) := by
  classical
  tauto

theorem initial33355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) := by
  have source := ElevenTheory.theory22611 t (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule33355 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2363) (meaning t m 2563) (meaning t m 2842) (meaning t m 2850) source

theorem rule33363 (p2027 p2352 p2542 p3324 p4194 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p4194) ∨ (¬ p2542) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2542) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial33363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory22619 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule33363 (meaning t m 2027) (meaning t m 2352) (meaning t m 2542) (meaning t m 3324) (meaning t m 4194) (meaning t m 4715) source

theorem rule33364 (p2027 p2505 p2590 p2928 p3319 p4137 p4644 : Prop) (h : p2027 ∨ (¬ p4644) ∨ (¬ p2928) ∨ (¬ p2590) ∨ (¬ p4137) ∨ (¬ p2505) ∨ (¬ p3319)) : (p2027) ∨ (¬ p2505) ∨ (¬ p2590) ∨ (¬ p2928) ∨ (¬ p3319) ∨ (¬ p4137) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial33364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory22620 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule33364 (meaning t m 2027) (meaning t m 2505) (meaning t m 2590) (meaning t m 2928) (meaning t m 3319) (meaning t m 4137) (meaning t m 4644) source

theorem rule33366 (p3291 p3506 p3767 : Prop) (h : (¬ p3767) ∨ (¬ p3291) ∨ p3506) : (¬ p3291) ∨ (p3506) ∨ (¬ p3767) := by
  classical
  tauto

theorem initial33366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3291)) ∨ (meaning t m 3506) ∨ (¬ (meaning t m 3767)) := by
  have source := ElevenTheory.theory22622 (m.theta 0 9) (m.theta 3 9) (m.theta 9 10)
  exact rule33366 (meaning t m 3291) (meaning t m 3506) (meaning t m 3767) source

theorem rule33373 (p2027 p2248 p2284 p2946 p3125 p3588 p3954 p4324 p4621 : Prop) (h : (¬ p2946) ∨ (¬ p3954) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4621) ∨ (¬ p4324) ∨ (¬ p3588) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial33373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory22629 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule33373 (meaning t m 2027) (meaning t m 2248) (meaning t m 2284) (meaning t m 2946) (meaning t m 3125) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4621) source

theorem rule33377 (p1992 p2027 p2608 p2997 p3319 p3549 p3946 p5015 : Prop) (h : (¬ p1992) ∨ p2997 ∨ (¬ p2608) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p3319) ∨ (¬ p5015) ∨ (¬ p3946)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2997) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial33377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory22633 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9)
  exact rule33377 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2997) (meaning t m 3319) (meaning t m 3549) (meaning t m 3946) (meaning t m 5015) source

theorem rule33379 (p1990 p2027 p2192 p2210 p2633 p3548 p4366 : Prop) (h : (¬ p3548) ∨ p2027 ∨ p2633 ∨ (¬ p4366) ∨ (¬ p1990) ∨ (¬ p2192) ∨ (¬ p2210)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (p2633) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial33379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory22635 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 7 8)
  exact rule33379 (meaning t m 1990) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2633) (meaning t m 3548) (meaning t m 4366) source

theorem rule33386 (p2027 p2088 p2751 p3027 p4066 p4340 p4364 p4590 : Prop) (h : (¬ p2751) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p4364) ∨ (¬ p4590) ∨ (¬ p4340) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial33386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory22642 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 7) (m.theta 8 9)
  exact rule33386 (meaning t m 2027) (meaning t m 2088) (meaning t m 2751) (meaning t m 3027) (meaning t m 4066) (meaning t m 4340) (meaning t m 4364) (meaning t m 4590) source

theorem rule33387 (p1998 p2027 p2373 p2542 p2608 p2707 p2717 p3008 p3574 p4120 p4524 : Prop) (h : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2608) ∨ p3008 ∨ (¬ p3574) ∨ (¬ p2717) ∨ (¬ p2707) ∨ (¬ p4524) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (p3008) ∨ (¬ p3574) ∨ (¬ p4120) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial33387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory22643 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8) (m.theta 7 8)
  exact rule33387 (meaning t m 1998) (meaning t m 2027) (meaning t m 2373) (meaning t m 2542) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3008) (meaning t m 3574) (meaning t m 4120) (meaning t m 4524) source

theorem rule33392 (p1995 p2027 p2499 p2766 p3422 p3874 p4347 p4432 : Prop) (h : (¬ p1995) ∨ p2766 ∨ (¬ p4347) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p4432) ∨ (¬ p3874) ∨ (¬ p3422)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (p2766) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p4347) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial33392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory22648 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule33392 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2766) (meaning t m 3422) (meaning t m 3874) (meaning t m 4347) (meaning t m 4432) source

theorem rule33393 (p2459 p3146 p4042 : Prop) (h : (¬ p2459) ∨ (¬ p4042) ∨ p3146) : (¬ p2459) ∨ (p3146) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial33393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (meaning t m 3146) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory22649 (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33393 (meaning t m 2459) (meaning t m 3146) (meaning t m 4042) source

theorem rule33394 (p2027 p2088 p2482 p2534 p2748 p3324 p3365 p3367 p3759 p4154 p4596 p4734 : Prop) (h : (¬ p4596) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2482) ∨ (¬ p2088) ∨ (¬ p4154) ∨ (¬ p3324) ∨ (¬ p2748) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (¬ p2748) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4154) ∨ (¬ p4596) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory22650 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule33394 (meaning t m 2027) (meaning t m 2088) (meaning t m 2482) (meaning t m 2534) (meaning t m 2748) (meaning t m 3324) (meaning t m 3365) (meaning t m 3367) (meaning t m 3759) (meaning t m 4154) (meaning t m 4596) (meaning t m 4734) source

theorem rule33401 (p2027 p2138 p2911 p2922 p3379 p3690 p4244 p4666 p4736 : Prop) (h : (¬ p3379) ∨ (¬ p2138) ∨ (¬ p2922) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p4736) ∨ (¬ p4244) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial33401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory22657 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33401 (meaning t m 2027) (meaning t m 2138) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3690) (meaning t m 4244) (meaning t m 4666) (meaning t m 4736) source

theorem rule33407 (p2027 p2156 p2187 p2247 p2363 p3359 p4111 p4521 p4697 : Prop) (h : (¬ p4697) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p2187) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial33407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory22663 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule33407 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2247) (meaning t m 2363) (meaning t m 3359) (meaning t m 4111) (meaning t m 4521) (meaning t m 4697) source

theorem rule33410 (p2010 p2027 p2901 p3246 p3497 p3578 p4278 : Prop) (h : (¬ p2010) ∨ p2027 ∨ (¬ p3497) ∨ p3578 ∨ (¬ p4278) ∨ (¬ p2901) ∨ (¬ p3246)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3497) ∨ (p3578) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial33410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory22666 t (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule33410 (meaning t m 2010) (meaning t m 2027) (meaning t m 2901) (meaning t m 3246) (meaning t m 3497) (meaning t m 3578) (meaning t m 4278) source

theorem rule33411 (p1975 p2027 p2132 p2192 p2274 p2842 p3055 p4418 : Prop) (h : (¬ p2132) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2192) ∨ (¬ p4418) ∨ p2842 ∨ (¬ p3055)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial33411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory22667 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule33411 (meaning t m 1975) (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2274) (meaning t m 2842) (meaning t m 3055) (meaning t m 4418) source

theorem rule33420 (p2005 p2027 p2166 p2210 p2699 p3016 p3497 p4700 : Prop) (h : (¬ p3497) ∨ (¬ p2210) ∨ p2699 ∨ p2027 ∨ (¬ p2166) ∨ (¬ p3016) ∨ (¬ p4700) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial33420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory22676 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8)
  exact rule33420 (meaning t m 2005) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2699) (meaning t m 3016) (meaning t m 3497) (meaning t m 4700) source

theorem rule33421 (p2027 p2187 p2192 p2255 p2459 p2946 p2996 p3412 p3857 p3961 p4133 p4155 : Prop) (h : (¬ p2255) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3857) ∨ (¬ p4155) ∨ (¬ p3961) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2459) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3412) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4133) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial33421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory22677 t (m.theta 0 3) (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33421 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2255) (meaning t m 2459) (meaning t m 2946) (meaning t m 2996) (meaning t m 3412) (meaning t m 3857) (meaning t m 3961) (meaning t m 4133) (meaning t m 4155) source

theorem rule33427 (p2440 p3237 p3359 : Prop) (h : (¬ p2440) ∨ (¬ p3237) ∨ p3359) : (¬ p2440) ∨ (¬ p3237) ∨ (p3359) := by
  classical
  tauto

theorem initial33427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3237)) ∨ (meaning t m 3359) := by
  have source := ElevenTheory.theory22683 (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule33427 (meaning t m 2440) (meaning t m 3237) (meaning t m 3359) source

theorem rule33430 (p2641 p3027 p4067 : Prop) (h : (¬ p3027) ∨ (¬ p4067) ∨ p2641) : (p2641) ∨ (¬ p3027) ∨ (¬ p4067) := by
  classical
  tauto

theorem initial33430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2641) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4067)) := by
  have source := ElevenTheory.theory22686 (m.theta 1 3) (m.theta 3 6) (m.theta 3 7)
  exact rule33430 (meaning t m 2641) (meaning t m 3027) (meaning t m 4067) source

theorem rule33435 (p2027 p2307 p2476 p2534 p2668 p2781 p3146 p3568 p3905 p4134 : Prop) (h : (¬ p4134) ∨ (¬ p2307) ∨ (¬ p3568) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2781) ∨ (¬ p3905) ∨ (¬ p2476) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p2781) ∨ (¬ p3146) ∨ (¬ p3568) ∨ (¬ p3905) ∨ (¬ p4134) := by
  classical
  tauto

theorem initial33435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4134)) := by
  have source := ElevenTheory.theory22691 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule33435 (meaning t m 2027) (meaning t m 2307) (meaning t m 2476) (meaning t m 2534) (meaning t m 2668) (meaning t m 2781) (meaning t m 3146) (meaning t m 3568) (meaning t m 3905) (meaning t m 4134) source

theorem rule33440 (p3367 p4242 p4354 : Prop) (h : (¬ p4242) ∨ (¬ p3367) ∨ (¬ p4354)) : (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4354) := by
  classical
  tauto

theorem initial33440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4354)) := by
  have source := ElevenTheory.theory22696 (m.theta 1 2) (m.theta 2 4) (m.theta 2 8)
  exact rule33440 (meaning t m 3367) (meaning t m 4242) (meaning t m 4354) source

theorem rule33448 (p3550 p3581 p3644 p3956 : Prop) (h : (¬ p3550) ∨ (¬ p3581) ∨ (¬ p3644) ∨ p3956) : (¬ p3550) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (p3956) := by
  classical
  tauto

theorem initial33448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (meaning t m 3956) := by
  have source := ElevenTheory.theory22704 (m.theta 4 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule33448 (meaning t m 3550) (meaning t m 3581) (meaning t m 3644) (meaning t m 3956) source

theorem rule33450 (p2027 p2138 p2553 p2573 p3367 p3759 p3989 p4173 p4243 p4501 p4734 : Prop) (h : p2027 ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2573) ∨ (¬ p2553) ∨ (¬ p4173) ∨ (¬ p4734) ∨ (¬ p2138) ∨ (¬ p4501) ∨ (¬ p4243) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4501) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory22706 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule33450 (meaning t m 2027) (meaning t m 2138) (meaning t m 2553) (meaning t m 2573) (meaning t m 3367) (meaning t m 3759) (meaning t m 3989) (meaning t m 4173) (meaning t m 4243) (meaning t m 4501) (meaning t m 4734) source

theorem rule33451 (p1978 p2027 p2449 p2995 p3497 p3556 p3578 p3690 : Prop) (h : (¬ p1978) ∨ (¬ p3690) ∨ p3578 ∨ (¬ p3556) ∨ (¬ p2995) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p2449)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (p3578) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial33451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory22707 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule33451 (meaning t m 1978) (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3497) (meaning t m 3556) (meaning t m 3578) (meaning t m 3690) source

theorem rule33452 (p1991 p2027 p2202 p2440 p2685 p2810 p3414 : Prop) (h : (¬ p2810) ∨ (¬ p1991) ∨ (¬ p3414) ∨ p2202 ∨ p2027 ∨ (¬ p2685) ∨ (¬ p2440)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial33452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory22708 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule33452 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2685) (meaning t m 2810) (meaning t m 3414) source

theorem rule33456 (p2027 p2589 p2696 p3005 p3256 p3744 p4110 p4604 p4729 : Prop) (h : (¬ p4604) ∨ (¬ p4110) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4604) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial33456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory22712 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule33456 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3744) (meaning t m 4110) (meaning t m 4604) (meaning t m 4729) source

theorem rule33457 (p2027 p3083 p3367 p4242 p4750 p5369 : Prop) (h : (¬ p5369) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p3083)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4750) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial33457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory22713 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 3 4) (m.theta 4 8)
  exact rule33457 (meaning t m 2027) (meaning t m 3083) (meaning t m 3367) (meaning t m 4242) (meaning t m 4750) (meaning t m 5369) source

theorem rule33460 (p2027 p2191 p2995 p3256 p3692 p4044 p4957 : Prop) (h : p2027 ∨ (¬ p4957) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p2995) ∨ (¬ p2191) ∨ (¬ p4044)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2995) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4044) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial33460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory22716 t (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule33460 (meaning t m 2027) (meaning t m 2191) (meaning t m 2995) (meaning t m 3256) (meaning t m 3692) (meaning t m 4044) (meaning t m 4957) source

theorem rule33462 (p2027 p2177 p2191 p2246 p2295 p2331 p2608 p2744 p3555 p4905 : Prop) (h : p2027 ∨ (¬ p4905) ∨ (¬ p2177) ∨ (¬ p3555) ∨ (¬ p2191) ∨ (¬ p2331) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2191) ∨ (¬ p2246) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3555) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial33462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory22718 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule33462 (meaning t m 2027) (meaning t m 2177) (meaning t m 2191) (meaning t m 2246) (meaning t m 2295) (meaning t m 2331) (meaning t m 2608) (meaning t m 2744) (meaning t m 3555) (meaning t m 4905) source

theorem rule33471 (p2532 p4345 p5045 : Prop) (h : (¬ p4345) ∨ (¬ p5045) ∨ p2532) : (p2532) ∨ (¬ p4345) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial33471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2532) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory22727 (m.theta 5 9) (m.theta 6 9) (m.theta 8 9)
  exact rule33471 (meaning t m 2532) (meaning t m 4345) (meaning t m 5045) source

theorem rule33475 (p1979 p2027 p2797 p2881 p2938 p3553 p3572 p4153 : Prop) (h : (¬ p2881) ∨ p2938 ∨ (¬ p4153) ∨ (¬ p2797) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p1979) ∨ (¬ p3572)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2797) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial33475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory22731 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule33475 (meaning t m 1979) (meaning t m 2027) (meaning t m 2797) (meaning t m 2881) (meaning t m 2938) (meaning t m 3553) (meaning t m 3572) (meaning t m 4153) source

theorem rule33476 (p2027 p2553 p2573 p2748 p3324 p3365 p3367 p3759 p4154 p4501 p4734 : Prop) (h : (¬ p2553) ∨ (¬ p4734) ∨ (¬ p2748) ∨ (¬ p4501) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2748) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4154) ∨ (¬ p4501) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory22732 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule33476 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2748) (meaning t m 3324) (meaning t m 3365) (meaning t m 3367) (meaning t m 3759) (meaning t m 4154) (meaning t m 4501) (meaning t m 4734) source

theorem rule33477 (p2027 p2230 p2982 p3680 p3954 p4242 p5123 p5190 p5612 : Prop) (h : (¬ p4242) ∨ (¬ p2982) ∨ (¬ p5190) ∨ (¬ p3680) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p5612) ∨ (¬ p5123) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p5123) ∨ (¬ p5190) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial33477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory22733 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule33477 (meaning t m 2027) (meaning t m 2230) (meaning t m 2982) (meaning t m 3680) (meaning t m 3954) (meaning t m 4242) (meaning t m 5123) (meaning t m 5190) (meaning t m 5612) source

theorem rule33482 (p2143 p3645 p4418 : Prop) (h : (¬ p4418) ∨ (¬ p2143) ∨ p3645) : (¬ p2143) ∨ (p3645) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial33482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (meaning t m 3645) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory22738 (m.theta 0 5) (m.theta 1 5) (m.theta 2 5)
  exact rule33482 (meaning t m 2143) (meaning t m 3645) (meaning t m 4418) source

theorem rule33484 (p1988 p2027 p2230 p2233 p2373 p3146 p3266 : Prop) (h : (¬ p2373) ∨ p2233 ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial33484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory22740 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule33484 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2373) (meaning t m 3146) (meaning t m 3266) source

theorem rule33487 (p2274 p3309 p3957 : Prop) (h : (¬ p3957) ∨ (¬ p3309) ∨ p2274) : (p2274) ∨ (¬ p3309) ∨ (¬ p3957) := by
  classical
  tauto

theorem initial33487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2274) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3957)) := by
  have source := ElevenTheory.theory22743 (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule33487 (meaning t m 2274) (meaning t m 3309) (meaning t m 3957) source

theorem rule33491 (p1987 p2027 p2169 p2363 p2737 p4242 p4340 : Prop) (h : (¬ p1987) ∨ (¬ p2363) ∨ p2027 ∨ p2169 ∨ (¬ p2737) ∨ (¬ p4242) ∨ (¬ p4340)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2737) ∨ (¬ p4242) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial33491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory22747 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule33491 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2737) (meaning t m 4242) (meaning t m 4340) source

theorem rule33494 (p1997 p2027 p2764 p2901 p4208 p4235 p4322 : Prop) (h : (¬ p4322) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p4235) ∨ p2764 ∨ (¬ p1997) ∨ (¬ p2901)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4235) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial33494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory22750 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule33494 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 2901) (meaning t m 4208) (meaning t m 4235) (meaning t m 4322) source

theorem rule33495 (p1982 p2027 p2248 p2331 p2363 p2668 p2707 p3008 p3425 p3584 p3585 p3873 : Prop) (h : (¬ p2363) ∨ p3008 ∨ (¬ p1982) ∨ (¬ p3585) ∨ (¬ p2248) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2331) ∨ (¬ p3425) ∨ (¬ p2707) ∨ (¬ p3873)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2707) ∨ (p3008) ∨ (¬ p3425) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial33495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory22751 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule33495 (meaning t m 1982) (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2707) (meaning t m 3008) (meaning t m 3425) (meaning t m 3584) (meaning t m 3585) (meaning t m 3873) source

theorem rule33501 (p1982 p2027 p2307 p2363 p2611 p2786 p2819 p3822 : Prop) (h : p2027 ∨ (¬ p3822) ∨ (¬ p2819) ∨ (¬ p2307) ∨ (¬ p1982) ∨ p2611 ∨ (¬ p2363) ∨ (¬ p2786)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial33501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory22757 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule33501 (meaning t m 1982) (meaning t m 2027) (meaning t m 2307) (meaning t m 2363) (meaning t m 2611) (meaning t m 2786) (meaning t m 2819) (meaning t m 3822) source

theorem rule33502 (p2027 p2387 p3246 p3872 p4107 p4356 p4501 : Prop) (h : (¬ p2387) ∨ (¬ p4356) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4501) ∨ (¬ p4107) ∨ (¬ p3872)) : (p2027) ∨ (¬ p2387) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p4107) ∨ (¬ p4356) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial33502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory22758 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule33502 (meaning t m 2027) (meaning t m 2387) (meaning t m 3246) (meaning t m 3872) (meaning t m 4107) (meaning t m 4356) (meaning t m 4501) source

theorem rule33516 (p2668 p3019 p3083 p4432 : Prop) (h : (¬ p3019) ∨ (¬ p2668) ∨ (¬ p4432) ∨ p3083) : (¬ p2668) ∨ (¬ p3019) ∨ (p3083) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial33516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (meaning t m 3083) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory22772 (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8)
  exact rule33516 (meaning t m 2668) (meaning t m 3019) (meaning t m 3083) (meaning t m 4432) source

theorem rule33518 (p2027 p2122 p2132 p2313 p2778 p4426 p5052 : Prop) (h : (¬ p5052) ∨ (¬ p2122) ∨ (¬ p4426) ∨ p2027 ∨ (¬ p2778) ∨ (¬ p2132) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p4426) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial33518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory22774 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7)
  exact rule33518 (meaning t m 2027) (meaning t m 2122) (meaning t m 2132) (meaning t m 2313) (meaning t m 2778) (meaning t m 4426) (meaning t m 5052) source

theorem rule33521 (p2386 p2504 p3204 : Prop) (h : (¬ p2504) ∨ p2386 ∨ (¬ p3204)) : (p2386) ∨ (¬ p2504) ∨ (¬ p3204) := by
  classical
  tauto

theorem initial33521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2386) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3204)) := by
  have source := ElevenTheory.theory22777 (m.theta 0 6) (m.theta 1 6) (m.theta 4 6)
  exact rule33521 (meaning t m 2386) (meaning t m 2504) (meaning t m 3204) source

theorem rule33528 (p1997 p2027 p2542 p2881 p2938 p3551 p3742 p4279 : Prop) (h : (¬ p3551) ∨ p2938 ∨ (¬ p2881) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p4279) ∨ (¬ p2542) ∨ (¬ p3742)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3551) ∨ (¬ p3742) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial33528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory22784 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule33528 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2881) (meaning t m 2938) (meaning t m 3551) (meaning t m 3742) (meaning t m 4279) source

theorem rule33532 (p2027 p2532 p3343 p4256 p4286 p4952 p5118 : Prop) (h : (¬ p5118) ∨ (¬ p2532) ∨ p2027 ∨ (¬ p4286) ∨ (¬ p4952) ∨ (¬ p3343) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4952) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial33532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4952)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory22788 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 9) (m.theta 8 10) (m.theta 8 9)
  exact rule33532 (meaning t m 2027) (meaning t m 2532) (meaning t m 3343) (meaning t m 4256) (meaning t m 4286) (meaning t m 4952) (meaning t m 5118) source

theorem rule33533 (p1992 p2027 p3008 p3055 p3471 p3584 p3588 : Prop) (h : (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3584) ∨ (¬ p1992) ∨ p3008 ∨ p2027 ∨ (¬ p3055)) : (¬ p1992) ∨ (p2027) ∨ (p3008) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3584) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial33533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory22789 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6)
  exact rule33533 (meaning t m 1992) (meaning t m 2027) (meaning t m 3008) (meaning t m 3055) (meaning t m 3471) (meaning t m 3584) (meaning t m 3588) source

theorem rule33535 (p2027 p2298 p2641 p3323 p4044 p4360 p4624 : Prop) (h : (¬ p4044) ∨ p2027 ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p4624) ∨ (¬ p4360) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p4044) ∨ (¬ p4360) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial33535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory22791 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 6 9)
  exact rule33535 (meaning t m 2027) (meaning t m 2298) (meaning t m 2641) (meaning t m 3323) (meaning t m 4044) (meaning t m 4360) (meaning t m 4624) source

theorem rule33540 (p2027 p2437 p2481 p2881 p3960 p4256 p4277 : Prop) (h : (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p4277) ∨ (¬ p2481) ∨ (¬ p2437) ∨ p2027) : (p2027) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial33540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory22796 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule33540 (meaning t m 2027) (meaning t m 2437) (meaning t m 2481) (meaning t m 2881) (meaning t m 3960) (meaning t m 4256) (meaning t m 4277) source

theorem rule33547 (p2027 p2255 p2996 p3516 p3947 p4104 : Prop) (h : (¬ p4104) ∨ (¬ p3947) ∨ (¬ p3516) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2996) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4104) := by
  classical
  tauto

theorem initial33547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4104)) := by
  have source := ElevenTheory.theory22803 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9)
  exact rule33547 (meaning t m 2027) (meaning t m 2255) (meaning t m 2996) (meaning t m 3516) (meaning t m 3947) (meaning t m 4104) source

theorem rule33549 (p2027 p2192 p2449 p2807 p2959 p3486 p3646 p4277 p4278 : Prop) (h : (¬ p3646) ∨ (¬ p2807) ∨ (¬ p3486) ∨ (¬ p2959) ∨ (¬ p4277) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2449) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2959) ∨ (¬ p3486) ∨ (¬ p3646) ∨ (¬ p4277) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial33549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2959)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory22805 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule33549 (meaning t m 2027) (meaning t m 2192) (meaning t m 2449) (meaning t m 2807) (meaning t m 2959) (meaning t m 3486) (meaning t m 3646) (meaning t m 4277) (meaning t m 4278) source

theorem rule33559 (p2027 p2563 p2850 p4173 p4202 p5214 : Prop) (h : (¬ p4202) ∨ (¬ p4173) ∨ (¬ p5214) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial33559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory22815 t (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule33559 (meaning t m 2027) (meaning t m 2563) (meaning t m 2850) (meaning t m 4173) (meaning t m 4202) (meaning t m 5214) source

theorem rule33561 (p2027 p2156 p2499 p3096 p3452 p4521 : Prop) (h : (¬ p3452) ∨ (¬ p2499) ∨ (¬ p4521) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3096)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p3452) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial33561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory22817 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6)
  exact rule33561 (meaning t m 2027) (meaning t m 2156) (meaning t m 2499) (meaning t m 3096) (meaning t m 3452) (meaning t m 4521) source

theorem rule33571 (p2027 p3171 p3189 p3956 p4113 p4154 p4976 : Prop) (h : (¬ p4154) ∨ (¬ p4976) ∨ (¬ p3956) ∨ (¬ p4113) ∨ (¬ p3189) ∨ (¬ p3171) ∨ p2027) : (p2027) ∨ (¬ p3171) ∨ (¬ p3189) ∨ (¬ p3956) ∨ (¬ p4113) ∨ (¬ p4154) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial33571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory22827 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule33571 (meaning t m 2027) (meaning t m 3171) (meaning t m 3189) (meaning t m 3956) (meaning t m 4113) (meaning t m 4154) (meaning t m 4976) source

theorem rule33572 (p2027 p2177 p2254 p2608 p2963 p3201 p3367 p3553 p4067 p4276 : Prop) (h : (¬ p2608) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p4276) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p3201) ∨ (¬ p2963) ∨ (¬ p3553) ∨ (¬ p4067)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial33572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory22828 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 3 6) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule33572 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2608) (meaning t m 2963) (meaning t m 3201) (meaning t m 3367) (meaning t m 3553) (meaning t m 4067) (meaning t m 4276) source

theorem rule33573 (p1998 p2027 p2230 p2427 p2622 p2630 p2656 p2881 : Prop) (h : p2622 ∨ (¬ p2630) ∨ (¬ p1998) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial33573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory22829 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule33573 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 2881) source

theorem rule33575 (p1979 p2027 p2287 p2657 p2727 p2946 p4154 : Prop) (h : p2027 ∨ (¬ p1979) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p2727) ∨ p2287 ∨ (¬ p4154)) : (¬ p1979) ∨ (p2027) ∨ (p2287) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial33575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory22831 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule33575 (meaning t m 1979) (meaning t m 2027) (meaning t m 2287) (meaning t m 2657) (meaning t m 2727) (meaning t m 2946) (meaning t m 4154) source

theorem rule33576 (p1999 p2027 p2264 p2323 p2807 p3564 p3581 p3644 : Prop) (h : (¬ p2264) ∨ (¬ p3581) ∨ (¬ p2807) ∨ (¬ p1999) ∨ p2027 ∨ (¬ p3564) ∨ p2323 ∨ (¬ p3644)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2807) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial33576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory22832 t (m.theta 0 3) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8)
  exact rule33576 (meaning t m 1999) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2807) (meaning t m 3564) (meaning t m 3581) (meaning t m 3644) source

theorem rule33577 (p3759 p4263 p4264 p5160 : Prop) (h : (¬ p3759) ∨ (¬ p4263) ∨ (¬ p5160) ∨ (¬ p4264)) : (¬ p3759) ∨ (¬ p4263) ∨ (¬ p4264) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial33577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4263)) ∨ (¬ (meaning t m 4264)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory22833 (m.theta 0 4) (m.theta 0 9) (m.theta 2 4) (m.theta 4 9)
  exact rule33577 (meaning t m 3759) (meaning t m 4263) (meaning t m 4264) (meaning t m 5160) source

theorem rule33580 (p2928 p3201 p4030 : Prop) (h : (¬ p2928) ∨ (¬ p4030) ∨ (¬ p3201)) : (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial33580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory22836 (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule33580 (meaning t m 2928) (meaning t m 3201) (meaning t m 4030) source

theorem rule33585 (p1983 p2027 p2341 p2417 p2656 p2688 p2727 p3644 p5201 : Prop) (h : (¬ p5201) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2727) ∨ p2688 ∨ (¬ p2341) ∨ (¬ p1983) ∨ (¬ p2656) ∨ (¬ p2417)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3644) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial33585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory22841 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33585 (meaning t m 1983) (meaning t m 2027) (meaning t m 2341) (meaning t m 2417) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3644) (meaning t m 5201) source

theorem rule33586 (p2027 p2608 p4181 p4416 p5312 p5590 : Prop) (h : (¬ p5312) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4181) ∨ (¬ p4416) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2608) ∨ (¬ p4181) ∨ (¬ p4416) ∨ (¬ p5312) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial33586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 5312)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory22842 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 8) (m.theta 8 10)
  exact rule33586 (meaning t m 2027) (meaning t m 2608) (meaning t m 4181) (meaning t m 4416) (meaning t m 5312) (meaning t m 5590) source

theorem rule33588 (p2027 p2241 p2750 p3527 p3551 p3687 p5206 : Prop) (h : (¬ p2241) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3527) ∨ (¬ p5206) ∨ (¬ p3551) ∨ (¬ p3687)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3687) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial33588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory22844 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 7 8)
  exact rule33588 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 3527) (meaning t m 3551) (meaning t m 3687) (meaning t m 5206) source

theorem rule33591 (p1994 p2027 p2764 p3346 p3389 p3742 p4381 p4636 : Prop) (h : (¬ p1994) ∨ p2764 ∨ (¬ p4381) ∨ p2027 ∨ (¬ p4636) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p3742)) : (¬ p1994) ∨ (p2027) ∨ (p2764) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4381) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial33591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory22847 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule33591 (meaning t m 1994) (meaning t m 2027) (meaning t m 2764) (meaning t m 3346) (meaning t m 3389) (meaning t m 3742) (meaning t m 4381) (meaning t m 4636) source

theorem rule33592 (p1983 p2027 p2246 p2341 p2545 p3434 p3659 p4104 p4111 : Prop) (h : p2027 ∨ (¬ p2246) ∨ p2545 ∨ (¬ p1983) ∨ (¬ p3434) ∨ (¬ p4111) ∨ (¬ p3659) ∨ (¬ p2341) ∨ (¬ p4104)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2341) ∨ (p2545) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p4104) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial33592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory22848 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 7 8) (m.theta 7 9)
  exact rule33592 (meaning t m 1983) (meaning t m 2027) (meaning t m 2246) (meaning t m 2341) (meaning t m 2545) (meaning t m 3434) (meaning t m 3659) (meaning t m 4104) (meaning t m 4111) source

theorem rule33595 (p2027 p2780 p2829 p3379 p3873 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3379) ∨ (¬ p2829) ∨ (¬ p3873) ∨ p2027 ∨ (¬ p2780)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3379) ∨ (¬ p3873) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial33595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory22851 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6)
  exact rule33595 (meaning t m 2027) (meaning t m 2780) (meaning t m 2829) (meaning t m 3379) (meaning t m 3873) (meaning t m 5216) source

theorem rule33601 (p2027 p2470 p2579 p3016 p3874 p4750 : Prop) (h : (¬ p3016) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p4750) ∨ (¬ p2470) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3874) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial33601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory22857 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule33601 (meaning t m 2027) (meaning t m 2470) (meaning t m 2579) (meaning t m 3016) (meaning t m 3874) (meaning t m 4750) source

theorem rule33602 (p2928 p3876 p4030 : Prop) (h : (¬ p2928) ∨ (¬ p4030) ∨ p3876) : (¬ p2928) ∨ (p3876) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial33602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2928)) ∨ (meaning t m 3876) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory22858 (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule33602 (meaning t m 2928) (meaning t m 3876) (meaning t m 4030) source

theorem rule33605 (p2926 p3031 p3402 : Prop) (h : (¬ p2926) ∨ p3031 ∨ (¬ p3402)) : (¬ p2926) ∨ (p3031) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial33605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2926)) ∨ (meaning t m 3031) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory22861 (m.theta 1 3) (m.theta 1 4) (m.theta 1 7)
  exact rule33605 (meaning t m 2926) (meaning t m 3031) (meaning t m 3402) source

theorem rule33612 (p2027 p2122 p2963 p3568 p4426 p4787 : Prop) (h : p2027 ∨ (¬ p4787) ∨ (¬ p2122) ∨ (¬ p4426) ∨ (¬ p3568) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4426) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial33612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory22868 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule33612 (meaning t m 2027) (meaning t m 2122) (meaning t m 2963) (meaning t m 3568) (meaning t m 4426) (meaning t m 4787) source

theorem rule33613 (p2027 p3146 p3644 p3747 p4277 p4348 : Prop) (h : p2027 ∨ (¬ p3747) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p4277) ∨ (¬ p4348)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3747) ∨ (¬ p4277) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial33613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory22869 t (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33613 (meaning t m 2027) (meaning t m 3146) (meaning t m 3644) (meaning t m 3747) (meaning t m 4277) (meaning t m 4348) source

theorem rule33614 (p2027 p2177 p2255 p2331 p2957 p3309 p3556 p3662 p3690 p4319 p4666 : Prop) (h : (¬ p4319) ∨ (¬ p4666) ∨ (¬ p2331) ∨ (¬ p2255) ∨ (¬ p3309) ∨ (¬ p2177) ∨ (¬ p3556) ∨ (¬ p2957) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4319) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial33614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory22870 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33614 (meaning t m 2027) (meaning t m 2177) (meaning t m 2255) (meaning t m 2331) (meaning t m 2957) (meaning t m 3309) (meaning t m 3556) (meaning t m 3662) (meaning t m 3690) (meaning t m 4319) (meaning t m 4666) source

theorem rule33616 (p2027 p2659 p3189 p3540 p3579 p3919 p4111 : Prop) (h : p2027 ∨ (¬ p2659) ∨ (¬ p3579) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p3919) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2659) ∨ (¬ p3189) ∨ (¬ p3540) ∨ (¬ p3579) ∨ (¬ p3919) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial33616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory22872 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7)
  exact rule33616 (meaning t m 2027) (meaning t m 2659) (meaning t m 3189) (meaning t m 3540) (meaning t m 3579) (meaning t m 3919) (meaning t m 4111) source

theorem rule33618 (p2027 p2307 p2588 p3125 p3958 p5378 p5379 : Prop) (h : (¬ p5379) ∨ (¬ p5378) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2307) ∨ (¬ p3958) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3125) ∨ (¬ p3958) ∨ (¬ p5378) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial33618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 5378)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory22874 t (m.theta 0 6) (m.theta 0 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule33618 (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 3125) (meaning t m 3958) (meaning t m 5378) (meaning t m 5379) source

theorem rule33619 (p1982 p2027 p2363 p2470 p2579 p2842 p3422 p4157 : Prop) (h : p2842 ∨ (¬ p2363) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p4157) ∨ (¬ p2470) ∨ (¬ p3422) ∨ (¬ p2579)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (p2842) ∨ (¬ p3422) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial33619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory22875 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule33619 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2470) (meaning t m 2579) (meaning t m 2842) (meaning t m 3422) (meaning t m 4157) source

theorem rule33621 (p2027 p2459 p2881 p3685 p4340 p4895 : Prop) (h : (¬ p4895) ∨ (¬ p4340) ∨ (¬ p3685) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial33621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory22877 t (m.theta 2 7) (m.theta 2 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule33621 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3685) (meaning t m 4340) (meaning t m 4895) source

theorem rule33633 (p1989 p2027 p2611 p2717 p3471 p3486 p3570 : Prop) (h : (¬ p3471) ∨ p2027 ∨ (¬ p1989) ∨ p2611 ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p2717)) : (¬ p1989) ∨ (p2027) ∨ (p2611) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3486) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial33633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory22889 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule33633 (meaning t m 1989) (meaning t m 2027) (meaning t m 2611) (meaning t m 2717) (meaning t m 3471) (meaning t m 3486) (meaning t m 3570) source

theorem rule33635 (p2027 p2220 p2588 p3646 p3958 p4119 p4140 : Prop) (h : (¬ p4140) ∨ (¬ p2588) ∨ (¬ p3958) ∨ (¬ p3646) ∨ (¬ p4119) ∨ p2027 ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2588) ∨ (¬ p3646) ∨ (¬ p3958) ∨ (¬ p4119) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial33635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory22891 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7)
  exact rule33635 (meaning t m 2027) (meaning t m 2220) (meaning t m 2588) (meaning t m 3646) (meaning t m 3958) (meaning t m 4119) (meaning t m 4140) source

theorem rule33638 (p2027 p3166 p3256 p4340 p4364 p4790 : Prop) (h : (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4790) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p3166)) : (p2027) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial33638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory22894 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule33638 (meaning t m 2027) (meaning t m 3166) (meaning t m 3256) (meaning t m 4340) (meaning t m 4364) (meaning t m 4790) source

theorem rule33640 (p2027 p2589 p2839 p3585 p3695 p4727 : Prop) (h : (¬ p2839) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p4727) ∨ (¬ p2589) ∨ (¬ p3695)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial33640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory22896 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule33640 (meaning t m 2027) (meaning t m 2589) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) (meaning t m 4727) source

theorem rule33649 (p2027 p3609 p3692 p3880 p4744 p4885 : Prop) (h : (¬ p3609) ∨ p2027 ∨ (¬ p4744) ∨ (¬ p4885) ∨ (¬ p3880) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4744) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial33649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory22905 t (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule33649 (meaning t m 2027) (meaning t m 3609) (meaning t m 3692) (meaning t m 3880) (meaning t m 4744) (meaning t m 4885) source

theorem rule33650 (p2027 p2946 p3156 p3540 p3644 p3905 p3969 p4348 p4786 p5122 : Prop) (h : (¬ p3969) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p5122) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p3156) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3905) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p4786) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial33650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory22906 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule33650 (meaning t m 2027) (meaning t m 2946) (meaning t m 3156) (meaning t m 3540) (meaning t m 3644) (meaning t m 3905) (meaning t m 3969) (meaning t m 4348) (meaning t m 4786) (meaning t m 5122) source

theorem rule33651 (p1992 p2027 p2241 p2699 p2743 p3027 p3572 : Prop) (h : (¬ p1992) ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3027)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2743) ∨ (¬ p3027) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial33651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory22907 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7)
  exact rule33651 (meaning t m 1992) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2743) (meaning t m 3027) (meaning t m 3572) source

theorem rule33653 (p1977 p2027 p2169 p2589 p2662 p3989 p4110 p4111 : Prop) (h : (¬ p4111) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2662) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p4110) ∨ (¬ p2589)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial33653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory22909 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule33653 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2589) (meaning t m 2662) (meaning t m 3989) (meaning t m 4110) (meaning t m 4111) source

theorem rule33656 (p3641 p3876 p4186 : Prop) (h : (¬ p3641) ∨ (¬ p4186) ∨ (¬ p3876)) : (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial33656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory22912 (m.theta 2 4) (m.theta 4 7) (m.theta 4 8)
  exact rule33656 (meaning t m 3641) (meaning t m 3876) (meaning t m 4186) source

theorem rule33661 (p3569 p3658 p4344 : Prop) (h : (¬ p3658) ∨ (¬ p3569) ∨ p4344) : (¬ p3569) ∨ (¬ p3658) ∨ (p4344) := by
  classical
  tauto

theorem initial33661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3658)) ∨ (meaning t m 4344) := by
  have source := ElevenTheory.theory22917 (m.theta 2 7) (m.theta 4 7) (m.theta 5 7)
  exact rule33661 (meaning t m 3569) (meaning t m 3658) (meaning t m 4344) source

theorem rule33668 (p2284 p3645 p3646 p4282 : Prop) (h : (¬ p3646) ∨ (¬ p3645) ∨ (¬ p2284) ∨ (¬ p4282)) : (¬ p2284) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial33668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory22924 (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule33668 (meaning t m 2284) (meaning t m 3645) (meaning t m 3646) (meaning t m 4282) source

theorem rule33669 (p1987 p2027 p2737 p2764 p2785 p3688 p3946 p4191 : Prop) (h : (¬ p1987) ∨ (¬ p3946) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p2785) ∨ (¬ p3688) ∨ p2764 ∨ (¬ p2737)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2764) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial33669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory22925 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 9) (m.theta 9 10)
  exact rule33669 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2764) (meaning t m 2785) (meaning t m 3688) (meaning t m 3946) (meaning t m 4191) source

theorem rule33670 (p3645 p4031 p4210 : Prop) (h : (¬ p4210) ∨ (¬ p3645) ∨ p4031) : (¬ p3645) ∨ (p4031) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial33670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3645)) ∨ (meaning t m 4031) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory22926 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5)
  exact rule33670 (meaning t m 3645) (meaning t m 4031) (meaning t m 4210) source

theorem rule33672 (p2027 p2210 p2247 p2589 p3347 p4210 p4813 : Prop) (h : (¬ p2589) ∨ (¬ p4210) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p4813) ∨ (¬ p3347) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p4210) ∨ (¬ p4813) := by
  classical
  tauto

theorem initial33672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4813)) := by
  have source := ElevenTheory.theory22928 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5)
  exact rule33672 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2589) (meaning t m 3347) (meaning t m 4210) (meaning t m 4813) source

theorem rule33676 (p1985 p2027 p2449 p2545 p2685 p2810 p3690 : Prop) (h : (¬ p1985) ∨ (¬ p3690) ∨ p2545 ∨ p2027 ∨ (¬ p2810) ∨ (¬ p2449) ∨ (¬ p2685)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2449) ∨ (p2545) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial33676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory22932 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule33676 (meaning t m 1985) (meaning t m 2027) (meaning t m 2449) (meaning t m 2545) (meaning t m 2685) (meaning t m 2810) (meaning t m 3690) source

theorem rule33677 (p1985 p2027 p2542 p2545 p2589 p3516 p3690 p5201 : Prop) (h : (¬ p1985) ∨ (¬ p3690) ∨ (¬ p2589) ∨ p2545 ∨ (¬ p5201) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3516)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial33677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory22933 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule33677 (meaning t m 1985) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 3516) (meaning t m 3690) (meaning t m 5201) source

theorem rule33685 (p1998 p2766 p4041 p4118 : Prop) (h : (¬ p1998) ∨ (¬ p4118) ∨ p2766 ∨ p4041) : (¬ p1998) ∨ (p2766) ∨ (p4041) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial33685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2766) ∨ (meaning t m 4041) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory22941 t (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33685 (meaning t m 1998) (meaning t m 2766) (meaning t m 4041) (meaning t m 4118) source

theorem rule33686 (p2509 p3193 p3358 : Prop) (h : (¬ p3193) ∨ (¬ p3358) ∨ p2509) : (p2509) ∨ (¬ p3193) ∨ (¬ p3358) := by
  classical
  tauto

theorem initial33686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3358)) := by
  have source := ElevenTheory.theory22942 (m.theta 1 4) (m.theta 4 8) (m.theta 4 9)
  exact rule33686 (meaning t m 2509) (meaning t m 3193) (meaning t m 3358) source

theorem rule33687 (p2027 p2146 p2156 p2839 p3688 p4428 : Prop) (h : p2027 ∨ (¬ p3688) ∨ (¬ p2146) ∨ (¬ p2839) ∨ (¬ p4428) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2156) ∨ (¬ p2839) ∨ (¬ p3688) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial33687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory22943 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6)
  exact rule33687 (meaning t m 2027) (meaning t m 2146) (meaning t m 2156) (meaning t m 2839) (meaning t m 3688) (meaning t m 4428) source

theorem rule33691 (p1994 p2027 p2169 p2274 p2630 p3822 p3989 p4841 : Prop) (h : (¬ p3989) ∨ (¬ p1994) ∨ (¬ p2274) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p4841) ∨ p2169 ∨ (¬ p2630)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2630) ∨ (¬ p3822) ∨ (¬ p3989) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial33691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory22947 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule33691 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2630) (meaning t m 3822) (meaning t m 3989) (meaning t m 4841) source

theorem rule33697 (p4430 p4512 p4938 : Prop) (h : (¬ p4512) ∨ (¬ p4430) ∨ p4938) : (¬ p4430) ∨ (¬ p4512) ∨ (p4938) := by
  classical
  tauto

theorem initial33697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4430)) ∨ (¬ (meaning t m 4512)) ∨ (meaning t m 4938) := by
  have source := ElevenTheory.theory22953 (m.theta 1 5) (m.theta 1 6) (m.theta 1 9)
  exact rule33697 (meaning t m 4430) (meaning t m 4512) (meaning t m 4938) source

theorem rule33707 (p1995 p2914 p3742 p4811 : Prop) (h : p2914 ∨ (¬ p3742) ∨ (¬ p1995) ∨ p4811) : (¬ p1995) ∨ (p2914) ∨ (¬ p3742) ∨ (p4811) := by
  classical
  tauto

theorem initial33707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3742)) ∨ (meaning t m 4811) := by
  have source := ElevenTheory.theory22963 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule33707 (meaning t m 1995) (meaning t m 2914) (meaning t m 3742) (meaning t m 4811) source

theorem rule33710 (p1998 p2027 p2210 p2699 p2891 p3146 p3747 p4348 : Prop) (h : (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3747) ∨ p2699 ∨ p2027 ∨ (¬ p2210) ∨ (¬ p1998) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial33710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory22966 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33710 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2891) (meaning t m 3146) (meaning t m 3747) (meaning t m 4348) source

theorem rule33717 (p3051 p3370 p4034 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p3370) ∨ (¬ p4034) ∨ (¬ p3051)) : (¬ p3051) ∨ (¬ p3370) ∨ (¬ p4034) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial33717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory22973 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule33717 (meaning t m 3051) (meaning t m 3370) (meaning t m 4034) (meaning t m 4235) source

theorem rule33719 (p1989 p2027 p2191 p2764 p3156 p4208 p4322 : Prop) (h : (¬ p4208) ∨ p2027 ∨ (¬ p4322) ∨ p2764 ∨ (¬ p3156) ∨ (¬ p1989) ∨ (¬ p2191)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2191) ∨ (p2764) ∨ (¬ p3156) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial33719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory22975 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 9 10)
  exact rule33719 (meaning t m 1989) (meaning t m 2027) (meaning t m 2191) (meaning t m 2764) (meaning t m 3156) (meaning t m 4208) (meaning t m 4322) source

theorem rule33721 (p2027 p2499 p2584 p3654 p4137 p5194 : Prop) (h : p2027 ∨ (¬ p5194) ∨ (¬ p2499) ∨ (¬ p3654) ∨ (¬ p2584) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial33721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory22977 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9)
  exact rule33721 (meaning t m 2027) (meaning t m 2499) (meaning t m 2584) (meaning t m 3654) (meaning t m 4137) (meaning t m 5194) source

theorem rule33726 (p2027 p2177 p3093 p3115 p3309 p3497 p4032 p4524 p4905 : Prop) (h : (¬ p4905) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p4032) ∨ (¬ p3309) ∨ (¬ p4524) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3115) ∨ (¬ p3309) ∨ (¬ p3497) ∨ (¬ p4032) ∨ (¬ p4524) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial33726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory22982 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8)
  exact rule33726 (meaning t m 2027) (meaning t m 2177) (meaning t m 3093) (meaning t m 3115) (meaning t m 3309) (meaning t m 3497) (meaning t m 4032) (meaning t m 4524) (meaning t m 4905) source

theorem rule33730 (p2027 p2264 p2727 p3031 p3548 p4650 : Prop) (h : p2027 ∨ (¬ p4650) ∨ (¬ p2264) ∨ (¬ p3031) ∨ (¬ p2727) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial33730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory22986 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule33730 (meaning t m 2027) (meaning t m 2264) (meaning t m 2727) (meaning t m 3031) (meaning t m 3548) (meaning t m 4650) source

theorem rule33733 (p1997 p2027 p2323 p2331 p2668 p3989 p4110 : Prop) (h : (¬ p2331) ∨ (¬ p4110) ∨ p2027 ∨ p2323 ∨ (¬ p1997) ∨ (¬ p3989) ∨ (¬ p2668)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial33733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory22989 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule33733 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2668) (meaning t m 3989) (meaning t m 4110) source

theorem rule33735 (p2027 p2589 p2608 p2829 p3483 p3692 p3880 p4330 p5193 : Prop) (h : (¬ p5193) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2589) ∨ (¬ p4330) ∨ (¬ p3880) ∨ (¬ p2829) ∨ (¬ p2608) ∨ (¬ p3483)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial33735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory22991 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule33735 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2829) (meaning t m 3483) (meaning t m 3692) (meaning t m 3880) (meaning t m 4330) (meaning t m 5193) source

theorem rule33736 (p3551 p3575 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p3575) ∨ p3551) : (p3551) ∨ (¬ p3575) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial33736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3551) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory22992 (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule33736 (meaning t m 3551) (meaning t m 3575) (meaning t m 3644) source

theorem rule33739 (p2313 p2667 p3549 p4319 : Prop) (h : (¬ p2667) ∨ (¬ p4319) ∨ (¬ p2313) ∨ p3549) : (¬ p2313) ∨ (¬ p2667) ∨ (p3549) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial33739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 3549) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory22995 (m.theta 0 6) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule33739 (meaning t m 2313) (meaning t m 2667) (meaning t m 3549) (meaning t m 4319) source

theorem rule33740 (p2313 p2667 p3568 : Prop) (h : (¬ p2313) ∨ (¬ p2667) ∨ p3568) : (¬ p2313) ∨ (¬ p2667) ∨ (p3568) := by
  classical
  tauto

theorem initial33740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 3568) := by
  have source := ElevenTheory.theory22996 (m.theta 0 6) (m.theta 3 6) (m.theta 6 7)
  exact rule33740 (meaning t m 2313) (meaning t m 2667) (meaning t m 3568) source

theorem rule33741 (p1975 p2027 p2122 p2331 p2611 p3323 p3917 p4117 : Prop) (h : (¬ p4117) ∨ (¬ p1975) ∨ (¬ p3917) ∨ (¬ p2122) ∨ p2027 ∨ p2611 ∨ (¬ p2331) ∨ (¬ p3323)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2331) ∨ (p2611) ∨ (¬ p3323) ∨ (¬ p3917) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial33741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory22997 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule33741 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2331) (meaning t m 2611) (meaning t m 3323) (meaning t m 3917) (meaning t m 4117) source

theorem rule33746 (p2027 p2220 p2958 p3583 p3694 p4117 p4737 : Prop) (h : p2027 ∨ (¬ p3583) ∨ (¬ p4737) ∨ (¬ p3694) ∨ (¬ p4117) ∨ (¬ p2220) ∨ (¬ p2958)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p4117) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial33746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory23002 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8)
  exact rule33746 (meaning t m 2027) (meaning t m 2220) (meaning t m 2958) (meaning t m 3583) (meaning t m 3694) (meaning t m 4117) (meaning t m 4737) source

theorem rule33754 (p1997 p2027 p2764 p3156 p3880 p4208 p4322 : Prop) (h : (¬ p1997) ∨ (¬ p4208) ∨ (¬ p4322) ∨ p2764 ∨ (¬ p3880) ∨ p2027 ∨ (¬ p3156)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p3156) ∨ (¬ p3880) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial33754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory23010 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 9 10)
  exact rule33754 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 3156) (meaning t m 3880) (meaning t m 4208) (meaning t m 4322) source

theorem rule33761 (p1984 p2027 p2462 p2737 p3365 p3588 p3873 p3947 p4777 : Prop) (h : p2462 ∨ (¬ p4777) ∨ (¬ p3947) ∨ (¬ p3588) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873) ∨ p2027 ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3947) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial33761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory23017 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule33761 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2737) (meaning t m 3365) (meaning t m 3588) (meaning t m 3873) (meaning t m 3947) (meaning t m 4777) source

theorem rule33763 (p2027 p3016 p3367 p3688 p4342 p4750 : Prop) (h : (¬ p3367) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p4342) ∨ (¬ p4750) ∨ (¬ p3688)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial33763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory23019 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule33763 (meaning t m 2027) (meaning t m 3016) (meaning t m 3367) (meaning t m 3688) (meaning t m 4342) (meaning t m 4750) source

theorem rule33764 (p1984 p2027 p2245 p2766 p3027 p3414 p4118 p4360 : Prop) (h : (¬ p3027) ∨ p2766 ∨ (¬ p4118) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2245) ∨ (¬ p4360)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2766) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial33764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory23020 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule33764 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2766) (meaning t m 3027) (meaning t m 3414) (meaning t m 4118) (meaning t m 4360) source

theorem rule33767 (p3486 p4210 p4235 : Prop) (h : (¬ p4210) ∨ (¬ p3486) ∨ p4235) : (¬ p3486) ∨ (¬ p4210) ∨ (p4235) := by
  classical
  tauto

theorem initial33767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4210)) ∨ (meaning t m 4235) := by
  have source := ElevenTheory.theory23023 (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule33767 (meaning t m 3486) (meaning t m 4210) (meaning t m 4235) source

theorem rule33768 (p2027 p2553 p3016 p3822 p4750 p5220 : Prop) (h : (¬ p5220) ∨ (¬ p3822) ∨ (¬ p2553) ∨ (¬ p4750) ∨ (¬ p3016) ∨ p2027) : (p2027) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3822) ∨ (¬ p4750) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial33768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory23024 t (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule33768 (meaning t m 2027) (meaning t m 2553) (meaning t m 3016) (meaning t m 3822) (meaning t m 4750) (meaning t m 5220) source

theorem rule33772 (p2027 p2707 p3585 p3658 p4637 p5160 : Prop) (h : (¬ p4637) ∨ (¬ p3658) ∨ (¬ p3585) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p5160)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4637) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial33772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4637)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory23028 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 4 9)
  exact rule33772 (meaning t m 2027) (meaning t m 2707) (meaning t m 3585) (meaning t m 3658) (meaning t m 4637) (meaning t m 5160) source

theorem rule33775 (p3413 p4652 p4919 : Prop) (h : (¬ p4652) ∨ (¬ p3413) ∨ p4919) : (¬ p3413) ∨ (¬ p4652) ∨ (p4919) := by
  classical
  tauto

theorem initial33775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4652)) ∨ (meaning t m 4919) := by
  have source := ElevenTheory.theory23031 t (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule33775 (meaning t m 3413) (meaning t m 4652) (meaning t m 4919) source

theorem rule33782 (p1994 p2027 p2202 p2341 p2589 p3644 p3742 p5201 : Prop) (h : p2027 ∨ (¬ p3742) ∨ (¬ p1994) ∨ (¬ p5201) ∨ p2202 ∨ (¬ p3644) ∨ (¬ p2589) ∨ (¬ p2341)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial33782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory23038 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule33782 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2341) (meaning t m 2589) (meaning t m 3644) (meaning t m 3742) (meaning t m 5201) source

theorem rule33791 (p2027 p3125 p3989 p4118 p4345 p4771 : Prop) (h : (¬ p3125) ∨ (¬ p4345) ∨ (¬ p4771) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p4118)) : (p2027) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4118) ∨ (¬ p4345) ∨ (¬ p4771) := by
  classical
  tauto

theorem initial33791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4771)) := by
  have source := ElevenTheory.theory23047 t (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule33791 (meaning t m 2027) (meaning t m 3125) (meaning t m 3989) (meaning t m 4118) (meaning t m 4345) (meaning t m 4771) source

theorem rule33806 (p1982 p2027 p2177 p2997 p3146 p3858 p3941 p4446 p5590 : Prop) (h : (¬ p1982) ∨ (¬ p3146) ∨ (¬ p5590) ∨ p2997 ∨ (¬ p3941) ∨ (¬ p4446) ∨ (¬ p3858) ∨ p2027 ∨ (¬ p2177)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3146) ∨ (¬ p3858) ∨ (¬ p3941) ∨ (¬ p4446) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial33806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3858)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory23062 t (m.theta 0 8) (m.theta 1 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule33806 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3146) (meaning t m 3858) (meaning t m 3941) (meaning t m 4446) (meaning t m 5590) source

theorem rule33808 (p2027 p2230 p2780 p2982 p3367 p3759 p4347 p4358 p4450 p4734 : Prop) (h : p2027 ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p2982) ∨ (¬ p3759) ∨ (¬ p2230) ∨ (¬ p4734) ∨ (¬ p3367) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4450) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory23064 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule33808 (meaning t m 2027) (meaning t m 2230) (meaning t m 2780) (meaning t m 2982) (meaning t m 3367) (meaning t m 3759) (meaning t m 4347) (meaning t m 4358) (meaning t m 4450) (meaning t m 4734) source

theorem rule33810 (p3073 p4118 p5074 : Prop) (h : (¬ p4118) ∨ (¬ p3073) ∨ (¬ p5074)) : (¬ p3073) ∨ (¬ p4118) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial33810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory23066 (m.theta 1 8) (m.theta 3 8) (m.theta 8 9)
  exact rule33810 (meaning t m 3073) (meaning t m 4118) (meaning t m 5074) source

theorem rule33812 (p2027 p2191 p2192 p2220 p4110 p4539 : Prop) (h : p2027 ∨ (¬ p2191) ∨ (¬ p4539) ∨ (¬ p4110) ∨ (¬ p2192) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2220) ∨ (¬ p4110) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial33812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory23068 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule33812 (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2220) (meaning t m 4110) (meaning t m 4539) source

theorem rule33821 (p2027 p3422 p3888 p4153 p4700 p4753 p5717 : Prop) (h : (¬ p4153) ∨ (¬ p4700) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p3888) ∨ (¬ p5717) ∨ (¬ p3422)) : (p2027) ∨ (¬ p3422) ∨ (¬ p3888) ∨ (¬ p4153) ∨ (¬ p4700) ∨ (¬ p4753) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial33821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4753)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory23077 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 6 10)
  exact rule33821 (meaning t m 2027) (meaning t m 3422) (meaning t m 3888) (meaning t m 4153) (meaning t m 4700) (meaning t m 4753) (meaning t m 5717) source

theorem rule33825 (p2027 p2230 p2299 p2373 p2780 p3367 p3759 p3822 p4734 p4902 : Prop) (h : (¬ p2299) ∨ (¬ p3822) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p3367) ∨ (¬ p2373) ∨ (¬ p3759) ∨ (¬ p4902) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2780) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3822) ∨ (¬ p4734) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial33825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory23081 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule33825 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2373) (meaning t m 2780) (meaning t m 3367) (meaning t m 3759) (meaning t m 3822) (meaning t m 4734) (meaning t m 4902) source

theorem rule33830 (p3923 p3990 p4026 : Prop) (h : (¬ p4026) ∨ (¬ p3990) ∨ p3923) : (p3923) ∨ (¬ p3990) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial33830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3923) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory23086 (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule33830 (meaning t m 3923) (meaning t m 3990) (meaning t m 4026) source

theorem rule33841 (p2027 p2255 p2946 p2996 p3156 p3821 p3969 p4155 p4381 p5119 : Prop) (h : (¬ p4155) ∨ (¬ p4381) ∨ (¬ p3969) ∨ (¬ p2996) ∨ (¬ p3156) ∨ (¬ p3821) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3156) ∨ (¬ p3821) ∨ (¬ p3969) ∨ (¬ p4155) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial33841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory23097 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule33841 (meaning t m 2027) (meaning t m 2255) (meaning t m 2946) (meaning t m 2996) (meaning t m 3156) (meaning t m 3821) (meaning t m 3969) (meaning t m 4155) (meaning t m 4381) (meaning t m 5119) source

theorem rule33842 (p2027 p2341 p3553 p3646 p4333 p4558 p4988 : Prop) (h : (¬ p4988) ∨ (¬ p4333) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4558) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4333) ∨ (¬ p4558) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial33842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory23098 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule33842 (meaning t m 2027) (meaning t m 2341) (meaning t m 3553) (meaning t m 3646) (meaning t m 4333) (meaning t m 4558) (meaning t m 4988) source

theorem rule33843 (p2027 p2088 p3425 p3685 p3873 p4340 p5239 : Prop) (h : (¬ p3425) ∨ (¬ p5239) ∨ p2027 ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p2088) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3425) ∨ (¬ p3685) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p5239) := by
  classical
  tauto

theorem initial33843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5239)) := by
  have source := ElevenTheory.theory23099 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 8) (m.theta 2 7) (m.theta 2 8) (m.theta 8 9)
  exact rule33843 (meaning t m 2027) (meaning t m 2088) (meaning t m 3425) (meaning t m 3685) (meaning t m 3873) (meaning t m 4340) (meaning t m 5239) source

theorem rule33845 (p1996 p2027 p2881 p2938 p3548 p3631 p3947 : Prop) (h : p2938 ∨ (¬ p2881) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p1996) ∨ (¬ p3947) ∨ (¬ p3631)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial33845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory23101 t (m.theta 1 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33845 (meaning t m 1996) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3548) (meaning t m 3631) (meaning t m 3947) source

theorem rule33848 (p2748 p2797 p4154 : Prop) (h : (¬ p2748) ∨ (¬ p4154) ∨ (¬ p2797)) : (¬ p2748) ∨ (¬ p2797) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial33848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory23104 (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule33848 (meaning t m 2748) (meaning t m 2797) (meaning t m 4154) source

theorem rule33852 (p2027 p2311 p2881 p3551 p3654 p4275 p4624 : Prop) (h : (¬ p4624) ∨ (¬ p4275) ∨ (¬ p2311) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p3654) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3654) ∨ (¬ p4275) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial33852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory23108 t (m.theta 0 6) (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule33852 (meaning t m 2027) (meaning t m 2311) (meaning t m 2881) (meaning t m 3551) (meaning t m 3654) (meaning t m 4275) (meaning t m 4624) source

theorem rule33855 (p2707 p2743 p4357 : Prop) (h : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4357)) : (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial33855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory23111 (m.theta 1 2) (m.theta 2 3) (m.theta 2 7)
  exact rule33855 (meaning t m 2707) (meaning t m 2743) (meaning t m 4357) source

theorem rule33859 (p2027 p2363 p2373 p2406 p2780 p3379 p4078 p4340 p4433 p4736 : Prop) (h : (¬ p4340) ∨ (¬ p4078) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p2780) ∨ (¬ p2363) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p4433) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2780) ∨ (¬ p3379) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4433) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial33859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23115 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule33859 (meaning t m 2027) (meaning t m 2363) (meaning t m 2373) (meaning t m 2406) (meaning t m 2780) (meaning t m 3379) (meaning t m 4078) (meaning t m 4340) (meaning t m 4433) (meaning t m 4736) source

theorem rule33862 (p2641 p3848 p4421 : Prop) (h : (¬ p2641) ∨ (¬ p3848) ∨ (¬ p4421)) : (¬ p2641) ∨ (¬ p3848) ∨ (¬ p4421) := by
  classical
  tauto

theorem initial33862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4421)) := by
  have source := ElevenTheory.theory23118 (m.theta 1 3) (m.theta 3 6) (m.theta 3 9)
  exact rule33862 (meaning t m 2641) (meaning t m 3848) (meaning t m 4421) source

theorem rule33865 (p2532 p3105 p4340 p4359 : Prop) (h : (¬ p3105) ∨ (¬ p4340) ∨ (¬ p2532) ∨ (¬ p4359)) : (¬ p2532) ∨ (¬ p3105) ∨ (¬ p4340) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial33865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory23121 (m.theta 2 5) (m.theta 2 8) (m.theta 5 9) (m.theta 8 9)
  exact rule33865 (meaning t m 2532) (meaning t m 3105) (meaning t m 4340) (meaning t m 4359) source

theorem rule33866 (p2027 p2518 p2528 p3379 p3425 p3461 p4604 p4736 p5228 p5387 : Prop) (h : (¬ p4604) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3425) ∨ (¬ p5387) ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p5228) ∨ (¬ p2518) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p4736) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial33866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory23122 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 2 9) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule33866 (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 3379) (meaning t m 3425) (meaning t m 3461) (meaning t m 4604) (meaning t m 4736) (meaning t m 5228) (meaning t m 5387) source

theorem rule33869 (p2027 p2241 p3055 p3189 p3256 p3876 p4278 p4669 p4736 : Prop) (h : (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p4278) ∨ (¬ p3876) ∨ (¬ p3055) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial33869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23125 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule33869 (meaning t m 2027) (meaning t m 2241) (meaning t m 3055) (meaning t m 3189) (meaning t m 3256) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) (meaning t m 4736) source

theorem rule33871 (p2002 p2027 p2299 p2313 p2633 p3654 p3917 : Prop) (h : p2633 ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3654) ∨ (¬ p3917) ∨ (¬ p2313) ∨ (¬ p2002)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p3654) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial33871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory23127 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule33871 (meaning t m 2002) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2633) (meaning t m 3654) (meaning t m 3917) source

theorem rule33874 (p3690 p3744 p3872 p4396 : Prop) (h : (¬ p3744) ∨ (¬ p4396) ∨ (¬ p3872) ∨ p3690) : (p3690) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial33874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3690) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory23130 (m.theta 5 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule33874 (meaning t m 3690) (meaning t m 3744) (meaning t m 3872) (meaning t m 4396) source

theorem rule33875 (p3246 p3744 p3872 p4396 : Prop) (h : (¬ p3744) ∨ (¬ p4396) ∨ (¬ p3872) ∨ (¬ p3246)) : (¬ p3246) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial33875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory23131 (m.theta 5 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule33875 (meaning t m 3246) (meaning t m 3744) (meaning t m 3872) (meaning t m 4396) source

theorem rule33881 (p1975 p2027 p2295 p2383 p2622 p2743 p3324 p4869 p5016 : Prop) (h : (¬ p2383) ∨ (¬ p2743) ∨ (¬ p3324) ∨ p2622 ∨ (¬ p4869) ∨ (¬ p5016) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3324) ∨ (¬ p4869) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial33881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory23137 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule33881 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2383) (meaning t m 2622) (meaning t m 2743) (meaning t m 3324) (meaning t m 4869) (meaning t m 5016) source

theorem rule33883 (p2027 p2177 p2230 p2373 p3367 p3425 p3548 p3576 p3759 p4119 p4556 p4734 : Prop) (h : (¬ p3425) ∨ (¬ p4734) ∨ (¬ p3576) ∨ (¬ p3548) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p4556) ∨ (¬ p2230) ∨ (¬ p3759) ∨ (¬ p4119) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3759) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory23139 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule33883 (meaning t m 2027) (meaning t m 2177) (meaning t m 2230) (meaning t m 2373) (meaning t m 3367) (meaning t m 3425) (meaning t m 3548) (meaning t m 3576) (meaning t m 3759) (meaning t m 4119) (meaning t m 4556) (meaning t m 4734) source

theorem rule33890 (p1975 p2027 p2295 p3333 p3498 p3874 p4037 p4331 : Prop) (h : (¬ p3333) ∨ (¬ p4331) ∨ (¬ p3874) ∨ (¬ p4037) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ p3498) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p3333) ∨ (p3498) ∨ (¬ p3874) ∨ (¬ p4037) ∨ (¬ p4331) := by
  classical
  tauto

theorem initial33890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3333)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4331)) := by
  have source := ElevenTheory.theory23146 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule33890 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 3333) (meaning t m 3498) (meaning t m 3874) (meaning t m 4037) (meaning t m 4331) source

theorem rule33892 (p2307 p3204 p3309 : Prop) (h : (¬ p3204) ∨ (¬ p3309) ∨ p2307) : (p2307) ∨ (¬ p3204) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial33892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2307) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory23148 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule33892 (meaning t m 2307) (meaning t m 3204) (meaning t m 3309) source

theorem rule33903 (p1977 p2027 p2177 p2311 p2462 p2667 p3551 p4107 p4154 : Prop) (h : (¬ p2177) ∨ p2027 ∨ (¬ p4107) ∨ p2462 ∨ (¬ p2311) ∨ (¬ p2667) ∨ (¬ p1977) ∨ (¬ p4154) ∨ (¬ p3551)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (p2462) ∨ (¬ p2667) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial33903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory23159 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33903 (meaning t m 1977) (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2462) (meaning t m 2667) (meaning t m 3551) (meaning t m 4107) (meaning t m 4154) source

theorem rule33909 (p1986 p2027 p2138 p2598 p3128 p3744 p3758 : Prop) (h : (¬ p1986) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p2598) ∨ p3128 ∨ p2027 ∨ (¬ p2138)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (p3128) ∨ (¬ p3744) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial33909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory23165 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9)
  exact rule33909 (meaning t m 1986) (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 3128) (meaning t m 3744) (meaning t m 3758) source

theorem rule33912 (p2027 p2299 p2341 p3691 p3744 p3872 p4620 : Prop) (h : (¬ p2341) ∨ (¬ p3691) ∨ (¬ p3872) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p4620)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3691) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial33912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory23168 t (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule33912 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 3691) (meaning t m 3744) (meaning t m 3872) (meaning t m 4620) source

theorem rule33916 (p2027 p3040 p3073 p3553 p4189 p4348 : Prop) (h : (¬ p3040) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4189) ∨ (¬ p4348)) : (p2027) ∨ (¬ p3040) ∨ (¬ p3073) ∨ (¬ p3553) ∨ (¬ p4189) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial33916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3040)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory23172 t (m.theta 1 7) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule33916 (meaning t m 2027) (meaning t m 3040) (meaning t m 3073) (meaning t m 3553) (meaning t m 4189) (meaning t m 4348) source

theorem rule33918 (p2027 p2247 p2459 p2476 p2534 p2744 p3063 p3093 p3366 p3905 p4133 : Prop) (h : (¬ p4133) ∨ (¬ p3093) ∨ (¬ p2459) ∨ (¬ p3366) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p2247) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial33918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory23174 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33918 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2744) (meaning t m 3063) (meaning t m 3093) (meaning t m 3366) (meaning t m 3905) (meaning t m 4133) source

theorem rule33919 (p1983 p2027 p2449 p2881 p2997 p3685 p3941 p4275 p4325 p5612 : Prop) (h : (¬ p3685) ∨ p2997 ∨ (¬ p2881) ∨ (¬ p1983) ∨ (¬ p4325) ∨ (¬ p2449) ∨ (¬ p5612) ∨ p2027 ∨ (¬ p4275) ∨ (¬ p3941)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2881) ∨ (p2997) ∨ (¬ p3685) ∨ (¬ p3941) ∨ (¬ p4275) ∨ (¬ p4325) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial33919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory23175 t (m.theta 2 7) (m.theta 2 8) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule33919 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2881) (meaning t m 2997) (meaning t m 3685) (meaning t m 3941) (meaning t m 4275) (meaning t m 4325) (meaning t m 5612) source

theorem rule33921 (p2027 p2295 p2383 p2588 p3324 p3743 p3958 : Prop) (h : (¬ p2383) ∨ (¬ p3743) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2295) ∨ (¬ p3958) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2588) ∨ (¬ p3324) ∨ (¬ p3743) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial33921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory23177 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule33921 (meaning t m 2027) (meaning t m 2295) (meaning t m 2383) (meaning t m 2588) (meaning t m 3324) (meaning t m 3743) (meaning t m 3958) source

theorem rule33923 (p3093 p3399 p4105 : Prop) (h : (¬ p3399) ∨ (¬ p4105) ∨ p3093) : (p3093) ∨ (¬ p3399) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial33923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3093) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory23179 (m.theta 0 1) (m.theta 1 6) (m.theta 1 7)
  exact rule33923 (meaning t m 3093) (meaning t m 3399) (meaning t m 4105) source

theorem rule33926 (p2027 p2449 p3551 p3959 p4325 p4443 p5118 p5558 : Prop) (h : (¬ p2449) ∨ (¬ p3959) ∨ (¬ p5558) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p4325) ∨ p2027 ∨ (¬ p3551)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3551) ∨ (¬ p3959) ∨ (¬ p4325) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial33926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory23182 t (m.theta 0 7) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule33926 (meaning t m 2027) (meaning t m 2449) (meaning t m 3551) (meaning t m 3959) (meaning t m 4325) (meaning t m 4443) (meaning t m 5118) (meaning t m 5558) source

theorem rule33929 (p2027 p2528 p2668 p4037 p4171 p4384 : Prop) (h : p2027 ∨ (¬ p4037) ∨ (¬ p2668) ∨ (¬ p4171) ∨ (¬ p4384) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4171) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial33929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory23185 t (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule33929 (meaning t m 2027) (meaning t m 2528) (meaning t m 2668) (meaning t m 4037) (meaning t m 4171) (meaning t m 4384) source

theorem rule33932 (p1975 p2027 p2295 p2765 p3105 p3758 p4037 p5045 : Prop) (h : p2765 ∨ (¬ p2295) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p3758) ∨ (¬ p5045) ∨ (¬ p1975) ∨ (¬ p3105)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2765) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p4037) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial33932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory23188 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule33932 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2765) (meaning t m 3105) (meaning t m 3758) (meaning t m 4037) (meaning t m 5045) source

theorem rule33937 (p2027 p2318 p3631 p3821 p3918 p4358 p4452 p4501 : Prop) (h : (¬ p3821) ∨ (¬ p2318) ∨ (¬ p3918) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4452) ∨ (¬ p4501)) : (p2027) ∨ (¬ p2318) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p3918) ∨ (¬ p4358) ∨ (¬ p4452) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial33937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory23193 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule33937 (meaning t m 2027) (meaning t m 2318) (meaning t m 3631) (meaning t m 3821) (meaning t m 3918) (meaning t m 4358) (meaning t m 4452) (meaning t m 4501) source

theorem rule33938 (p2027 p2187 p2284 p2946 p3073 p3551 p4348 p4853 p4998 : Prop) (h : (¬ p4998) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p3073) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3551) ∨ (¬ p4853) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3073) ∨ (¬ p3551) ∨ (¬ p4348) ∨ (¬ p4853) ∨ (¬ p4998) := by
  classical
  tauto

theorem initial33938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4853)) ∨ (¬ (meaning t m 4998)) := by
  have source := ElevenTheory.theory23194 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33938 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2946) (meaning t m 3073) (meaning t m 3551) (meaning t m 4348) (meaning t m 4853) (meaning t m 4998) source

theorem rule33944 (p2417 p3570 p3657 p4001 : Prop) (h : (¬ p2417) ∨ (¬ p3570) ∨ (¬ p4001) ∨ (¬ p3657)) : (¬ p2417) ∨ (¬ p3570) ∨ (¬ p3657) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial33944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory23200 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33944 (meaning t m 2417) (meaning t m 3570) (meaning t m 3657) (meaning t m 4001) source

theorem rule33945 (p2027 p2459 p2717 p3544 p4261 p4794 : Prop) (h : (¬ p3544) ∨ (¬ p2459) ∨ (¬ p4794) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p4261)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4794) := by
  classical
  tauto

theorem initial33945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4794)) := by
  have source := ElevenTheory.theory23201 t (m.theta 1 7) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule33945 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 3544) (meaning t m 4261) (meaning t m 4794) source

theorem rule33947 (p2027 p3238 p3516 p3519 p3579 p3947 p4646 p5201 : Prop) (h : (¬ p3519) ∨ (¬ p3579) ∨ (¬ p5201) ∨ (¬ p3516) ∨ (¬ p3238) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p3947)) : (p2027) ∨ (¬ p3238) ∨ (¬ p3516) ∨ (¬ p3519) ∨ (¬ p3579) ∨ (¬ p3947) ∨ (¬ p4646) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial33947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory23203 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule33947 (meaning t m 2027) (meaning t m 3238) (meaning t m 3516) (meaning t m 3519) (meaning t m 3579) (meaning t m 3947) (meaning t m 4646) (meaning t m 5201) source

theorem rule33953 (p3834 p4366 p5357 : Prop) (h : (¬ p5357) ∨ (¬ p4366) ∨ p3834) : (p3834) ∨ (¬ p4366) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial33953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3834) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory23209 (m.theta 0 1) (m.theta 1 7) (m.theta 1 9)
  exact rule33953 (meaning t m 3834) (meaning t m 4366) (meaning t m 5357) source

theorem rule33954 (p1984 p2027 p2462 p3583 p3690 p3954 p4244 : Prop) (h : (¬ p4244) ∨ p2027 ∨ (¬ p3583) ∨ p2462 ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p3583) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial33954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory23210 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9)
  exact rule33954 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 3583) (meaning t m 3690) (meaning t m 3954) (meaning t m 4244) source

theorem rule33955 (p2027 p2246 p2284 p2717 p2744 p2946 p3125 p3366 p3551 p3820 p4324 p4621 : Prop) (h : (¬ p3820) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4324) ∨ (¬ p4621) ∨ (¬ p3125) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2717) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4324) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial33955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory23211 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule33955 (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2717) (meaning t m 2744) (meaning t m 2946) (meaning t m 3125) (meaning t m 3366) (meaning t m 3551) (meaning t m 3820) (meaning t m 4324) (meaning t m 4621) source

theorem rule33960 (p2027 p2248 p2274 p2284 p2717 p2946 p3548 p4366 p4477 : Prop) (h : (¬ p4366) ∨ (¬ p2717) ∨ (¬ p2248) ∨ (¬ p2274) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4477) ∨ (¬ p2946) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2717) ∨ (¬ p2946) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial33960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory23216 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule33960 (meaning t m 2027) (meaning t m 2248) (meaning t m 2274) (meaning t m 2284) (meaning t m 2717) (meaning t m 2946) (meaning t m 3548) (meaning t m 4366) (meaning t m 4477) source

theorem rule33964 (p2027 p2383 p2579 p3905 p3956 p3987 p4786 : Prop) (h : (¬ p2383) ∨ (¬ p4786) ∨ (¬ p3956) ∨ (¬ p3987) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2579) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p3987) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial33964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory23220 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 6 8)
  exact rule33964 (meaning t m 2027) (meaning t m 2383) (meaning t m 2579) (meaning t m 3905) (meaning t m 3956) (meaning t m 3987) (meaning t m 4786) source

theorem rule33967 (p2248 p2781 p3873 p3987 : Prop) (h : (¬ p3873) ∨ (¬ p3987) ∨ (¬ p2248) ∨ p2781) : (¬ p2248) ∨ (p2781) ∨ (¬ p3873) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial33967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2248)) ∨ (meaning t m 2781) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory23223 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 0 6)
  exact rule33967 (meaning t m 2248) (meaning t m 2781) (meaning t m 3873) (meaning t m 3987) source

theorem rule33975 (p2027 p2156 p2246 p2363 p2668 p2744 p2958 p3201 p3366 p3540 p3745 p3905 p4697 p5160 : Prop) (h : (¬ p3366) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2156) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4697) ∨ (¬ p2246) ∨ (¬ p3540) ∨ (¬ p5160) ∨ (¬ p2958) ∨ (¬ p3201) ∨ (¬ p3905)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3745) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial33975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory23231 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule33975 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2363) (meaning t m 2668) (meaning t m 2744) (meaning t m 2958) (meaning t m 3201) (meaning t m 3366) (meaning t m 3540) (meaning t m 3745) (meaning t m 3905) (meaning t m 4697) (meaning t m 5160) source

theorem rule33977 (p1988 p2027 p2611 p2696 p2797 p3323 p3461 : Prop) (h : (¬ p2696) ∨ p2611 ∨ (¬ p3323) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial33977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory23233 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule33977 (meaning t m 1988) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2797) (meaning t m 3323) (meaning t m 3461) source

theorem rule33979 (p2027 p2246 p2331 p2744 p3201 p3256 p3358 p3366 p3540 p3905 p4341 p4347 p4384 p5160 : Prop) (h : (¬ p3366) ∨ (¬ p3201) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2331) ∨ (¬ p3905) ∨ (¬ p4341) ∨ (¬ p3540) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p5160) ∨ (¬ p3358) ∨ (¬ p4384)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2744) ∨ (¬ p3201) ∨ (¬ p3256) ∨ (¬ p3358) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial33979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory23235 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule33979 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2744) (meaning t m 3201) (meaning t m 3256) (meaning t m 3358) (meaning t m 3366) (meaning t m 3540) (meaning t m 3905) (meaning t m 4341) (meaning t m 4347) (meaning t m 4384) (meaning t m 5160) source

theorem rule33981 (p1998 p2027 p2427 p2598 p2611 p2850 p2881 : Prop) (h : (¬ p1998) ∨ p2611 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2427)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial33981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory23237 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule33981 (meaning t m 1998) (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 2881) source

theorem rule33994 (p2027 p2246 p2383 p2589 p2744 p3323 p3324 p3366 p3690 p3695 p3905 p3987 p4244 p4621 : Prop) (h : p2027 ∨ (¬ p3695) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2589) ∨ (¬ p3324) ∨ (¬ p2383) ∨ (¬ p3987) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p3905) ∨ (¬ p4621) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2383) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p3695) ∨ (¬ p3905) ∨ (¬ p3987) ∨ (¬ p4244) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial33994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory23250 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule33994 (meaning t m 2027) (meaning t m 2246) (meaning t m 2383) (meaning t m 2589) (meaning t m 2744) (meaning t m 3323) (meaning t m 3324) (meaning t m 3366) (meaning t m 3690) (meaning t m 3695) (meaning t m 3905) (meaning t m 3987) (meaning t m 4244) (meaning t m 4621) source

theorem rule33999 (p3346 p3904 p4032 p4952 : Prop) (h : (¬ p3904) ∨ (¬ p4952) ∨ (¬ p4032) ∨ p3346) : (p3346) ∨ (¬ p3904) ∨ (¬ p4032) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial33999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3346) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory23255 (m.theta 0 4) (m.theta 0 5) (m.theta 4 9) (m.theta 5 9)
  exact rule33999 (meaning t m 3346) (meaning t m 3904) (meaning t m 4032) (meaning t m 4952) source

theorem rule34000 (p2027 p2589 p3166 p3256 p3266 p3695 p3905 p4244 p4786 p4831 p5660 : Prop) (h : (¬ p3695) ∨ (¬ p5660) ∨ (¬ p2589) ∨ (¬ p3905) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p3166) ∨ (¬ p4244) ∨ (¬ p3256) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3695) ∨ (¬ p3905) ∨ (¬ p4244) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial34000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory23256 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule34000 (meaning t m 2027) (meaning t m 2589) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3695) (meaning t m 3905) (meaning t m 4244) (meaning t m 4786) (meaning t m 4831) (meaning t m 5660) source

theorem rule34009 (p2027 p2341 p2839 p3548 p3759 p4400 p4884 p5201 : Prop) (h : (¬ p4884) ∨ p2027 ∨ (¬ p4400) ∨ (¬ p3548) ∨ (¬ p3759) ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2839) ∨ (¬ p3548) ∨ (¬ p3759) ∨ (¬ p4400) ∨ (¬ p4884) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial34009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4884)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory23265 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 5) (m.theta 7 8)
  exact rule34009 (meaning t m 2027) (meaning t m 2341) (meaning t m 2839) (meaning t m 3548) (meaning t m 3759) (meaning t m 4400) (meaning t m 4884) (meaning t m 5201) source

theorem rule34010 (p2027 p2341 p3452 p3545 p3548 p4376 p4400 : Prop) (h : (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3545) ∨ (¬ p4400) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3452)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3452) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p4376) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial34010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory23266 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 7 8)
  exact rule34010 (meaning t m 2027) (meaning t m 2341) (meaning t m 3452) (meaning t m 3545) (meaning t m 3548) (meaning t m 4376) (meaning t m 4400) source

theorem rule34012 (p2027 p2707 p2785 p3688 p3946 p4475 p4620 : Prop) (h : (¬ p3946) ∨ (¬ p2785) ∨ (¬ p2707) ∨ (¬ p4475) ∨ (¬ p4620) ∨ (¬ p3688) ∨ p2027) : (p2027) ∨ (¬ p2707) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4475) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial34012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory23268 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 9)
  exact rule34012 (meaning t m 2027) (meaning t m 2707) (meaning t m 2785) (meaning t m 3688) (meaning t m 3946) (meaning t m 4475) (meaning t m 4620) source

theorem rule34019 (p1983 p2027 p2247 p2744 p2938 p3333 p3346 p3347 p3399 p3631 p3684 p4235 p4257 : Prop) (h : p2938 ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3684) ∨ (¬ p3346) ∨ (¬ p3333) ∨ (¬ p3347) ∨ (¬ p2744) ∨ (¬ p4257) ∨ (¬ p1983) ∨ (¬ p3631) ∨ (¬ p2247) ∨ (¬ p3399)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (p2938) ∨ (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial34019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory23275 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule34019 (meaning t m 1983) (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 2938) (meaning t m 3333) (meaning t m 3346) (meaning t m 3347) (meaning t m 3399) (meaning t m 3631) (meaning t m 3684) (meaning t m 4235) (meaning t m 4257) source

theorem rule34021 (p2027 p2241 p2579 p3027 p3931 p4137 p4191 p4826 p5193 : Prop) (h : (¬ p3931) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p2241) ∨ (¬ p4191) ∨ (¬ p5193) ∨ (¬ p4137) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial34021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory23277 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule34021 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 3027) (meaning t m 3931) (meaning t m 4137) (meaning t m 4191) (meaning t m 4826) (meaning t m 5193) source

theorem rule34025 (p2406 p2518 p4607 : Prop) (h : (¬ p2518) ∨ (¬ p4607) ∨ p2406) : (p2406) ∨ (¬ p2518) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial34025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2406) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory23281 (m.theta 1 4) (m.theta 4 5) (m.theta 4 8)
  exact rule34025 (meaning t m 2406) (meaning t m 2518) (meaning t m 4607) source

theorem rule34026 (p2006 p2027 p2766 p2901 p3497 p3692 p4244 : Prop) (h : (¬ p2901) ∨ (¬ p4244) ∨ (¬ p3692) ∨ p2766 ∨ (¬ p2006) ∨ p2027 ∨ (¬ p3497)) : (¬ p2006) ∨ (p2027) ∨ (p2766) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial34026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory23282 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule34026 (meaning t m 2006) (meaning t m 2027) (meaning t m 2766) (meaning t m 2901) (meaning t m 3497) (meaning t m 3692) (meaning t m 4244) source

theorem rule34027 (p2027 p2246 p2651 p2744 p3083 p3366 p3425 p4149 p4324 p4381 p5119 : Prop) (h : (¬ p3425) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p3366) ∨ (¬ p4149) ∨ (¬ p2246) ∨ (¬ p5119) ∨ (¬ p3083) ∨ (¬ p2744) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4149) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial34027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory23283 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule34027 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 3083) (meaning t m 3366) (meaning t m 3425) (meaning t m 4149) (meaning t m 4324) (meaning t m 4381) (meaning t m 5119) source

theorem rule34029 (p2027 p2383 p2584 p2761 p3323 p3324 p3519 p3645 p4032 p4322 p4376 p4621 p4874 : Prop) (h : (¬ p3323) ∨ (¬ p4621) ∨ (¬ p3324) ∨ (¬ p2761) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p3645) ∨ (¬ p3519) ∨ (¬ p4874) ∨ (¬ p2584) ∨ (¬ p2383) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2761) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4376) ∨ (¬ p4621) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial34029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory23285 t (m.theta 0 4) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule34029 (meaning t m 2027) (meaning t m 2383) (meaning t m 2584) (meaning t m 2761) (meaning t m 3323) (meaning t m 3324) (meaning t m 3519) (meaning t m 3645) (meaning t m 4032) (meaning t m 4322) (meaning t m 4376) (meaning t m 4621) (meaning t m 4874) source

theorem rule34031 (p1988 p2027 p2114 p2331 p2737 p2811 p3323 p3461 : Prop) (h : (¬ p3323) ∨ (¬ p2737) ∨ (¬ p2331) ∨ (¬ p1988) ∨ (¬ p3461) ∨ p2027 ∨ p2114 ∨ (¬ p2811)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3323) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial34031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory23287 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule34031 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2331) (meaning t m 2737) (meaning t m 2811) (meaning t m 3323) (meaning t m 3461) source

theorem rule34036 (p2027 p2254 p2352 p2459 p2493 p3379 p3414 p3919 p4118 p4133 : Prop) (h : (¬ p2459) ∨ (¬ p3919) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2493) ∨ (¬ p3414) ∨ (¬ p3379) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial34036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory23292 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34036 (meaning t m 2027) (meaning t m 2254) (meaning t m 2352) (meaning t m 2459) (meaning t m 2493) (meaning t m 3379) (meaning t m 3414) (meaning t m 3919) (meaning t m 4118) (meaning t m 4133) source

theorem rule34037 (p2027 p2352 p2459 p2493 p3379 p3692 p4120 p4133 p4524 : Prop) (h : (¬ p3379) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p2352) ∨ (¬ p4133) ∨ (¬ p4524) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p4120)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4133) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial34037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory23293 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34037 (meaning t m 2027) (meaning t m 2352) (meaning t m 2459) (meaning t m 2493) (meaning t m 3379) (meaning t m 3692) (meaning t m 4120) (meaning t m 4133) (meaning t m 4524) source

theorem rule34043 (p2027 p3365 p3545 p4283 p4315 p4320 p4736 : Prop) (h : (¬ p4315) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3545) ∨ (¬ p3365) ∨ (¬ p4736) ∨ (¬ p4283)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3545) ∨ (¬ p4283) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23299 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7)
  exact rule34043 (meaning t m 2027) (meaning t m 3365) (meaning t m 3545) (meaning t m 4283) (meaning t m 4315) (meaning t m 4320) (meaning t m 4736) source

theorem rule34044 (p2027 p2761 p3073 p3449 p3452 p3645 p4032 p4322 p4376 p4669 p4874 : Prop) (h : (¬ p4669) ∨ (¬ p4874) ∨ (¬ p4322) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3645) ∨ (¬ p2761) ∨ (¬ p4032) ∨ (¬ p3452) ∨ (¬ p3449) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4376) ∨ (¬ p4669) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial34044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory23300 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 1 8) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34044 (meaning t m 2027) (meaning t m 2761) (meaning t m 3073) (meaning t m 3449) (meaning t m 3452) (meaning t m 3645) (meaning t m 4032) (meaning t m 4322) (meaning t m 4376) (meaning t m 4669) (meaning t m 4874) source

theorem rule34047 (p2027 p2707 p3434 p4242 p4668 p4800 : Prop) (h : p2027 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4668) ∨ (¬ p4800) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4242) ∨ (¬ p4668) ∨ (¬ p4800) := by
  classical
  tauto

theorem initial34047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4800)) := by
  have source := ElevenTheory.theory23303 t (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8) (m.theta 7 9)
  exact rule34047 (meaning t m 2027) (meaning t m 2707) (meaning t m 3434) (meaning t m 4242) (meaning t m 4668) (meaning t m 4800) source

end SunPrize.SMT
