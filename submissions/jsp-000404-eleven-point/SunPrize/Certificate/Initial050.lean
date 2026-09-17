import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory034
import SunPrize.Certificate.Theory035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule22129 (p2027 p2553 p3422 p3568 p4194 p4753 : Prop) (h : p2027 ∨ (¬ p3422) ∨ (¬ p4753) ∨ (¬ p3568) ∨ (¬ p2553) ∨ (¬ p4194)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3568) ∨ (¬ p4194) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial22129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory11385 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule22129 (meaning t m 2027) (meaning t m 2553) (meaning t m 3422) (meaning t m 3568) (meaning t m 4194) (meaning t m 4753) source

theorem rule22130 (p2027 p3227 p3355 p3540 p4107 p4712 p5362 : Prop) (h : (¬ p3540) ∨ p2027 ∨ (¬ p5362) ∨ (¬ p4107) ∨ (¬ p3355) ∨ (¬ p3227) ∨ (¬ p4712)) : (p2027) ∨ (¬ p3227) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4107) ∨ (¬ p4712) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial22130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory11386 t (m.theta 0 4) (m.theta 1 9) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule22130 (meaning t m 2027) (meaning t m 3227) (meaning t m 3355) (meaning t m 3540) (meaning t m 4107) (meaning t m 4712) (meaning t m 5362) source

theorem rule22131 (p2027 p3276 p4037 p4191 p4422 p4973 : Prop) (h : (¬ p3276) ∨ (¬ p4422) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p4973) ∨ (¬ p4191)) : (p2027) ∨ (¬ p3276) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial22131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory11387 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule22131 (meaning t m 2027) (meaning t m 3276) (meaning t m 4037) (meaning t m 4191) (meaning t m 4422) (meaning t m 4973) source

theorem rule22133 (p2027 p2319 p3516 p3549 p4107 p5022 : Prop) (h : (¬ p5022) ∨ (¬ p3549) ∨ (¬ p3516) ∨ (¬ p2319) ∨ (¬ p4107) ∨ p2027) : (p2027) ∨ (¬ p2319) ∨ (¬ p3516) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p5022) := by
  classical
  tauto

theorem initial22133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 5022)) := by
  have source := ElevenTheory.theory11389 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 7 9)
  exact rule22133 (meaning t m 2027) (meaning t m 2319) (meaning t m 3516) (meaning t m 3549) (meaning t m 4107) (meaning t m 5022) source

theorem rule22135 (p2027 p2619 p3680 p4334 p4509 p5025 p5387 : Prop) (h : (¬ p2619) ∨ (¬ p4334) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p5025) ∨ (¬ p4509) ∨ (¬ p5387)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3680) ∨ (¬ p4334) ∨ (¬ p4509) ∨ (¬ p5025) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial22135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 5025)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory11391 t (m.theta 2 5) (m.theta 2 9) (m.theta 5 6) (m.theta 5 8) (m.theta 5 9) (m.theta 9 10)
  exact rule22135 (meaning t m 2027) (meaning t m 2619) (meaning t m 3680) (meaning t m 4334) (meaning t m 4509) (meaning t m 5025) (meaning t m 5387) source

theorem rule22136 (p2027 p3063 p3549 p3550 p4260 p5559 : Prop) (h : (¬ p5559) ∨ (¬ p3550) ∨ (¬ p4260) ∨ (¬ p3063) ∨ (¬ p3549) ∨ p2027) : (p2027) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p4260) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial22136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory11392 t (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule22136 (meaning t m 2027) (meaning t m 3063) (meaning t m 3549) (meaning t m 3550) (meaning t m 4260) (meaning t m 5559) source

theorem rule22139 (p2027 p2177 p3093 p3309 p3365 p3497 p4315 p4736 p4905 : Prop) (h : p2027 ∨ (¬ p4905) ∨ (¬ p3497) ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p2177) ∨ (¬ p4736) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p4315) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial22139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory11395 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule22139 (meaning t m 2027) (meaning t m 2177) (meaning t m 3093) (meaning t m 3309) (meaning t m 3365) (meaning t m 3497) (meaning t m 4315) (meaning t m 4736) (meaning t m 4905) source

theorem rule22140 (p2027 p2138 p2459 p3399 p3527 p3744 p3758 p4604 p4736 : Prop) (h : (¬ p3527) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3399) ∨ (¬ p2459) ∨ (¬ p3758) ∨ (¬ p3744) ∨ (¬ p2138) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2459) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11396 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22140 (meaning t m 2027) (meaning t m 2138) (meaning t m 2459) (meaning t m 3399) (meaning t m 3527) (meaning t m 3744) (meaning t m 3758) (meaning t m 4604) (meaning t m 4736) source

theorem rule22144 (p2027 p2437 p3367 p3588 p4106 p4750 : Prop) (h : (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4106) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p4750)) : (p2027) ∨ (¬ p2437) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11400 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7)
  exact rule22144 (meaning t m 2027) (meaning t m 2437) (meaning t m 3367) (meaning t m 3588) (meaning t m 4106) (meaning t m 4750) source

theorem rule22148 (p2027 p2313 p3654 p3690 p4556 p4623 : Prop) (h : (¬ p4556) ∨ (¬ p3690) ∨ (¬ p2313) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p4623)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial22148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory11404 t (m.theta 0 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule22148 (meaning t m 2027) (meaning t m 2313) (meaning t m 3654) (meaning t m 3690) (meaning t m 4556) (meaning t m 4623) source

theorem rule22149 (p2313 p3654 p4025 : Prop) (h : (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4025)) : (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial22149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory11405 (m.theta 0 6) (m.theta 6 7) (m.theta 6 9)
  exact rule22149 (meaning t m 2313) (meaning t m 3654) (meaning t m 4025) source

theorem rule22150 (p1982 p2027 p2459 p2499 p2927 p2997 p3323 p3389 p3527 p3568 p4137 p5194 : Prop) (h : (¬ p2499) ∨ (¬ p3323) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p5194) ∨ (¬ p2927) ∨ (¬ p1982) ∨ p2997 ∨ (¬ p3527) ∨ (¬ p2459) ∨ (¬ p3568) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2927) ∨ (p2997) ∨ (¬ p3323) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3568) ∨ (¬ p4137) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2927)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11406 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 7) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22150 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2499) (meaning t m 2927) (meaning t m 2997) (meaning t m 3323) (meaning t m 3389) (meaning t m 3527) (meaning t m 3568) (meaning t m 4137) (meaning t m 5194) source

theorem rule22151 (p2027 p2254 p2298 p2797 p2963 p3399 p3527 p3570 p3572 p4556 : Prop) (h : (¬ p3570) ∨ (¬ p3399) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4556) ∨ (¬ p2298) ∨ (¬ p2797) ∨ (¬ p3572) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2298) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3572) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory11407 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22151 (meaning t m 2027) (meaning t m 2254) (meaning t m 2298) (meaning t m 2797) (meaning t m 2963) (meaning t m 3399) (meaning t m 3527) (meaning t m 3570) (meaning t m 3572) (meaning t m 4556) source

theorem rule22152 (p2027 p2307 p2657 p3568 p3987 p4975 : Prop) (h : (¬ p2657) ∨ (¬ p3987) ∨ (¬ p4975) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p3568)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2657) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial22152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory11408 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule22152 (meaning t m 2027) (meaning t m 2307) (meaning t m 2657) (meaning t m 3568) (meaning t m 3987) (meaning t m 4975) source

theorem rule22154 (p2027 p2417 p2665 p3389 p3947 p4112 : Prop) (h : (¬ p2417) ∨ (¬ p2665) ∨ (¬ p3947) ∨ (¬ p4112) ∨ p2027 ∨ (¬ p3389)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2665) ∨ (¬ p3389) ∨ (¬ p3947) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial22154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory11410 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule22154 (meaning t m 2027) (meaning t m 2417) (meaning t m 2665) (meaning t m 3389) (meaning t m 3947) (meaning t m 4112) source

theorem rule22155 (p2027 p2138 p2518 p2528 p3379 p3690 p4244 p4669 p4736 : Prop) (h : (¬ p4669) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2138) ∨ (¬ p3379) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11411 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22155 (meaning t m 2027) (meaning t m 2138) (meaning t m 2518) (meaning t m 2528) (meaning t m 3379) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) (meaning t m 4736) source

theorem rule22156 (p2027 p2138 p2241 p3189 p3256 p3690 p4244 p4669 p4736 : Prop) (h : (¬ p3256) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p4736) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11412 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22156 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 3189) (meaning t m 3256) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) (meaning t m 4736) source

theorem rule22157 (p2027 p2307 p2960 p2962 p3097 p3952 : Prop) (h : p2027 ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial22157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory11413 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule22157 (meaning t m 2027) (meaning t m 2307) (meaning t m 2960) (meaning t m 2962) (meaning t m 3097) (meaning t m 3952) source

theorem rule22159 (p2027 p2307 p2786 p3055 p3822 p5224 : Prop) (h : (¬ p3055) ∨ (¬ p5224) ∨ (¬ p2786) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3822) ∨ (¬ p5224) := by
  classical
  tauto

theorem initial22159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 5224)) := by
  have source := ElevenTheory.theory11415 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule22159 (meaning t m 2027) (meaning t m 2307) (meaning t m 2786) (meaning t m 3055) (meaning t m 3822) (meaning t m 5224) source

theorem rule22160 (p2027 p2138 p2417 p2922 p3379 p3692 p3694 p3950 p4736 : Prop) (h : (¬ p2922) ∨ (¬ p3950) ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p2417) ∨ (¬ p2138) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p3692)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11416 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22160 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 2922) (meaning t m 3379) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4736) source

theorem rule22165 (p2027 p2417 p2922 p3365 p3379 p3877 p3950 p4118 p4736 : Prop) (h : (¬ p4118) ∨ (¬ p3379) ∨ (¬ p3877) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4736) ∨ (¬ p3950) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11421 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22165 (meaning t m 2027) (meaning t m 2417) (meaning t m 2922) (meaning t m 3365) (meaning t m 3379) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4736) source

theorem rule22166 (p2027 p2307 p2962 p3549 p4120 p4507 p4516 : Prop) (h : (¬ p2962) ∨ (¬ p4120) ∨ (¬ p3549) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4516) ∨ (¬ p4507)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p4120) ∨ (¬ p4507) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial22166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory11422 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule22166 (meaning t m 2027) (meaning t m 2307) (meaning t m 2962) (meaning t m 3549) (meaning t m 4120) (meaning t m 4507) (meaning t m 4516) source

theorem rule22168 (p2307 p2584 p3389 p3921 : Prop) (h : (¬ p2584) ∨ (¬ p3921) ∨ (¬ p2307) ∨ p3389) : (¬ p2307) ∨ (¬ p2584) ∨ (p3389) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial22168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (meaning t m 3389) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory11424 (m.theta 0 4) (m.theta 0 6) (m.theta 4 7) (m.theta 6 7)
  exact rule22168 (meaning t m 2307) (meaning t m 2584) (meaning t m 3389) (meaning t m 3921) source

theorem rule22169 (p2027 p2363 p2383 p3692 p3988 p4489 : Prop) (h : (¬ p2383) ∨ p2027 ∨ (¬ p3988) ∨ (¬ p4489) ∨ (¬ p3692) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial22169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory11425 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule22169 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 3692) (meaning t m 3988) (meaning t m 4489) source

theorem rule22171 (p2027 p2122 p2598 p3549 p3953 p4375 p4737 : Prop) (h : (¬ p4375) ∨ (¬ p2598) ∨ (¬ p4737) ∨ (¬ p3549) ∨ (¬ p3953) ∨ p2027 ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2598) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4375) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11427 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule22171 (meaning t m 2027) (meaning t m 2122) (meaning t m 2598) (meaning t m 3549) (meaning t m 3953) (meaning t m 4375) (meaning t m 4737) source

theorem rule22173 (p2584 p3355 p3654 p4022 : Prop) (h : (¬ p4022) ∨ (¬ p2584) ∨ (¬ p3654) ∨ p3355) : (¬ p2584) ∨ (p3355) ∨ (¬ p3654) ∨ (¬ p4022) := by
  classical
  tauto

theorem initial22173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2584)) ∨ (meaning t m 3355) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4022)) := by
  have source := ElevenTheory.theory11429 (m.theta 0 4) (m.theta 0 6) (m.theta 4 9) (m.theta 6 9)
  exact rule22173 (meaning t m 2584) (meaning t m 3355) (meaning t m 3654) (meaning t m 4022) source

theorem rule22176 (p2027 p2187 p2590 p2982 p3956 p5046 : Prop) (h : (¬ p2187) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p2590) ∨ (¬ p3956) ∨ (¬ p5046)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2590) ∨ (¬ p2982) ∨ (¬ p3956) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11432 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8)
  exact rule22176 (meaning t m 2027) (meaning t m 2187) (meaning t m 2590) (meaning t m 2982) (meaning t m 3956) (meaning t m 5046) source

theorem rule22179 (p2027 p3256 p3956 p4341 p4347 p4976 : Prop) (h : (¬ p4341) ∨ (¬ p4976) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4347) ∨ (¬ p3956)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3956) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial22179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory11435 t (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule22179 (meaning t m 2027) (meaning t m 3256) (meaning t m 3956) (meaning t m 4341) (meaning t m 4347) (meaning t m 4976) source

theorem rule22182 (p2027 p3125 p3324 p3986 p4345 p5118 p5580 : Prop) (h : (¬ p3125) ∨ (¬ p5580) ∨ (¬ p4345) ∨ (¬ p3986) ∨ (¬ p3324) ∨ (¬ p5118) ∨ p2027) : (p2027) ∨ (¬ p3125) ∨ (¬ p3324) ∨ (¬ p3986) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial22182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory11438 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule22182 (meaning t m 2027) (meaning t m 3125) (meaning t m 3324) (meaning t m 3986) (meaning t m 4345) (meaning t m 5118) (meaning t m 5580) source

theorem rule22183 (p1975 p2027 p2295 p2383 p2545 p2657 p3324 p3987 : Prop) (h : p2027 ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p2295) ∨ (¬ p1975) ∨ (¬ p3987) ∨ (¬ p2657) ∨ p2545) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3324) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial22183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory11439 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22183 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2383) (meaning t m 2545) (meaning t m 2657) (meaning t m 3324) (meaning t m 3987) source

theorem rule22184 (p1975 p2027 p2114 p2295 p2383 p2737 p2811 p3324 p3987 : Prop) (h : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p3987) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p1975) ∨ (¬ p2811) ∨ (¬ p2737) ∨ p2114) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3324) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial22184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory11440 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22184 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2295) (meaning t m 2383) (meaning t m 2737) (meaning t m 2811) (meaning t m 3324) (meaning t m 3987) source

theorem rule22187 (p2027 p2248 p2295 p2383 p3324 p3585 p3876 p3954 p3987 p4712 : Prop) (h : (¬ p2248) ∨ (¬ p2295) ∨ (¬ p3987) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4712) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p3954) ∨ (¬ p3987) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial22187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11443 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule22187 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2383) (meaning t m 3324) (meaning t m 3585) (meaning t m 3876) (meaning t m 3954) (meaning t m 3987) (meaning t m 4712) source

theorem rule22201 (p1990 p2027 p2295 p2323 p2383 p3097 p3324 p3987 : Prop) (h : (¬ p3324) ∨ p2323 ∨ (¬ p3987) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p1990) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2383) ∨ (¬ p3097) ∨ (¬ p3324) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial22201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory11457 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22201 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2383) (meaning t m 3097) (meaning t m 3324) (meaning t m 3987) source

theorem rule22203 (p1983 p2027 p2295 p2323 p2383 p2396 p3324 p3987 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2383) ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p1983) ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2383) ∨ (¬ p2396) ∨ (¬ p3324) ∨ (¬ p3987) := by
  classical
  tauto

theorem initial22203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) := by
  have source := ElevenTheory.theory11459 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule22203 (meaning t m 1983) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2383) (meaning t m 2396) (meaning t m 3324) (meaning t m 3987) source

theorem rule22204 (p2027 p2589 p2696 p3005 p4009 p4322 p4729 p4948 p5119 : Prop) (h : (¬ p4009) ∨ (¬ p2589) ∨ (¬ p4948) ∨ (¬ p3005) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p4729) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4948) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial22204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory11460 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule22204 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 3005) (meaning t m 4009) (meaning t m 4322) (meaning t m 4729) (meaning t m 4948) (meaning t m 5119) source

theorem rule22205 (p2027 p2696 p2797 p3323 p3346 p3680 p4368 p4425 p4729 : Prop) (h : (¬ p3323) ∨ (¬ p4368) ∨ (¬ p3680) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3346) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4368) ∨ (¬ p4425) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial22205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory11461 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule22205 (meaning t m 2027) (meaning t m 2696) (meaning t m 2797) (meaning t m 3323) (meaning t m 3346) (meaning t m 3680) (meaning t m 4368) (meaning t m 4425) (meaning t m 4729) source

theorem rule22207 (p2027 p2982 p3570 p4135 p4235 p4668 : Prop) (h : (¬ p2982) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11463 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule22207 (meaning t m 2027) (meaning t m 2982) (meaning t m 3570) (meaning t m 4135) (meaning t m 4235) (meaning t m 4668) source

theorem rule22211 (p2027 p2254 p2417 p2922 p2952 p3379 p3570 p4320 p4668 : Prop) (h : (¬ p2254) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3379) ∨ (¬ p2952) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3570) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11467 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22211 (meaning t m 2027) (meaning t m 2254) (meaning t m 2417) (meaning t m 2922) (meaning t m 2952) (meaning t m 3379) (meaning t m 3570) (meaning t m 4320) (meaning t m 4668) source

theorem rule22216 (p2027 p2307 p2584 p2588 p3346 p5321 : Prop) (h : (¬ p2307) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2584) ∨ (¬ p5321) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3346) ∨ (¬ p5321) := by
  classical
  tauto

theorem initial22216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 5321)) := by
  have source := ElevenTheory.theory11472 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7)
  exact rule22216 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 3346) (meaning t m 5321) source

theorem rule22222 (p2027 p3266 p3609 p4322 p4335 p4746 : Prop) (h : (¬ p4335) ∨ (¬ p4322) ∨ (¬ p4746) ∨ (¬ p3609) ∨ p2027 ∨ (¬ p3266)) : (p2027) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4746) := by
  classical
  tauto

theorem initial22222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4746)) := by
  have source := ElevenTheory.theory11478 t (m.theta 2 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule22222 (meaning t m 2027) (meaning t m 3266) (meaning t m 3609) (meaning t m 4322) (meaning t m 4335) (meaning t m 4746) source

theorem rule22232 (p2027 p2307 p2584 p2839 p3549 p3759 p3953 p4884 : Prop) (h : (¬ p4884) ∨ (¬ p2584) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p3549) ∨ (¬ p2307) ∨ (¬ p3759) ∨ (¬ p3953)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2839) ∨ (¬ p3549) ∨ (¬ p3759) ∨ (¬ p3953) ∨ (¬ p4884) := by
  classical
  tauto

theorem initial22232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4884)) := by
  have source := ElevenTheory.theory11488 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 5) (m.theta 6 7)
  exact rule22232 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2839) (meaning t m 3549) (meaning t m 3759) (meaning t m 3953) (meaning t m 4884) source

theorem rule22233 (p2027 p2132 p2191 p2619 p4737 p4874 : Prop) (h : (¬ p4737) ∨ (¬ p2619) ∨ (¬ p2132) ∨ (¬ p4874) ∨ (¬ p2191) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p4737) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial22233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory11489 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule22233 (meaning t m 2027) (meaning t m 2132) (meaning t m 2191) (meaning t m 2619) (meaning t m 4737) (meaning t m 4874) source

theorem rule22234 (p2027 p2230 p2641 p2656 p3238 p3402 p4975 : Prop) (h : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p3402) ∨ (¬ p4975) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial22234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory11490 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule22234 (meaning t m 2027) (meaning t m 2230) (meaning t m 2641) (meaning t m 2656) (meaning t m 3238) (meaning t m 3402) (meaning t m 4975) source

theorem rule22235 (p2027 p2373 p2406 p2459 p3379 p3425 p3685 p4340 p4736 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p4736) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p2406) ∨ (¬ p3685) ∨ (¬ p3425) ∨ (¬ p2373) ∨ (¬ p4340) ∨ p2027) : (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial22235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory11491 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22235 (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 2459) (meaning t m 3379) (meaning t m 3425) (meaning t m 3685) (meaning t m 4340) (meaning t m 4736) (meaning t m 4902) source

theorem rule22236 (p1985 p2027 p2210 p2427 p2766 p2972 p3425 p3659 p4348 p4736 p4948 : Prop) (h : (¬ p4736) ∨ (¬ p4348) ∨ (¬ p4948) ∨ (¬ p2210) ∨ (¬ p1985) ∨ (¬ p2427) ∨ (¬ p2972) ∨ p2766 ∨ p2027 ∨ (¬ p3425) ∨ (¬ p3659)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2427) ∨ (p2766) ∨ (¬ p2972) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial22236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory11492 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22236 (meaning t m 1985) (meaning t m 2027) (meaning t m 2210) (meaning t m 2427) (meaning t m 2766) (meaning t m 2972) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) (meaning t m 4736) (meaning t m 4948) source

theorem rule22237 (p2027 p2406 p2982 p3379 p3425 p3659 p4348 p4450 p4736 : Prop) (h : (¬ p2406) ∨ (¬ p4450) ∨ (¬ p3379) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4736) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11493 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22237 (meaning t m 2027) (meaning t m 2406) (meaning t m 2982) (meaning t m 3379) (meaning t m 3425) (meaning t m 3659) (meaning t m 4348) (meaning t m 4450) (meaning t m 4736) source

theorem rule22240 (p2027 p2307 p2584 p2737 p3549 p3759 p3953 p4749 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p2584) ∨ (¬ p2737) ∨ (¬ p3759) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2737) ∨ (¬ p3549) ∨ (¬ p3759) ∨ (¬ p3953) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial22240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory11496 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 6 7)
  exact rule22240 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2737) (meaning t m 3549) (meaning t m 3759) (meaning t m 3953) (meaning t m 4749) source

theorem rule22241 (p2027 p2177 p2253 p2946 p3027 p3425 p3659 p3662 p4570 p4736 : Prop) (h : (¬ p2253) ∨ (¬ p2946) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p3027) ∨ (¬ p4570) ∨ (¬ p3425) ∨ (¬ p2177) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3662) ∨ (¬ p4570) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11497 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22241 (meaning t m 2027) (meaning t m 2177) (meaning t m 2253) (meaning t m 2946) (meaning t m 3027) (meaning t m 3425) (meaning t m 3659) (meaning t m 3662) (meaning t m 4570) (meaning t m 4736) source

theorem rule22244 (p2027 p3425 p3767 p4439 p4736 p5228 p5387 : Prop) (h : p2027 ∨ (¬ p3425) ∨ (¬ p4736) ∨ (¬ p4439) ∨ (¬ p5387) ∨ (¬ p5228) ∨ (¬ p3767)) : (p2027) ∨ (¬ p3425) ∨ (¬ p3767) ∨ (¬ p4439) ∨ (¬ p4736) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial22244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4439)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory11500 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 9) (m.theta 2 7) (m.theta 2 9) (m.theta 9 10)
  exact rule22244 (meaning t m 2027) (meaning t m 3425) (meaning t m 3767) (meaning t m 4439) (meaning t m 4736) (meaning t m 5228) (meaning t m 5387) source

theorem rule22247 (p1988 p2027 p2307 p2699 p3319 p3461 p3549 p5020 : Prop) (h : (¬ p3319) ∨ (¬ p3461) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p5020) ∨ p2699 ∨ (¬ p2307)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2307) ∨ (p2699) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3549) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial22247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory11503 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule22247 (meaning t m 1988) (meaning t m 2027) (meaning t m 2307) (meaning t m 2699) (meaning t m 3319) (meaning t m 3461) (meaning t m 3549) (meaning t m 5020) source

theorem rule22253 (p2027 p2210 p2891 p3246 p3365 p4037 p4195 p4625 p4736 : Prop) (h : (¬ p4037) ∨ (¬ p4625) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3246) ∨ (¬ p2210) ∨ (¬ p4195) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11509 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule22253 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3246) (meaning t m 3365) (meaning t m 4037) (meaning t m 4195) (meaning t m 4625) (meaning t m 4736) source

theorem rule22254 (p2027 p2459 p3365 p3399 p3527 p4037 p4195 p4604 p4736 : Prop) (h : (¬ p3399) ∨ (¬ p3365) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p4736) ∨ (¬ p3527) ∨ (¬ p4195) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11510 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22254 (meaning t m 2027) (meaning t m 2459) (meaning t m 3365) (meaning t m 3399) (meaning t m 3527) (meaning t m 4037) (meaning t m 4195) (meaning t m 4604) (meaning t m 4736) source

theorem rule22256 (p4343 p4811 p5214 : Prop) (h : (¬ p4811) ∨ (¬ p4343) ∨ p5214) : (¬ p4343) ∨ (¬ p4811) ∨ (p5214) := by
  classical
  tauto

theorem initial22256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4811)) ∨ (meaning t m 5214) := by
  have source := ElevenTheory.theory11512 t (m.theta 1 4) (m.theta 2 4) (m.theta 3 4)
  exact rule22256 (meaning t m 4343) (meaning t m 4811) (meaning t m 5214) source

theorem rule22258 (p2027 p2220 p3238 p3880 p4399 p5194 : Prop) (h : (¬ p5194) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p2220) ∨ (¬ p4399)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11514 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8)
  exact rule22258 (meaning t m 2027) (meaning t m 2220) (meaning t m 3238) (meaning t m 3880) (meaning t m 4399) (meaning t m 5194) source

theorem rule22259 (p2027 p2177 p2307 p3553 p4067 p4584 : Prop) (h : (¬ p2307) ∨ (¬ p4067) ∨ (¬ p4584) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4584) := by
  classical
  tauto

theorem initial22259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4584)) := by
  have source := ElevenTheory.theory11515 t (m.theta 0 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22259 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 3553) (meaning t m 4067) (meaning t m 4584) source

theorem rule22260 (p2027 p2230 p3238 p3591 p4079 p4257 p4866 : Prop) (h : (¬ p3238) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p4257) ∨ (¬ p4079) ∨ (¬ p3591) ∨ (¬ p4866)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4866) := by
  classical
  tauto

theorem initial22260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4866)) := by
  have source := ElevenTheory.theory11516 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5)
  exact rule22260 (meaning t m 2027) (meaning t m 2230) (meaning t m 3238) (meaning t m 3591) (meaning t m 4079) (meaning t m 4257) (meaning t m 4866) source

theorem rule22261 (p2027 p2138 p2241 p2449 p3027 p3692 p3694 p3950 p4736 : Prop) (h : (¬ p3950) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p2449) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11517 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22261 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4736) source

theorem rule22262 (p2027 p2274 p2313 p2982 p4031 p4198 p5046 : Prop) (h : (¬ p5046) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p4198) ∨ (¬ p4031) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2982) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11518 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule22262 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2982) (meaning t m 4031) (meaning t m 4198) (meaning t m 5046) source

theorem rule22263 (p2027 p2497 p2553 p2573 p3549 p5194 : Prop) (h : (¬ p2573) ∨ (¬ p5194) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3549) ∨ (¬ p2497)) : (p2027) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3549) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11519 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule22263 (meaning t m 2027) (meaning t m 2497) (meaning t m 2553) (meaning t m 2573) (meaning t m 3549) (meaning t m 5194) source

theorem rule22264 (p2027 p2088 p2482 p2509 p2534 p5194 : Prop) (h : (¬ p2509) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p5194)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11520 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9)
  exact rule22264 (meaning t m 2027) (meaning t m 2088) (meaning t m 2482) (meaning t m 2509) (meaning t m 2534) (meaning t m 5194) source

theorem rule22265 (p2027 p3821 p4063 p4191 p4621 p4828 : Prop) (h : p2027 ∨ (¬ p4191) ∨ (¬ p3821) ∨ (¬ p4828) ∨ (¬ p4063) ∨ (¬ p4621)) : (p2027) ∨ (¬ p3821) ∨ (¬ p4063) ∨ (¬ p4191) ∨ (¬ p4621) ∨ (¬ p4828) := by
  classical
  tauto

theorem initial22265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4828)) := by
  have source := ElevenTheory.theory11521 t (m.theta 0 7) (m.theta 6 9) (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule22265 (meaning t m 2027) (meaning t m 3821) (meaning t m 4063) (meaning t m 4191) (meaning t m 4621) (meaning t m 4828) source

theorem rule22268 (p2027 p2210 p2881 p2891 p3365 p3572 p3947 p4666 p4736 : Prop) (h : (¬ p3365) ∨ (¬ p3947) ∨ (¬ p3572) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p4666) ∨ (¬ p2881) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11524 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22268 (meaning t m 2027) (meaning t m 2210) (meaning t m 2881) (meaning t m 2891) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4666) (meaning t m 4736) source

theorem rule22269 (p2027 p2352 p2497 p2573 p3923 p5194 : Prop) (h : (¬ p2352) ∨ p2027 ∨ (¬ p2497) ∨ (¬ p2573) ∨ (¬ p5194) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2497) ∨ (¬ p2573) ∨ (¬ p3923) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11525 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule22269 (meaning t m 2027) (meaning t m 2352) (meaning t m 2497) (meaning t m 2573) (meaning t m 3923) (meaning t m 5194) source

theorem rule22271 (p2027 p2427 p2839 p3588 p3691 p3959 p4882 : Prop) (h : (¬ p3959) ∨ (¬ p2839) ∨ (¬ p3691) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3588) ∨ (¬ p4882)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p3691) ∨ (¬ p3959) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial22271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11527 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7)
  exact rule22271 (meaning t m 2027) (meaning t m 2427) (meaning t m 2839) (meaning t m 3588) (meaning t m 3691) (meaning t m 3959) (meaning t m 4882) source

theorem rule22272 (p2027 p2136 p2619 p2839 p4120 p4734 : Prop) (h : p2027 ∨ (¬ p4734) ∨ (¬ p2136) ∨ (¬ p2839) ∨ (¬ p4120) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p4120) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11528 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8)
  exact rule22272 (meaning t m 2027) (meaning t m 2136) (meaning t m 2619) (meaning t m 2839) (meaning t m 4120) (meaning t m 4734) source

theorem rule22273 (p2027 p2138 p2241 p2264 p3027 p3690 p4244 p4666 p4736 : Prop) (h : (¬ p4244) ∨ (¬ p3690) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2138) ∨ (¬ p4736) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4666)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11529 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22273 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2264) (meaning t m 3027) (meaning t m 3690) (meaning t m 4244) (meaning t m 4666) (meaning t m 4736) source

theorem rule22274 (p1992 p2027 p2396 p2997 p3238 p3690 p4235 p4257 : Prop) (h : p2997 ∨ (¬ p3238) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p4235) ∨ (¬ p4257) ∨ (¬ p3690) ∨ (¬ p2396)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3238) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial22274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory11530 t (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22274 (meaning t m 1992) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3238) (meaning t m 3690) (meaning t m 4235) (meaning t m 4257) source

theorem rule22275 (p2482 p4590 p5201 : Prop) (h : (¬ p5201) ∨ (¬ p4590) ∨ p2482) : (p2482) ∨ (¬ p4590) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial22275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2482) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory11531 (m.theta 0 4) (m.theta 0 7) (m.theta 0 8)
  exact rule22275 (meaning t m 2482) (meaning t m 4590) (meaning t m 5201) source

theorem rule22278 (p2027 p2187 p2230 p2563 p3365 p3568 p4079 p4195 p4405 p4736 : Prop) (h : (¬ p4195) ∨ (¬ p4079) ∨ (¬ p3568) ∨ (¬ p4405) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4079) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11534 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22278 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 3365) (meaning t m 3568) (meaning t m 4079) (meaning t m 4195) (meaning t m 4405) (meaning t m 4736) source

theorem rule22280 (p2027 p2230 p2254 p2518 p2797 p2963 p3238 p3877 p4079 p5012 : Prop) (h : (¬ p2963) ∨ (¬ p5012) ∨ (¬ p3877) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p2230) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3238) ∨ (¬ p3877) ∨ (¬ p4079) ∨ (¬ p5012) := by
  classical
  tauto

theorem initial22280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 5012)) := by
  have source := ElevenTheory.theory11536 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8)
  exact rule22280 (meaning t m 2027) (meaning t m 2230) (meaning t m 2254) (meaning t m 2518) (meaning t m 2797) (meaning t m 2963) (meaning t m 3238) (meaning t m 3877) (meaning t m 4079) (meaning t m 5012) source

theorem rule22286 (p2027 p2493 p2928 p3564 p3921 p4624 : Prop) (h : (¬ p3921) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p2493) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3564) ∨ (¬ p3921) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11542 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22286 (meaning t m 2027) (meaning t m 2493) (meaning t m 2928) (meaning t m 3564) (meaning t m 3921) (meaning t m 4624) source

theorem rule22288 (p2104 p2737 p3366 p4373 : Prop) (h : (¬ p2104) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4373)) : (¬ p2104) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4373) := by
  classical
  tauto

theorem initial22288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4373)) := by
  have source := ElevenTheory.theory11544 (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8)
  exact rule22288 (meaning t m 2104) (meaning t m 2737) (meaning t m 3366) (meaning t m 4373) source

theorem rule22289 (p2027 p2104 p2630 p2737 p3366 p4963 p5008 : Prop) (h : (¬ p2737) ∨ (¬ p2104) ∨ p2027 ∨ (¬ p5008) ∨ (¬ p2630) ∨ (¬ p3366) ∨ (¬ p4963)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4963) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial22289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4963)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11545 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8)
  exact rule22289 (meaning t m 2027) (meaning t m 2104) (meaning t m 2630) (meaning t m 2737) (meaning t m 3366) (meaning t m 4963) (meaning t m 5008) source

theorem rule22290 (p2027 p2307 p3688 p3822 p3987 p4117 p4737 : Prop) (h : (¬ p4737) ∨ (¬ p4117) ∨ (¬ p3822) ∨ (¬ p3987) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3987) ∨ (¬ p4117) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11546 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7)
  exact rule22290 (meaning t m 2027) (meaning t m 2307) (meaning t m 3688) (meaning t m 3822) (meaning t m 3987) (meaning t m 4117) (meaning t m 4737) source

theorem rule22291 (p2027 p2230 p2427 p2579 p3096 p4558 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11547 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule22291 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2579) (meaning t m 3096) (meaning t m 4558) source

theorem rule22292 (p2027 p2274 p2619 p3822 p4193 p4509 : Prop) (h : (¬ p2274) ∨ (¬ p4193) ∨ (¬ p3822) ∨ (¬ p4509) ∨ (¬ p2619) ∨ p2027) : (p2027) ∨ (¬ p2274) ∨ (¬ p2619) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory11548 t (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule22292 (meaning t m 2027) (meaning t m 2274) (meaning t m 2619) (meaning t m 3822) (meaning t m 4193) (meaning t m 4509) source

theorem rule22293 (p2027 p3115 p3413 p3574 p4031 p4032 p4715 : Prop) (h : (¬ p3115) ∨ (¬ p3413) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p3574) ∨ (¬ p4032) ∨ (¬ p4031)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p3574) ∨ (¬ p4031) ∨ (¬ p4032) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11549 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule22293 (meaning t m 2027) (meaning t m 3115) (meaning t m 3413) (meaning t m 3574) (meaning t m 4031) (meaning t m 4032) (meaning t m 4715) source

theorem rule22295 (p2027 p2341 p2751 p3027 p3659 p4066 p4357 : Prop) (h : (¬ p4066) ∨ (¬ p3027) ∨ (¬ p3659) ∨ (¬ p2341) ∨ (¬ p4357) ∨ p2027 ∨ (¬ p2751)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3659) ∨ (¬ p4066) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial22295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory11551 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule22295 (meaning t m 2027) (meaning t m 2341) (meaning t m 2751) (meaning t m 3027) (meaning t m 3659) (meaning t m 4066) (meaning t m 4357) source

theorem rule22297 (p2027 p2187 p2363 p4118 p4196 p4564 : Prop) (h : p2027 ∨ (¬ p4564) ∨ (¬ p4196) ∨ (¬ p4118) ∨ (¬ p2187) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial22297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory11553 t (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule22297 (meaning t m 2027) (meaning t m 2187) (meaning t m 2363) (meaning t m 4118) (meaning t m 4196) (meaning t m 4564) source

theorem rule22298 (p2027 p3222 p3742 p4107 p4116 p4451 p4712 : Prop) (h : (¬ p3222) ∨ p2027 ∨ (¬ p4116) ∨ (¬ p3742) ∨ (¬ p4712) ∨ (¬ p4107) ∨ (¬ p4451)) : (p2027) ∨ (¬ p3222) ∨ (¬ p3742) ∨ (¬ p4107) ∨ (¬ p4116) ∨ (¬ p4451) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial22298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11554 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule22298 (meaning t m 2027) (meaning t m 3222) (meaning t m 3742) (meaning t m 4107) (meaning t m 4116) (meaning t m 4451) (meaning t m 4712) source

theorem rule22299 (p2027 p2156 p2727 p2951 p3368 p4173 p4701 : Prop) (h : (¬ p2951) ∨ (¬ p2727) ∨ (¬ p2156) ∨ (¬ p4173) ∨ (¬ p4701) ∨ p2027 ∨ (¬ p3368)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2727) ∨ (¬ p2951) ∨ (¬ p3368) ∨ (¬ p4173) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11555 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule22299 (meaning t m 2027) (meaning t m 2156) (meaning t m 2727) (meaning t m 2951) (meaning t m 3368) (meaning t m 4173) (meaning t m 4701) source

theorem rule22300 (p2027 p2253 p2651 p2741 p4111 p4366 p4793 : Prop) (h : (¬ p2741) ∨ (¬ p2253) ∨ (¬ p4793) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4366) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial22300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory11556 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4)
  exact rule22300 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2741) (meaning t m 4111) (meaning t m 4366) (meaning t m 4793) source

theorem rule22301 (p2027 p2253 p2651 p2741 p3555 p4111 p4377 : Prop) (h : (¬ p3555) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4111) ∨ (¬ p2741)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p3555) ∨ (¬ p4111) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial22301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory11557 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4)
  exact rule22301 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2741) (meaning t m 3555) (meaning t m 4111) (meaning t m 4377) source

theorem rule22302 (p2027 p3038 p3527 p3553 p3662 p4112 p4701 : Prop) (h : (¬ p3553) ∨ (¬ p3038) ∨ (¬ p4112) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p4701) ∨ (¬ p3527)) : (p2027) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p3662) ∨ (¬ p4112) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11558 t (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule22302 (meaning t m 2027) (meaning t m 3038) (meaning t m 3527) (meaning t m 3553) (meaning t m 3662) (meaning t m 4112) (meaning t m 4701) source

theorem rule22303 (p2737 p3475 p3585 : Prop) (h : (¬ p3475) ∨ (¬ p3585) ∨ (¬ p2737)) : (¬ p2737) ∨ (¬ p3475) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial22303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory11559 (m.theta 1 2) (m.theta 2 3) (m.theta 2 4)
  exact rule22303 (meaning t m 2737) (meaning t m 3475) (meaning t m 3585) source

theorem rule22304 (p2027 p2132 p2192 p2534 p2663 p3125 p3172 p3363 p3585 p4330 p4418 p4437 p4737 : Prop) (h : (¬ p2192) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p3172) ∨ (¬ p4437) ∨ (¬ p2663) ∨ (¬ p4330) ∨ (¬ p3363) ∨ (¬ p2534) ∨ (¬ p4418) ∨ (¬ p2132) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2534) ∨ (¬ p2663) ∨ (¬ p3125) ∨ (¬ p3172) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4330) ∨ (¬ p4418) ∨ (¬ p4437) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11560 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22304 (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2534) (meaning t m 2663) (meaning t m 3125) (meaning t m 3172) (meaning t m 3363) (meaning t m 3585) (meaning t m 4330) (meaning t m 4418) (meaning t m 4437) (meaning t m 4737) source

theorem rule22305 (p2027 p2299 p3055 p3399 p3527 p3684 p4235 p4559 p4736 : Prop) (h : (¬ p4235) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p2299) ∨ (¬ p4736) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11561 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22305 (meaning t m 2027) (meaning t m 2299) (meaning t m 3055) (meaning t m 3399) (meaning t m 3527) (meaning t m 3684) (meaning t m 4235) (meaning t m 4559) (meaning t m 4736) source

theorem rule22306 (p2027 p2299 p3055 p3093 p3527 p3684 p4235 p4452 p4559 p4736 : Prop) (h : (¬ p4235) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p4736) ∨ (¬ p4452) ∨ (¬ p2299) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4452) ∨ (¬ p4559) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11562 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22306 (meaning t m 2027) (meaning t m 2299) (meaning t m 3055) (meaning t m 3093) (meaning t m 3527) (meaning t m 3684) (meaning t m 4235) (meaning t m 4452) (meaning t m 4559) (meaning t m 4736) source

theorem rule22307 (p3347 p3363 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p3347) ∨ p3363) : (¬ p3347) ∨ (p3363) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial22307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3347)) ∨ (meaning t m 3363) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory11563 (m.theta 0 4) (m.theta 1 4) (m.theta 2 4)
  exact rule22307 (meaning t m 3347) (meaning t m 3363) (meaning t m 4030) source

theorem rule22309 (p2027 p2299 p2717 p3238 p3452 p3471 p4235 p4559 p4733 : Prop) (h : (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3452) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3238) ∨ (¬ p2299) ∨ (¬ p4559)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11565 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22309 (meaning t m 2027) (meaning t m 2299) (meaning t m 2717) (meaning t m 3238) (meaning t m 3452) (meaning t m 3471) (meaning t m 4235) (meaning t m 4559) (meaning t m 4733) source

theorem rule22310 (p2027 p2641 p2749 p3365 p4195 p4734 : Prop) (h : (¬ p4195) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3365)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11566 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule22310 (meaning t m 2027) (meaning t m 2641) (meaning t m 2749) (meaning t m 3365) (meaning t m 4195) (meaning t m 4734) source

theorem rule22311 (p2004 p3360 p3399 p5207 : Prop) (h : p5207 ∨ p3360 ∨ (¬ p3399) ∨ (¬ p2004)) : (¬ p2004) ∨ (p3360) ∨ (¬ p3399) ∨ (p5207) := by
  classical
  tauto

theorem initial22311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3399)) ∨ (meaning t m 5207) := by
  have source := ElevenTheory.theory11567 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 7)
  exact rule22311 (meaning t m 2004) (meaning t m 3360) (meaning t m 3399) (meaning t m 5207) source

theorem rule22312 (p2027 p2210 p2245 p2749 p3027 p3414 p4877 : Prop) (h : (¬ p2749) ∨ p2027 ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p2245)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2245) ∨ (¬ p2749) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial22312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory11568 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 7)
  exact rule22312 (meaning t m 2027) (meaning t m 2210) (meaning t m 2245) (meaning t m 2749) (meaning t m 3027) (meaning t m 3414) (meaning t m 4877) source

theorem rule22313 (p1983 p2027 p2299 p2319 p2341 p2396 p2622 p2797 p3567 : Prop) (h : (¬ p2341) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p1983) ∨ p2027 ∨ p2622 ∨ (¬ p2396) ∨ (¬ p3567) ∨ (¬ p2797)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial22313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory11569 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22313 (meaning t m 1983) (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2396) (meaning t m 2622) (meaning t m 2797) (meaning t m 3567) source

theorem rule22314 (p2027 p2499 p2850 p3222 p4715 p5158 p5159 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p5159) ∨ (¬ p2850) ∨ (¬ p5158) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2850) ∨ (¬ p3222) ∨ (¬ p4715) ∨ (¬ p5158) ∨ (¬ p5159) := by
  classical
  tauto

theorem initial22314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5158)) ∨ (¬ (meaning t m 5159)) := by
  have source := ElevenTheory.theory11570 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 9) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule22314 (meaning t m 2027) (meaning t m 2499) (meaning t m 2850) (meaning t m 3222) (meaning t m 4715) (meaning t m 5158) (meaning t m 5159) source

theorem rule22315 (p2027 p2696 p2727 p2751 p3055 p4343 : Prop) (h : (¬ p2751) ∨ (¬ p4343) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3055) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial22315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory11571 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule22315 (meaning t m 2027) (meaning t m 2696) (meaning t m 2727) (meaning t m 2751) (meaning t m 3055) (meaning t m 4343) source

theorem rule22317 (p2245 p2663 p4108 : Prop) (h : (¬ p4108) ∨ (¬ p2663) ∨ p2245) : (p2245) ∨ (¬ p2663) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial22317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2245) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory11573 (m.theta 0 1) (m.theta 0 3) (m.theta 0 4)
  exact rule22317 (meaning t m 2245) (meaning t m 2663) (meaning t m 4108) source

theorem rule22320 (p2027 p2406 p2911 p2926 p3548 p4644 : Prop) (h : p2027 ∨ (¬ p3548) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p2406) ∨ (¬ p4644)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial22320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory11576 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule22320 (meaning t m 2027) (meaning t m 2406) (meaning t m 2911) (meaning t m 2926) (meaning t m 3548) (meaning t m 4644) source

theorem rule22321 (p2027 p2192 p2307 p3486 p4275 p4489 : Prop) (h : (¬ p2192) ∨ (¬ p4275) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4489)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2307) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial22321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory11577 t (m.theta 0 6) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule22321 (meaning t m 2027) (meaning t m 2192) (meaning t m 2307) (meaning t m 3486) (meaning t m 4275) (meaning t m 4489) source

theorem rule22322 (p2027 p2396 p3055 p3093 p3309 p3684 p3951 p4736 p4948 : Prop) (h : (¬ p4736) ∨ (¬ p3055) ∨ (¬ p4948) ∨ (¬ p3093) ∨ (¬ p3684) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3951)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p3951) ∨ (¬ p4736) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial22322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory11578 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule22322 (meaning t m 2027) (meaning t m 2396) (meaning t m 3055) (meaning t m 3093) (meaning t m 3309) (meaning t m 3684) (meaning t m 3951) (meaning t m 4736) (meaning t m 4948) source

theorem rule22324 (p2027 p2651 p2741 p2811 p2839 p4111 p5052 : Prop) (h : (¬ p2741) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p2651) ∨ (¬ p2811) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2839) ∨ (¬ p4111) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial22324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory11580 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4)
  exact rule22324 (meaning t m 2027) (meaning t m 2651) (meaning t m 2741) (meaning t m 2811) (meaning t m 2839) (meaning t m 4111) (meaning t m 5052) source

theorem rule22326 (p3461 p3707 p5148 : Prop) (h : (¬ p3707) ∨ (¬ p5148) ∨ p3461) : (p3461) ∨ (¬ p3707) ∨ (¬ p5148) := by
  classical
  tauto

theorem initial22326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3461) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 5148)) := by
  have source := ElevenTheory.theory11582 (m.theta 1 9) (m.theta 6 9) (m.theta 9 10)
  exact rule22326 (meaning t m 3461) (meaning t m 3707) (meaning t m 5148) source

theorem rule22327 (p2027 p2307 p2459 p3055 p3527 p3684 p4427 p4736 p4948 p5020 p5059 : Prop) (h : p2027 ∨ (¬ p5059) ∨ (¬ p4427) ∨ (¬ p4948) ∨ (¬ p2307) ∨ (¬ p4736) ∨ (¬ p3527) ∨ (¬ p2459) ∨ (¬ p3684) ∨ (¬ p5020) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4427) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5020) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial22327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5020)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory11583 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule22327 (meaning t m 2027) (meaning t m 2307) (meaning t m 2459) (meaning t m 3055) (meaning t m 3527) (meaning t m 3684) (meaning t m 4427) (meaning t m 4736) (meaning t m 4948) (meaning t m 5020) (meaning t m 5059) source

theorem rule22332 (p1977 p2287 p2745 p4195 : Prop) (h : p2287 ∨ (¬ p4195) ∨ (¬ p1977) ∨ p2745) : (¬ p1977) ∨ (p2287) ∨ (p2745) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial22332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2287) ∨ (meaning t m 2745) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory11588 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule22332 (meaning t m 1977) (meaning t m 2287) (meaning t m 2745) (meaning t m 4195) source

theorem rule22339 (p2027 p2191 p2192 p2383 p4489 p4506 : Prop) (h : (¬ p2383) ∨ (¬ p4506) ∨ (¬ p4489) ∨ (¬ p2192) ∨ (¬ p2191) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2383) ∨ (¬ p4489) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial22339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 4489)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory11595 t (m.theta 0 6) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule22339 (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2383) (meaning t m 4489) (meaning t m 4506) source

theorem rule22341 (p2027 p2651 p2963 p3083 p4389 p4598 : Prop) (h : (¬ p3083) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4598) ∨ (¬ p4389)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3083) ∨ (¬ p4389) ∨ (¬ p4598) := by
  classical
  tauto

theorem initial22341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4598)) := by
  have source := ElevenTheory.theory11597 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8)
  exact rule22341 (meaning t m 2027) (meaning t m 2651) (meaning t m 2963) (meaning t m 3083) (meaning t m 4389) (meaning t m 4598) source

theorem rule22344 (p2027 p2210 p2534 p2891 p3055 p3246 p3874 p3950 p4736 : Prop) (h : (¬ p3950) ∨ (¬ p3246) ∨ (¬ p3055) ∨ (¬ p4736) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p2210) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2534) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11600 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22344 (meaning t m 2027) (meaning t m 2210) (meaning t m 2534) (meaning t m 2891) (meaning t m 3055) (meaning t m 3246) (meaning t m 3874) (meaning t m 3950) (meaning t m 4736) source

theorem rule22346 (p3540 p3759 p3876 : Prop) (h : (¬ p3876) ∨ (¬ p3759) ∨ p3540) : (p3540) ∨ (¬ p3759) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial22346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3540) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory11602 (m.theta 0 4) (m.theta 2 4) (m.theta 4 7)
  exact rule22346 (meaning t m 3540) (meaning t m 3759) (meaning t m 3876) source

theorem rule22348 (p2027 p2156 p2190 p3055 p3146 p3644 p3876 p4133 p4172 p4347 p4736 : Prop) (h : (¬ p3876) ∨ (¬ p3055) ∨ (¬ p2156) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p2190) ∨ (¬ p4347) ∨ (¬ p3146) ∨ (¬ p4172) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4172) ∨ (¬ p4347) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11604 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22348 (meaning t m 2027) (meaning t m 2156) (meaning t m 2190) (meaning t m 3055) (meaning t m 3146) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) (meaning t m 4172) (meaning t m 4347) (meaning t m 4736) source

theorem rule22349 (p2027 p2891 p3989 p4140 p4173 p4501 : Prop) (h : (¬ p4173) ∨ (¬ p4140) ∨ (¬ p4501) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2891)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3989) ∨ (¬ p4140) ∨ (¬ p4173) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11605 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule22349 (meaning t m 2027) (meaning t m 2891) (meaning t m 3989) (meaning t m 4140) (meaning t m 4173) (meaning t m 4501) source

theorem rule22351 (p2027 p2187 p2192 p2210 p3055 p3644 p3876 p4133 p4736 : Prop) (h : (¬ p3876) ∨ (¬ p3055) ∨ (¬ p2210) ∨ (¬ p3644) ∨ (¬ p4736) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11607 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule22351 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 3055) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) (meaning t m 4736) source

theorem rule22352 (p2027 p2156 p2166 p3055 p3644 p3876 p4172 p4173 p4736 p4902 : Prop) (h : (¬ p4172) ∨ (¬ p3644) ∨ (¬ p4902) ∨ (¬ p3876) ∨ (¬ p3055) ∨ (¬ p2166) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial22352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory11608 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule22352 (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 3055) (meaning t m 3644) (meaning t m 3876) (meaning t m 4172) (meaning t m 4173) (meaning t m 4736) (meaning t m 4902) source

theorem rule22353 (p2027 p2156 p2891 p2911 p3425 p3659 p4172 p4173 p4647 p4736 : Prop) (h : (¬ p3659) ∨ (¬ p2891) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p4172) ∨ (¬ p4736) ∨ (¬ p2911) ∨ (¬ p4647) ∨ (¬ p2156) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2891) ∨ (¬ p2911) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4647) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11609 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 7) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule22353 (meaning t m 2027) (meaning t m 2156) (meaning t m 2891) (meaning t m 2911) (meaning t m 3425) (meaning t m 3659) (meaning t m 4172) (meaning t m 4173) (meaning t m 4647) (meaning t m 4736) source

theorem rule22355 (p2027 p2383 p3055 p3319 p3876 p3923 p4278 p4621 p4736 p5020 : Prop) (h : (¬ p5020) ∨ (¬ p4621) ∨ (¬ p3319) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p4278) ∨ (¬ p3055) ∨ (¬ p4736) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3319) ∨ (¬ p3876) ∨ (¬ p3923) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4736) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial22355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory11611 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule22355 (meaning t m 2027) (meaning t m 2383) (meaning t m 3055) (meaning t m 3319) (meaning t m 3876) (meaning t m 3923) (meaning t m 4278) (meaning t m 4621) (meaning t m 4736) (meaning t m 5020) source

theorem rule22356 (p2027 p2811 p2946 p3156 p3745 p4195 p4509 : Prop) (h : (¬ p2811) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p4509) ∨ (¬ p2946) ∨ (¬ p3745) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory11612 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8)
  exact rule22356 (meaning t m 2027) (meaning t m 2811) (meaning t m 2946) (meaning t m 3156) (meaning t m 3745) (meaning t m 4195) (meaning t m 4509) source

theorem rule22357 (p2027 p2396 p2534 p3055 p3093 p3309 p3874 p3950 p4736 : Prop) (h : (¬ p3950) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p4736) ∨ (¬ p3309) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11613 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22357 (meaning t m 2027) (meaning t m 2396) (meaning t m 2534) (meaning t m 3055) (meaning t m 3093) (meaning t m 3309) (meaning t m 3874) (meaning t m 3950) (meaning t m 4736) source

theorem rule22358 (p2027 p2156 p2960 p2992 p3745 p4154 : Prop) (h : (¬ p2156) ∨ (¬ p4154) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p2960) ∨ p2027) : (p2027) ∨ (¬ p2156) ∨ (¬ p2960) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial22358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory11614 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule22358 (meaning t m 2027) (meaning t m 2156) (meaning t m 2960) (meaning t m 2992) (meaning t m 3745) (meaning t m 4154) source

theorem rule22360 (p2027 p3276 p4110 p4322 p4449 p5046 : Prop) (h : (¬ p5046) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4449) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3276) ∨ (¬ p4110) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4449)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11616 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule22360 (meaning t m 2027) (meaning t m 3276) (meaning t m 4110) (meaning t m 4322) (meaning t m 4449) (meaning t m 5046) source

theorem rule22361 (p2027 p2449 p3822 p4107 p4156 p4843 : Prop) (h : p2027 ∨ (¬ p4843) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p3822) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial22361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory11617 t (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22361 (meaning t m 2027) (meaning t m 2449) (meaning t m 3822) (meaning t m 4107) (meaning t m 4156) (meaning t m 4843) source

theorem rule22362 (p2027 p2132 p2860 p4173 p4737 p4874 : Prop) (h : (¬ p4737) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p2132) ∨ (¬ p4874) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p4173) ∨ (¬ p4737) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial22362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory11618 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule22362 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 4173) (meaning t m 4737) (meaning t m 4874) source

theorem rule22363 (p2027 p2088 p2788 p4114 p4347 p4358 : Prop) (h : (¬ p4114) ∨ (¬ p2088) ∨ (¬ p2788) ∨ (¬ p4358) ∨ (¬ p4347) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p2788) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial22363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2788)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory11619 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule22363 (meaning t m 2027) (meaning t m 2088) (meaning t m 2788) (meaning t m 4114) (meaning t m 4347) (meaning t m 4358) source

theorem rule22364 (p2027 p2518 p2528 p2780 p3379 p3822 p4107 p4669 p4736 : Prop) (h : (¬ p3379) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2780) ∨ (¬ p4736) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2780) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11620 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22364 (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2780) (meaning t m 3379) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) (meaning t m 4736) source

theorem rule22366 (p2027 p3027 p3662 p3952 p4333 p4558 : Prop) (h : (¬ p4333) ∨ (¬ p3027) ∨ (¬ p3952) ∨ (¬ p3662) ∨ (¬ p4558) ∨ p2027) : (p2027) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4333) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11622 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22366 (meaning t m 2027) (meaning t m 3027) (meaning t m 3662) (meaning t m 3952) (meaning t m 4333) (meaning t m 4558) source

theorem rule22367 (p2027 p2331 p3172 p3309 p4319 p4501 p4769 : Prop) (h : (¬ p3309) ∨ (¬ p4769) ∨ (¬ p3172) ∨ (¬ p4319) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p4319) ∨ (¬ p4501) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial22367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory11623 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule22367 (meaning t m 2027) (meaning t m 2331) (meaning t m 3172) (meaning t m 3309) (meaning t m 4319) (meaning t m 4501) (meaning t m 4769) source

theorem rule22368 (p2027 p2459 p2911 p3955 p4347 p4712 : Prop) (h : (¬ p3955) ∨ (¬ p4712) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial22368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11624 t (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22368 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3955) (meaning t m 4347) (meaning t m 4712) source

theorem rule22370 (p2027 p2210 p2891 p3055 p3246 p3644 p3876 p4668 p4736 : Prop) (h : (¬ p2210) ∨ (¬ p4668) ∨ (¬ p3644) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11626 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22370 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3055) (meaning t m 3246) (meaning t m 3644) (meaning t m 3876) (meaning t m 4668) (meaning t m 4736) source

theorem rule22371 (p2027 p2579 p3389 p3956 p4501 p4710 : Prop) (h : (¬ p4501) ∨ (¬ p2579) ∨ (¬ p4710) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p3956)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial22371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory11627 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule22371 (meaning t m 2027) (meaning t m 2579) (meaning t m 3389) (meaning t m 3956) (meaning t m 4501) (meaning t m 4710) source

theorem rule22372 (p2027 p2138 p3063 p3093 p3979 p4322 p4385 p4736 p5119 : Prop) (h : (¬ p4736) ∨ (¬ p2138) ∨ (¬ p3093) ∨ (¬ p4322) ∨ (¬ p3063) ∨ (¬ p3979) ∨ (¬ p4385) ∨ (¬ p5119) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4736) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial22372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory11628 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule22372 (meaning t m 2027) (meaning t m 2138) (meaning t m 3063) (meaning t m 3093) (meaning t m 3979) (meaning t m 4322) (meaning t m 4385) (meaning t m 4736) (meaning t m 5119) source

theorem rule22374 (p2027 p3570 p3680 p4192 p4381 p4668 : Prop) (h : p2027 ∨ (¬ p4668) ∨ (¬ p4192) ∨ (¬ p3570) ∨ (¬ p3680) ∨ (¬ p4381)) : (p2027) ∨ (¬ p3570) ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11630 t (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule22374 (meaning t m 2027) (meaning t m 3570) (meaning t m 3680) (meaning t m 4192) (meaning t m 4381) (meaning t m 4668) source

theorem rule22375 (p2027 p2255 p2331 p2363 p2957 p3063 p3556 p3662 p3690 p4319 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3556) ∨ (¬ p2255) ∨ (¬ p2363) ∨ (¬ p4319) ∨ (¬ p2331) ∨ (¬ p3063)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2957) ∨ (¬ p3063) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4319) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial22375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory11631 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22375 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2363) (meaning t m 2957) (meaning t m 3063) (meaning t m 3556) (meaning t m 3662) (meaning t m 3690) (meaning t m 4319) (meaning t m 4669) source

theorem rule22376 (p2027 p3192 p3276 p3644 p4381 p4668 : Prop) (h : (¬ p3276) ∨ (¬ p3192) ∨ (¬ p4381) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p4668)) : (p2027) ∨ (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3644) ∨ (¬ p4381) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11632 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule22376 (meaning t m 2027) (meaning t m 3192) (meaning t m 3276) (meaning t m 3644) (meaning t m 4381) (meaning t m 4668) source

theorem rule22377 (p2027 p3212 p3556 p3570 p4135 p4668 : Prop) (h : (¬ p3556) ∨ (¬ p4135) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3570) ∨ (¬ p3212)) : (p2027) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4135) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11633 t (m.theta 0 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule22377 (meaning t m 2027) (meaning t m 3212) (meaning t m 3556) (meaning t m 3570) (meaning t m 4135) (meaning t m 4668) source

theorem rule22378 (p2027 p2406 p2497 p3564 p4026 p4715 : Prop) (h : (¬ p2497) ∨ (¬ p2406) ∨ (¬ p3564) ∨ (¬ p4715) ∨ (¬ p4026) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p3564) ∨ (¬ p4026) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11634 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule22378 (meaning t m 2027) (meaning t m 2406) (meaning t m 2497) (meaning t m 3564) (meaning t m 4026) (meaning t m 4715) source

theorem rule22381 (p2027 p2138 p2493 p3379 p3564 p3692 p3694 p4330 p4736 : Prop) (h : p2027 ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p3379) ∨ (¬ p2138) ∨ (¬ p2493) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11637 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule22381 (meaning t m 2027) (meaning t m 2138) (meaning t m 2493) (meaning t m 3379) (meaning t m 3564) (meaning t m 3692) (meaning t m 3694) (meaning t m 4330) (meaning t m 4736) source

theorem rule22387 (p2027 p2528 p3309 p4261 p4371 p4432 p4501 : Prop) (h : (¬ p3309) ∨ (¬ p4261) ∨ (¬ p2528) ∨ (¬ p4371) ∨ (¬ p4432) ∨ p2027 ∨ (¬ p4501)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3309) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11643 t (m.theta 1 6) (m.theta 1 8) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule22387 (meaning t m 2027) (meaning t m 2528) (meaning t m 3309) (meaning t m 4261) (meaning t m 4371) (meaning t m 4432) (meaning t m 4501) source

theorem rule22388 (p2497 p3226 p5153 : Prop) (h : p2497 ∨ (¬ p5153) ∨ (¬ p3226)) : (p2497) ∨ (¬ p3226) ∨ (¬ p5153) := by
  classical
  tauto

theorem initial22388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2497) ∨ (¬ (meaning t m 3226)) ∨ (¬ (meaning t m 5153)) := by
  have source := ElevenTheory.theory11644 (m.theta 1 4) (m.theta 1 6) (m.theta 1 9)
  exact rule22388 (meaning t m 2497) (meaning t m 3226) (meaning t m 5153) source

theorem rule22389 (p2027 p3276 p3956 p4025 p4191 p4422 p4501 : Prop) (h : (¬ p3956) ∨ (¬ p4025) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p4422) ∨ (¬ p3276) ∨ (¬ p4191)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3956) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11645 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule22389 (meaning t m 2027) (meaning t m 3276) (meaning t m 3956) (meaning t m 4025) (meaning t m 4191) (meaning t m 4422) (meaning t m 4501) source

theorem rule22390 (p2027 p3868 p3872 p3989 p4001 p4260 p4501 : Prop) (h : (¬ p4001) ∨ p2027 ∨ (¬ p3872) ∨ (¬ p4260) ∨ (¬ p3868) ∨ (¬ p3989) ∨ (¬ p4501)) : (p2027) ∨ (¬ p3868) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4001) ∨ (¬ p4260) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11646 t (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule22390 (meaning t m 2027) (meaning t m 3868) (meaning t m 3872) (meaning t m 3989) (meaning t m 4001) (meaning t m 4260) (meaning t m 4501) source

theorem rule22393 (p2027 p2387 p2667 p3027 p3552 p4154 p4501 : Prop) (h : (¬ p3552) ∨ (¬ p3027) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p4501) ∨ (¬ p2667)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4154) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11649 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8)
  exact rule22393 (meaning t m 2027) (meaning t m 2387) (meaning t m 2667) (meaning t m 3027) (meaning t m 3552) (meaning t m 4154) (meaning t m 4501) source

theorem rule22395 (p2027 p2911 p3125 p3570 p3921 p4204 p4624 : Prop) (h : (¬ p4204) ∨ (¬ p3570) ∨ (¬ p3921) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p4624)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3125) ∨ (¬ p3570) ∨ (¬ p3921) ∨ (¬ p4204) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11651 t (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule22395 (meaning t m 2027) (meaning t m 2911) (meaning t m 3125) (meaning t m 3570) (meaning t m 3921) (meaning t m 4204) (meaning t m 4624) source

theorem rule22396 (p2027 p2255 p2437 p2651 p2928 p3402 : Prop) (h : (¬ p2928) ∨ (¬ p3402) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2928) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial22396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory11652 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule22396 (meaning t m 2027) (meaning t m 2255) (meaning t m 2437) (meaning t m 2651) (meaning t m 2928) (meaning t m 3402) source

theorem rule22399 (p2027 p2192 p2253 p2946 p3412 p3425 p3737 p4324 p4381 p4736 p5250 : Prop) (h : (¬ p2253) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4736) ∨ (¬ p5250) ∨ (¬ p3737) ∨ (¬ p3412) ∨ (¬ p2192) ∨ (¬ p4324) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3425) ∨ (¬ p3737) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4736) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial22399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory11655 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule22399 (meaning t m 2027) (meaning t m 2192) (meaning t m 2253) (meaning t m 2946) (meaning t m 3412) (meaning t m 3425) (meaning t m 3737) (meaning t m 4324) (meaning t m 4381) (meaning t m 4736) (meaning t m 5250) source

theorem rule22400 (p1975 p2027 p2299 p2323 p2651 p2911 p2922 p4116 : Prop) (h : p2323 ∨ (¬ p4116) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2911) ∨ (¬ p2299) ∨ (¬ p2922)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial22400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory11656 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22400 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2323) (meaning t m 2651) (meaning t m 2911) (meaning t m 2922) (meaning t m 4116) source

theorem rule22403 (p2027 p2307 p3979 p4197 p4501 p5590 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p4501) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p4501) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial22403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory11659 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule22403 (meaning t m 2027) (meaning t m 2307) (meaning t m 3979) (meaning t m 4197) (meaning t m 4501) (meaning t m 5590) source

theorem rule22404 (p2027 p2386 p2387 p3564 p4345 p5118 p5580 : Prop) (h : p2027 ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p5580) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p3564) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial22404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory11660 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule22404 (meaning t m 2027) (meaning t m 2386) (meaning t m 2387) (meaning t m 3564) (meaning t m 4345) (meaning t m 5118) (meaning t m 5580) source

theorem rule22407 (p2027 p2352 p2387 p2437 p2577 p2662 p4711 : Prop) (h : (¬ p4711) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p2577) ∨ (¬ p2387) ∨ (¬ p2352) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2437) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial22407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory11663 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule22407 (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2437) (meaning t m 2577) (meaning t m 2662) (meaning t m 4711) source

theorem rule22411 (p3125 p3319 p4516 : Prop) (h : (¬ p3125) ∨ (¬ p4516) ∨ p3319) : (¬ p3125) ∨ (p3319) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial22411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (meaning t m 3319) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory11667 (m.theta 1 6) (m.theta 5 6) (m.theta 6 9)
  exact rule22411 (meaning t m 3125) (meaning t m 3319) (meaning t m 4516) source

theorem rule22413 (p2027 p2192 p2255 p2761 p2946 p2996 p3125 p3412 p3773 p4155 p4621 p5294 : Prop) (h : (¬ p2255) ∨ (¬ p4621) ∨ (¬ p4155) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p2192) ∨ (¬ p3125) ∨ (¬ p2996) ∨ (¬ p2761) ∨ (¬ p3773) ∨ (¬ p5294)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2761) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3125) ∨ (¬ p3412) ∨ (¬ p3773) ∨ (¬ p4155) ∨ (¬ p4621) ∨ (¬ p5294) := by
  classical
  tauto

theorem initial22413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5294)) := by
  have source := ElevenTheory.theory11669 t (m.theta 0 3) (m.theta 0 7) (m.theta 0 9) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule22413 (meaning t m 2027) (meaning t m 2192) (meaning t m 2255) (meaning t m 2761) (meaning t m 2946) (meaning t m 2996) (meaning t m 3125) (meaning t m 3412) (meaning t m 3773) (meaning t m 4155) (meaning t m 4621) (meaning t m 5294) source

theorem rule22416 (p2027 p2313 p3063 p3204 p3550 p4260 p5559 : Prop) (h : p2027 ∨ (¬ p3550) ∨ (¬ p5559) ∨ (¬ p4260) ∨ (¬ p2313) ∨ (¬ p3063) ∨ (¬ p3204)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3063) ∨ (¬ p3204) ∨ (¬ p3550) ∨ (¬ p4260) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial22416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory11672 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule22416 (meaning t m 2027) (meaning t m 2313) (meaning t m 3063) (meaning t m 3204) (meaning t m 3550) (meaning t m 4260) (meaning t m 5559) source

theorem rule22419 (p3125 p3323 p3986 : Prop) (h : (¬ p3125) ∨ (¬ p3986) ∨ p3323) : (¬ p3125) ∨ (p3323) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial22419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (meaning t m 3323) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory11675 (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule22419 (meaning t m 3125) (meaning t m 3323) (meaning t m 3986) source

theorem rule22420 (p2027 p2274 p3988 p3998 p4170 p4501 p5568 : Prop) (h : (¬ p3988) ∨ (¬ p3998) ∨ p2027 ∨ (¬ p4170) ∨ (¬ p5568) ∨ (¬ p4501) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p3988) ∨ (¬ p3998) ∨ (¬ p4170) ∨ (¬ p4501) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial22420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory11676 t (m.theta 0 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule22420 (meaning t m 2027) (meaning t m 2274) (meaning t m 3988) (meaning t m 3998) (meaning t m 4170) (meaning t m 4501) (meaning t m 5568) source

theorem rule22421 (p2027 p2255 p2387 p2667 p2946 p3146 p3156 p4154 p5118 p5580 : Prop) (h : (¬ p2946) ∨ p2027 ∨ (¬ p5580) ∨ (¬ p2255) ∨ (¬ p2387) ∨ (¬ p5118) ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p3146) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4154) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial22421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory11677 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule22421 (meaning t m 2027) (meaning t m 2255) (meaning t m 2387) (meaning t m 2667) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 4154) (meaning t m 5118) (meaning t m 5580) source

theorem rule22424 (p2027 p2190 p2891 p3146 p3857 p3858 p4492 p4558 : Prop) (h : (¬ p3858) ∨ (¬ p4558) ∨ (¬ p3146) ∨ (¬ p2891) ∨ (¬ p2190) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p4492)) : (p2027) ∨ (¬ p2190) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3857) ∨ (¬ p3858) ∨ (¬ p4492) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3858)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11680 t (m.theta 0 8) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule22424 (meaning t m 2027) (meaning t m 2190) (meaning t m 2891) (meaning t m 3146) (meaning t m 3857) (meaning t m 3858) (meaning t m 4492) (meaning t m 4558) source

theorem rule22425 (p2027 p2656 p3051 p3574 p4235 p4399 p4715 : Prop) (h : (¬ p4235) ∨ (¬ p4399) ∨ (¬ p3574) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2656) ∨ (¬ p3051) ∨ (¬ p3574) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11681 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule22425 (meaning t m 2027) (meaning t m 2656) (meaning t m 3051) (meaning t m 3574) (meaning t m 4235) (meaning t m 4399) (meaning t m 4715) source

theorem rule22429 (p2027 p2589 p3389 p3569 p4110 p4558 : Prop) (h : (¬ p3569) ∨ (¬ p4110) ∨ (¬ p3389) ∨ (¬ p4558) ∨ (¬ p2589) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11685 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22429 (meaning t m 2027) (meaning t m 2589) (meaning t m 3389) (meaning t m 3569) (meaning t m 4110) (meaning t m 4558) source

theorem rule22430 (p2027 p2088 p3646 p3692 p4119 p4238 p4558 : Prop) (h : (¬ p3646) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p4238) ∨ (¬ p3692) ∨ (¬ p4119)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4238) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11686 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule22430 (meaning t m 2027) (meaning t m 2088) (meaning t m 3646) (meaning t m 3692) (meaning t m 4119) (meaning t m 4238) (meaning t m 4558) source

theorem rule22432 (p2027 p2191 p3097 p3309 p4338 p4507 : Prop) (h : (¬ p2191) ∨ (¬ p4338) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p4507)) : (p2027) ∨ (¬ p2191) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4338) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial22432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory11688 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule22432 (meaning t m 2027) (meaning t m 2191) (meaning t m 3097) (meaning t m 3309) (meaning t m 4338) (meaning t m 4507) source

theorem rule22433 (p2027 p2248 p2553 p2651 p2881 p3016 p3548 p4366 p4559 : Prop) (h : (¬ p2553) ∨ (¬ p4366) ∨ (¬ p3548) ∨ (¬ p2881) ∨ (¬ p4559) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial22433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory11689 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22433 (meaning t m 2027) (meaning t m 2248) (meaning t m 2553) (meaning t m 2651) (meaning t m 2881) (meaning t m 3016) (meaning t m 3548) (meaning t m 4366) (meaning t m 4559) source

theorem rule22435 (p2027 p2136 p2553 p2619 p2651 p3016 p4120 p4244 p4559 p4786 : Prop) (h : (¬ p4244) ∨ (¬ p2553) ∨ (¬ p2619) ∨ (¬ p4120) ∨ (¬ p2136) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2553) ∨ (¬ p2619) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4559) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial22435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory11691 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7)
  exact rule22435 (meaning t m 2027) (meaning t m 2136) (meaning t m 2553) (meaning t m 2619) (meaning t m 2651) (meaning t m 3016) (meaning t m 4120) (meaning t m 4244) (meaning t m 4559) (meaning t m 4786) source

theorem rule22438 (p2027 p2210 p3585 p3954 p4243 p4884 : Prop) (h : (¬ p4243) ∨ (¬ p2210) ∨ (¬ p3585) ∨ (¬ p4884) ∨ (¬ p3954) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p4884) := by
  classical
  tauto

theorem initial22438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4884)) := by
  have source := ElevenTheory.theory11694 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5)
  exact rule22438 (meaning t m 2027) (meaning t m 2210) (meaning t m 3585) (meaning t m 3954) (meaning t m 4243) (meaning t m 4884) source

theorem rule22439 (p4169 p4477 p4559 : Prop) (h : (¬ p4559) ∨ (¬ p4169) ∨ p4477) : (¬ p4169) ∨ (p4477) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial22439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4169)) ∨ (meaning t m 4477) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory11695 t (m.theta 2 7) (m.theta 5 7) (m.theta 6 7)
  exact rule22439 (meaning t m 4169) (meaning t m 4477) (meaning t m 4559) source

theorem rule22440 (p3949 p4135 p4445 : Prop) (h : (¬ p4135) ∨ p4445 ∨ (¬ p3949)) : (¬ p3949) ∨ (¬ p4135) ∨ (p4445) := by
  classical
  tauto

theorem initial22440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4135)) ∨ (meaning t m 4445) := by
  have source := ElevenTheory.theory11696 (m.theta 5 9) (m.theta 7 9) (m.theta 8 9)
  exact rule22440 (meaning t m 3949) (meaning t m 4135) (meaning t m 4445) source

theorem rule22441 (p2027 p2707 p2717 p3551 p3820 p4734 : Prop) (h : (¬ p4734) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p3551) ∨ (¬ p2717) ∨ (¬ p3820)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11697 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 7 8)
  exact rule22441 (meaning t m 2027) (meaning t m 2707) (meaning t m 2717) (meaning t m 3551) (meaning t m 3820) (meaning t m 4734) source

theorem rule22442 (p3696 p3960 p4042 : Prop) (h : (¬ p4042) ∨ (¬ p3960) ∨ p3696) : (p3696) ∨ (¬ p3960) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial22442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3696) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory11698 (m.theta 0 8) (m.theta 5 8) (m.theta 7 8)
  exact rule22442 (meaning t m 3696) (meaning t m 3960) (meaning t m 4042) source

theorem rule22444 (p3449 p3960 p3961 p5206 p5307 : Prop) (h : (¬ p5307) ∨ (¬ p3960) ∨ (¬ p3961) ∨ (¬ p5206) ∨ (¬ p3449)) : (¬ p3449) ∨ (¬ p3960) ∨ (¬ p3961) ∨ (¬ p5206) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial22444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 5206)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory11700 (m.theta 0 1) (m.theta 0 7) (m.theta 0 8) (m.theta 1 8) (m.theta 7 8)
  exact rule22444 (meaning t m 3449) (meaning t m 3960) (meaning t m 3961) (meaning t m 5206) (meaning t m 5307) source

theorem rule22445 (p2027 p2318 p3246 p3821 p3872 p3989 p4501 : Prop) (h : (¬ p3872) ∨ (¬ p3821) ∨ (¬ p3989) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p2318)) : (p2027) ∨ (¬ p2318) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11701 t (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule22445 (meaning t m 2027) (meaning t m 2318) (meaning t m 3246) (meaning t m 3821) (meaning t m 3872) (meaning t m 3989) (meaning t m 4501) source

theorem rule22446 (p2027 p2553 p3319 p3549 p3744 p4718 : Prop) (h : p2027 ∨ (¬ p2553) ∨ (¬ p3744) ∨ (¬ p3549) ∨ (¬ p4718) ∨ (¬ p3319)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3744) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial22446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory11702 t (m.theta 1 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule22446 (meaning t m 2027) (meaning t m 2553) (meaning t m 3319) (meaning t m 3549) (meaning t m 3744) (meaning t m 4718) source

theorem rule22447 (p2027 p2341 p2427 p3659 p3691 p4136 p4882 : Prop) (h : (¬ p3691) ∨ (¬ p4136) ∨ (¬ p3659) ∨ (¬ p2341) ∨ (¬ p2427) ∨ (¬ p4882) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3659) ∨ (¬ p3691) ∨ (¬ p4136) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial22447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11703 t (m.theta 0 7) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule22447 (meaning t m 2027) (meaning t m 2341) (meaning t m 2427) (meaning t m 3659) (meaning t m 3691) (meaning t m 4136) (meaning t m 4882) source

theorem rule22450 (p2027 p2696 p3055 p3136 p4343 p4704 : Prop) (h : (¬ p4704) ∨ (¬ p3136) ∨ (¬ p3055) ∨ (¬ p2696) ∨ (¬ p4343) ∨ p2027) : (p2027) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3136) ∨ (¬ p4343) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial22450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory11706 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5)
  exact rule22450 (meaning t m 2027) (meaning t m 2696) (meaning t m 3055) (meaning t m 3136) (meaning t m 4343) (meaning t m 4704) source

theorem rule22451 (p1982 p2027 p2323 p2946 p3146 p3189 p3662 p4311 : Prop) (h : p2323 ∨ (¬ p1982) ∨ (¬ p4311) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial22451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory11707 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule22451 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3146) (meaning t m 3189) (meaning t m 3662) (meaning t m 4311) source

theorem rule22452 (p2027 p2177 p3960 p3998 p4119 p4556 p5568 : Prop) (h : (¬ p3960) ∨ (¬ p2177) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p3998) ∨ (¬ p4119) ∨ (¬ p4556)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3960) ∨ (¬ p3998) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial22452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory11708 t (m.theta 0 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule22452 (meaning t m 2027) (meaning t m 2177) (meaning t m 3960) (meaning t m 3998) (meaning t m 4119) (meaning t m 4556) (meaning t m 5568) source

theorem rule22453 (p2027 p2177 p2373 p2406 p3379 p3425 p3659 p4119 p4556 p4736 : Prop) (h : (¬ p4119) ∨ (¬ p2373) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3379) ∨ (¬ p2177) ∨ (¬ p4556) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11709 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule22453 (meaning t m 2027) (meaning t m 2177) (meaning t m 2373) (meaning t m 2406) (meaning t m 3379) (meaning t m 3425) (meaning t m 3659) (meaning t m 4119) (meaning t m 4556) (meaning t m 4736) source

theorem rule22455 (p2027 p3516 p3941 p3961 p4668 p5590 : Prop) (h : (¬ p3516) ∨ p2027 ∨ (¬ p3941) ∨ (¬ p3961) ∨ (¬ p5590) ∨ (¬ p4668)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3941) ∨ (¬ p3961) ∨ (¬ p4668) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial22455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory11711 t (m.theta 0 7) (m.theta 0 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule22455 (meaning t m 2027) (meaning t m 3516) (meaning t m 3941) (meaning t m 3961) (meaning t m 4668) (meaning t m 5590) source

theorem rule22458 (p2027 p2177 p3516 p3551 p3690 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p3516) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3690) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory11714 t (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22458 (meaning t m 2027) (meaning t m 2177) (meaning t m 3516) (meaning t m 3551) (meaning t m 3690) (meaning t m 4556) source

theorem rule22460 (p2027 p2166 p2210 p2780 p3146 p3659 p3689 p4736 p5118 p5558 : Prop) (h : p2027 ∨ (¬ p5118) ∨ (¬ p3146) ∨ (¬ p2210) ∨ (¬ p5558) ∨ (¬ p2780) ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p3689) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3146) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p4736) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial22460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory11716 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule22460 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2780) (meaning t m 3146) (meaning t m 3659) (meaning t m 3689) (meaning t m 4736) (meaning t m 5118) (meaning t m 5558) source

theorem rule22461 (p2027 p2881 p3553 p3564 p3984 p4067 p4275 p4624 : Prop) (h : (¬ p3984) ∨ (¬ p4624) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p2881) ∨ (¬ p4067) ∨ (¬ p3553) ∨ (¬ p4275)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4275) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11717 t (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule22461 (meaning t m 2027) (meaning t m 2881) (meaning t m 3553) (meaning t m 3564) (meaning t m 3984) (meaning t m 4067) (meaning t m 4275) (meaning t m 4624) source

theorem rule22465 (p2027 p2588 p2780 p3471 p4475 p5225 : Prop) (h : (¬ p5225) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4475) ∨ (¬ p3471) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4475) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial22465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory11721 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7)
  exact rule22465 (meaning t m 2027) (meaning t m 2588) (meaning t m 2780) (meaning t m 3471) (meaning t m 4475) (meaning t m 5225) source

theorem rule22466 (p2996 p3189 p3919 : Prop) (h : (¬ p3189) ∨ (¬ p3919) ∨ (¬ p2996)) : (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3919) := by
  classical
  tauto

theorem initial22466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3919)) := by
  have source := ElevenTheory.theory11722 (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule22466 (meaning t m 2996) (meaning t m 3189) (meaning t m 3919) source

theorem rule22468 (p3097 p3822 p4428 : Prop) (h : (¬ p4428) ∨ (¬ p3097) ∨ p3822) : (¬ p3097) ∨ (p3822) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial22468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (meaning t m 3822) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory11724 (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule22468 (meaning t m 3097) (meaning t m 3822) (meaning t m 4428) source

theorem rule22469 (p2027 p2774 p3425 p3483 p4471 p4624 : Prop) (h : p2027 ∨ (¬ p3483) ∨ (¬ p3425) ∨ (¬ p2774) ∨ (¬ p4471) ∨ (¬ p4624)) : (p2027) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3483) ∨ (¬ p4471) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11725 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22469 (meaning t m 2027) (meaning t m 2774) (meaning t m 3425) (meaning t m 3483) (meaning t m 4471) (meaning t m 4624) source

theorem rule22471 (p2027 p2299 p2534 p2780 p3073 p3379 p3822 p4420 p4688 p4736 : Prop) (h : (¬ p3379) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3073) ∨ (¬ p4688) ∨ (¬ p2780) ∨ (¬ p4736) ∨ (¬ p4420) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2534) ∨ (¬ p2780) ∨ (¬ p3073) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4420) ∨ (¬ p4688) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4688)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11727 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule22471 (meaning t m 2027) (meaning t m 2299) (meaning t m 2534) (meaning t m 2780) (meaning t m 3073) (meaning t m 3379) (meaning t m 3822) (meaning t m 4420) (meaning t m 4688) (meaning t m 4736) source

theorem rule22472 (p2027 p2573 p2589 p3880 p4203 p4507 : Prop) (h : (¬ p4203) ∨ (¬ p4507) ∨ (¬ p2573) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p2589)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p4203) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial22472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory11728 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule22472 (meaning t m 2027) (meaning t m 2573) (meaning t m 2589) (meaning t m 3880) (meaning t m 4203) (meaning t m 4507) source

theorem rule22475 (p2027 p2241 p2727 p3412 p3555 p4701 : Prop) (h : (¬ p3412) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2241) ∨ (¬ p4701)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11731 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5)
  exact rule22475 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3412) (meaning t m 3555) (meaning t m 4701) source

theorem rule22476 (p2027 p2253 p2274 p2579 p2588 p2641 p2807 p2996 p4564 p5193 : Prop) (h : (¬ p4564) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2253) ∨ (¬ p5193) ∨ (¬ p2274) ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2274) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4564) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory11732 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule22476 (meaning t m 2027) (meaning t m 2253) (meaning t m 2274) (meaning t m 2579) (meaning t m 2588) (meaning t m 2641) (meaning t m 2807) (meaning t m 2996) (meaning t m 4564) (meaning t m 5193) source

theorem rule22477 (p2027 p2298 p2553 p2641 p2996 p4973 : Prop) (h : (¬ p2641) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2298) ∨ (¬ p4973)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2553) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial22477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory11733 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule22477 (meaning t m 2027) (meaning t m 2298) (meaning t m 2553) (meaning t m 2641) (meaning t m 2996) (meaning t m 4973) source

theorem rule22478 (p2027 p2493 p2579 p2662 p4281 p4360 p5008 : Prop) (h : (¬ p2579) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p4360) ∨ (¬ p5008) ∨ (¬ p2662) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p4281) ∨ (¬ p4360) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial22478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11734 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6)
  exact rule22478 (meaning t m 2027) (meaning t m 2493) (meaning t m 2579) (meaning t m 2662) (meaning t m 4281) (meaning t m 4360) (meaning t m 5008) source

theorem rule22481 (p2027 p2630 p2737 p3583 p4316 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p2630) ∨ (¬ p4316) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11737 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule22481 (meaning t m 2027) (meaning t m 2630) (meaning t m 2737) (meaning t m 3583) (meaning t m 4316) (meaning t m 4701) source

theorem rule22482 (p2027 p2191 p2727 p3156 p3368 p4701 : Prop) (h : (¬ p3156) ∨ (¬ p4701) ∨ (¬ p2191) ∨ (¬ p3368) ∨ (¬ p2727) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2727) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11738 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule22482 (meaning t m 2027) (meaning t m 2191) (meaning t m 2727) (meaning t m 3156) (meaning t m 3368) (meaning t m 4701) source

theorem rule22484 (p3695 p4241 p5051 : Prop) (h : p3695 ∨ (¬ p5051) ∨ (¬ p4241)) : (p3695) ∨ (¬ p4241) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial22484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3695) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory11740 (m.theta 2 5) (m.theta 3 5) (m.theta 4 5)
  exact rule22484 (meaning t m 3695) (meaning t m 4241) (meaning t m 5051) source

theorem rule22488 (p2027 p3212 p3954 p4172 p4363 p4877 : Prop) (h : (¬ p4877) ∨ (¬ p3212) ∨ (¬ p4363) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4172)) : (p2027) ∨ (¬ p3212) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4363) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial22488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory11744 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 9)
  exact rule22488 (meaning t m 2027) (meaning t m 3212) (meaning t m 3954) (meaning t m 4172) (meaning t m 4363) (meaning t m 4877) source

theorem rule22489 (p2027 p2911 p3551 p3741 p4244 p4283 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p3741) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4244) ∨ (¬ p4283)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3741) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial22489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11745 t (m.theta 0 7) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule22489 (meaning t m 2027) (meaning t m 2911) (meaning t m 3551) (meaning t m 3741) (meaning t m 4244) (meaning t m 4283) (meaning t m 4882) source

theorem rule22490 (p2027 p2928 p3222 p3644 p4451 p4668 : Prop) (h : (¬ p4451) ∨ (¬ p3644) ∨ (¬ p2928) ∨ (¬ p3222) ∨ p2027 ∨ (¬ p4668)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3644) ∨ (¬ p4451) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11746 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8) (m.theta 7 9)
  exact rule22490 (meaning t m 2027) (meaning t m 2928) (meaning t m 3222) (meaning t m 3644) (meaning t m 4451) (meaning t m 4668) source

theorem rule22491 (p2027 p2146 p3516 p3690 p4244 p4988 : Prop) (h : p2027 ∨ (¬ p3690) ∨ (¬ p3516) ∨ (¬ p2146) ∨ (¬ p4244) ∨ (¬ p4988)) : (p2027) ∨ (¬ p2146) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial22491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory11747 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9)
  exact rule22491 (meaning t m 2027) (meaning t m 2146) (meaning t m 3516) (meaning t m 3690) (meaning t m 4244) (meaning t m 4988) source

theorem rule22492 (p2027 p2911 p3051 p4120 p4132 p4647 : Prop) (h : (¬ p2911) ∨ (¬ p3051) ∨ (¬ p4647) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p4132)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial22492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory11748 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule22492 (meaning t m 2027) (meaning t m 2911) (meaning t m 3051) (meaning t m 4120) (meaning t m 4132) (meaning t m 4647) source

theorem rule22494 (p2027 p2230 p2313 p2553 p2577 p4715 : Prop) (h : (¬ p2577) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p4715) ∨ (¬ p2230) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11750 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule22494 (meaning t m 2027) (meaning t m 2230) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 4715) source

theorem rule22495 (p2027 p2187 p2563 p3324 p4153 p4702 : Prop) (h : (¬ p4153) ∨ p2027 ∨ (¬ p4702) ∨ (¬ p2563) ∨ (¬ p2187) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2563) ∨ (¬ p3324) ∨ (¬ p4153) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial22495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory11751 t (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule22495 (meaning t m 2027) (meaning t m 2187) (meaning t m 2563) (meaning t m 3324) (meaning t m 4153) (meaning t m 4702) source

theorem rule22496 (p1980 p2284 p2388 p4564 : Prop) (h : p2388 ∨ (¬ p1980) ∨ (¬ p2284) ∨ p4564) : (¬ p1980) ∨ (¬ p2284) ∨ (p2388) ∨ (p4564) := by
  classical
  tauto

theorem initial22496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (meaning t m 4564) := by
  have source := ElevenTheory.theory11752 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule22496 (meaning t m 1980) (meaning t m 2284) (meaning t m 2388) (meaning t m 4564) source

theorem rule22497 (p2657 p2667 p3987 p4194 : Prop) (h : (¬ p2657) ∨ (¬ p3987) ∨ (¬ p2667) ∨ (¬ p4194)) : (¬ p2657) ∨ (¬ p2667) ∨ (¬ p3987) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial22497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory11753 (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6)
  exact rule22497 (meaning t m 2657) (meaning t m 2667) (meaning t m 3987) (meaning t m 4194) source

theorem rule22498 (p2027 p2245 p2641 p2963 p3379 p4813 : Prop) (h : p2027 ∨ (¬ p4813) ∨ (¬ p3379) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p4813) := by
  classical
  tauto

theorem initial22498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4813)) := by
  have source := ElevenTheory.theory11754 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6)
  exact rule22498 (meaning t m 2027) (meaning t m 2245) (meaning t m 2641) (meaning t m 2963) (meaning t m 3379) (meaning t m 4813) source

theorem rule22499 (p1984 p2027 p2440 p2765 p2810 p3365 p3873 p4110 : Prop) (h : (¬ p1984) ∨ (¬ p2440) ∨ p2765 ∨ (¬ p3873) ∨ (¬ p3365) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p4110)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2440) ∨ (p2765) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial22499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory11755 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule22499 (meaning t m 1984) (meaning t m 2027) (meaning t m 2440) (meaning t m 2765) (meaning t m 2810) (meaning t m 3365) (meaning t m 3873) (meaning t m 4110) source

end SunPrize.SMT
