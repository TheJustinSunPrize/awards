import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory012
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule12282 (p2598 p3362 p3363 p4729 p4730 : Prop) : (p3363) ∨ (((¬ p2598) ∨ (¬ p4729) ∨ (¬ p3363) ∨ (¬ p3362) ∨ (¬ p4730))) := by
  classical
  tauto

theorem initial12282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3363) ∨ (meaning t m 5882) := by
  exact rule12282 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule12283 (p2598 p3362 p3363 p4729 p4730 : Prop) : (p3362) ∨ (((¬ p2598) ∨ (¬ p4729) ∨ (¬ p3363) ∨ (¬ p3362) ∨ (¬ p4730))) := by
  classical
  tauto

theorem initial12283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3362) ∨ (meaning t m 5882) := by
  exact rule12283 (meaning t m 2598) (meaning t m 3362) (meaning t m 3363) (meaning t m 4729) (meaning t m 4730)

theorem rule12288 (p5881 p5882 : Prop) : (¬ ((¬ p5881) ∨ (¬ p5882))) ∨ (¬ p5881) ∨ (¬ p5882) := by
  classical
  tauto

theorem initial12288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5880)) ∨ (¬ (meaning t m 5881)) ∨ (¬ (meaning t m 5882)) := by
  exact rule12288 (meaning t m 5881) (meaning t m 5882)

theorem rule12289 (p4725 p5880 : Prop) (h : (p4725 ↔ p5880)) : (¬ p4725) ∨ (p5880) := by
  classical
  tauto

theorem initial12289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4725)) ∨ (meaning t m 5880) := by
  have source := ElevenTheory.theory3258 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule12289 (meaning t m 4725) (meaning t m 5880) source

theorem rule12291 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p2753) ∨ (((¬ p2753) ∨ (¬ p3954) ∨ (¬ p4733) ∨ (¬ p3873) ∨ (¬ p4734))) := by
  classical
  tauto

theorem initial12291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2753) ∨ (meaning t m 5884) := by
  exact rule12291 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule12292 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p3954) ∨ (((¬ p2753) ∨ (¬ p3954) ∨ (¬ p4733) ∨ (¬ p3873) ∨ (¬ p4734))) := by
  classical
  tauto

theorem initial12292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3954) ∨ (meaning t m 5884) := by
  exact rule12292 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule12294 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p3873) ∨ (((¬ p2753) ∨ (¬ p3954) ∨ (¬ p4733) ∨ (¬ p3873) ∨ (¬ p4734))) := by
  classical
  tauto

theorem initial12294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3873) ∨ (meaning t m 5884) := by
  exact rule12294 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule12295 (p2753 p3873 p3954 p4733 p4734 : Prop) : (p4734) ∨ (((¬ p2753) ∨ (¬ p3954) ∨ (¬ p4733) ∨ (¬ p3873) ∨ (¬ p4734))) := by
  classical
  tauto

theorem initial12295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4734) ∨ (meaning t m 5884) := by
  exact rule12295 (meaning t m 2753) (meaning t m 3873) (meaning t m 3954) (meaning t m 4733) (meaning t m 4734)

theorem rule12297 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p3366) ∨ (((¬ p3366) ∨ (¬ p4736) ∨ (¬ p4737) ∨ (¬ p2608) ∨ (¬ p3589))) := by
  classical
  tauto

theorem initial12297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3366) ∨ (meaning t m 5885) := by
  exact rule12297 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule12299 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p4737) ∨ (((¬ p3366) ∨ (¬ p4736) ∨ (¬ p4737) ∨ (¬ p2608) ∨ (¬ p3589))) := by
  classical
  tauto

theorem initial12299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4737) ∨ (meaning t m 5885) := by
  exact rule12299 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule12300 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p2608) ∨ (((¬ p3366) ∨ (¬ p4736) ∨ (¬ p4737) ∨ (¬ p2608) ∨ (¬ p3589))) := by
  classical
  tauto

theorem initial12300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2608) ∨ (meaning t m 5885) := by
  exact rule12300 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule12301 (p2608 p3366 p3589 p4736 p4737 : Prop) : (p3589) ∨ (((¬ p3366) ∨ (¬ p4736) ∨ (¬ p4737) ∨ (¬ p2608) ∨ (¬ p3589))) := by
  classical
  tauto

theorem initial12301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3589) ∨ (meaning t m 5885) := by
  exact rule12301 (meaning t m 2608) (meaning t m 3366) (meaning t m 3589) (meaning t m 4736) (meaning t m 4737)

theorem rule12305 (p5884 p5885 : Prop) : (¬ ((¬ p5884) ∨ (¬ p5885))) ∨ (¬ p5884) ∨ (¬ p5885) := by
  classical
  tauto

theorem initial12305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5883)) ∨ (¬ (meaning t m 5884)) ∨ (¬ (meaning t m 5885)) := by
  exact rule12305 (meaning t m 5884) (meaning t m 5885)

theorem rule12306 (p4731 p5883 : Prop) (h : (p4731 ↔ p5883)) : (¬ p4731) ∨ (p5883) := by
  classical
  tauto

theorem initial12306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4731)) ∨ (meaning t m 5883) := by
  have source := ElevenTheory.theory3259 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule12306 (meaning t m 4731) (meaning t m 5883) source

theorem rule12308 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p4740) ∨ (((¬ p4740) ∨ (¬ p3694) ∨ (¬ p4359) ∨ (¬ p4741) ∨ (¬ p4742))) := by
  classical
  tauto

theorem initial12308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4740) ∨ (meaning t m 5887) := by
  exact rule12308 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule12309 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p3694) ∨ (((¬ p4740) ∨ (¬ p3694) ∨ (¬ p4359) ∨ (¬ p4741) ∨ (¬ p4742))) := by
  classical
  tauto

theorem initial12309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3694) ∨ (meaning t m 5887) := by
  exact rule12309 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule12310 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p4359) ∨ (((¬ p4740) ∨ (¬ p3694) ∨ (¬ p4359) ∨ (¬ p4741) ∨ (¬ p4742))) := by
  classical
  tauto

theorem initial12310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4359) ∨ (meaning t m 5887) := by
  exact rule12310 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule12311 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p4741) ∨ (((¬ p4740) ∨ (¬ p3694) ∨ (¬ p4359) ∨ (¬ p4741) ∨ (¬ p4742))) := by
  classical
  tauto

theorem initial12311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4741) ∨ (meaning t m 5887) := by
  exact rule12311 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule12312 (p3694 p4359 p4740 p4741 p4742 : Prop) : (p4742) ∨ (((¬ p4740) ∨ (¬ p3694) ∨ (¬ p4359) ∨ (¬ p4741) ∨ (¬ p4742))) := by
  classical
  tauto

theorem initial12312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4742) ∨ (meaning t m 5887) := by
  exact rule12312 (meaning t m 3694) (meaning t m 4359) (meaning t m 4740) (meaning t m 4741) (meaning t m 4742)

theorem rule12314 (p2619 p4188 p4744 p4745 p4746 : Prop) : (p4188) ∨ (((¬ p4188) ∨ (¬ p4744) ∨ (¬ p2619) ∨ (¬ p4745) ∨ (¬ p4746))) := by
  classical
  tauto

theorem initial12314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4188) ∨ (meaning t m 5888) := by
  exact rule12314 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule12315 (p2619 p4188 p4744 p4745 p4746 : Prop) : (p4744) ∨ (((¬ p4188) ∨ (¬ p4744) ∨ (¬ p2619) ∨ (¬ p4745) ∨ (¬ p4746))) := by
  classical
  tauto

theorem initial12315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4744) ∨ (meaning t m 5888) := by
  exact rule12315 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule12316 (p2619 p4188 p4744 p4745 p4746 : Prop) : (p2619) ∨ (((¬ p4188) ∨ (¬ p4744) ∨ (¬ p2619) ∨ (¬ p4745) ∨ (¬ p4746))) := by
  classical
  tauto

theorem initial12316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2619) ∨ (meaning t m 5888) := by
  exact rule12316 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule12318 (p2619 p4188 p4744 p4745 p4746 : Prop) : (p4746) ∨ (((¬ p4188) ∨ (¬ p4744) ∨ (¬ p2619) ∨ (¬ p4745) ∨ (¬ p4746))) := by
  classical
  tauto

theorem initial12318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4746) ∨ (meaning t m 5888) := by
  exact rule12318 (meaning t m 2619) (meaning t m 4188) (meaning t m 4744) (meaning t m 4745) (meaning t m 4746)

theorem rule12322 (p5887 p5888 : Prop) : (¬ ((¬ p5887) ∨ (¬ p5888))) ∨ (¬ p5887) ∨ (¬ p5888) := by
  classical
  tauto

theorem initial12322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5886)) ∨ (¬ (meaning t m 5887)) ∨ (¬ (meaning t m 5888)) := by
  exact rule12322 (meaning t m 5887) (meaning t m 5888)

theorem rule12323 (p4738 p5886 : Prop) (h : (p4738 ↔ p5886)) : (¬ p4738) ∨ (p5886) := by
  classical
  tauto

theorem initial12323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4738)) ∨ (meaning t m 5886) := by
  have source := ElevenTheory.theory3260 t (m.theta 2 5) (m.theta 2 8) (m.theta 5 8)
  exact rule12323 (meaning t m 4738) (meaning t m 5886) source

theorem rule12325 (p2810 p3364 p4343 p4749 p4750 : Prop) : (p4343) ∨ (((¬ p4343) ∨ (¬ p2810) ∨ (¬ p3364) ∨ (¬ p4749) ∨ (¬ p4750))) := by
  classical
  tauto

theorem initial12325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4343) ∨ (meaning t m 5890) := by
  exact rule12325 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule12326 (p2810 p3364 p4343 p4749 p4750 : Prop) : (p2810) ∨ (((¬ p4343) ∨ (¬ p2810) ∨ (¬ p3364) ∨ (¬ p4749) ∨ (¬ p4750))) := by
  classical
  tauto

theorem initial12326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2810) ∨ (meaning t m 5890) := by
  exact rule12326 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule12327 (p2810 p3364 p4343 p4749 p4750 : Prop) : (p3364) ∨ (((¬ p4343) ∨ (¬ p2810) ∨ (¬ p3364) ∨ (¬ p4749) ∨ (¬ p4750))) := by
  classical
  tauto

theorem initial12327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3364) ∨ (meaning t m 5890) := by
  exact rule12327 (meaning t m 2810) (meaning t m 3364) (meaning t m 4343) (meaning t m 4749) (meaning t m 4750)

theorem rule12331 (p2630 p3475 p3683 p4752 p4753 : Prop) : (p3683) ∨ (((¬ p3683) ∨ (¬ p3475) ∨ (¬ p2630) ∨ (¬ p4752) ∨ (¬ p4753))) := by
  classical
  tauto

theorem initial12331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3683) ∨ (meaning t m 5891) := by
  exact rule12331 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule12332 (p2630 p3475 p3683 p4752 p4753 : Prop) : (p3475) ∨ (((¬ p3683) ∨ (¬ p3475) ∨ (¬ p2630) ∨ (¬ p4752) ∨ (¬ p4753))) := by
  classical
  tauto

theorem initial12332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3475) ∨ (meaning t m 5891) := by
  exact rule12332 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule12333 (p2630 p3475 p3683 p4752 p4753 : Prop) : (p2630) ∨ (((¬ p3683) ∨ (¬ p3475) ∨ (¬ p2630) ∨ (¬ p4752) ∨ (¬ p4753))) := by
  classical
  tauto

theorem initial12333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2630) ∨ (meaning t m 5891) := by
  exact rule12333 (meaning t m 2630) (meaning t m 3475) (meaning t m 3683) (meaning t m 4752) (meaning t m 4753)

theorem rule12339 (p5890 p5891 : Prop) : (¬ ((¬ p5890) ∨ (¬ p5891))) ∨ (¬ p5890) ∨ (¬ p5891) := by
  classical
  tauto

theorem initial12339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5889)) ∨ (¬ (meaning t m 5890)) ∨ (¬ (meaning t m 5891)) := by
  exact rule12339 (meaning t m 5890) (meaning t m 5891)

theorem rule12340 (p4747 p5889 : Prop) (h : (p4747 ↔ p5889)) : (¬ p4747) ∨ (p5889) := by
  classical
  tauto

theorem initial12340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4747)) ∨ (meaning t m 5889) := by
  have source := ElevenTheory.theory3261 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule12340 (meaning t m 4747) (meaning t m 5889) source

theorem rule12342 (p1984 p2027 p2247 p2299 p2633 p3568 p4154 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3568) ∨ (¬ p2247) ∨ (¬ p4154) ∨ p2633 ∨ (¬ p2299)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial12342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory3262 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule12342 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2633) (meaning t m 3568) (meaning t m 4154) source

theorem rule12343 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4245) ∨ (((¬ p4245) ∨ (¬ p4757) ∨ (¬ p4756) ∨ (¬ p4319) ∨ (¬ p4154))) := by
  classical
  tauto

theorem initial12343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4245) ∨ (meaning t m 5893) := by
  exact rule12343 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule12344 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4757) ∨ (((¬ p4245) ∨ (¬ p4757) ∨ (¬ p4756) ∨ (¬ p4319) ∨ (¬ p4154))) := by
  classical
  tauto

theorem initial12344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4757) ∨ (meaning t m 5893) := by
  exact rule12344 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule12345 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4756) ∨ (((¬ p4245) ∨ (¬ p4757) ∨ (¬ p4756) ∨ (¬ p4319) ∨ (¬ p4154))) := by
  classical
  tauto

theorem initial12345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4756) ∨ (meaning t m 5893) := by
  exact rule12345 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule12346 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4319) ∨ (((¬ p4245) ∨ (¬ p4757) ∨ (¬ p4756) ∨ (¬ p4319) ∨ (¬ p4154))) := by
  classical
  tauto

theorem initial12346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4319) ∨ (meaning t m 5893) := by
  exact rule12346 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule12347 (p4154 p4245 p4319 p4756 p4757 : Prop) : (p4154) ∨ (((¬ p4245) ∨ (¬ p4757) ∨ (¬ p4756) ∨ (¬ p4319) ∨ (¬ p4154))) := by
  classical
  tauto

theorem initial12347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4154) ∨ (meaning t m 5893) := by
  exact rule12347 (meaning t m 4154) (meaning t m 4245) (meaning t m 4319) (meaning t m 4756) (meaning t m 4757)

theorem rule12349 (p2641 p3922 p4759 p4760 p4761 : Prop) : (p2641) ∨ (((¬ p2641) ∨ (¬ p4760) ∨ (¬ p3922) ∨ (¬ p4759) ∨ (¬ p4761))) := by
  classical
  tauto

theorem initial12349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2641) ∨ (meaning t m 5894) := by
  exact rule12349 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule12350 (p2641 p3922 p4759 p4760 p4761 : Prop) : (p4760) ∨ (((¬ p2641) ∨ (¬ p4760) ∨ (¬ p3922) ∨ (¬ p4759) ∨ (¬ p4761))) := by
  classical
  tauto

theorem initial12350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4760) ∨ (meaning t m 5894) := by
  exact rule12350 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule12351 (p2641 p3922 p4759 p4760 p4761 : Prop) : (p3922) ∨ (((¬ p2641) ∨ (¬ p4760) ∨ (¬ p3922) ∨ (¬ p4759) ∨ (¬ p4761))) := by
  classical
  tauto

theorem initial12351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3922) ∨ (meaning t m 5894) := by
  exact rule12351 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule12352 (p2641 p3922 p4759 p4760 p4761 : Prop) : (p4759) ∨ (((¬ p2641) ∨ (¬ p4760) ∨ (¬ p3922) ∨ (¬ p4759) ∨ (¬ p4761))) := by
  classical
  tauto

theorem initial12352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4759) ∨ (meaning t m 5894) := by
  exact rule12352 (meaning t m 2641) (meaning t m 3922) (meaning t m 4759) (meaning t m 4760) (meaning t m 4761)

theorem rule12357 (p5893 p5894 : Prop) : (¬ ((¬ p5893) ∨ (¬ p5894))) ∨ (¬ p5893) ∨ (¬ p5894) := by
  classical
  tauto

theorem initial12357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5892)) ∨ (¬ (meaning t m 5893)) ∨ (¬ (meaning t m 5894)) := by
  exact rule12357 (meaning t m 5893) (meaning t m 5894)

theorem rule12358 (p4754 p5892 : Prop) (h : (p4754 ↔ p5892)) : (¬ p4754) ∨ (p5892) := by
  classical
  tauto

theorem initial12358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4754)) ∨ (meaning t m 5892) := by
  have source := ElevenTheory.theory3263 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule12358 (meaning t m 4754) (meaning t m 5892) source

theorem rule12360 (p3324 p4196 p4769 p4770 p4771 : Prop) : (p4769) ∨ (((¬ p4769) ∨ (¬ p3324) ∨ (¬ p4196) ∨ (¬ p4770) ∨ (¬ p4771))) := by
  classical
  tauto

theorem initial12360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4769) ∨ (meaning t m 5896) := by
  exact rule12360 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule12361 (p3324 p4196 p4769 p4770 p4771 : Prop) : (p3324) ∨ (((¬ p4769) ∨ (¬ p3324) ∨ (¬ p4196) ∨ (¬ p4770) ∨ (¬ p4771))) := by
  classical
  tauto

theorem initial12361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3324) ∨ (meaning t m 5896) := by
  exact rule12361 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule12362 (p3324 p4196 p4769 p4770 p4771 : Prop) : (p4196) ∨ (((¬ p4769) ∨ (¬ p3324) ∨ (¬ p4196) ∨ (¬ p4770) ∨ (¬ p4771))) := by
  classical
  tauto

theorem initial12362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4196) ∨ (meaning t m 5896) := by
  exact rule12362 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule12364 (p3324 p4196 p4769 p4770 p4771 : Prop) : (p4771) ∨ (((¬ p4769) ∨ (¬ p3324) ∨ (¬ p4196) ∨ (¬ p4770) ∨ (¬ p4771))) := by
  classical
  tauto

theorem initial12364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4771) ∨ (meaning t m 5896) := by
  exact rule12364 (meaning t m 3324) (meaning t m 4196) (meaning t m 4769) (meaning t m 4770) (meaning t m 4771)

theorem rule12366 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p4417) ∨ (((¬ p4417) ∨ (¬ p4341) ∨ (¬ p2668) ∨ (¬ p4773) ∨ (¬ p4774))) := by
  classical
  tauto

theorem initial12366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4417) ∨ (meaning t m 5897) := by
  exact rule12366 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule12367 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p4341) ∨ (((¬ p4417) ∨ (¬ p4341) ∨ (¬ p2668) ∨ (¬ p4773) ∨ (¬ p4774))) := by
  classical
  tauto

theorem initial12367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4341) ∨ (meaning t m 5897) := by
  exact rule12367 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule12368 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p2668) ∨ (((¬ p4417) ∨ (¬ p4341) ∨ (¬ p2668) ∨ (¬ p4773) ∨ (¬ p4774))) := by
  classical
  tauto

theorem initial12368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2668) ∨ (meaning t m 5897) := by
  exact rule12368 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule12369 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p4773) ∨ (((¬ p4417) ∨ (¬ p4341) ∨ (¬ p2668) ∨ (¬ p4773) ∨ (¬ p4774))) := by
  classical
  tauto

theorem initial12369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4773) ∨ (meaning t m 5897) := by
  exact rule12369 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule12370 (p2668 p4341 p4417 p4773 p4774 : Prop) : (p4774) ∨ (((¬ p4417) ∨ (¬ p4341) ∨ (¬ p2668) ∨ (¬ p4773) ∨ (¬ p4774))) := by
  classical
  tauto

theorem initial12370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4774) ∨ (meaning t m 5897) := by
  exact rule12370 (meaning t m 2668) (meaning t m 4341) (meaning t m 4417) (meaning t m 4773) (meaning t m 4774)

theorem rule12374 (p5896 p5897 : Prop) : (¬ ((¬ p5896) ∨ (¬ p5897))) ∨ (¬ p5896) ∨ (¬ p5897) := by
  classical
  tauto

theorem initial12374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5895)) ∨ (¬ (meaning t m 5896)) ∨ (¬ (meaning t m 5897)) := by
  exact rule12374 (meaning t m 5896) (meaning t m 5897)

theorem rule12375 (p4767 p5895 : Prop) (h : (p4767 ↔ p5895)) : (¬ p4767) ∨ (p5895) := by
  classical
  tauto

theorem initial12375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4767)) ∨ (meaning t m 5895) := by
  have source := ElevenTheory.theory3264 t (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule12375 (meaning t m 4767) (meaning t m 5895) source

theorem rule12377 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p4777) ∨ (((¬ p4777) ∨ (¬ p3572) ∨ (¬ p4357) ∨ (¬ p4778) ∨ (¬ p4779))) := by
  classical
  tauto

theorem initial12377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4777) ∨ (meaning t m 5899) := by
  exact rule12377 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule12378 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p3572) ∨ (((¬ p4777) ∨ (¬ p3572) ∨ (¬ p4357) ∨ (¬ p4778) ∨ (¬ p4779))) := by
  classical
  tauto

theorem initial12378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3572) ∨ (meaning t m 5899) := by
  exact rule12378 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule12379 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p4357) ∨ (((¬ p4777) ∨ (¬ p3572) ∨ (¬ p4357) ∨ (¬ p4778) ∨ (¬ p4779))) := by
  classical
  tauto

theorem initial12379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4357) ∨ (meaning t m 5899) := by
  exact rule12379 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule12380 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p4778) ∨ (((¬ p4777) ∨ (¬ p3572) ∨ (¬ p4357) ∨ (¬ p4778) ∨ (¬ p4779))) := by
  classical
  tauto

theorem initial12380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4778) ∨ (meaning t m 5899) := by
  exact rule12380 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule12381 (p3572 p4357 p4777 p4778 p4779 : Prop) : (p4779) ∨ (((¬ p4777) ∨ (¬ p3572) ∨ (¬ p4357) ∨ (¬ p4778) ∨ (¬ p4779))) := by
  classical
  tauto

theorem initial12381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4779) ∨ (meaning t m 5899) := by
  exact rule12381 (meaning t m 3572) (meaning t m 4357) (meaning t m 4777) (meaning t m 4778) (meaning t m 4779)

theorem rule12383 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p4325) ∨ (((¬ p4325) ∨ (¬ p4781) ∨ (¬ p2685) ∨ (¬ p4782) ∨ (¬ p4783))) := by
  classical
  tauto

theorem initial12383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4325) ∨ (meaning t m 5900) := by
  exact rule12383 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule12384 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p4781) ∨ (((¬ p4325) ∨ (¬ p4781) ∨ (¬ p2685) ∨ (¬ p4782) ∨ (¬ p4783))) := by
  classical
  tauto

theorem initial12384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4781) ∨ (meaning t m 5900) := by
  exact rule12384 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule12385 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p2685) ∨ (((¬ p4325) ∨ (¬ p4781) ∨ (¬ p2685) ∨ (¬ p4782) ∨ (¬ p4783))) := by
  classical
  tauto

theorem initial12385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (meaning t m 5900) := by
  exact rule12385 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule12386 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p4782) ∨ (((¬ p4325) ∨ (¬ p4781) ∨ (¬ p2685) ∨ (¬ p4782) ∨ (¬ p4783))) := by
  classical
  tauto

theorem initial12386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4782) ∨ (meaning t m 5900) := by
  exact rule12386 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule12387 (p2685 p4325 p4781 p4782 p4783 : Prop) : (p4783) ∨ (((¬ p4325) ∨ (¬ p4781) ∨ (¬ p2685) ∨ (¬ p4782) ∨ (¬ p4783))) := by
  classical
  tauto

theorem initial12387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4783) ∨ (meaning t m 5900) := by
  exact rule12387 (meaning t m 2685) (meaning t m 4325) (meaning t m 4781) (meaning t m 4782) (meaning t m 4783)

theorem rule12391 (p5899 p5900 : Prop) : (¬ ((¬ p5899) ∨ (¬ p5900))) ∨ (¬ p5899) ∨ (¬ p5900) := by
  classical
  tauto

theorem initial12391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5898)) ∨ (¬ (meaning t m 5899)) ∨ (¬ (meaning t m 5900)) := by
  exact rule12391 (meaning t m 5899) (meaning t m 5900)

theorem rule12392 (p4775 p5898 : Prop) (h : (p4775 ↔ p5898)) : (¬ p4775) ∨ (p5898) := by
  classical
  tauto

theorem initial12392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4775)) ∨ (meaning t m 5898) := by
  have source := ElevenTheory.theory3265 t (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule12392 (meaning t m 4775) (meaning t m 5898) source

theorem rule12394 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p2811) ∨ (((¬ p2811) ∨ (¬ p3365) ∨ (¬ p4787) ∨ (¬ p4236) ∨ (¬ p4786))) := by
  classical
  tauto

theorem initial12394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2811) ∨ (meaning t m 5902) := by
  exact rule12394 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule12395 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p3365) ∨ (((¬ p2811) ∨ (¬ p3365) ∨ (¬ p4787) ∨ (¬ p4236) ∨ (¬ p4786))) := by
  classical
  tauto

theorem initial12395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3365) ∨ (meaning t m 5902) := by
  exact rule12395 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule12396 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p4787) ∨ (((¬ p2811) ∨ (¬ p3365) ∨ (¬ p4787) ∨ (¬ p4236) ∨ (¬ p4786))) := by
  classical
  tauto

theorem initial12396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4787) ∨ (meaning t m 5902) := by
  exact rule12396 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule12397 (p2811 p3365 p4236 p4786 p4787 : Prop) : (p4236) ∨ (((¬ p2811) ∨ (¬ p3365) ∨ (¬ p4787) ∨ (¬ p4236) ∨ (¬ p4786))) := by
  classical
  tauto

theorem initial12397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4236) ∨ (meaning t m 5902) := by
  exact rule12397 (meaning t m 2811) (meaning t m 3365) (meaning t m 4236) (meaning t m 4786) (meaning t m 4787)

theorem rule12400 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p3361) ∨ (((¬ p3361) ∨ (¬ p4117) ∨ (¬ p4790) ∨ (¬ p2696) ∨ (¬ p4789))) := by
  classical
  tauto

theorem initial12400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3361) ∨ (meaning t m 5903) := by
  exact rule12400 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule12401 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p4117) ∨ (((¬ p3361) ∨ (¬ p4117) ∨ (¬ p4790) ∨ (¬ p2696) ∨ (¬ p4789))) := by
  classical
  tauto

theorem initial12401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4117) ∨ (meaning t m 5903) := by
  exact rule12401 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule12402 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p4790) ∨ (((¬ p3361) ∨ (¬ p4117) ∨ (¬ p4790) ∨ (¬ p2696) ∨ (¬ p4789))) := by
  classical
  tauto

theorem initial12402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4790) ∨ (meaning t m 5903) := by
  exact rule12402 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule12403 (p2696 p3361 p4117 p4789 p4790 : Prop) : (p2696) ∨ (((¬ p3361) ∨ (¬ p4117) ∨ (¬ p4790) ∨ (¬ p2696) ∨ (¬ p4789))) := by
  classical
  tauto

theorem initial12403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2696) ∨ (meaning t m 5903) := by
  exact rule12403 (meaning t m 2696) (meaning t m 3361) (meaning t m 4117) (meaning t m 4789) (meaning t m 4790)

theorem rule12408 (p5902 p5903 : Prop) : (¬ ((¬ p5902) ∨ (¬ p5903))) ∨ (¬ p5902) ∨ (¬ p5903) := by
  classical
  tauto

theorem initial12408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5901)) ∨ (¬ (meaning t m 5902)) ∨ (¬ (meaning t m 5903)) := by
  exact rule12408 (meaning t m 5902) (meaning t m 5903)

theorem rule12409 (p4784 p5901 : Prop) (h : (p4784 ↔ p5901)) : (¬ p4784) ∨ (p5901) := by
  classical
  tauto

theorem initial12409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4784)) ∨ (meaning t m 5901) := by
  have source := ElevenTheory.theory3266 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3)
  exact rule12409 (meaning t m 4784) (meaning t m 5901) source

theorem rule12411 (p1977 p2241 p2699 p2811 p4790 : Prop) (h : (¬ p2241) ∨ (¬ p1977) ∨ p2699 ∨ p4790 ∨ (¬ p2811)) : (¬ p1977) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2811) ∨ (p4790) := by
  classical
  tauto

theorem initial12411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2811)) ∨ (meaning t m 4790) := by
  have source := ElevenTheory.theory3267 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3)
  exact rule12411 (meaning t m 1977) (meaning t m 2241) (meaning t m 2699) (meaning t m 2811) (meaning t m 4790) source

theorem rule12412 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p4424) ∨ (((¬ p4424) ∨ (¬ p4794) ∨ (¬ p4400) ∨ (¬ p3588) ∨ (¬ p4793))) := by
  classical
  tauto

theorem initial12412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4424) ∨ (meaning t m 5905) := by
  exact rule12412 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule12413 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p4794) ∨ (((¬ p4424) ∨ (¬ p4794) ∨ (¬ p4400) ∨ (¬ p3588) ∨ (¬ p4793))) := by
  classical
  tauto

theorem initial12413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4794) ∨ (meaning t m 5905) := by
  exact rule12413 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule12414 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p4400) ∨ (((¬ p4424) ∨ (¬ p4794) ∨ (¬ p4400) ∨ (¬ p3588) ∨ (¬ p4793))) := by
  classical
  tauto

theorem initial12414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4400) ∨ (meaning t m 5905) := by
  exact rule12414 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule12415 (p3588 p4400 p4424 p4793 p4794 : Prop) : (p3588) ∨ (((¬ p4424) ∨ (¬ p4794) ∨ (¬ p4400) ∨ (¬ p3588) ∨ (¬ p4793))) := by
  classical
  tauto

theorem initial12415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3588) ∨ (meaning t m 5905) := by
  exact rule12415 (meaning t m 3588) (meaning t m 4400) (meaning t m 4424) (meaning t m 4793) (meaning t m 4794)

theorem rule12419 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p4797) ∨ (((¬ p4796) ∨ (¬ p4797) ∨ (¬ p3687) ∨ (¬ p2707) ∨ (¬ p3576))) := by
  classical
  tauto

theorem initial12419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4797) ∨ (meaning t m 5906) := by
  exact rule12419 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule12420 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p3687) ∨ (((¬ p4796) ∨ (¬ p4797) ∨ (¬ p3687) ∨ (¬ p2707) ∨ (¬ p3576))) := by
  classical
  tauto

theorem initial12420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3687) ∨ (meaning t m 5906) := by
  exact rule12420 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule12421 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p2707) ∨ (((¬ p4796) ∨ (¬ p4797) ∨ (¬ p3687) ∨ (¬ p2707) ∨ (¬ p3576))) := by
  classical
  tauto

theorem initial12421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2707) ∨ (meaning t m 5906) := by
  exact rule12421 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule12422 (p2707 p3576 p3687 p4796 p4797 : Prop) : (p3576) ∨ (((¬ p4796) ∨ (¬ p4797) ∨ (¬ p3687) ∨ (¬ p2707) ∨ (¬ p3576))) := by
  classical
  tauto

theorem initial12422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3576) ∨ (meaning t m 5906) := by
  exact rule12422 (meaning t m 2707) (meaning t m 3576) (meaning t m 3687) (meaning t m 4796) (meaning t m 4797)

theorem rule12426 (p5905 p5906 : Prop) : (¬ ((¬ p5905) ∨ (¬ p5906))) ∨ (¬ p5905) ∨ (¬ p5906) := by
  classical
  tauto

theorem initial12426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5904)) ∨ (¬ (meaning t m 5905)) ∨ (¬ (meaning t m 5906)) := by
  exact rule12426 (meaning t m 5905) (meaning t m 5906)

theorem rule12427 (p4791 p5904 : Prop) (h : (p4791 ↔ p5904)) : (¬ p4791) ∨ (p5904) := by
  classical
  tauto

theorem initial12427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4791)) ∨ (meaning t m 5904) := by
  have source := ElevenTheory.theory3268 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 7)
  exact rule12427 (meaning t m 4791) (meaning t m 5904) source

theorem rule12430 (p3659 p3685 p4800 p4801 p4802 : Prop) : (p4800) ∨ (((¬ p4800) ∨ (¬ p3659) ∨ (¬ p3685) ∨ (¬ p4801) ∨ (¬ p4802))) := by
  classical
  tauto

theorem initial12430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4800) ∨ (meaning t m 5908) := by
  exact rule12430 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule12431 (p3659 p3685 p4800 p4801 p4802 : Prop) : (p3659) ∨ (((¬ p4800) ∨ (¬ p3659) ∨ (¬ p3685) ∨ (¬ p4801) ∨ (¬ p4802))) := by
  classical
  tauto

theorem initial12431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3659) ∨ (meaning t m 5908) := by
  exact rule12431 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule12432 (p3659 p3685 p4800 p4801 p4802 : Prop) : (p3685) ∨ (((¬ p4800) ∨ (¬ p3659) ∨ (¬ p3685) ∨ (¬ p4801) ∨ (¬ p4802))) := by
  classical
  tauto

theorem initial12432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3685) ∨ (meaning t m 5908) := by
  exact rule12432 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule12434 (p3659 p3685 p4800 p4801 p4802 : Prop) : (p4802) ∨ (((¬ p4800) ∨ (¬ p3659) ∨ (¬ p3685) ∨ (¬ p4801) ∨ (¬ p4802))) := by
  classical
  tauto

theorem initial12434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4802) ∨ (meaning t m 5908) := by
  exact rule12434 (meaning t m 3659) (meaning t m 3685) (meaning t m 4800) (meaning t m 4801) (meaning t m 4802)

theorem rule12436 (p2717 p4804 p4805 p4806 p4807 : Prop) : (p4804) ∨ (((¬ p4804) ∨ (¬ p4805) ∨ (¬ p2717) ∨ (¬ p4806) ∨ (¬ p4807))) := by
  classical
  tauto

theorem initial12436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4804) ∨ (meaning t m 5909) := by
  exact rule12436 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule12437 (p2717 p4804 p4805 p4806 p4807 : Prop) : (p4805) ∨ (((¬ p4804) ∨ (¬ p4805) ∨ (¬ p2717) ∨ (¬ p4806) ∨ (¬ p4807))) := by
  classical
  tauto

theorem initial12437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4805) ∨ (meaning t m 5909) := by
  exact rule12437 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule12438 (p2717 p4804 p4805 p4806 p4807 : Prop) : (p2717) ∨ (((¬ p4804) ∨ (¬ p4805) ∨ (¬ p2717) ∨ (¬ p4806) ∨ (¬ p4807))) := by
  classical
  tauto

theorem initial12438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2717) ∨ (meaning t m 5909) := by
  exact rule12438 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule12439 (p2717 p4804 p4805 p4806 p4807 : Prop) : (p4806) ∨ (((¬ p4804) ∨ (¬ p4805) ∨ (¬ p2717) ∨ (¬ p4806) ∨ (¬ p4807))) := by
  classical
  tauto

theorem initial12439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4806) ∨ (meaning t m 5909) := by
  exact rule12439 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule12440 (p2717 p4804 p4805 p4806 p4807 : Prop) : (p4807) ∨ (((¬ p4804) ∨ (¬ p4805) ∨ (¬ p2717) ∨ (¬ p4806) ∨ (¬ p4807))) := by
  classical
  tauto

theorem initial12440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4807) ∨ (meaning t m 5909) := by
  exact rule12440 (meaning t m 2717) (meaning t m 4804) (meaning t m 4805) (meaning t m 4806) (meaning t m 4807)

theorem rule12444 (p5908 p5909 : Prop) : (¬ ((¬ p5908) ∨ (¬ p5909))) ∨ (¬ p5908) ∨ (¬ p5909) := by
  classical
  tauto

theorem initial12444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5907)) ∨ (¬ (meaning t m 5908)) ∨ (¬ (meaning t m 5909)) := by
  exact rule12444 (meaning t m 5908) (meaning t m 5909)

theorem rule12445 (p4798 p5907 : Prop) (h : (p4798 ↔ p5907)) : (¬ p4798) ∨ (p5907) := by
  classical
  tauto

theorem initial12445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4798)) ∨ (meaning t m 5907) := by
  have source := ElevenTheory.theory3270 t (m.theta 2 7) (m.theta 2 8) (m.theta 7 8)
  exact rule12445 (meaning t m 4798) (meaning t m 5907) source

theorem rule12447 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p3402) ∨ (((¬ p3402) ∨ (¬ p4116) ∨ (¬ p4111) ∨ (¬ p4810) ∨ (¬ p4811))) := by
  classical
  tauto

theorem initial12447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3402) ∨ (meaning t m 5911) := by
  exact rule12447 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule12448 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p4116) ∨ (((¬ p3402) ∨ (¬ p4116) ∨ (¬ p4111) ∨ (¬ p4810) ∨ (¬ p4811))) := by
  classical
  tauto

theorem initial12448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4116) ∨ (meaning t m 5911) := by
  exact rule12448 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule12449 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p4111) ∨ (((¬ p3402) ∨ (¬ p4116) ∨ (¬ p4111) ∨ (¬ p4810) ∨ (¬ p4811))) := by
  classical
  tauto

theorem initial12449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4111) ∨ (meaning t m 5911) := by
  exact rule12449 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule12450 (p3402 p4111 p4116 p4810 p4811 : Prop) : (p4810) ∨ (((¬ p3402) ∨ (¬ p4116) ∨ (¬ p4111) ∨ (¬ p4810) ∨ (¬ p4811))) := by
  classical
  tauto

theorem initial12450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4810) ∨ (meaning t m 5911) := by
  exact rule12450 (meaning t m 3402) (meaning t m 4111) (meaning t m 4116) (meaning t m 4810) (meaning t m 4811)

theorem rule12454 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p4281) ∨ (((¬ p4814) ∨ (¬ p4281) ∨ (¬ p3487) ∨ (¬ p2727) ∨ (¬ p4813))) := by
  classical
  tauto

theorem initial12454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4281) ∨ (meaning t m 5912) := by
  exact rule12454 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule12455 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p3487) ∨ (((¬ p4814) ∨ (¬ p4281) ∨ (¬ p3487) ∨ (¬ p2727) ∨ (¬ p4813))) := by
  classical
  tauto

theorem initial12455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3487) ∨ (meaning t m 5912) := by
  exact rule12455 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule12456 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p2727) ∨ (((¬ p4814) ∨ (¬ p4281) ∨ (¬ p3487) ∨ (¬ p2727) ∨ (¬ p4813))) := by
  classical
  tauto

theorem initial12456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2727) ∨ (meaning t m 5912) := by
  exact rule12456 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule12457 (p2727 p3487 p4281 p4813 p4814 : Prop) : (p4813) ∨ (((¬ p4814) ∨ (¬ p4281) ∨ (¬ p3487) ∨ (¬ p2727) ∨ (¬ p4813))) := by
  classical
  tauto

theorem initial12457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4813) ∨ (meaning t m 5912) := by
  exact rule12457 (meaning t m 2727) (meaning t m 3487) (meaning t m 4281) (meaning t m 4813) (meaning t m 4814)

theorem rule12461 (p5911 p5912 : Prop) : (¬ ((¬ p5911) ∨ (¬ p5912))) ∨ (¬ p5911) ∨ (¬ p5912) := by
  classical
  tauto

theorem initial12461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5910)) ∨ (¬ (meaning t m 5911)) ∨ (¬ (meaning t m 5912)) := by
  exact rule12461 (meaning t m 5911) (meaning t m 5912)

theorem rule12462 (p4808 p5910 : Prop) (h : (p4808 ↔ p5910)) : (¬ p4808) ∨ (p5910) := by
  classical
  tauto

theorem initial12462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4808)) ∨ (meaning t m 5910) := by
  have source := ElevenTheory.theory3271 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4)
  exact rule12462 (meaning t m 4808) (meaning t m 5910) source

theorem rule12465 (p4381 p4823 p4824 p4825 p4826 : Prop) : (p4824) ∨ (((¬ p4824) ∨ (¬ p4381) ∨ (¬ p4823) ∨ (¬ p4825) ∨ (¬ p4826))) := by
  classical
  tauto

theorem initial12465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4824) ∨ (meaning t m 5914) := by
  exact rule12465 (meaning t m 4381) (meaning t m 4823) (meaning t m 4824) (meaning t m 4825) (meaning t m 4826)

theorem rule12466 (p4381 p4823 p4824 p4825 p4826 : Prop) : (p4381) ∨ (((¬ p4824) ∨ (¬ p4381) ∨ (¬ p4823) ∨ (¬ p4825) ∨ (¬ p4826))) := by
  classical
  tauto

theorem initial12466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4381) ∨ (meaning t m 5914) := by
  exact rule12466 (meaning t m 4381) (meaning t m 4823) (meaning t m 4824) (meaning t m 4825) (meaning t m 4826)

theorem rule12467 (p4381 p4823 p4824 p4825 p4826 : Prop) : (p4823) ∨ (((¬ p4824) ∨ (¬ p4381) ∨ (¬ p4823) ∨ (¬ p4825) ∨ (¬ p4826))) := by
  classical
  tauto

theorem initial12467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4823) ∨ (meaning t m 5914) := by
  exact rule12467 (meaning t m 4381) (meaning t m 4823) (meaning t m 4824) (meaning t m 4825) (meaning t m 4826)

theorem rule12471 (p2761 p4828 p4829 p4830 p4831 : Prop) : (p4828) ∨ (((¬ p4828) ∨ (¬ p4829) ∨ (¬ p2761) ∨ (¬ p4830) ∨ (¬ p4831))) := by
  classical
  tauto

theorem initial12471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4828) ∨ (meaning t m 5915) := by
  exact rule12471 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule12472 (p2761 p4828 p4829 p4830 p4831 : Prop) : (p4829) ∨ (((¬ p4828) ∨ (¬ p4829) ∨ (¬ p2761) ∨ (¬ p4830) ∨ (¬ p4831))) := by
  classical
  tauto

theorem initial12472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4829) ∨ (meaning t m 5915) := by
  exact rule12472 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule12473 (p2761 p4828 p4829 p4830 p4831 : Prop) : (p2761) ∨ (((¬ p4828) ∨ (¬ p4829) ∨ (¬ p2761) ∨ (¬ p4830) ∨ (¬ p4831))) := by
  classical
  tauto

theorem initial12473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2761) ∨ (meaning t m 5915) := by
  exact rule12473 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule12474 (p2761 p4828 p4829 p4830 p4831 : Prop) : (p4830) ∨ (((¬ p4828) ∨ (¬ p4829) ∨ (¬ p2761) ∨ (¬ p4830) ∨ (¬ p4831))) := by
  classical
  tauto

theorem initial12474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4830) ∨ (meaning t m 5915) := by
  exact rule12474 (meaning t m 2761) (meaning t m 4828) (meaning t m 4829) (meaning t m 4830) (meaning t m 4831)

theorem rule12479 (p5914 p5915 : Prop) : (¬ ((¬ p5914) ∨ (¬ p5915))) ∨ (¬ p5914) ∨ (¬ p5915) := by
  classical
  tauto

theorem initial12479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5913)) ∨ (¬ (meaning t m 5914)) ∨ (¬ (meaning t m 5915)) := by
  exact rule12479 (meaning t m 5914) (meaning t m 5915)

theorem rule12480 (p4821 p5913 : Prop) (h : (p4821 ↔ p5913)) : (¬ p4821) ∨ (p5913) := by
  classical
  tauto

theorem initial12480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4821)) ∨ (meaning t m 5913) := by
  have source := ElevenTheory.theory3273 t (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule12480 (meaning t m 4821) (meaning t m 5913) source

theorem rule12482 (p1976 p2027 p2764 p2780 p3822 p4107 p4381 : Prop) (h : (¬ p2780) ∨ (¬ p1976) ∨ p2764 ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4381) ∨ (¬ p4107)) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial12482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory3274 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule12482 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 2780) (meaning t m 3822) (meaning t m 4107) (meaning t m 4381) source

theorem rule12483 (p1985 p2274 p2765 p4556 : Prop) (h : (¬ p2274) ∨ (¬ p1985) ∨ p4556 ∨ p2765) : (¬ p1985) ∨ (¬ p2274) ∨ (p2765) ∨ (p4556) := by
  classical
  tauto

theorem initial12483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (meaning t m 4556) := by
  have source := ElevenTheory.theory3275 t (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule12483 (meaning t m 1985) (meaning t m 2274) (meaning t m 2765) (meaning t m 4556) source

theorem rule12484 (p1976 p2027 p2299 p2766 p2780 p3822 p4348 : Prop) (h : p2027 ∨ (¬ p1976) ∨ p2766 ∨ (¬ p3822) ∨ (¬ p4348) ∨ (¬ p2780) ∨ (¬ p2299)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2299) ∨ (p2766) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial12484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3276 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule12484 (meaning t m 1976) (meaning t m 2027) (meaning t m 2299) (meaning t m 2766) (meaning t m 2780) (meaning t m 3822) (meaning t m 4348) source

theorem rule12485 (p4195 p4337 p4841 p4842 p4843 : Prop) : (p4337) ∨ (((¬ p4337) ∨ (¬ p4195) ∨ (¬ p4841) ∨ (¬ p4842) ∨ (¬ p4843))) := by
  classical
  tauto

theorem initial12485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4337) ∨ (meaning t m 5917) := by
  exact rule12485 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule12486 (p4195 p4337 p4841 p4842 p4843 : Prop) : (p4195) ∨ (((¬ p4337) ∨ (¬ p4195) ∨ (¬ p4841) ∨ (¬ p4842) ∨ (¬ p4843))) := by
  classical
  tauto

theorem initial12486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4195) ∨ (meaning t m 5917) := by
  exact rule12486 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule12487 (p4195 p4337 p4841 p4842 p4843 : Prop) : (p4841) ∨ (((¬ p4337) ∨ (¬ p4195) ∨ (¬ p4841) ∨ (¬ p4842) ∨ (¬ p4843))) := by
  classical
  tauto

theorem initial12487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4841) ∨ (meaning t m 5917) := by
  exact rule12487 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule12488 (p4195 p4337 p4841 p4842 p4843 : Prop) : (p4842) ∨ (((¬ p4337) ∨ (¬ p4195) ∨ (¬ p4841) ∨ (¬ p4842) ∨ (¬ p4843))) := by
  classical
  tauto

theorem initial12488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4842) ∨ (meaning t m 5917) := by
  exact rule12488 (meaning t m 4195) (meaning t m 4337) (meaning t m 4841) (meaning t m 4842) (meaning t m 4843)

theorem rule12491 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p4328) ∨ (((¬ p4328) ∨ (¬ p4426) ∨ (¬ p2797) ∨ (¬ p4845) ∨ (¬ p4846))) := by
  classical
  tauto

theorem initial12491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4328) ∨ (meaning t m 5918) := by
  exact rule12491 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule12492 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p4426) ∨ (((¬ p4328) ∨ (¬ p4426) ∨ (¬ p2797) ∨ (¬ p4845) ∨ (¬ p4846))) := by
  classical
  tauto

theorem initial12492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4426) ∨ (meaning t m 5918) := by
  exact rule12492 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule12493 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p2797) ∨ (((¬ p4328) ∨ (¬ p4426) ∨ (¬ p2797) ∨ (¬ p4845) ∨ (¬ p4846))) := by
  classical
  tauto

theorem initial12493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2797) ∨ (meaning t m 5918) := by
  exact rule12493 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule12494 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p4845) ∨ (((¬ p4328) ∨ (¬ p4426) ∨ (¬ p2797) ∨ (¬ p4845) ∨ (¬ p4846))) := by
  classical
  tauto

theorem initial12494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4845) ∨ (meaning t m 5918) := by
  exact rule12494 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule12495 (p2797 p4328 p4426 p4845 p4846 : Prop) : (p4846) ∨ (((¬ p4328) ∨ (¬ p4426) ∨ (¬ p2797) ∨ (¬ p4845) ∨ (¬ p4846))) := by
  classical
  tauto

theorem initial12495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4846) ∨ (meaning t m 5918) := by
  exact rule12495 (meaning t m 2797) (meaning t m 4328) (meaning t m 4426) (meaning t m 4845) (meaning t m 4846)

theorem rule12499 (p5917 p5918 : Prop) : (¬ ((¬ p5917) ∨ (¬ p5918))) ∨ (¬ p5917) ∨ (¬ p5918) := by
  classical
  tauto

theorem initial12499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5916)) ∨ (¬ (meaning t m 5917)) ∨ (¬ (meaning t m 5918)) := by
  exact rule12499 (meaning t m 5917) (meaning t m 5918)

theorem rule12500 (p4839 p5916 : Prop) (h : (p4839 ↔ p5916)) : (¬ p4839) ∨ (p5916) := by
  classical
  tauto

theorem initial12500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4839)) ∨ (meaning t m 5916) := by
  have source := ElevenTheory.theory3277 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule12500 (meaning t m 4839) (meaning t m 5916) source

theorem rule12502 (p2667 p2811 p3987 p4195 : Prop) (h : (¬ p4195) ∨ (¬ p2811) ∨ (¬ p2667) ∨ (¬ p3987)) : (¬ p2667) ∨ (¬ p2811) ∨ (¬ p3987) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial12502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory3278 (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6)
  exact rule12502 (meaning t m 2667) (meaning t m 2811) (meaning t m 3987) (meaning t m 4195) source

theorem rule12503 (p3414 p4066 p4849 p4850 p4851 : Prop) : (p3414) ∨ (((¬ p3414) ∨ (¬ p4849) ∨ (¬ p4850) ∨ (¬ p4066) ∨ (¬ p4851))) := by
  classical
  tauto

theorem initial12503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3414) ∨ (meaning t m 5920) := by
  exact rule12503 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule12504 (p3414 p4066 p4849 p4850 p4851 : Prop) : (p4849) ∨ (((¬ p3414) ∨ (¬ p4849) ∨ (¬ p4850) ∨ (¬ p4066) ∨ (¬ p4851))) := by
  classical
  tauto

theorem initial12504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4849) ∨ (meaning t m 5920) := by
  exact rule12504 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule12505 (p3414 p4066 p4849 p4850 p4851 : Prop) : (p4850) ∨ (((¬ p3414) ∨ (¬ p4849) ∨ (¬ p4850) ∨ (¬ p4066) ∨ (¬ p4851))) := by
  classical
  tauto

theorem initial12505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4850) ∨ (meaning t m 5920) := by
  exact rule12505 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule12506 (p3414 p4066 p4849 p4850 p4851 : Prop) : (p4066) ∨ (((¬ p3414) ∨ (¬ p4849) ∨ (¬ p4850) ∨ (¬ p4066) ∨ (¬ p4851))) := by
  classical
  tauto

theorem initial12506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4066) ∨ (meaning t m 5920) := by
  exact rule12506 (meaning t m 3414) (meaning t m 4066) (meaning t m 4849) (meaning t m 4850) (meaning t m 4851)

theorem rule12509 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p4853) ∨ (((¬ p4853) ∨ (¬ p4854) ∨ (¬ p4104) ∨ (¬ p2807) ∨ (¬ p4155))) := by
  classical
  tauto

theorem initial12509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4853) ∨ (meaning t m 5921) := by
  exact rule12509 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule12510 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p4854) ∨ (((¬ p4853) ∨ (¬ p4854) ∨ (¬ p4104) ∨ (¬ p2807) ∨ (¬ p4155))) := by
  classical
  tauto

theorem initial12510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4854) ∨ (meaning t m 5921) := by
  exact rule12510 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule12511 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p4104) ∨ (((¬ p4853) ∨ (¬ p4854) ∨ (¬ p4104) ∨ (¬ p2807) ∨ (¬ p4155))) := by
  classical
  tauto

theorem initial12511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4104) ∨ (meaning t m 5921) := by
  exact rule12511 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule12512 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p2807) ∨ (((¬ p4853) ∨ (¬ p4854) ∨ (¬ p4104) ∨ (¬ p2807) ∨ (¬ p4155))) := by
  classical
  tauto

theorem initial12512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2807) ∨ (meaning t m 5921) := by
  exact rule12512 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule12513 (p2807 p4104 p4155 p4853 p4854 : Prop) : (p4155) ∨ (((¬ p4853) ∨ (¬ p4854) ∨ (¬ p4104) ∨ (¬ p2807) ∨ (¬ p4155))) := by
  classical
  tauto

theorem initial12513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4155) ∨ (meaning t m 5921) := by
  exact rule12513 (meaning t m 2807) (meaning t m 4104) (meaning t m 4155) (meaning t m 4853) (meaning t m 4854)

theorem rule12517 (p5920 p5921 : Prop) : (¬ ((¬ p5920) ∨ (¬ p5921))) ∨ (¬ p5920) ∨ (¬ p5921) := by
  classical
  tauto

theorem initial12517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5919)) ∨ (¬ (meaning t m 5920)) ∨ (¬ (meaning t m 5921)) := by
  exact rule12517 (meaning t m 5920) (meaning t m 5921)

theorem rule12518 (p4847 p5919 : Prop) (h : (p4847 ↔ p5919)) : (¬ p4847) ∨ (p5919) := by
  classical
  tauto

theorem initial12518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4847)) ∨ (meaning t m 5919) := by
  have source := ElevenTheory.theory3279 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 7)
  exact rule12518 (meaning t m 4847) (meaning t m 5919) source

theorem rule12521 (p2246 p2651 p3402 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2246) ∨ (¬ p3402) ∨ (¬ p2651)) : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3402) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial12521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory3281 (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4)
  exact rule12521 (meaning t m 2246) (meaning t m 2651) (meaning t m 3402) (meaning t m 4116) source

theorem rule12522 (p1983 p2027 p2148 p2156 p2396 p2891 p4140 p4173 : Prop) (h : (¬ p1983) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p4140) ∨ (¬ p2891) ∨ (¬ p4173) ∨ (¬ p2156) ∨ p2148) : (¬ p1983) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2396) ∨ (¬ p2891) ∨ (¬ p4140) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial12522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory3282 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule12522 (meaning t m 1983) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2396) (meaning t m 2891) (meaning t m 4140) (meaning t m 4173) source

theorem rule12523 (p1983 p2027 p2192 p2210 p2274 p2396 p2699 : Prop) (h : (¬ p2274) ∨ p2699 ∨ (¬ p2192) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2396) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (p2699) := by
  classical
  tauto

theorem initial12523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory3283 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule12523 (meaning t m 1983) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2396) (meaning t m 2699) source

theorem rule12524 (p4078 p4358 p4857 p4858 p4859 : Prop) : (p4857) ∨ (((¬ p4857) ∨ (¬ p4358) ∨ (¬ p4078) ∨ (¬ p4858) ∨ (¬ p4859))) := by
  classical
  tauto

theorem initial12524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4857) ∨ (meaning t m 5923) := by
  exact rule12524 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule12525 (p4078 p4358 p4857 p4858 p4859 : Prop) : (p4358) ∨ (((¬ p4857) ∨ (¬ p4358) ∨ (¬ p4078) ∨ (¬ p4858) ∨ (¬ p4859))) := by
  classical
  tauto

theorem initial12525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4358) ∨ (meaning t m 5923) := by
  exact rule12525 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule12526 (p4078 p4358 p4857 p4858 p4859 : Prop) : (p4078) ∨ (((¬ p4857) ∨ (¬ p4358) ∨ (¬ p4078) ∨ (¬ p4858) ∨ (¬ p4859))) := by
  classical
  tauto

theorem initial12526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4078) ∨ (meaning t m 5923) := by
  exact rule12526 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule12528 (p4078 p4358 p4857 p4858 p4859 : Prop) : (p4859) ∨ (((¬ p4857) ∨ (¬ p4358) ∨ (¬ p4078) ∨ (¬ p4858) ∨ (¬ p4859))) := by
  classical
  tauto

theorem initial12528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4859) ∨ (meaning t m 5923) := by
  exact rule12528 (meaning t m 4078) (meaning t m 4358) (meaning t m 4857) (meaning t m 4858) (meaning t m 4859)

theorem rule12530 (p2819 p4326 p4861 p4862 p4863 : Prop) : (p4326) ∨ (((¬ p4326) ∨ (¬ p4861) ∨ (¬ p2819) ∨ (¬ p4862) ∨ (¬ p4863))) := by
  classical
  tauto

theorem initial12530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4326) ∨ (meaning t m 5924) := by
  exact rule12530 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule12531 (p2819 p4326 p4861 p4862 p4863 : Prop) : (p4861) ∨ (((¬ p4326) ∨ (¬ p4861) ∨ (¬ p2819) ∨ (¬ p4862) ∨ (¬ p4863))) := by
  classical
  tauto

theorem initial12531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4861) ∨ (meaning t m 5924) := by
  exact rule12531 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule12532 (p2819 p4326 p4861 p4862 p4863 : Prop) : (p2819) ∨ (((¬ p4326) ∨ (¬ p4861) ∨ (¬ p2819) ∨ (¬ p4862) ∨ (¬ p4863))) := by
  classical
  tauto

theorem initial12532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2819) ∨ (meaning t m 5924) := by
  exact rule12532 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule12534 (p2819 p4326 p4861 p4862 p4863 : Prop) : (p4863) ∨ (((¬ p4326) ∨ (¬ p4861) ∨ (¬ p2819) ∨ (¬ p4862) ∨ (¬ p4863))) := by
  classical
  tauto

theorem initial12534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4863) ∨ (meaning t m 5924) := by
  exact rule12534 (meaning t m 2819) (meaning t m 4326) (meaning t m 4861) (meaning t m 4862) (meaning t m 4863)

theorem rule12538 (p5923 p5924 : Prop) : (¬ ((¬ p5923) ∨ (¬ p5924))) ∨ (¬ p5923) ∨ (¬ p5924) := by
  classical
  tauto

theorem initial12538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5922)) ∨ (¬ (meaning t m 5923)) ∨ (¬ (meaning t m 5924)) := by
  exact rule12538 (meaning t m 5923) (meaning t m 5924)

theorem rule12539 (p4855 p5922 : Prop) (h : (p4855 ↔ p5922)) : (¬ p4855) ∨ (p5922) := by
  classical
  tauto

theorem initial12539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4855)) ∨ (meaning t m 5922) := by
  have source := ElevenTheory.theory3284 t (m.theta 2 6) (m.theta 2 8) (m.theta 6 8)
  exact rule12539 (meaning t m 4855) (meaning t m 5922) source

theorem rule12541 (p1982 p2027 p2363 p2608 p2699 p2819 p2829 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2819)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2819) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial12541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory3285 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule12541 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2608) (meaning t m 2699) (meaning t m 2819) (meaning t m 2829) source

theorem rule12542 (p3688 p3918 p3953 p4866 p4867 : Prop) : (p3688) ∨ (((¬ p3688) ∨ (¬ p3953) ∨ (¬ p4867) ∨ (¬ p3918) ∨ (¬ p4866))) := by
  classical
  tauto

theorem initial12542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3688) ∨ (meaning t m 5926) := by
  exact rule12542 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule12543 (p3688 p3918 p3953 p4866 p4867 : Prop) : (p3953) ∨ (((¬ p3688) ∨ (¬ p3953) ∨ (¬ p4867) ∨ (¬ p3918) ∨ (¬ p4866))) := by
  classical
  tauto

theorem initial12543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3953) ∨ (meaning t m 5926) := by
  exact rule12543 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule12545 (p3688 p3918 p3953 p4866 p4867 : Prop) : (p3918) ∨ (((¬ p3688) ∨ (¬ p3953) ∨ (¬ p4867) ∨ (¬ p3918) ∨ (¬ p4866))) := by
  classical
  tauto

theorem initial12545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3918) ∨ (meaning t m 5926) := by
  exact rule12545 (meaning t m 3688) (meaning t m 3918) (meaning t m 3953) (meaning t m 4866) (meaning t m 4867)

theorem rule12548 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p4871) ∨ (((¬ p4871) ∨ (¬ p4870) ∨ (¬ p4024) ∨ (¬ p4869) ∨ (¬ p2829))) := by
  classical
  tauto

theorem initial12548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4871) ∨ (meaning t m 5927) := by
  exact rule12548 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule12549 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p4870) ∨ (((¬ p4871) ∨ (¬ p4870) ∨ (¬ p4024) ∨ (¬ p4869) ∨ (¬ p2829))) := by
  classical
  tauto

theorem initial12549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4870) ∨ (meaning t m 5927) := by
  exact rule12549 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule12550 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p4024) ∨ (((¬ p4871) ∨ (¬ p4870) ∨ (¬ p4024) ∨ (¬ p4869) ∨ (¬ p2829))) := by
  classical
  tauto

theorem initial12550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4024) ∨ (meaning t m 5927) := by
  exact rule12550 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule12551 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p4869) ∨ (((¬ p4871) ∨ (¬ p4870) ∨ (¬ p4024) ∨ (¬ p4869) ∨ (¬ p2829))) := by
  classical
  tauto

theorem initial12551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4869) ∨ (meaning t m 5927) := by
  exact rule12551 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule12552 (p2829 p4024 p4869 p4870 p4871 : Prop) : (p2829) ∨ (((¬ p4871) ∨ (¬ p4870) ∨ (¬ p4024) ∨ (¬ p4869) ∨ (¬ p2829))) := by
  classical
  tauto

theorem initial12552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2829) ∨ (meaning t m 5927) := by
  exact rule12552 (meaning t m 2829) (meaning t m 4024) (meaning t m 4869) (meaning t m 4870) (meaning t m 4871)

theorem rule12556 (p5926 p5927 : Prop) : (¬ ((¬ p5926) ∨ (¬ p5927))) ∨ (¬ p5926) ∨ (¬ p5927) := by
  classical
  tauto

theorem initial12556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5925)) ∨ (¬ (meaning t m 5926)) ∨ (¬ (meaning t m 5927)) := by
  exact rule12556 (meaning t m 5926) (meaning t m 5927)

theorem rule12557 (p4864 p5925 : Prop) (h : (p4864 ↔ p5925)) : (¬ p4864) ∨ (p5925) := by
  classical
  tauto

theorem initial12557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4864)) ∨ (meaning t m 5925) := by
  have source := ElevenTheory.theory3286 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 6)
  exact rule12557 (meaning t m 4864) (meaning t m 5925) source

theorem rule12559 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p3583) ∨ (((¬ p3583) ∨ (¬ p4875) ∨ (¬ p4418) ∨ (¬ p4377) ∨ (¬ p4874))) := by
  classical
  tauto

theorem initial12559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3583) ∨ (meaning t m 5929) := by
  exact rule12559 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule12560 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p4875) ∨ (((¬ p3583) ∨ (¬ p4875) ∨ (¬ p4418) ∨ (¬ p4377) ∨ (¬ p4874))) := by
  classical
  tauto

theorem initial12560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4875) ∨ (meaning t m 5929) := by
  exact rule12560 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule12561 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p4418) ∨ (((¬ p3583) ∨ (¬ p4875) ∨ (¬ p4418) ∨ (¬ p4377) ∨ (¬ p4874))) := by
  classical
  tauto

theorem initial12561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4418) ∨ (meaning t m 5929) := by
  exact rule12561 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule12563 (p3583 p4377 p4418 p4874 p4875 : Prop) : (p4874) ∨ (((¬ p3583) ∨ (¬ p4875) ∨ (¬ p4418) ∨ (¬ p4377) ∨ (¬ p4874))) := by
  classical
  tauto

theorem initial12563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4874) ∨ (meaning t m 5929) := by
  exact rule12563 (meaning t m 3583) (meaning t m 4377) (meaning t m 4418) (meaning t m 4874) (meaning t m 4875)

theorem rule12567 (p2839 p3371 p4243 p4877 p4878 : Prop) : (p3371) ∨ (((¬ p4878) ∨ (¬ p4877) ∨ (¬ p3371) ∨ (¬ p2839) ∨ (¬ p4243))) := by
  classical
  tauto

theorem initial12567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3371) ∨ (meaning t m 5930) := by
  exact rule12567 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule12568 (p2839 p3371 p4243 p4877 p4878 : Prop) : (p2839) ∨ (((¬ p4878) ∨ (¬ p4877) ∨ (¬ p3371) ∨ (¬ p2839) ∨ (¬ p4243))) := by
  classical
  tauto

theorem initial12568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2839) ∨ (meaning t m 5930) := by
  exact rule12568 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule12569 (p2839 p3371 p4243 p4877 p4878 : Prop) : (p4243) ∨ (((¬ p4878) ∨ (¬ p4877) ∨ (¬ p3371) ∨ (¬ p2839) ∨ (¬ p4243))) := by
  classical
  tauto

theorem initial12569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4243) ∨ (meaning t m 5930) := by
  exact rule12569 (meaning t m 2839) (meaning t m 3371) (meaning t m 4243) (meaning t m 4877) (meaning t m 4878)

theorem rule12573 (p5929 p5930 : Prop) : (¬ ((¬ p5929) ∨ (¬ p5930))) ∨ (¬ p5929) ∨ (¬ p5930) := by
  classical
  tauto

theorem initial12573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5928)) ∨ (¬ (meaning t m 5929)) ∨ (¬ (meaning t m 5930)) := by
  exact rule12573 (meaning t m 5929) (meaning t m 5930)

theorem rule12574 (p4872 p5928 : Prop) (h : (p4872 ↔ p5928)) : (¬ p4872) ∨ (p5928) := by
  classical
  tauto

theorem initial12574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4872)) ∨ (meaning t m 5928) := by
  have source := ElevenTheory.theory3287 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5)
  exact rule12574 (meaning t m 4872) (meaning t m 5928) source

theorem rule12576 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p3698) ∨ (((¬ p3698) ∨ (¬ p3684) ∨ (¬ p3054) ∨ (¬ p4881) ∨ (¬ p4882))) := by
  classical
  tauto

theorem initial12576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3698) ∨ (meaning t m 5932) := by
  exact rule12576 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule12577 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p3684) ∨ (((¬ p3698) ∨ (¬ p3684) ∨ (¬ p3054) ∨ (¬ p4881) ∨ (¬ p4882))) := by
  classical
  tauto

theorem initial12577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3684) ∨ (meaning t m 5932) := by
  exact rule12577 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule12578 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p3054) ∨ (((¬ p3698) ∨ (¬ p3684) ∨ (¬ p3054) ∨ (¬ p4881) ∨ (¬ p4882))) := by
  classical
  tauto

theorem initial12578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3054) ∨ (meaning t m 5932) := by
  exact rule12578 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule12579 (p3054 p3684 p3698 p4881 p4882 : Prop) : (p4881) ∨ (((¬ p3698) ∨ (¬ p3684) ∨ (¬ p3054) ∨ (¬ p4881) ∨ (¬ p4882))) := by
  classical
  tauto

theorem initial12579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4881) ∨ (meaning t m 5932) := by
  exact rule12579 (meaning t m 3054) (meaning t m 3684) (meaning t m 3698) (meaning t m 4881) (meaning t m 4882)

theorem rule12582 (p2850 p3582 p3695 p4884 p4885 : Prop) : (p3695) ∨ (((¬ p3695) ∨ (¬ p3582) ∨ (¬ p2850) ∨ (¬ p4884) ∨ (¬ p4885))) := by
  classical
  tauto

theorem initial12582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3695) ∨ (meaning t m 5933) := by
  exact rule12582 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule12583 (p2850 p3582 p3695 p4884 p4885 : Prop) : (p3582) ∨ (((¬ p3695) ∨ (¬ p3582) ∨ (¬ p2850) ∨ (¬ p4884) ∨ (¬ p4885))) := by
  classical
  tauto

theorem initial12583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3582) ∨ (meaning t m 5933) := by
  exact rule12583 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule12584 (p2850 p3582 p3695 p4884 p4885 : Prop) : (p2850) ∨ (((¬ p3695) ∨ (¬ p3582) ∨ (¬ p2850) ∨ (¬ p4884) ∨ (¬ p4885))) := by
  classical
  tauto

theorem initial12584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2850) ∨ (meaning t m 5933) := by
  exact rule12584 (meaning t m 2850) (meaning t m 3582) (meaning t m 3695) (meaning t m 4884) (meaning t m 4885)

theorem rule12590 (p5932 p5933 : Prop) : (¬ ((¬ p5932) ∨ (¬ p5933))) ∨ (¬ p5932) ∨ (¬ p5933) := by
  classical
  tauto

theorem initial12590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5931)) ∨ (¬ (meaning t m 5932)) ∨ (¬ (meaning t m 5933)) := by
  exact rule12590 (meaning t m 5932) (meaning t m 5933)

theorem rule12591 (p4879 p5931 : Prop) (h : (p4879 ↔ p5931)) : (¬ p4879) ∨ (p5931) := by
  classical
  tauto

theorem initial12591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4879)) ∨ (meaning t m 5931) := by
  have source := ElevenTheory.theory3288 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule12591 (meaning t m 4879) (meaning t m 5931) source

theorem rule12593 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p4428) ∨ (((¬ p4428) ∨ (¬ p3758) ∨ (¬ p4193) ∨ (¬ p4888) ∨ (¬ p4889))) := by
  classical
  tauto

theorem initial12593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4428) ∨ (meaning t m 5935) := by
  exact rule12593 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule12594 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p3758) ∨ (((¬ p4428) ∨ (¬ p3758) ∨ (¬ p4193) ∨ (¬ p4888) ∨ (¬ p4889))) := by
  classical
  tauto

theorem initial12594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3758) ∨ (meaning t m 5935) := by
  exact rule12594 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule12595 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p4193) ∨ (((¬ p4428) ∨ (¬ p3758) ∨ (¬ p4193) ∨ (¬ p4888) ∨ (¬ p4889))) := by
  classical
  tauto

theorem initial12595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4193) ∨ (meaning t m 5935) := by
  exact rule12595 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule12597 (p3758 p4193 p4428 p4888 p4889 : Prop) : (p4889) ∨ (((¬ p4428) ∨ (¬ p3758) ∨ (¬ p4193) ∨ (¬ p4888) ∨ (¬ p4889))) := by
  classical
  tauto

theorem initial12597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4889) ∨ (meaning t m 5935) := by
  exact rule12597 (meaning t m 3758) (meaning t m 4193) (meaning t m 4428) (meaning t m 4888) (meaning t m 4889)

theorem rule12599 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p4185) ∨ (((¬ p4185) ∨ (¬ p3985) ∨ (¬ p2860) ∨ (¬ p4891) ∨ (¬ p4401))) := by
  classical
  tauto

theorem initial12599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4185) ∨ (meaning t m 5936) := by
  exact rule12599 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule12600 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p3985) ∨ (((¬ p4185) ∨ (¬ p3985) ∨ (¬ p2860) ∨ (¬ p4891) ∨ (¬ p4401))) := by
  classical
  tauto

theorem initial12600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3985) ∨ (meaning t m 5936) := by
  exact rule12600 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule12601 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p2860) ∨ (((¬ p4185) ∨ (¬ p3985) ∨ (¬ p2860) ∨ (¬ p4891) ∨ (¬ p4401))) := by
  classical
  tauto

theorem initial12601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2860) ∨ (meaning t m 5936) := by
  exact rule12601 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule12603 (p2860 p3985 p4185 p4401 p4891 : Prop) : (p4401) ∨ (((¬ p4185) ∨ (¬ p3985) ∨ (¬ p2860) ∨ (¬ p4891) ∨ (¬ p4401))) := by
  classical
  tauto

theorem initial12603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4401) ∨ (meaning t m 5936) := by
  exact rule12603 (meaning t m 2860) (meaning t m 3985) (meaning t m 4185) (meaning t m 4401) (meaning t m 4891)

theorem rule12607 (p5935 p5936 : Prop) : (¬ ((¬ p5935) ∨ (¬ p5936))) ∨ (¬ p5935) ∨ (¬ p5936) := by
  classical
  tauto

theorem initial12607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5934)) ∨ (¬ (meaning t m 5935)) ∨ (¬ (meaning t m 5936)) := by
  exact rule12607 (meaning t m 5935) (meaning t m 5936)

theorem rule12608 (p4886 p5934 : Prop) (h : (p4886 ↔ p5934)) : (¬ p4886) ∨ (p5934) := by
  classical
  tauto

theorem initial12608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4886)) ∨ (meaning t m 5934) := by
  have source := ElevenTheory.theory3289 t (m.theta 2 5) (m.theta 2 6) (m.theta 5 6)
  exact rule12608 (meaning t m 4886) (meaning t m 5934) source

theorem rule12610 (p1982 p2027 p2132 p2187 p2363 p2611 p2860 : Prop) (h : (¬ p2132) ∨ (¬ p2363) ∨ (¬ p2187) ∨ p2611 ∨ (¬ p2860) ∨ p2027 ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial12610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory3290 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule12610 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2363) (meaning t m 2611) (meaning t m 2860) source

theorem rule12611 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4169) ∨ (((¬ p4169) ∨ (¬ p4244) ∨ (¬ p4136) ∨ (¬ p4894) ∨ (¬ p4895))) := by
  classical
  tauto

theorem initial12611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4169) ∨ (meaning t m 5938) := by
  exact rule12611 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

theorem rule12612 (p4136 p4169 p4244 p4894 p4895 : Prop) : (p4244) ∨ (((¬ p4169) ∨ (¬ p4244) ∨ (¬ p4136) ∨ (¬ p4894) ∨ (¬ p4895))) := by
  classical
  tauto

theorem initial12612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4244) ∨ (meaning t m 5938) := by
  exact rule12612 (meaning t m 4136) (meaning t m 4169) (meaning t m 4244) (meaning t m 4894) (meaning t m 4895)

end SunPrize.SMT
