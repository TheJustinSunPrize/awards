import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory032
import SunPrize.Certificate.Theory033
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule21439 (p2027 p2298 p2331 p2668 p3414 p4405 : Prop) (h : (¬ p2331) ∨ (¬ p2298) ∨ (¬ p2668) ∨ (¬ p3414) ∨ (¬ p4405) ∨ p2027) : (p2027) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3414) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial21439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory10695 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8)
  exact rule21439 (meaning t m 2027) (meaning t m 2298) (meaning t m 2331) (meaning t m 2668) (meaning t m 3414) (meaning t m 4405) source

theorem rule21440 (p2027 p2177 p2248 p2295 p2331 p3583 p3694 p3954 p4905 : Prop) (h : (¬ p2177) ∨ (¬ p3583) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3954) ∨ (¬ p2248) ∨ (¬ p3694) ∨ (¬ p4905)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial21440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory10696 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21440 (meaning t m 2027) (meaning t m 2177) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 3583) (meaning t m 3694) (meaning t m 3954) (meaning t m 4905) source

theorem rule21442 (p2027 p2255 p2449 p2761 p2807 p2957 p3662 p4120 p5123 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p3662) ∨ (¬ p2957) ∨ (¬ p5123) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2255) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial21442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory10698 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21442 (meaning t m 2027) (meaning t m 2255) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 2957) (meaning t m 3662) (meaning t m 4120) (meaning t m 5123) (meaning t m 5568) source

theorem rule21443 (p2027 p2088 p2255 p4104 p4118 p4360 p4590 : Prop) (h : (¬ p4104) ∨ (¬ p4360) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4590) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2255) ∨ (¬ p4104) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial21443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory10699 t (m.theta 0 3) (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 3 8) (m.theta 8 9)
  exact rule21443 (meaning t m 2027) (meaning t m 2088) (meaning t m 2255) (meaning t m 4104) (meaning t m 4118) (meaning t m 4360) (meaning t m 4590) source

theorem rule21445 (p2027 p2248 p2331 p2819 p3555 p3979 p4322 p4337 p4363 p5119 : Prop) (h : (¬ p4337) ∨ p2027 ∨ (¬ p4363) ∨ (¬ p2248) ∨ (¬ p3555) ∨ (¬ p2819) ∨ (¬ p2331) ∨ (¬ p4322) ∨ (¬ p5119) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4337) ∨ (¬ p4363) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10701 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21445 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2819) (meaning t m 3555) (meaning t m 3979) (meaning t m 4322) (meaning t m 4337) (meaning t m 4363) (meaning t m 5119) source

theorem rule21446 (p2027 p2248 p2264 p2807 p3555 p3941 p4322 p4363 p5119 : Prop) (h : (¬ p2248) ∨ (¬ p4322) ∨ (¬ p2264) ∨ (¬ p4363) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3555) ∨ (¬ p3941) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10702 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21446 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2807) (meaning t m 3555) (meaning t m 3941) (meaning t m 4322) (meaning t m 4363) (meaning t m 5119) source

theorem rule21447 (p2027 p2248 p2264 p2459 p2807 p3688 p3917 p3954 p4604 : Prop) (h : (¬ p3688) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p2264) ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p2248) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial21447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory10703 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21447 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4604) source

theorem rule21448 (p2027 p2248 p2449 p2761 p2807 p3688 p3954 p4329 p5254 : Prop) (h : (¬ p3688) ∨ (¬ p5254) ∨ (¬ p2449) ∨ (¬ p3954) ∨ (¬ p2761) ∨ (¬ p2248) ∨ (¬ p4329) ∨ (¬ p2807) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4329) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial21448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory10704 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule21448 (meaning t m 2027) (meaning t m 2248) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3688) (meaning t m 3954) (meaning t m 4329) (meaning t m 5254) source

theorem rule21449 (p2027 p2248 p2331 p2685 p3246 p3817 p4195 p4280 p4366 : Prop) (h : (¬ p2331) ∨ (¬ p4280) ∨ (¬ p4366) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3246) ∨ (¬ p4195) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2685) ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4195) ∨ (¬ p4280) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial21449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory10705 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule21449 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2685) (meaning t m 3246) (meaning t m 3817) (meaning t m 4195) (meaning t m 4280) (meaning t m 4366) source

theorem rule21451 (p2246 p3166 p3189 : Prop) (h : (¬ p3166) ∨ (¬ p2246) ∨ p3189) : (¬ p2246) ∨ (¬ p3166) ∨ (p3189) := by
  classical
  tauto

theorem initial21451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 3166)) ∨ (meaning t m 3189) := by
  have source := ElevenTheory.theory10707 (m.theta 0 3) (m.theta 1 3) (m.theta 3 8)
  exact rule21451 (meaning t m 2246) (meaning t m 3166) (meaning t m 3189) source

theorem rule21456 (p2027 p2248 p2542 p2651 p2982 p3591 p3923 p4347 p4450 : Prop) (h : (¬ p2982) ∨ (¬ p4347) ∨ (¬ p2542) ∨ (¬ p2248) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p4450) ∨ (¬ p2651) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2982) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial21456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory10712 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule21456 (meaning t m 2027) (meaning t m 2248) (meaning t m 2542) (meaning t m 2651) (meaning t m 2982) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) (meaning t m 4450) source

theorem rule21458 (p2027 p2156 p2255 p2663 p3662 p3952 p4399 : Prop) (h : (¬ p2663) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p2156) ∨ (¬ p4399) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2255) ∨ (¬ p2663) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial21458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory10714 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6)
  exact rule21458 (meaning t m 2027) (meaning t m 2156) (meaning t m 2255) (meaning t m 2663) (meaning t m 3662) (meaning t m 3952) (meaning t m 4399) source

theorem rule21459 (p2027 p2248 p2449 p2807 p3583 p3954 p4107 p4244 p4559 : Prop) (h : (¬ p4244) ∨ (¬ p4559) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4244) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial21459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory10715 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule21459 (meaning t m 2027) (meaning t m 2248) (meaning t m 2449) (meaning t m 2807) (meaning t m 3583) (meaning t m 3954) (meaning t m 4107) (meaning t m 4244) (meaning t m 4559) source

theorem rule21461 (p2027 p2138 p2248 p2449 p2807 p2839 p3588 p3873 p4107 p4477 : Prop) (h : (¬ p2138) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2248) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p3873) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2839) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4107) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial21461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory10717 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule21461 (meaning t m 2027) (meaning t m 2138) (meaning t m 2248) (meaning t m 2449) (meaning t m 2807) (meaning t m 2839) (meaning t m 3588) (meaning t m 3873) (meaning t m 4107) (meaning t m 4477) source

theorem rule21463 (p2027 p2177 p2248 p2295 p2331 p2928 p3452 p4278 p4666 : Prop) (h : (¬ p2177) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3452) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2928) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10719 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21463 (meaning t m 2027) (meaning t m 2177) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4666) source

theorem rule21464 (p2027 p2191 p2248 p2331 p3323 p3461 p3555 p5123 p5568 : Prop) (h : p2027 ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p2191) ∨ (¬ p5568) ∨ (¬ p3555) ∨ (¬ p3461) ∨ (¬ p5123) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3555) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial21464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory10720 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21464 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2331) (meaning t m 3323) (meaning t m 3461) (meaning t m 3555) (meaning t m 5123) (meaning t m 5568) source

theorem rule21467 (p2027 p2248 p2437 p2651 p2911 p3486 p3555 p3690 p4666 : Prop) (h : p2027 ∨ (¬ p4666) ∨ (¬ p2651) ∨ (¬ p3555) ∨ (¬ p3486) ∨ (¬ p2911) ∨ (¬ p3690) ∨ (¬ p2437) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10723 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21467 (meaning t m 2027) (meaning t m 2248) (meaning t m 2437) (meaning t m 2651) (meaning t m 2911) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4666) source

theorem rule21469 (p2027 p2387 p2581 p3083 p3574 p4157 : Prop) (h : (¬ p2581) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p4157)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2581) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial21469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory10725 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule21469 (meaning t m 2027) (meaning t m 2387) (meaning t m 2581) (meaning t m 3083) (meaning t m 3574) (meaning t m 4157) source

theorem rule21470 (p1997 p2027 p2191 p2766 p2891 p4132 p4235 p4348 : Prop) (h : (¬ p4348) ∨ p2766 ∨ (¬ p4235) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p2191) ∨ (¬ p4132)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2191) ∨ (p2766) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p4235) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10726 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21470 (meaning t m 1997) (meaning t m 2027) (meaning t m 2191) (meaning t m 2766) (meaning t m 2891) (meaning t m 4132) (meaning t m 4235) (meaning t m 4348) source

theorem rule21471 (p1984 p2027 p2247 p3043 p3662 p3680 p4314 p5284 : Prop) (h : (¬ p1984) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p5284) ∨ (¬ p3680) ∨ (¬ p4314) ∨ p3043) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p3043) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4314)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10727 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule21471 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3043) (meaning t m 3662) (meaning t m 3680) (meaning t m 4314) (meaning t m 5284) source

theorem rule21472 (p2027 p2177 p2254 p3093 p3146 p3172 p3309 p4118 p4905 : Prop) (h : (¬ p4118) ∨ (¬ p4905) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3172) ∨ (¬ p2254) ∨ (¬ p3093) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p4118) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial21472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory10728 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21472 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 3093) (meaning t m 3146) (meaning t m 3172) (meaning t m 3309) (meaning t m 4118) (meaning t m 4905) source

theorem rule21476 (p2027 p2177 p2254 p2528 p3093 p3172 p3309 p4118 p4438 : Prop) (h : (¬ p2528) ∨ (¬ p3172) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p3093) ∨ (¬ p4438) ∨ (¬ p3309) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p4118) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial21476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory10732 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21476 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2528) (meaning t m 3093) (meaning t m 3172) (meaning t m 3309) (meaning t m 4118) (meaning t m 4438) source

theorem rule21477 (p2027 p2254 p2307 p2534 p2657 p3319 p3549 p4256 p4330 p5020 : Prop) (h : (¬ p3319) ∨ (¬ p3549) ∨ (¬ p5020) ∨ (¬ p4330) ∨ (¬ p4256) ∨ (¬ p2254) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p4256) ∨ (¬ p4330) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial21477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory10733 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule21477 (meaning t m 2027) (meaning t m 2254) (meaning t m 2307) (meaning t m 2534) (meaning t m 2657) (meaning t m 3319) (meaning t m 3549) (meaning t m 4256) (meaning t m 4330) (meaning t m 5020) source

theorem rule21478 (p2027 p2254 p2396 p2534 p2657 p3093 p3309 p3950 p4256 : Prop) (h : (¬ p3093) ∨ (¬ p3950) ∨ (¬ p2657) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4256) ∨ (¬ p2254) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3950) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial21478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory10734 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21478 (meaning t m 2027) (meaning t m 2254) (meaning t m 2396) (meaning t m 2534) (meaning t m 2657) (meaning t m 3093) (meaning t m 3309) (meaning t m 3950) (meaning t m 4256) source

theorem rule21480 (p2019 p4166 p4339 p5682 : Prop) (h : (¬ p2019) ∨ p4339 ∨ p5682 ∨ (¬ p4166)) : (¬ p2019) ∨ (¬ p4166) ∨ (p4339) ∨ (p5682) := by
  classical
  tauto

theorem initial21480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2019)) ∨ (¬ (meaning t m 4166)) ∨ (meaning t m 4339) ∨ (meaning t m 5682) := by
  have source := ElevenTheory.theory10736 t (m.theta 2 10) (m.theta 2 4) (m.theta 4 10)
  exact rule21480 (meaning t m 2019) (meaning t m 4166) (meaning t m 4339) (meaning t m 5682) source

theorem rule21482 (p2027 p2248 p2295 p2331 p2396 p2509 p2534 p3452 p3950 : Prop) (h : (¬ p2248) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2509) ∨ (¬ p3452) ∨ (¬ p2295) ∨ (¬ p2534) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial21482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory10738 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21482 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 2509) (meaning t m 2534) (meaning t m 3452) (meaning t m 3950) source

theorem rule21483 (p2027 p2177 p2248 p2295 p2331 p2528 p3860 p4261 p4438 : Prop) (h : (¬ p3860) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p2331) ∨ (¬ p2248) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2528) ∨ (¬ p4438)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2528) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial21483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory10739 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21483 (meaning t m 2027) (meaning t m 2177) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2528) (meaning t m 3860) (meaning t m 4261) (meaning t m 4438) source

theorem rule21485 (p2313 p2779 p3325 p4358 : Prop) (h : (¬ p3325) ∨ (¬ p4358) ∨ (¬ p2779) ∨ p2313) : (p2313) ∨ (¬ p2779) ∨ (¬ p3325) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial21485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2313) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory10741 (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule21485 (meaning t m 2313) (meaning t m 2779) (meaning t m 3325) (meaning t m 4358) source

theorem rule21486 (p2027 p2248 p2509 p2534 p2958 p3051 p3115 p3452 p3950 p4135 p4320 : Prop) (h : p2027 ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p3115) ∨ (¬ p4135) ∨ (¬ p2958) ∨ (¬ p3950) ∨ (¬ p2534) ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3115) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4135) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial21486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory10742 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9)
  exact rule21486 (meaning t m 2027) (meaning t m 2248) (meaning t m 2509) (meaning t m 2534) (meaning t m 2958) (meaning t m 3051) (meaning t m 3115) (meaning t m 3452) (meaning t m 3950) (meaning t m 4135) (meaning t m 4320) source

theorem rule21487 (p1990 p2027 p2307 p2622 p2743 p2779 p2829 p3097 : Prop) (h : (¬ p1990) ∨ (¬ p3097) ∨ (¬ p2779) ∨ p2622 ∨ (¬ p2829) ∨ (¬ p2743) ∨ (¬ p2307) ∨ p2027) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial21487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory10743 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule21487 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2622) (meaning t m 2743) (meaning t m 2779) (meaning t m 2829) (meaning t m 3097) source

theorem rule21488 (p2027 p2098 p3055 p3238 p4030 p4610 p5373 : Prop) (h : (¬ p4030) ∨ (¬ p2098) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p4610) ∨ (¬ p5373) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2098) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p4030) ∨ (¬ p4610) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial21488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory10744 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 8)
  exact rule21488 (meaning t m 2027) (meaning t m 2098) (meaning t m 3055) (meaning t m 3238) (meaning t m 4030) (meaning t m 4610) (meaning t m 5373) source

theorem rule21489 (p2027 p2248 p2331 p2363 p2668 p3583 p3954 p4385 p5059 : Prop) (h : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2248) ∨ (¬ p5059) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial21489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory10745 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule21489 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3583) (meaning t m 3954) (meaning t m 4385) (meaning t m 5059) source

theorem rule21491 (p1984 p2027 p3073 p3818 p3954 p4242 p4317 p4340 : Prop) (h : p2027 ∨ (¬ p3954) ∨ (¬ p1984) ∨ (¬ p3073) ∨ p3818 ∨ (¬ p4317) ∨ (¬ p4242) ∨ (¬ p4340)) : (¬ p1984) ∨ (p2027) ∨ (¬ p3073) ∨ (p3818) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4317) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial21491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory10747 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 8) (m.theta 8 9)
  exact rule21491 (meaning t m 1984) (meaning t m 2027) (meaning t m 3073) (meaning t m 3818) (meaning t m 3954) (meaning t m 4242) (meaning t m 4317) (meaning t m 4340) source

theorem rule21492 (p2136 p2598 p3684 p4109 : Prop) (h : (¬ p4109) ∨ (¬ p2136) ∨ (¬ p2598) ∨ p3684) : (¬ p2136) ∨ (¬ p2598) ∨ (p3684) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial21492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 3684) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory10748 (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5)
  exact rule21492 (meaning t m 2136) (meaning t m 2598) (meaning t m 3684) (meaning t m 4109) source

theorem rule21493 (p2027 p2210 p2579 p3422 p3527 p3570 p3876 p4431 p4647 p5193 : Prop) (h : (¬ p2579) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p4431) ∨ (¬ p3570) ∨ (¬ p4647) ∨ (¬ p5193) ∨ (¬ p3876) ∨ (¬ p3527) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p4431) ∨ (¬ p4647) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial21493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory10749 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule21493 (meaning t m 2027) (meaning t m 2210) (meaning t m 2579) (meaning t m 3422) (meaning t m 3527) (meaning t m 3570) (meaning t m 3876) (meaning t m 4431) (meaning t m 4647) (meaning t m 5193) source

theorem rule21494 (p1981 p2027 p2284 p2323 p2946 p3322 p3680 p4191 p4334 : Prop) (h : p2323 ∨ (¬ p3680) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4334) ∨ (¬ p1981) ∨ (¬ p4191) ∨ (¬ p3322)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3322) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial21494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory10750 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule21494 (meaning t m 1981) (meaning t m 2027) (meaning t m 2284) (meaning t m 2323) (meaning t m 2946) (meaning t m 3322) (meaning t m 3680) (meaning t m 4191) (meaning t m 4334) source

theorem rule21495 (p2027 p2248 p2509 p2534 p2901 p2946 p3246 p3452 p3950 : Prop) (h : (¬ p2248) ∨ (¬ p3950) ∨ (¬ p2901) ∨ (¬ p2534) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial21495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory10751 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21495 (meaning t m 2027) (meaning t m 2248) (meaning t m 2509) (meaning t m 2534) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3452) (meaning t m 3950) source

theorem rule21496 (p2027 p2187 p2307 p2528 p2781 p3055 p3097 p4340 p4384 p5368 : Prop) (h : (¬ p2187) ∨ (¬ p3055) ∨ (¬ p2781) ∨ (¬ p4384) ∨ (¬ p3097) ∨ (¬ p5368) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2528) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3097) ∨ (¬ p4340) ∨ (¬ p4384) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial21496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory10752 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule21496 (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2528) (meaning t m 2781) (meaning t m 3055) (meaning t m 3097) (meaning t m 4340) (meaning t m 4384) (meaning t m 5368) source

theorem rule21497 (p2027 p2248 p2901 p2946 p3246 p3688 p3917 p3954 p4625 : Prop) (h : (¬ p3917) ∨ (¬ p4625) ∨ (¬ p2248) ∨ (¬ p3688) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial21497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory10753 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule21497 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4625) source

theorem rule21498 (p1998 p2027 p2137 p2622 p2743 p2839 p2881 p3051 : Prop) (h : (¬ p2743) ∨ (¬ p1998) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2137) ∨ p2622 ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2137) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p3051) := by
  classical
  tauto

theorem initial21498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) := by
  have source := ElevenTheory.theory10754 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule21498 (meaning t m 1998) (meaning t m 2027) (meaning t m 2137) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 2881) (meaning t m 3051) source

theorem rule21503 (p2004 p3441 p3548 p5309 : Prop) (h : p3441 ∨ (¬ p2004) ∨ p5309 ∨ (¬ p3548)) : (¬ p2004) ∨ (p3441) ∨ (¬ p3548) ∨ (p5309) := by
  classical
  tauto

theorem initial21503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 3441) ∨ (¬ (meaning t m 3548)) ∨ (meaning t m 5309) := by
  have source := ElevenTheory.theory10759 t (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule21503 (meaning t m 2004) (meaning t m 3441) (meaning t m 3548) (meaning t m 5309) source

theorem rule21504 (p2027 p2210 p2254 p2657 p2972 p3680 p4256 p4286 p5123 : Prop) (h : (¬ p4286) ∨ (¬ p5123) ∨ (¬ p4256) ∨ (¬ p2254) ∨ (¬ p2972) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3680) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial21504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory10760 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21504 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2972) (meaning t m 3680) (meaning t m 4256) (meaning t m 4286) (meaning t m 5123) source

theorem rule21506 (p2027 p2210 p2254 p2534 p2657 p2891 p3246 p3950 p4256 : Prop) (h : (¬ p2657) ∨ (¬ p2254) ∨ (¬ p2210) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p2534) ∨ (¬ p3246) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial21506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory10762 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21506 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2534) (meaning t m 2657) (meaning t m 2891) (meaning t m 3246) (meaning t m 3950) (meaning t m 4256) source

theorem rule21507 (p2027 p2210 p2254 p2528 p2881 p2891 p3172 p4118 p4438 : Prop) (h : p2027 ∨ (¬ p2254) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p2528) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4438)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial21507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory10763 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21507 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2528) (meaning t m 2881) (meaning t m 2891) (meaning t m 3172) (meaning t m 4118) (meaning t m 4438) source

theorem rule21508 (p2027 p2737 p3434 p3817 p4400 p4778 : Prop) (h : (¬ p4778) ∨ (¬ p2737) ∨ (¬ p4400) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3434) ∨ (¬ p3817) ∨ (¬ p4400) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial21508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory10764 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule21508 (meaning t m 2027) (meaning t m 2737) (meaning t m 3434) (meaning t m 3817) (meaning t m 4400) (meaning t m 4778) source

theorem rule21511 (p2027 p2318 p2437 p3097 p3574 p3575 p4718 : Prop) (h : (¬ p3574) ∨ (¬ p2318) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3575) ∨ (¬ p2437) ∨ (¬ p4718)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2437) ∨ (¬ p3097) ∨ (¬ p3574) ∨ (¬ p3575) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial21511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory10767 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule21511 (meaning t m 2027) (meaning t m 2318) (meaning t m 2437) (meaning t m 3097) (meaning t m 3574) (meaning t m 3575) (meaning t m 4718) source

theorem rule21512 (p2027 p2187 p2192 p2210 p2254 p2459 p3414 p3919 p4118 p4133 : Prop) (h : p2027 ∨ (¬ p2210) ∨ (¬ p3414) ∨ (¬ p2254) ∨ (¬ p4133) ∨ (¬ p2192) ∨ (¬ p2187) ∨ (¬ p4118) ∨ (¬ p2459) ∨ (¬ p3919)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial21512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory10768 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21512 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2459) (meaning t m 3414) (meaning t m 3919) (meaning t m 4118) (meaning t m 4133) source

theorem rule21513 (p2027 p2192 p2210 p2254 p3125 p3414 p3553 p4330 p4348 : Prop) (h : (¬ p2192) ∨ (¬ p2254) ∨ (¬ p3125) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p3414) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10769 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21513 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 3125) (meaning t m 3414) (meaning t m 3553) (meaning t m 4330) (meaning t m 4348) source

theorem rule21519 (p2027 p3343 p3692 p4256 p4434 p4695 : Prop) (h : (¬ p3692) ∨ (¬ p3343) ∨ (¬ p4695) ∨ (¬ p4434) ∨ p2027 ∨ (¬ p4256)) : (p2027) ∨ (¬ p3343) ∨ (¬ p3692) ∨ (¬ p4256) ∨ (¬ p4434) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial21519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory10775 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule21519 (meaning t m 2027) (meaning t m 3343) (meaning t m 3692) (meaning t m 4256) (meaning t m 4434) (meaning t m 4695) source

theorem rule21521 (p2027 p3105 p3680 p4321 p4875 p4938 : Prop) (h : p2027 ∨ (¬ p4938) ∨ (¬ p4321) ∨ (¬ p3680) ∨ (¬ p4875) ∨ (¬ p3105)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4875) ∨ (¬ p4938) := by
  classical
  tauto

theorem initial21521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4875)) ∨ (¬ (meaning t m 4938)) := by
  have source := ElevenTheory.theory10777 t (m.theta 1 5) (m.theta 1 9) (m.theta 2 5) (m.theta 5 9) (m.theta 9 10)
  exact rule21521 (meaning t m 2027) (meaning t m 3105) (meaning t m 3680) (meaning t m 4321) (meaning t m 4875) (meaning t m 4938) source

theorem rule21522 (p2027 p2254 p2608 p2963 p3324 p3537 p3969 p4188 p4347 p5122 : Prop) (h : (¬ p3324) ∨ (¬ p3969) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4347) ∨ (¬ p3537) ∨ (¬ p4188)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3537) ∨ (¬ p3969) ∨ (¬ p4188) ∨ (¬ p4347) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial21522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory10778 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21522 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2963) (meaning t m 3324) (meaning t m 3537) (meaning t m 3969) (meaning t m 4188) (meaning t m 4347) (meaning t m 5122) source

theorem rule21523 (p2027 p2210 p2254 p2891 p3246 p3266 p3292 p3950 p5284 : Prop) (h : p2027 ∨ (¬ p3292) ∨ (¬ p2254) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p5284) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3950) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10779 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 9) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21523 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2891) (meaning t m 3246) (meaning t m 3266) (meaning t m 3292) (meaning t m 3950) (meaning t m 5284) source

theorem rule21524 (p2027 p2210 p2254 p2891 p3172 p4118 p4129 p4444 p4826 : Prop) (h : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p2254) ∨ (¬ p4444) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p3172) ∨ (¬ p4129)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2891) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4129) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial21524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory10780 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule21524 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2891) (meaning t m 3172) (meaning t m 4118) (meaning t m 4129) (meaning t m 4444) (meaning t m 4826) source

theorem rule21525 (p2531 p2534 p3146 : Prop) (h : (¬ p2534) ∨ (¬ p2531) ∨ (¬ p3146)) : (¬ p2531) ∨ (¬ p2534) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial21525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory10781 (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule21525 (meaning t m 2531) (meaning t m 2534) (meaning t m 3146) source

theorem rule21526 (p1981 p2027 p2114 p2137 p2187 p2307 p2839 p2962 p3097 : Prop) (h : (¬ p3097) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2962) ∨ (¬ p1981) ∨ (¬ p2187) ∨ (¬ p2307) ∨ p2114) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2839) ∨ (¬ p2962) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial21526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory10782 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule21526 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2187) (meaning t m 2307) (meaning t m 2839) (meaning t m 2962) (meaning t m 3097) source

theorem rule21528 (p2027 p2166 p2210 p2254 p2579 p2655 p3016 p3146 p3359 p4697 : Prop) (h : p2027 ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p2655) ∨ (¬ p4697) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p2254) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3016) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial21528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory10784 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule21528 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 2579) (meaning t m 2655) (meaning t m 3016) (meaning t m 3146) (meaning t m 3359) (meaning t m 4697) source

theorem rule21531 (p2027 p2156 p2177 p2274 p2528 p3370 p3585 p4340 p4377 p4438 p5368 : Prop) (h : (¬ p3585) ∨ (¬ p2528) ∨ (¬ p5368) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2156) ∨ (¬ p4377) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3370) ∨ (¬ p4438)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3370) ∨ (¬ p3585) ∨ (¬ p4340) ∨ (¬ p4377) ∨ (¬ p4438) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial21531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory10787 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21531 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2528) (meaning t m 3370) (meaning t m 3585) (meaning t m 4340) (meaning t m 4377) (meaning t m 4438) (meaning t m 5368) source

theorem rule21532 (p2027 p2187 p2528 p3093 p3555 p3585 p4340 p4377 p4384 p4516 p5368 : Prop) (h : (¬ p4516) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p5368) ∨ (¬ p4377) ∨ (¬ p4384) ∨ (¬ p2187) ∨ (¬ p3585) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3585) ∨ (¬ p4340) ∨ (¬ p4377) ∨ (¬ p4384) ∨ (¬ p4516) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial21532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory10788 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule21532 (meaning t m 2027) (meaning t m 2187) (meaning t m 2528) (meaning t m 3093) (meaning t m 3555) (meaning t m 3585) (meaning t m 4340) (meaning t m 4377) (meaning t m 4384) (meaning t m 4516) (meaning t m 5368) source

theorem rule21534 (p1992 p2027 p2510 p2528 p2588 p2997 p3585 p4340 p5368 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p2588) ∨ (¬ p1992) ∨ (¬ p3585) ∨ (¬ p2528) ∨ (¬ p5368) ∨ (¬ p2510) ∨ (¬ p4340)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3585) ∨ (¬ p4340) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial21534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory10790 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 8 9)
  exact rule21534 (meaning t m 1992) (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 2588) (meaning t m 2997) (meaning t m 3585) (meaning t m 4340) (meaning t m 5368) source

theorem rule21535 (p1981 p2027 p2114 p2737 p2797 p3256 p4341 p4347 : Prop) (h : (¬ p2737) ∨ p2114 ∨ (¬ p3256) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p4341) ∨ (¬ p2797) ∨ (¬ p4347)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3256) ∨ (¬ p4341) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10791 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21535 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2797) (meaning t m 3256) (meaning t m 4341) (meaning t m 4347) source

theorem rule21536 (p2027 p2248 p2331 p2363 p2668 p3588 p3954 p4324 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p3588) ∨ (¬ p2668) ∨ (¬ p2363) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2248) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10792 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21536 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4669) source

theorem rule21537 (p2248 p3873 p4786 : Prop) (h : (¬ p3873) ∨ p4786 ∨ (¬ p2248)) : (¬ p2248) ∨ (¬ p3873) ∨ (p4786) := by
  classical
  tauto

theorem initial21537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3873)) ∨ (meaning t m 4786) := by
  have source := ElevenTheory.theory10793 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3)
  exact rule21537 (meaning t m 2248) (meaning t m 3873) (meaning t m 4786) source

theorem rule21539 (p2027 p2254 p2440 p2657 p3399 p3631 p4107 p4235 p4559 : Prop) (h : (¬ p4559) ∨ (¬ p4235) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p4107) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial21539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory10795 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule21539 (meaning t m 2027) (meaning t m 2254) (meaning t m 2440) (meaning t m 2657) (meaning t m 3399) (meaning t m 3631) (meaning t m 4107) (meaning t m 4235) (meaning t m 4559) source

theorem rule21540 (p2027 p2254 p2657 p3073 p3093 p3644 p3742 p4133 p4317 p4347 : Prop) (h : (¬ p3073) ∨ (¬ p4317) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4347) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p2657) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3073) ∨ (¬ p3093) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4133) ∨ (¬ p4317) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10796 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21540 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3073) (meaning t m 3093) (meaning t m 3644) (meaning t m 3742) (meaning t m 4133) (meaning t m 4317) (meaning t m 4347) source

theorem rule21542 (p2027 p3063 p3486 p3989 p4338 p4555 : Prop) (h : (¬ p3063) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p4338) ∨ (¬ p3989) ∨ (¬ p3486)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3486) ∨ (¬ p3989) ∨ (¬ p4338) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial21542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory10798 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule21542 (meaning t m 2027) (meaning t m 3063) (meaning t m 3486) (meaning t m 3989) (meaning t m 4338) (meaning t m 4555) source

theorem rule21543 (p2017 p2462 p2761 p4826 : Prop) (h : (¬ p2761) ∨ p2462 ∨ (¬ p2017) ∨ p4826) : (¬ p2017) ∨ (p2462) ∨ (¬ p2761) ∨ (p4826) := by
  classical
  tauto

theorem initial21543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 4826) := by
  have source := ElevenTheory.theory10799 t (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule21543 (meaning t m 2017) (meaning t m 2462) (meaning t m 2761) (meaning t m 4826) source

theorem rule21544 (p1987 p2027 p2766 p2957 p3646 p3989 p4315 p4347 : Prop) (h : p2027 ∨ (¬ p3989) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p1987) ∨ p2766 ∨ (¬ p2957) ∨ (¬ p4315)) : (¬ p1987) ∨ (p2027) ∨ (p2766) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4315) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10800 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule21544 (meaning t m 1987) (meaning t m 2027) (meaning t m 2766) (meaning t m 2957) (meaning t m 3646) (meaning t m 3989) (meaning t m 4315) (meaning t m 4347) source

theorem rule21546 (p2014 p2169 p3461 p3990 p5250 : Prop) (h : p5250 ∨ p2169 ∨ (¬ p3461) ∨ (¬ p2014) ∨ (¬ p3990)) : (¬ p2014) ∨ (p2169) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (p5250) := by
  classical
  tauto

theorem initial21546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2014)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (meaning t m 5250) := by
  have source := ElevenTheory.theory10802 t (m.theta 6 10) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule21546 (meaning t m 2014) (meaning t m 2169) (meaning t m 3461) (meaning t m 3990) (meaning t m 5250) source

theorem rule21547 (p2000 p2027 p2493 p2579 p2633 p2928 p3644 : Prop) (h : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2928) ∨ p2633 ∨ (¬ p3644) ∨ (¬ p2493)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial21547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory10803 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule21547 (meaning t m 2000) (meaning t m 2027) (meaning t m 2493) (meaning t m 2579) (meaning t m 2633) (meaning t m 2928) (meaning t m 3644) source

theorem rule21548 (p1984 p2027 p2509 p2534 p2641 p2688 p3323 p3452 p3461 p3950 p4381 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3950) ∨ p2688 ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p2641) ∨ (¬ p4381)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p3950) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial21548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory10804 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21548 (meaning t m 1984) (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2641) (meaning t m 2688) (meaning t m 3323) (meaning t m 3452) (meaning t m 3461) (meaning t m 3950) (meaning t m 4381) source

theorem rule21553 (p2027 p2717 p2753 p3471 p4379 p4666 p5229 : Prop) (h : (¬ p4666) ∨ p2027 ∨ (¬ p5229) ∨ (¬ p3471) ∨ (¬ p4379) ∨ (¬ p2717) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p4379) ∨ (¬ p4666) ∨ (¬ p5229) := by
  classical
  tauto

theorem initial21553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5229)) := by
  have source := ElevenTheory.theory10809 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 7) (m.theta 2 9) (m.theta 7 8) (m.theta 7 9)
  exact rule21553 (meaning t m 2027) (meaning t m 2717) (meaning t m 2753) (meaning t m 3471) (meaning t m 4379) (meaning t m 4666) (meaning t m 5229) source

theorem rule21555 (p2027 p2665 p2911 p3389 p3553 p4112 : Prop) (h : (¬ p2911) ∨ (¬ p4112) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2665) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3553) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial21555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory10811 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule21555 (meaning t m 2027) (meaning t m 2665) (meaning t m 2911) (meaning t m 3389) (meaning t m 3553) (meaning t m 4112) source

theorem rule21556 (p1997 p2027 p2765 p2850 p2901 p3876 p3952 p4001 : Prop) (h : (¬ p3952) ∨ (¬ p4001) ∨ p2027 ∨ (¬ p1997) ∨ p2765 ∨ (¬ p2850) ∨ (¬ p2901) ∨ (¬ p3876)) : (¬ p1997) ∨ (p2027) ∨ (p2765) ∨ (¬ p2850) ∨ (¬ p2901) ∨ (¬ p3876) ∨ (¬ p3952) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial21556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory10812 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule21556 (meaning t m 1997) (meaning t m 2027) (meaning t m 2765) (meaning t m 2850) (meaning t m 2901) (meaning t m 3876) (meaning t m 3952) (meaning t m 4001) source

theorem rule21559 (p2027 p2313 p3027 p3552 p4154 p4581 : Prop) (h : p2027 ∨ (¬ p3552) ∨ (¬ p3027) ∨ (¬ p4154) ∨ (¬ p2313) ∨ (¬ p4581)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4154) ∨ (¬ p4581) := by
  classical
  tauto

theorem initial21559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4581)) := by
  have source := ElevenTheory.theory10815 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule21559 (meaning t m 2027) (meaning t m 2313) (meaning t m 3027) (meaning t m 3552) (meaning t m 4154) (meaning t m 4581) source

theorem rule21560 (p1975 p2027 p2138 p2230 p2274 p2563 p3362 p3474 : Prop) (h : (¬ p3362) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2138) ∨ p3474) : (¬ p1975) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3362) ∨ (p3474) := by
  classical
  tauto

theorem initial21560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3362)) ∨ (meaning t m 3474) := by
  have source := ElevenTheory.theory10816 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule21560 (meaning t m 1975) (meaning t m 2027) (meaning t m 2138) (meaning t m 2230) (meaning t m 2274) (meaning t m 2563) (meaning t m 3362) (meaning t m 3474) source

theorem rule21564 (p2331 p3172 p3956 p3984 p4769 : Prop) (h : (¬ p2331) ∨ (¬ p4769) ∨ (¬ p3172) ∨ (¬ p3984) ∨ p3956) : (¬ p2331) ∨ (¬ p3172) ∨ (p3956) ∨ (¬ p3984) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial21564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3172)) ∨ (meaning t m 3956) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory10820 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule21564 (meaning t m 2331) (meaning t m 3172) (meaning t m 3956) (meaning t m 3984) (meaning t m 4769) source

theorem rule21566 (p3422 p4343 p4422 p5170 p5171 : Prop) (h : (¬ p3422) ∨ (¬ p5170) ∨ (¬ p4422) ∨ (¬ p4343) ∨ (¬ p5171)) : (¬ p3422) ∨ (¬ p4343) ∨ (¬ p4422) ∨ (¬ p5170) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial21566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 5170)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory10822 (m.theta 2 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9)
  exact rule21566 (meaning t m 3422) (meaning t m 4343) (meaning t m 4422) (meaning t m 5170) (meaning t m 5171) source

theorem rule21567 (p1975 p2027 p2114 p2383 p2553 p2584 p3367 p3759 p3956 : Prop) (h : (¬ p3759) ∨ (¬ p2553) ∨ (¬ p1975) ∨ (¬ p3367) ∨ p2114 ∨ p2027 ∨ (¬ p2584) ∨ (¬ p2383) ∨ (¬ p3956)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (¬ p2584) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial21567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory10823 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule21567 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2383) (meaning t m 2553) (meaning t m 2584) (meaning t m 3367) (meaning t m 3759) (meaning t m 3956) source

theorem rule21568 (p2138 p2952 p4117 p4316 : Prop) (h : (¬ p4316) ∨ (¬ p4117) ∨ (¬ p2138) ∨ p2952) : (¬ p2138) ∨ (p2952) ∨ (¬ p4117) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial21568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (meaning t m 2952) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory10824 (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 5)
  exact rule21568 (meaning t m 2138) (meaning t m 2952) (meaning t m 4117) (meaning t m 4316) source

theorem rule21570 (p2137 p3694 p4120 : Prop) (h : (¬ p3694) ∨ (¬ p2137) ∨ p4120) : (¬ p2137) ∨ (¬ p3694) ∨ (p4120) := by
  classical
  tauto

theorem initial21570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 3694)) ∨ (meaning t m 4120) := by
  have source := ElevenTheory.theory10826 (m.theta 0 5) (m.theta 2 5) (m.theta 5 8)
  exact rule21570 (meaning t m 2137) (meaning t m 3694) (meaning t m 4120) source

theorem rule21572 (p2027 p2608 p2707 p3452 p3590 p5086 : Prop) (h : (¬ p3590) ∨ (¬ p5086) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p5086) := by
  classical
  tauto

theorem initial21572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 5086)) := by
  have source := ElevenTheory.theory10828 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7)
  exact rule21572 (meaning t m 2027) (meaning t m 2608) (meaning t m 2707) (meaning t m 3452) (meaning t m 3590) (meaning t m 5086) source

theorem rule21574 (p1976 p2027 p2737 p2765 p3365 p3583 p3952 p4316 : Prop) (h : (¬ p3365) ∨ (¬ p1976) ∨ (¬ p3952) ∨ (¬ p2737) ∨ (¬ p3583) ∨ p2765 ∨ p2027 ∨ (¬ p4316)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2737) ∨ (p2765) ∨ (¬ p3365) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial21574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory10830 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule21574 (meaning t m 1976) (meaning t m 2027) (meaning t m 2737) (meaning t m 2765) (meaning t m 3365) (meaning t m 3583) (meaning t m 3952) (meaning t m 4316) source

theorem rule21575 (p1976 p2027 p2264 p2462 p3425 p3659 p3947 : Prop) (h : (¬ p2264) ∨ (¬ p3947) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3425) ∨ p2462 ∨ (¬ p3659)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2264) ∨ (p2462) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial21575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory10831 t (m.theta 0 2) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21575 (meaning t m 1976) (meaning t m 2027) (meaning t m 2264) (meaning t m 2462) (meaning t m 3425) (meaning t m 3659) (meaning t m 3947) source

theorem rule21577 (p3222 p3590 p4340 p4695 p5368 : Prop) (h : (¬ p3590) ∨ (¬ p3222) ∨ (¬ p4695) ∨ (¬ p4340) ∨ (¬ p5368)) : (¬ p3222) ∨ (¬ p3590) ∨ (¬ p4340) ∨ (¬ p4695) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial21577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4695)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory10833 (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 9) (m.theta 8 9)
  exact rule21577 (meaning t m 3222) (meaning t m 3590) (meaning t m 4340) (meaning t m 4695) (meaning t m 5368) source

theorem rule21579 (p2027 p2449 p2995 p3690 p4235 p4705 : Prop) (h : (¬ p4235) ∨ (¬ p2995) ∨ (¬ p4705) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial21579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory10835 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule21579 (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3690) (meaning t m 4235) (meaning t m 4705) source

theorem rule21580 (p1998 p2027 p2470 p2528 p2622 p2630 p3519 p4116 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1998) ∨ p2027 ∨ p2622 ∨ (¬ p4116) ∨ (¬ p3519) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p2630)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p4116) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10836 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21580 (meaning t m 1998) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2622) (meaning t m 2630) (meaning t m 3519) (meaning t m 4116) (meaning t m 4348) source

theorem rule21582 (p1984 p2027 p2737 p2870 p3365 p3474 p3486 p3873 p4874 : Prop) (h : p3474 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4874) ∨ (¬ p2870) ∨ (¬ p2737) ∨ (¬ p3486)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p2870) ∨ (¬ p3365) ∨ (p3474) ∨ (¬ p3486) ∨ (¬ p3873) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial21582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3365)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory10838 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule21582 (meaning t m 1984) (meaning t m 2027) (meaning t m 2737) (meaning t m 2870) (meaning t m 3365) (meaning t m 3474) (meaning t m 3486) (meaning t m 3873) (meaning t m 4874) source

theorem rule21588 (p2027 p3238 p3389 p3519 p3569 p4320 p4702 : Prop) (h : (¬ p3519) ∨ p2027 ∨ (¬ p4702) ∨ (¬ p3238) ∨ (¬ p4320) ∨ (¬ p3389) ∨ (¬ p3569)) : (p2027) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial21588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory10844 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule21588 (meaning t m 2027) (meaning t m 3238) (meaning t m 3389) (meaning t m 3519) (meaning t m 3569) (meaning t m 4320) (meaning t m 4702) source

theorem rule21589 (p2027 p2187 p2192 p2590 p4358 p4390 p4632 : Prop) (h : p2027 ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p2187) ∨ (¬ p4358) ∨ (¬ p4632) ∨ (¬ p4390)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p4358) ∨ (¬ p4390) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial21589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory10845 t (m.theta 1 5) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule21589 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2590) (meaning t m 4358) (meaning t m 4390) (meaning t m 4632) source

theorem rule21590 (p2247 p2608 p2749 : Prop) (h : (¬ p2247) ∨ (¬ p2749) ∨ (¬ p2608)) : (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2749) := by
  classical
  tauto

theorem initial21590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2749)) := by
  have source := ElevenTheory.theory10846 (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule21590 (meaning t m 2247) (meaning t m 2608) (meaning t m 2749) source

theorem rule21591 (p1975 p2027 p2299 p2717 p2753 p2842 p3471 p3585 : Prop) (h : p2842 ∨ (¬ p3471) ∨ (¬ p2753) ∨ (¬ p3585) ∨ (¬ p1975) ∨ (¬ p2299) ∨ (¬ p2717) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (p2842) ∨ (¬ p3471) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial21591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory10847 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21591 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2717) (meaning t m 2753) (meaning t m 2842) (meaning t m 3471) (meaning t m 3585) source

theorem rule21594 (p2027 p2246 p2751 p2958 p3051 p4315 p4320 : Prop) (h : (¬ p2246) ∨ (¬ p2751) ∨ (¬ p4320) ∨ (¬ p2958) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4315) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial21594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory10850 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7)
  exact rule21594 (meaning t m 2027) (meaning t m 2246) (meaning t m 2751) (meaning t m 2958) (meaning t m 3051) (meaning t m 4315) (meaning t m 4320) source

theorem rule21596 (p2027 p2248 p2807 p3005 p3555 p3572 p3989 p4173 p4771 : Prop) (h : p2027 ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p4173) ∨ (¬ p3989) ∨ (¬ p3555) ∨ (¬ p2807) ∨ (¬ p2248) ∨ (¬ p4771)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3555) ∨ (¬ p3572) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4771) := by
  classical
  tauto

theorem initial21596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4771)) := by
  have source := ElevenTheory.theory10852 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule21596 (meaning t m 2027) (meaning t m 2248) (meaning t m 2807) (meaning t m 3005) (meaning t m 3555) (meaning t m 3572) (meaning t m 3989) (meaning t m 4173) (meaning t m 4771) source

theorem rule21597 (p2027 p2630 p2665 p3389 p3572 p3740 : Prop) (h : (¬ p3572) ∨ p2027 ∨ (¬ p2665) ∨ (¬ p3389) ∨ (¬ p2630) ∨ (¬ p3740)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3389) ∨ (¬ p3572) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial21597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory10853 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule21597 (meaning t m 2027) (meaning t m 2630) (meaning t m 2665) (meaning t m 3389) (meaning t m 3572) (meaning t m 3740) source

theorem rule21599 (p1988 p2027 p2323 p2331 p3461 p3755 p4195 p4367 : Prop) (h : (¬ p4367) ∨ p2323 ∨ (¬ p4195) ∨ (¬ p2331) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p3461) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4367) := by
  classical
  tauto

theorem initial21599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4367)) := by
  have source := ElevenTheory.theory10855 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule21599 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 3461) (meaning t m 3755) (meaning t m 4195) (meaning t m 4367) source

theorem rule21602 (p1997 p2027 p2274 p2313 p2542 p2630 p2696 p2766 p2787 p3989 p4347 : Prop) (h : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3989) ∨ (¬ p2313) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2787) ∨ (¬ p1997) ∨ (¬ p4347) ∨ p2766) : (¬ p1997) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (p2766) ∨ (¬ p2787) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10858 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule21602 (meaning t m 1997) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2542) (meaning t m 2630) (meaning t m 2696) (meaning t m 2766) (meaning t m 2787) (meaning t m 3989) (meaning t m 4347) source

theorem rule21603 (p2437 p3201 p3683 : Prop) (h : (¬ p2437) ∨ (¬ p3683) ∨ p3201) : (¬ p2437) ∨ (p3201) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial21603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (meaning t m 3201) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory10859 (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule21603 (meaning t m 2437) (meaning t m 3201) (meaning t m 3683) source

theorem rule21605 (p2027 p2274 p2313 p2787 p3286 p3670 p3744 p4117 p4425 p5322 p5454 : Prop) (h : (¬ p5322) ∨ (¬ p4425) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p3286) ∨ (¬ p3744) ∨ (¬ p2787) ∨ (¬ p2313) ∨ (¬ p3670) ∨ (¬ p2274) ∨ (¬ p5454)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2787) ∨ (¬ p3286) ∨ (¬ p3670) ∨ (¬ p3744) ∨ (¬ p4117) ∨ (¬ p4425) ∨ (¬ p5322) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial21605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5322)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory10861 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 9) (m.theta 3 9) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule21605 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2787) (meaning t m 3286) (meaning t m 3670) (meaning t m 3744) (meaning t m 4117) (meaning t m 4425) (meaning t m 5322) (meaning t m 5454) source

theorem rule21608 (p2027 p2098 p2274 p2313 p2534 p2787 p3609 p3989 p4596 : Prop) (h : (¬ p2313) ∨ (¬ p2787) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p4596) ∨ (¬ p3609) ∨ (¬ p2534) ∨ (¬ p3989) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2534) ∨ (¬ p2787) ∨ (¬ p3609) ∨ (¬ p3989) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial21608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory10864 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule21608 (meaning t m 2027) (meaning t m 2098) (meaning t m 2274) (meaning t m 2313) (meaning t m 2534) (meaning t m 2787) (meaning t m 3609) (meaning t m 3989) (meaning t m 4596) source

theorem rule21610 (p2027 p2254 p3172 p3998 p5242 p5600 : Prop) (h : p2027 ∨ (¬ p5242) ∨ (¬ p3172) ∨ (¬ p2254) ∨ (¬ p3998) ∨ (¬ p5600)) : (p2027) ∨ (¬ p2254) ∨ (¬ p3172) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial21610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5242)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory10866 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 8) (m.theta 3 8) (m.theta 8 10)
  exact rule21610 (meaning t m 2027) (meaning t m 2254) (meaning t m 3172) (meaning t m 3998) (meaning t m 5242) (meaning t m 5600) source

theorem rule21611 (p2027 p2254 p2534 p2657 p3063 p3093 p3683 p3874 p3979 p5122 : Prop) (h : (¬ p5122) ∨ (¬ p3874) ∨ (¬ p3683) ∨ (¬ p3979) ∨ (¬ p2657) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p2254) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3683) ∨ (¬ p3874) ∨ (¬ p3979) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial21611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory10867 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21611 (meaning t m 2027) (meaning t m 2254) (meaning t m 2534) (meaning t m 2657) (meaning t m 3063) (meaning t m 3093) (meaning t m 3683) (meaning t m 3874) (meaning t m 3979) (meaning t m 5122) source

theorem rule21612 (p2027 p2449 p2534 p3553 p4420 p4443 : Prop) (h : (¬ p4420) ∨ (¬ p4443) ∨ (¬ p2534) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p3553)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2534) ∨ (¬ p3553) ∨ (¬ p4420) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial21612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory10868 t (m.theta 3 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21612 (meaning t m 2027) (meaning t m 2449) (meaning t m 2534) (meaning t m 3553) (meaning t m 4420) (meaning t m 4443) source

theorem rule21613 (p1997 p2027 p2406 p2509 p2534 p3146 p3578 : Prop) (h : (¬ p1997) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2534) ∨ p3578 ∨ (¬ p3146)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (p3578) := by
  classical
  tauto

theorem initial21613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) := by
  have source := ElevenTheory.theory10869 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule21613 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 2534) (meaning t m 3146) (meaning t m 3578) source

theorem rule21614 (p2254 p3589 p4789 : Prop) (h : (¬ p3589) ∨ (¬ p2254) ∨ p4789) : (¬ p2254) ∨ (¬ p3589) ∨ (p4789) := by
  classical
  tauto

theorem initial21614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3589)) ∨ (meaning t m 4789) := by
  have source := ElevenTheory.theory10870 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3)
  exact rule21614 (meaning t m 2254) (meaning t m 3589) (meaning t m 4789) source

theorem rule21616 (p2027 p2254 p2459 p2608 p2819 p2829 p3172 p4118 p4133 : Prop) (h : (¬ p4118) ∨ (¬ p2459) ∨ (¬ p2819) ∨ (¬ p4133) ∨ (¬ p3172) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial21616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory10872 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21616 (meaning t m 2027) (meaning t m 2254) (meaning t m 2459) (meaning t m 2608) (meaning t m 2819) (meaning t m 2829) (meaning t m 3172) (meaning t m 4118) (meaning t m 4133) source

theorem rule21617 (p2027 p2254 p2459 p2608 p3172 p3367 p3641 p4118 p4420 : Prop) (h : (¬ p4420) ∨ (¬ p2459) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p2254) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p3172) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p4118) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial21617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory10873 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21617 (meaning t m 2027) (meaning t m 2254) (meaning t m 2459) (meaning t m 2608) (meaning t m 3172) (meaning t m 3367) (meaning t m 3641) (meaning t m 4118) (meaning t m 4420) source

theorem rule21619 (p2027 p2255 p2387 p2667 p2946 p2972 p3412 p3680 p4154 p5123 p5580 : Prop) (h : (¬ p2387) ∨ (¬ p3412) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p5580) ∨ (¬ p2946) ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p2972) ∨ (¬ p5123) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p2972) ∨ (¬ p3412) ∨ (¬ p3680) ∨ (¬ p4154) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial21619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory10875 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21619 (meaning t m 2027) (meaning t m 2255) (meaning t m 2387) (meaning t m 2667) (meaning t m 2946) (meaning t m 2972) (meaning t m 3412) (meaning t m 3680) (meaning t m 4154) (meaning t m 5123) (meaning t m 5580) source

theorem rule21620 (p2027 p2743 p2946 p4117 p4315 p4737 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p4315) ∨ (¬ p4117) ∨ (¬ p2743) ∨ (¬ p4737)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial21620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory10876 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5)
  exact rule21620 (meaning t m 2027) (meaning t m 2743) (meaning t m 2946) (meaning t m 4117) (meaning t m 4315) (meaning t m 4737) source

theorem rule21621 (p2027 p2248 p2352 p2459 p2651 p3016 p3544 p4133 p4261 p4366 : Prop) (h : (¬ p2248) ∨ (¬ p3016) ∨ (¬ p4133) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p3544) ∨ (¬ p2459) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3544) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial21621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory10877 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 1 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21621 (meaning t m 2027) (meaning t m 2248) (meaning t m 2352) (meaning t m 2459) (meaning t m 2651) (meaning t m 3016) (meaning t m 3544) (meaning t m 4133) (meaning t m 4261) (meaning t m 4366) source

theorem rule21622 (p2027 p2299 p3005 p3543 p3572 p4155 p4378 p5145 : Prop) (h : (¬ p3005) ∨ (¬ p3543) ∨ (¬ p5145) ∨ (¬ p4155) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p4378)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3005) ∨ (¬ p3543) ∨ (¬ p3572) ∨ (¬ p4155) ∨ (¬ p4378) ∨ (¬ p5145) := by
  classical
  tauto

theorem initial21622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 5145)) := by
  have source := ElevenTheory.theory10878 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21622 (meaning t m 2027) (meaning t m 2299) (meaning t m 3005) (meaning t m 3543) (meaning t m 3572) (meaning t m 4155) (meaning t m 4378) (meaning t m 5145) source

theorem rule21624 (p2027 p2248 p2651 p3016 p3266 p3440 p3564 p3860 p4321 p4330 : Prop) (h : (¬ p2651) ∨ (¬ p3860) ∨ (¬ p4321) ∨ (¬ p3016) ∨ (¬ p3440) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3266) ∨ (¬ p3440) ∨ (¬ p3564) ∨ (¬ p3860) ∨ (¬ p4321) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial21624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory10880 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 1 9) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21624 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3016) (meaning t m 3266) (meaning t m 3440) (meaning t m 3564) (meaning t m 3860) (meaning t m 4321) (meaning t m 4330) source

theorem rule21625 (p2027 p2248 p2417 p2437 p2651 p3591 p3923 p3950 p4347 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2651) ∨ (¬ p2417) ∨ (¬ p4347) ∨ (¬ p2437) ∨ (¬ p2248) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10881 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21625 (meaning t m 2027) (meaning t m 2248) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3591) (meaning t m 3923) (meaning t m 3950) (meaning t m 4347) source

theorem rule21627 (p2027 p2248 p2437 p2651 p2911 p3588 p3954 p4324 p4666 : Prop) (h : (¬ p2651) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p3588) ∨ (¬ p2248) ∨ (¬ p2911) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10883 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21627 (meaning t m 2027) (meaning t m 2248) (meaning t m 2437) (meaning t m 2651) (meaning t m 2911) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4666) source

theorem rule21629 (p2027 p2248 p2528 p2651 p3083 p3588 p3954 p4324 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p3954) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3588) ∨ (¬ p2528) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10885 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21629 (meaning t m 2027) (meaning t m 2248) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4669) source

theorem rule21630 (p2027 p2248 p2946 p3146 p3156 p3549 p3591 p4107 p4669 : Prop) (h : (¬ p2946) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p2248) ∨ (¬ p3156) ∨ (¬ p3549) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10886 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21630 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4669) source

theorem rule21631 (p2027 p2248 p2299 p2534 p3166 p3256 p3549 p3591 p4420 : Prop) (h : (¬ p3166) ∨ (¬ p3591) ∨ (¬ p3549) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4420) ∨ (¬ p2248) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2534) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial21631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory10887 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21631 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2534) (meaning t m 3166) (meaning t m 3256) (meaning t m 3549) (meaning t m 3591) (meaning t m 4420) source

theorem rule21632 (p2027 p2248 p2528 p2651 p3083 p3549 p3591 p4107 p4669 : Prop) (h : (¬ p4107) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p4669) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3549) ∨ (¬ p2528) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial21632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10888 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21632 (meaning t m 2027) (meaning t m 2248) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4669) source

theorem rule21640 (p2027 p2311 p2352 p2581 p3961 p3979 p5590 : Prop) (h : (¬ p2352) ∨ p2027 ∨ (¬ p2581) ∨ (¬ p3961) ∨ (¬ p2311) ∨ (¬ p5590) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2352) ∨ (¬ p2581) ∨ (¬ p3961) ∨ (¬ p3979) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial21640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory10896 t (m.theta 0 6) (m.theta 0 7) (m.theta 0 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10)
  exact rule21640 (meaning t m 2027) (meaning t m 2311) (meaning t m 2352) (meaning t m 2581) (meaning t m 3961) (meaning t m 3979) (meaning t m 5590) source

theorem rule21641 (p1990 p2027 p2284 p2873 p2972 p3136 p4035 p4040 : Prop) (h : p2873 ∨ (¬ p2972) ∨ (¬ p3136) ∨ (¬ p1990) ∨ (¬ p2284) ∨ (¬ p4040) ∨ (¬ p4035) ∨ p2027) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2873) ∨ (¬ p2972) ∨ (¬ p3136) ∨ (¬ p4035) ∨ (¬ p4040) := by
  classical
  tauto

theorem initial21641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4040)) := by
  have source := ElevenTheory.theory10897 t (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 6) (m.theta 5 9)
  exact rule21641 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2873) (meaning t m 2972) (meaning t m 3136) (meaning t m 4035) (meaning t m 4040) source

theorem rule21644 (p2027 p2440 p2860 p3582 p3646 p4031 p4753 : Prop) (h : (¬ p4753) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p3582) ∨ (¬ p2860) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2860) ∨ (¬ p3582) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial21644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory10900 t (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule21644 (meaning t m 2027) (meaning t m 2440) (meaning t m 2860) (meaning t m 3582) (meaning t m 3646) (meaning t m 4031) (meaning t m 4753) source

theorem rule21645 (p2027 p2860 p3051 p3646 p4235 p4885 : Prop) (h : p2027 ∨ (¬ p4235) ∨ (¬ p3646) ∨ (¬ p3051) ∨ (¬ p4885) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2860) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial21645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory10901 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule21645 (meaning t m 2027) (meaning t m 2860) (meaning t m 3051) (meaning t m 3646) (meaning t m 4235) (meaning t m 4885) source

theorem rule21646 (p1982 p2027 p2098 p2355 p2459 p3365 p3572 p4804 : Prop) (h : (¬ p1982) ∨ p2355 ∨ (¬ p2098) ∨ (¬ p4804) ∨ (¬ p3365) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3572)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (p2355) ∨ (¬ p2459) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4804) := by
  classical
  tauto

theorem initial21646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4804)) := by
  have source := ElevenTheory.theory10902 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21646 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2355) (meaning t m 2459) (meaning t m 3365) (meaning t m 3572) (meaning t m 4804) source

theorem rule21647 (p1982 p2027 p2352 p2363 p2573 p2656 p2688 p2727 : Prop) (h : (¬ p1982) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2727) ∨ p2688) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial21647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory10903 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule21647 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) source

theorem rule21649 (p2027 p2608 p2761 p3051 p3246 p3519 p3860 p4353 p4376 p4399 p5123 p5612 : Prop) (h : (¬ p5123) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4353) ∨ (¬ p3860) ∨ (¬ p3519) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p5612) ∨ (¬ p4399) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p4353) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial21649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4353)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory10905 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21649 (meaning t m 2027) (meaning t m 2608) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 3519) (meaning t m 3860) (meaning t m 4353) (meaning t m 4376) (meaning t m 4399) (meaning t m 5123) (meaning t m 5612) source

theorem rule21652 (p2027 p2156 p2190 p2608 p3146 p3519 p3548 p4133 p4347 p4366 p4376 p4399 : Prop) (h : (¬ p4376) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2156) ∨ (¬ p3519) ∨ (¬ p3548) ∨ (¬ p4347) ∨ (¬ p2608) ∨ (¬ p4133) ∨ (¬ p4399) ∨ (¬ p2190) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (¬ p3519) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial21652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory10908 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21652 (meaning t m 2027) (meaning t m 2156) (meaning t m 2190) (meaning t m 2608) (meaning t m 3146) (meaning t m 3519) (meaning t m 3548) (meaning t m 4133) (meaning t m 4347) (meaning t m 4366) (meaning t m 4376) (meaning t m 4399) source

theorem rule21655 (p1987 p2027 p2287 p2295 p2696 p2780 p3822 : Prop) (h : (¬ p1987) ∨ p2027 ∨ p2287 ∨ (¬ p2295) ∨ (¬ p3822) ∨ (¬ p2780) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial21655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory10911 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule21655 (meaning t m 1987) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2696) (meaning t m 2780) (meaning t m 3822) source

theorem rule21656 (p2027 p3073 p3585 p4340 p4364 p4749 p5316 : Prop) (h : (¬ p4364) ∨ (¬ p4749) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p5316) ∨ (¬ p4340)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3585) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4749) ∨ (¬ p5316) := by
  classical
  tauto

theorem initial21656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5316)) := by
  have source := ElevenTheory.theory10912 t (m.theta 1 2) (m.theta 1 8) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 8 9)
  exact rule21656 (meaning t m 2027) (meaning t m 3073) (meaning t m 3585) (meaning t m 4340) (meaning t m 4364) (meaning t m 4749) (meaning t m 5316) source

theorem rule21658 (p2027 p2373 p3979 p4199 p4433 p5433 : Prop) (h : (¬ p4433) ∨ (¬ p3979) ∨ (¬ p2373) ∨ (¬ p5433) ∨ p2027 ∨ (¬ p4199)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3979) ∨ (¬ p4199) ∨ (¬ p4433) ∨ (¬ p5433) := by
  classical
  tauto

theorem initial21658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4199)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5433)) := by
  have source := ElevenTheory.theory10914 t (m.theta 4 5) (m.theta 5 10) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10)
  exact rule21658 (meaning t m 2027) (meaning t m 2373) (meaning t m 3979) (meaning t m 4199) (meaning t m 4433) (meaning t m 5433) source

theorem rule21659 (p2563 p3957 p4210 p4338 : Prop) (h : (¬ p2563) ∨ (¬ p3957) ∨ p4338 ∨ (¬ p4210)) : (¬ p2563) ∨ (¬ p3957) ∨ (¬ p4210) ∨ (p4338) := by
  classical
  tauto

theorem initial21659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4210)) ∨ (meaning t m 4338) := by
  have source := ElevenTheory.theory10915 (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6)
  exact rule21659 (meaning t m 2563) (meaning t m 3957) (meaning t m 4210) (meaning t m 4338) source

theorem rule21661 (p2027 p2241 p2750 p2839 p2870 p2881 p3860 p3947 p4044 p4666 p5074 : Prop) (h : p2027 ∨ (¬ p2839) ∨ (¬ p2750) ∨ (¬ p5074) ∨ (¬ p2241) ∨ (¬ p4044) ∨ (¬ p2881) ∨ (¬ p4666) ∨ (¬ p3860) ∨ (¬ p3947) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3860) ∨ (¬ p3947) ∨ (¬ p4044) ∨ (¬ p4666) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial21661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory10917 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21661 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2839) (meaning t m 2870) (meaning t m 2881) (meaning t m 3860) (meaning t m 3947) (meaning t m 4044) (meaning t m 4666) (meaning t m 5074) source

theorem rule21664 (p1982 p2027 p2459 p2622 p2630 p2656 p2911 p3389 : Prop) (h : (¬ p2656) ∨ (¬ p2630) ∨ p2622 ∨ (¬ p3389) ∨ (¬ p2911) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2911) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial21664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory10920 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21664 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 2911) (meaning t m 3389) source

theorem rule21666 (p2027 p2156 p2427 p4110 p4984 p4990 : Prop) (h : (¬ p4990) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4984)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4984) ∨ (¬ p4990) := by
  classical
  tauto

theorem initial21666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4984)) ∨ (¬ (meaning t m 4990)) := by
  have source := ElevenTheory.theory10922 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule21666 (meaning t m 2027) (meaning t m 2156) (meaning t m 2427) (meaning t m 4110) (meaning t m 4984) (meaning t m 4990) source

theorem rule21670 (p2027 p2166 p2210 p2254 p2963 p3969 p4328 p4347 p4358 p5122 : Prop) (h : (¬ p4358) ∨ (¬ p2963) ∨ (¬ p2254) ∨ (¬ p4347) ∨ (¬ p4328) ∨ (¬ p2166) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3969) ∨ (¬ p4328) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial21670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory10926 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21670 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 2963) (meaning t m 3969) (meaning t m 4328) (meaning t m 4347) (meaning t m 4358) (meaning t m 5122) source

theorem rule21671 (p2027 p2132 p3452 p3583 p3589 p4376 : Prop) (h : (¬ p2132) ∨ (¬ p3589) ∨ (¬ p3583) ∨ (¬ p3452) ∨ (¬ p4376) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p3452) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial21671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory10927 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5)
  exact rule21671 (meaning t m 2027) (meaning t m 2132) (meaning t m 3452) (meaning t m 3583) (meaning t m 3589) (meaning t m 4376) source

theorem rule21673 (p2027 p2254 p2352 p2493 p2952 p3379 p3570 p4133 p4320 : Prop) (h : (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p4320) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial21673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory10929 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule21673 (meaning t m 2027) (meaning t m 2254) (meaning t m 2352) (meaning t m 2493) (meaning t m 2952) (meaning t m 3379) (meaning t m 3570) (meaning t m 4133) (meaning t m 4320) source

theorem rule21674 (p2027 p2254 p2352 p2459 p2493 p3172 p3379 p4118 p4133 : Prop) (h : (¬ p3172) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2493) ∨ (¬ p4133) ∨ (¬ p4118) ∨ (¬ p3379) ∨ (¬ p2352) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p4118) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial21674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory10930 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21674 (meaning t m 2027) (meaning t m 2254) (meaning t m 2352) (meaning t m 2459) (meaning t m 2493) (meaning t m 3172) (meaning t m 3379) (meaning t m 4118) (meaning t m 4133) source

theorem rule21675 (p2027 p2254 p2493 p3379 p3414 p3553 p3564 p4330 p4348 : Prop) (h : (¬ p3414) ∨ (¬ p4348) ∨ (¬ p3564) ∨ (¬ p2493) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4330) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10931 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21675 (meaning t m 2027) (meaning t m 2254) (meaning t m 2493) (meaning t m 3379) (meaning t m 3414) (meaning t m 3553) (meaning t m 3564) (meaning t m 4330) (meaning t m 4348) source

theorem rule21677 (p2027 p2254 p2952 p3073 p3449 p3570 p4133 p4320 p4347 : Prop) (h : (¬ p3449) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320) ∨ (¬ p3073) ∨ (¬ p2952) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4320) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10933 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21677 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3073) (meaning t m 3449) (meaning t m 3570) (meaning t m 4133) (meaning t m 4320) (meaning t m 4347) source

theorem rule21679 (p2027 p2254 p2528 p2608 p2619 p2839 p3172 p4118 p4434 : Prop) (h : (¬ p2839) ∨ (¬ p4118) ∨ (¬ p2608) ∨ (¬ p3172) ∨ (¬ p4434) ∨ (¬ p2619) ∨ (¬ p2528) ∨ (¬ p2254) ∨ p2027) : (p2027) ∨ (¬ p2254) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial21679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory10935 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule21679 (meaning t m 2027) (meaning t m 2254) (meaning t m 2528) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 3172) (meaning t m 4118) (meaning t m 4434) source

theorem rule21683 (p2027 p2440 p2657 p2786 p3461 p3654 p3951 p4381 p4789 p4948 : Prop) (h : (¬ p2786) ∨ (¬ p4948) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p4789) ∨ (¬ p3951)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p3951) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial21683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory10939 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21683 (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2786) (meaning t m 3461) (meaning t m 3654) (meaning t m 3951) (meaning t m 4381) (meaning t m 4789) (meaning t m 4948) source

theorem rule21685 (p2027 p2542 p2589 p2655 p2786 p3359 p3461 p3654 p4444 p4697 p4789 : Prop) (h : (¬ p2786) ∨ (¬ p2655) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p4789) ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p3654) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2786) ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial21685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory10941 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21685 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2786) (meaning t m 3359) (meaning t m 3461) (meaning t m 3654) (meaning t m 4444) (meaning t m 4697) (meaning t m 4789) source

theorem rule21686 (p2027 p2177 p2307 p2440 p2459 p2657 p2786 p4789 p4948 p5059 : Prop) (h : (¬ p4789) ∨ (¬ p2786) ∨ (¬ p2459) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2657) ∨ (¬ p2440) ∨ (¬ p5059) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p4789) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial21686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory10942 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21686 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2440) (meaning t m 2459) (meaning t m 2657) (meaning t m 2786) (meaning t m 4789) (meaning t m 4948) (meaning t m 5059) source

theorem rule21690 (p2027 p2254 p2774 p2952 p3537 p3570 p3589 p3688 p4320 p4802 : Prop) (h : (¬ p4802) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p3589) ∨ (¬ p2254) ∨ (¬ p3537) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3537) ∨ (¬ p3570) ∨ (¬ p3589) ∨ (¬ p3688) ∨ (¬ p4320) ∨ (¬ p4802) := by
  classical
  tauto

theorem initial21690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4802)) := by
  have source := ElevenTheory.theory10946 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule21690 (meaning t m 2027) (meaning t m 2254) (meaning t m 2774) (meaning t m 2952) (meaning t m 3537) (meaning t m 3570) (meaning t m 3589) (meaning t m 3688) (meaning t m 4320) (meaning t m 4802) source

theorem rule21691 (p2008 p2027 p2088 p2254 p2633 p2707 p2952 p3570 p4114 p4242 p4320 p4340 p5020 : Prop) (h : p2027 ∨ (¬ p2008) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p2952) ∨ p2633 ∨ (¬ p5020) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p2088) ∨ (¬ p4114)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2254) ∨ (p2633) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4114) ∨ (¬ p4242) ∨ (¬ p4320) ∨ (¬ p4340) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial21691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2254)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory10947 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 0 8) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21691 (meaning t m 2008) (meaning t m 2027) (meaning t m 2088) (meaning t m 2254) (meaning t m 2633) (meaning t m 2707) (meaning t m 2952) (meaning t m 3570) (meaning t m 4114) (meaning t m 4242) (meaning t m 4320) (meaning t m 4340) (meaning t m 5020) source

theorem rule21692 (p2027 p3016 p3564 p4026 p4202 p4512 p4811 : Prop) (h : (¬ p4811) ∨ p2027 ∨ (¬ p4202) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p3016) ∨ (¬ p3564)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p4026) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial21692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory10948 t (m.theta 1 4) (m.theta 1 5) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9)
  exact rule21692 (meaning t m 2027) (meaning t m 3016) (meaning t m 3564) (meaning t m 4026) (meaning t m 4202) (meaning t m 4512) (meaning t m 4811) source

theorem rule21693 (p2534 p4261 p4370 : Prop) (h : (¬ p4370) ∨ (¬ p2534) ∨ p4261) : (¬ p2534) ∨ (p4261) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial21693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2534)) ∨ (meaning t m 4261) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory10949 (m.theta 1 8) (m.theta 4 8) (m.theta 8 9)
  exact rule21693 (meaning t m 2534) (meaning t m 4261) (meaning t m 4370) source

theorem rule21694 (p1985 p2027 p2166 p2765 p2870 p3412 p3694 p3952 : Prop) (h : (¬ p3694) ∨ p2765 ∨ p2027 ∨ (¬ p1985) ∨ (¬ p3412) ∨ (¬ p2166) ∨ (¬ p3952) ∨ (¬ p2870)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2166) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p3412) ∨ (¬ p3694) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial21694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory10950 t (m.theta 1 5) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule21694 (meaning t m 1985) (meaning t m 2027) (meaning t m 2166) (meaning t m 2765) (meaning t m 2870) (meaning t m 3412) (meaning t m 3694) (meaning t m 3952) source

theorem rule21695 (p2027 p2254 p2608 p2829 p3414 p3483 p3553 p4330 p4348 : Prop) (h : (¬ p3483) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3414) ∨ (¬ p3483) ∨ (¬ p3553) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial21695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10951 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21695 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 3414) (meaning t m 3483) (meaning t m 3553) (meaning t m 4330) (meaning t m 4348) source

theorem rule21696 (p2027 p2254 p2493 p2952 p3379 p3497 p3564 p3692 p4330 : Prop) (h : p2027 ∨ (¬ p3692) ∨ (¬ p4330) ∨ (¬ p2493) ∨ (¬ p3564) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2493) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial21696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory10952 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule21696 (meaning t m 2027) (meaning t m 2254) (meaning t m 2493) (meaning t m 2952) (meaning t m 3379) (meaning t m 3497) (meaning t m 3564) (meaning t m 3692) (meaning t m 4330) source

theorem rule21698 (p2027 p2254 p2396 p2952 p3093 p3309 p3497 p3692 p3950 : Prop) (h : (¬ p3692) ∨ (¬ p2254) ∨ (¬ p3497) ∨ (¬ p3950) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p2396) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2396) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial21698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory10954 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21698 (meaning t m 2027) (meaning t m 2254) (meaning t m 2396) (meaning t m 2952) (meaning t m 3093) (meaning t m 3309) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule21699 (p2027 p2254 p2952 p3093 p3319 p3461 p3497 p5123 p5568 : Prop) (h : p2027 ∨ (¬ p3497) ∨ (¬ p3319) ∨ (¬ p5123) ∨ (¬ p2952) ∨ (¬ p5568) ∨ (¬ p3093) ∨ (¬ p2254) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3497) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial21699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory10955 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21699 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 3497) (meaning t m 5123) (meaning t m 5568) source

theorem rule21700 (p2027 p2254 p2657 p3063 p3093 p3359 p3979 p4425 p5119 : Prop) (h : (¬ p3979) ∨ (¬ p3093) ∨ (¬ p3359) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3063) ∨ p2027) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3359) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory10956 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21700 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3063) (meaning t m 3093) (meaning t m 3359) (meaning t m 3979) (meaning t m 4425) (meaning t m 5119) source

theorem rule21702 (p2210 p3954 p4436 p4496 : Prop) (h : (¬ p3954) ∨ (¬ p2210) ∨ (¬ p4496) ∨ (¬ p4436)) : (¬ p2210) ∨ (¬ p3954) ∨ (¬ p4436) ∨ (¬ p4496) := by
  classical
  tauto

theorem initial21702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 4496)) := by
  have source := ElevenTheory.theory10958 (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8)
  exact rule21702 (meaning t m 2210) (meaning t m 3954) (meaning t m 4436) (meaning t m 4496) source

theorem rule21703 (p1982 p2027 p2177 p2427 p2459 p2765 p4110 p4140 : Prop) (h : (¬ p4140) ∨ (¬ p2177) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (p2765) ∨ (¬ p4110) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial21703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory10959 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21703 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2427) (meaning t m 2459) (meaning t m 2765) (meaning t m 4110) (meaning t m 4140) source

theorem rule21708 (p2027 p2406 p2870 p2928 p4001 p4885 : Prop) (h : (¬ p2406) ∨ (¬ p4885) ∨ (¬ p2870) ∨ (¬ p2928) ∨ (¬ p4001) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p2870) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial21708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory10964 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule21708 (meaning t m 2027) (meaning t m 2406) (meaning t m 2870) (meaning t m 2928) (meaning t m 4001) (meaning t m 4885) source

theorem rule21710 (p2027 p2254 p2608 p2829 p3414 p3914 p3947 p4381 p5250 : Prop) (h : p2027 ∨ (¬ p2829) ∨ (¬ p3914) ∨ (¬ p2608) ∨ (¬ p5250) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p4381) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3414) ∨ (¬ p3914) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial21710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory10966 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule21710 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 3414) (meaning t m 3914) (meaning t m 3947) (meaning t m 4381) (meaning t m 5250) source

theorem rule21711 (p2027 p2254 p2608 p2839 p3105 p3266 p3292 p4450 p5284 : Prop) (h : p2027 ∨ (¬ p4450) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p3105) ∨ (¬ p2839) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p4450) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10967 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 9) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21711 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 3266) (meaning t m 3292) (meaning t m 4450) (meaning t m 5284) source

theorem rule21713 (p2156 p2951 p3872 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p2156) ∨ (¬ p2951) ∨ (¬ p3872)) : (¬ p2156) ∨ (¬ p2951) ∨ (¬ p3872) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial21713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory10969 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule21713 (meaning t m 2156) (meaning t m 2951) (meaning t m 3872) (meaning t m 4320) source

theorem rule21715 (p2027 p3309 p3461 p4321 p4430 p4620 : Prop) (h : (¬ p4620) ∨ (¬ p4430) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3461) ∨ (¬ p4321)) : (p2027) ∨ (¬ p3309) ∨ (¬ p3461) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial21715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4430)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory10971 t (m.theta 1 6) (m.theta 1 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule21715 (meaning t m 2027) (meaning t m 3309) (meaning t m 3461) (meaning t m 4321) (meaning t m 4430) (meaning t m 4620) source

theorem rule21717 (p2027 p2254 p2406 p2963 p2982 p3324 p3379 p4347 p4450 : Prop) (h : (¬ p2982) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p4450) ∨ (¬ p3324) ∨ (¬ p2406) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2406) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial21717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory10973 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule21717 (meaning t m 2027) (meaning t m 2254) (meaning t m 2406) (meaning t m 2963) (meaning t m 2982) (meaning t m 3324) (meaning t m 3379) (meaning t m 4347) (meaning t m 4450) source

theorem rule21718 (p2027 p2254 p2963 p3222 p3276 p3324 p3379 p5123 p5580 : Prop) (h : p2027 ∨ (¬ p5580) ∨ (¬ p3324) ∨ (¬ p2963) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial21718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory10974 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21718 (meaning t m 2027) (meaning t m 2254) (meaning t m 2963) (meaning t m 3222) (meaning t m 3276) (meaning t m 3324) (meaning t m 3379) (meaning t m 5123) (meaning t m 5580) source

theorem rule21720 (p2027 p2254 p2417 p2922 p3292 p3379 p3461 p4625 p5284 : Prop) (h : (¬ p2922) ∨ (¬ p4625) ∨ (¬ p2417) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p5284) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3292) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p4625) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial21720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10976 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21720 (meaning t m 2027) (meaning t m 2254) (meaning t m 2417) (meaning t m 2922) (meaning t m 3292) (meaning t m 3379) (meaning t m 3461) (meaning t m 4625) (meaning t m 5284) source

theorem rule21722 (p3093 p3860 p4317 : Prop) (h : (¬ p3860) ∨ (¬ p3093) ∨ (¬ p4317)) : (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial21722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory10978 (m.theta 0 1) (m.theta 1 6) (m.theta 1 8)
  exact rule21722 (meaning t m 3093) (meaning t m 3860) (meaning t m 4317) source

theorem rule21723 (p1982 p2027 p3042 p3506 p3755 p3877 p4444 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p4444) ∨ (¬ p3877) ∨ (¬ p3755) ∨ p3042 ∨ (¬ p3506)) : (¬ p1982) ∨ (p2027) ∨ (p3042) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial21723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory10979 t (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21723 (meaning t m 1982) (meaning t m 2027) (meaning t m 3042) (meaning t m 3506) (meaning t m 3755) (meaning t m 3877) (meaning t m 4444) source

theorem rule21724 (p1982 p2027 p2363 p2383 p2545 p2797 p2810 p3567 : Prop) (h : (¬ p1982) ∨ (¬ p2797) ∨ (¬ p2363) ∨ (¬ p3567) ∨ p2027 ∨ (¬ p2810) ∨ p2545 ∨ (¬ p2383)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial21724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory10980 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule21724 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 3567) source

theorem rule21728 (p2027 p2254 p2608 p2839 p3105 p3414 p3553 p4348 p4450 : Prop) (h : (¬ p4348) ∨ (¬ p3553) ∨ (¬ p3105) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p4450) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial21728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory10984 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21728 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) (meaning t m 4450) source

theorem rule21729 (p2027 p2254 p2657 p2761 p3399 p3574 p3631 p5254 p5514 : Prop) (h : (¬ p3574) ∨ (¬ p5254) ∨ (¬ p2761) ∨ (¬ p5514) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3574) ∨ (¬ p3631) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial21729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory10985 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule21729 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 2761) (meaning t m 3399) (meaning t m 3574) (meaning t m 3631) (meaning t m 5254) (meaning t m 5514) source

theorem rule21730 (p2780 p3055 p5220 : Prop) (h : (¬ p3055) ∨ (¬ p5220) ∨ p2780) : (p2780) ∨ (¬ p3055) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial21730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2780) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory10986 (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule21730 (meaning t m 2780) (meaning t m 3055) (meaning t m 5220) source

theorem rule21732 (p2027 p3379 p3641 p3860 p4370 p5214 : Prop) (h : (¬ p4370) ∨ (¬ p5214) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p3860)) : (p2027) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p4370) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial21732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory10988 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 2 4) (m.theta 4 8)
  exact rule21732 (meaning t m 2027) (meaning t m 3379) (meaning t m 3641) (meaning t m 3860) (meaning t m 4370) (meaning t m 5214) source

theorem rule21735 (p1976 p2622 p4232 p5460 : Prop) (h : (¬ p4232) ∨ p2622 ∨ (¬ p1976) ∨ p5460) : (¬ p1976) ∨ (p2622) ∨ (¬ p4232) ∨ (p5460) := by
  classical
  tauto

theorem initial21735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 4232)) ∨ (meaning t m 5460) := by
  have source := ElevenTheory.theory10991 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 9)
  exact rule21735 (meaning t m 1976) (meaning t m 2622) (meaning t m 4232) (meaning t m 5460) source

theorem rule21740 (p2027 p2230 p2299 p2440 p2780 p3083 p3822 p4419 p4420 : Prop) (h : (¬ p2230) ∨ (¬ p4419) ∨ (¬ p2780) ∨ (¬ p2440) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p4420) ∨ (¬ p2299) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p3083) ∨ (¬ p3822) ∨ (¬ p4419) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial21740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory10996 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21740 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2440) (meaning t m 2780) (meaning t m 3083) (meaning t m 3822) (meaning t m 4419) (meaning t m 4420) source

theorem rule21741 (p2027 p2104 p2284 p2946 p3125 p3266 p4330 p4786 p5338 p5387 : Prop) (h : (¬ p3125) ∨ (¬ p2284) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p4786) ∨ (¬ p2104) ∨ (¬ p5387) ∨ (¬ p3266) ∨ (¬ p5338)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p4330) ∨ (¬ p4786) ∨ (¬ p5338) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial21741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5338)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory10997 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 2 9) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule21741 (meaning t m 2027) (meaning t m 2104) (meaning t m 2284) (meaning t m 2946) (meaning t m 3125) (meaning t m 3266) (meaning t m 4330) (meaning t m 4786) (meaning t m 5338) (meaning t m 5387) source

theorem rule21744 (p2373 p2982 p4335 : Prop) (h : (¬ p4335) ∨ (¬ p2982) ∨ p2373) : (p2373) ∨ (¬ p2982) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial21744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2373) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory11000 (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule21744 (meaning t m 2373) (meaning t m 2982) (meaning t m 4335) source

theorem rule21745 (p3822 p3955 p4358 : Prop) (h : (¬ p3955) ∨ (¬ p3822) ∨ p4358) : (¬ p3822) ∨ (¬ p3955) ∨ (p4358) := by
  classical
  tauto

theorem initial21745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3955)) ∨ (meaning t m 4358) := by
  have source := ElevenTheory.theory11001 (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule21745 (meaning t m 3822) (meaning t m 3955) (meaning t m 4358) source

theorem rule21746 (p2717 p3945 p4324 : Prop) (h : (¬ p4324) ∨ (¬ p3945) ∨ (¬ p2717)) : (¬ p2717) ∨ (¬ p3945) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial21746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory11002 (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21746 (meaning t m 2717) (meaning t m 3945) (meaning t m 4324) source

theorem rule21747 (p1976 p2027 p2588 p2810 p2997 p3365 p3574 : Prop) (h : (¬ p2810) ∨ (¬ p1976) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2588) ∨ p2997) : (¬ p1976) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2810) ∨ (p2997) ∨ (¬ p3365) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial21747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory11003 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule21747 (meaning t m 1976) (meaning t m 2027) (meaning t m 2588) (meaning t m 2810) (meaning t m 2997) (meaning t m 3365) (meaning t m 3574) source

theorem rule21748 (p2027 p2264 p3034 p3399 p3542 p3860 : Prop) (h : (¬ p2264) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p3542) ∨ (¬ p3034)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3034) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) := by
  classical
  tauto

theorem initial21748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3034)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3860)) := by
  have source := ElevenTheory.theory11004 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8)
  exact rule21748 (meaning t m 2027) (meaning t m 2264) (meaning t m 3034) (meaning t m 3399) (meaning t m 3542) (meaning t m 3860) source

theorem rule21750 (p3005 p3755 p5111 : Prop) (h : (¬ p5111) ∨ (¬ p3005) ∨ p3755) : (¬ p3005) ∨ (p3755) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial21750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3005)) ∨ (meaning t m 3755) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory11006 (m.theta 2 3) (m.theta 3 8) (m.theta 3 9)
  exact rule21750 (meaning t m 3005) (meaning t m 3755) (meaning t m 5111) source

theorem rule21751 (p2363 p3073 p4318 : Prop) (h : (¬ p4318) ∨ (¬ p2363) ∨ p3073) : (¬ p2363) ∨ (p3073) ∨ (¬ p4318) := by
  classical
  tauto

theorem initial21751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (meaning t m 3073) ∨ (¬ (meaning t m 4318)) := by
  have source := ElevenTheory.theory11007 (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21751 (meaning t m 2363) (meaning t m 3073) (meaning t m 4318) source

theorem rule21752 (p3740 p3868 p3931 : Prop) (h : (¬ p3740) ∨ (¬ p3931) ∨ p3868) : (¬ p3740) ∨ (p3868) ∨ (¬ p3931) := by
  classical
  tauto

theorem initial21752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3740)) ∨ (meaning t m 3868) ∨ (¬ (meaning t m 3931)) := by
  have source := ElevenTheory.theory11008 (m.theta 3 7) (m.theta 4 7) (m.theta 7 10)
  exact rule21752 (meaning t m 3740) (meaning t m 3868) (meaning t m 3931) source

theorem rule21753 (p1988 p2027 p2210 p2254 p2299 p2633 p2972 p3414 p3680 p3791 p4391 : Prop) (h : p2633 ∨ (¬ p2299) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p1988) ∨ (¬ p3791) ∨ (¬ p3414)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2972) ∨ (¬ p3414) ∨ (¬ p3680) ∨ (¬ p3791) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial21753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory11009 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8) (m.theta 9 10)
  exact rule21753 (meaning t m 1988) (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2299) (meaning t m 2633) (meaning t m 2972) (meaning t m 3414) (meaning t m 3680) (meaning t m 3791) (meaning t m 4391) source

theorem rule21756 (p2027 p2191 p3005 p3171 p4115 p4315 p4957 : Prop) (h : (¬ p2191) ∨ (¬ p4115) ∨ (¬ p3005) ∨ (¬ p4957) ∨ p2027 ∨ (¬ p3171) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2191) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4115) ∨ (¬ p4315) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial21756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory11012 t (m.theta 0 8) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule21756 (meaning t m 2027) (meaning t m 2191) (meaning t m 3005) (meaning t m 3171) (meaning t m 4115) (meaning t m 4315) (meaning t m 4957) source

theorem rule21760 (p2027 p2248 p2651 p3083 p3591 p4026 p4149 p4191 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p4191) ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p2248) ∨ (¬ p3083) ∨ (¬ p4149) ∨ (¬ p2651) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory11016 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21760 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3083) (meaning t m 3591) (meaning t m 4026) (meaning t m 4149) (meaning t m 4191) (meaning t m 5119) source

theorem rule21762 (p2027 p3483 p3692 p4358 p4433 p4460 p5379 : Prop) (h : p2027 ∨ (¬ p5379) ∨ (¬ p4460) ∨ (¬ p4358) ∨ (¬ p3483) ∨ (¬ p3692) ∨ (¬ p4433)) : (p2027) ∨ (¬ p3483) ∨ (¬ p3692) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p4460) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial21762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4460)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory11018 t (m.theta 0 9) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule21762 (meaning t m 2027) (meaning t m 3483) (meaning t m 3692) (meaning t m 4358) (meaning t m 4433) (meaning t m 4460) (meaning t m 5379) source

theorem rule21763 (p3956 p4342 p4358 : Prop) (h : (¬ p3956) ∨ (¬ p4342) ∨ p4358) : (¬ p3956) ∨ (¬ p4342) ∨ (p4358) := by
  classical
  tauto

theorem initial21763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4342)) ∨ (meaning t m 4358) := by
  have source := ElevenTheory.theory11019 (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule21763 (meaning t m 3956) (meaning t m 4342) (meaning t m 4358) source

theorem rule21765 (p3366 p3589 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p3366) ∨ (¬ p3589)) : (¬ p3366) ∨ (¬ p3589) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial21765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory11021 (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule21765 (meaning t m 3366) (meaning t m 3589) (meaning t m 3954) source

theorem rule21767 (p2027 p2156 p2247 p2373 p2996 p3553 p4110 p4133 p4441 p4521 : Prop) (h : (¬ p4521) ∨ (¬ p4110) ∨ (¬ p3553) ∨ (¬ p2247) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4133) ∨ (¬ p2373) ∨ (¬ p4441)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4110) ∨ (¬ p4133) ∨ (¬ p4441) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial21767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory11023 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule21767 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2373) (meaning t m 2996) (meaning t m 3553) (meaning t m 4110) (meaning t m 4133) (meaning t m 4441) (meaning t m 4521) source

theorem rule21770 (p2027 p2248 p2651 p3083 p3555 p4149 p4322 p4363 p5119 : Prop) (h : (¬ p3555) ∨ (¬ p4363) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p4149) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3555) ∨ (¬ p4149) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial21770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory11026 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21770 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3083) (meaning t m 3555) (meaning t m 4149) (meaning t m 4322) (meaning t m 4363) (meaning t m 5119) source

theorem rule21771 (p2027 p2248 p2264 p2459 p2807 p3555 p3744 p4173 p4604 : Prop) (h : p2027 ∨ (¬ p2264) ∨ (¬ p2248) ∨ (¬ p4604) ∨ (¬ p4173) ∨ (¬ p3744) ∨ (¬ p3555) ∨ (¬ p2807) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial21771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory11027 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21771 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4604) source

theorem rule21772 (p2027 p2248 p2352 p2651 p3016 p3486 p3555 p3570 p4133 : Prop) (h : (¬ p4133) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3486) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial21772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory11028 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule21772 (meaning t m 2027) (meaning t m 2248) (meaning t m 2352) (meaning t m 2651) (meaning t m 3016) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4133) source

theorem rule21773 (p2027 p2248 p2331 p3256 p3486 p3555 p3570 p4133 p4341 p4347 : Prop) (h : (¬ p4341) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2331) ∨ (¬ p2248) ∨ (¬ p3256) ∨ (¬ p3555) ∨ (¬ p4347) ∨ (¬ p3486) ∨ (¬ p4133)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3256) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4341) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory11029 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21773 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 3256) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4133) (meaning t m 4341) (meaning t m 4347) source

theorem rule21776 (p2027 p2406 p2528 p3453 p4261 p4608 : Prop) (h : (¬ p4608) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2528) ∨ (¬ p4261) ∨ (¬ p3453)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2528) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial21776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory11032 t (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule21776 (meaning t m 2027) (meaning t m 2406) (meaning t m 2528) (meaning t m 3453) (meaning t m 4261) (meaning t m 4608) source

theorem rule21778 (p1976 p2027 p2136 p2764 p2870 p3556 p4381 p4382 p4385 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p2870) ∨ (¬ p2136) ∨ (¬ p4381) ∨ (¬ p3556) ∨ p2764 ∨ (¬ p4385) ∨ (¬ p4382)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2136) ∨ (p2764) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4381) ∨ (¬ p4382) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial21778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory11034 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21778 (meaning t m 1976) (meaning t m 2027) (meaning t m 2136) (meaning t m 2764) (meaning t m 2870) (meaning t m 3556) (meaning t m 4381) (meaning t m 4382) (meaning t m 4385) source

theorem rule21783 (p1988 p2027 p2323 p2573 p2663 p3276 p3343 p3574 : Prop) (h : (¬ p1988) ∨ (¬ p3574) ∨ (¬ p3276) ∨ (¬ p2663) ∨ (¬ p2573) ∨ p2027 ∨ p2323 ∨ (¬ p3343)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial21783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory11039 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule21783 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2573) (meaning t m 2663) (meaning t m 3276) (meaning t m 3343) (meaning t m 3574) source

theorem rule21784 (p3449 p3830 p4351 : Prop) (h : (¬ p3449) ∨ (¬ p4351) ∨ p3830) : (¬ p3449) ∨ (p3830) ∨ (¬ p4351) := by
  classical
  tauto

theorem initial21784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (meaning t m 3830) ∨ (¬ (meaning t m 4351)) := by
  have source := ElevenTheory.theory11040 (m.theta 0 1) (m.theta 1 8) (m.theta 1 9)
  exact rule21784 (meaning t m 3449) (meaning t m 3830) (meaning t m 4351) source

theorem rule21785 (p1985 p2027 p2114 p2137 p2156 p2839 p2901 p3952 : Prop) (h : p2027 ∨ (¬ p2137) ∨ (¬ p2156) ∨ p2114 ∨ (¬ p2839) ∨ (¬ p2901) ∨ (¬ p1985) ∨ (¬ p3952)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2839) ∨ (¬ p2901) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial21785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory11041 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule21785 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2156) (meaning t m 2839) (meaning t m 2901) (meaning t m 3952) source

theorem rule21786 (p1986 p2027 p2138 p2202 p2563 p2598 p3758 : Prop) (h : (¬ p2598) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3758) ∨ p2202 ∨ (¬ p2138) ∨ (¬ p2563)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2138) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial21786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory11042 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule21786 (meaning t m 1986) (meaning t m 2027) (meaning t m 2138) (meaning t m 2202) (meaning t m 2563) (meaning t m 2598) (meaning t m 3758) source

theorem rule21787 (p1978 p2027 p2202 p2563 p2972 p4032 p4173 : Prop) (h : (¬ p1978) ∨ p2027 ∨ (¬ p4173) ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2972) ∨ (¬ p4032)) : (¬ p1978) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2972) ∨ (¬ p4032) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial21787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory11043 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule21787 (meaning t m 1978) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2972) (meaning t m 4032) (meaning t m 4173) source

theorem rule21788 (p1982 p2027 p2248 p2331 p2363 p2589 p2668 p2938 p3105 p4108 p4244 p4948 : Prop) (h : (¬ p3105) ∨ p2938 ∨ (¬ p4948) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p4108) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2248) ∨ (¬ p2589)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (p2938) ∨ (¬ p3105) ∨ (¬ p4108) ∨ (¬ p4244) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial21788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory11044 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule21788 (meaning t m 1982) (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2589) (meaning t m 2668) (meaning t m 2938) (meaning t m 3105) (meaning t m 4108) (meaning t m 4244) (meaning t m 4948) source

theorem rule21789 (p2027 p2248 p2331 p3256 p3588 p3659 p3954 p4133 p4341 p4347 : Prop) (h : (¬ p2331) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3954) ∨ (¬ p3659) ∨ (¬ p3588) ∨ (¬ p4133) ∨ (¬ p3256) ∨ (¬ p4347) ∨ (¬ p4341)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3256) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p4341) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory11045 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21789 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 3256) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4133) (meaning t m 4341) (meaning t m 4347) source

end SunPrize.SMT
