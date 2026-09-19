import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory066
import SunPrize.Certificate.Theory067
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule38269 (p2027 p2657 p3166 p3874 p4687 p4750 p5074 : Prop) (h : (¬ p4687) ∨ (¬ p3874) ∨ (¬ p3166) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p5074) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3874) ∨ (¬ p4687) ∨ (¬ p4750) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial38269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4687)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory27525 t (m.theta 0 3) (m.theta 1 8) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule38269 (meaning t m 2027) (meaning t m 2657) (meaning t m 3166) (meaning t m 3874) (meaning t m 4687) (meaning t m 4750) (meaning t m 5074) source

theorem rule38275 (p2166 p3063 p4441 p4512 : Prop) (h : (¬ p2166) ∨ (¬ p4441) ∨ (¬ p4512) ∨ p3063) : (¬ p2166) ∨ (p3063) ∨ (¬ p4441) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial38275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (meaning t m 3063) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory27531 (m.theta 1 5) (m.theta 1 6) (m.theta 5 8) (m.theta 6 8)
  exact rule38275 (meaning t m 2166) (meaning t m 3063) (meaning t m 4441) (meaning t m 4512) source

theorem rule38277 (p2027 p3333 p3379 p3645 p3646 p3954 p3989 p4030 p4332 p4347 p4877 : Prop) (h : (¬ p3989) ∨ (¬ p3379) ∨ (¬ p4030) ∨ (¬ p4347) ∨ (¬ p4332) ∨ (¬ p3333) ∨ (¬ p3954) ∨ (¬ p3645) ∨ (¬ p4877) ∨ p2027 ∨ (¬ p3646)) : (p2027) ∨ (¬ p3333) ∨ (¬ p3379) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4030) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial38277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27533 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule38277 (meaning t m 2027) (meaning t m 3333) (meaning t m 3379) (meaning t m 3645) (meaning t m 3646) (meaning t m 3954) (meaning t m 3989) (meaning t m 4030) (meaning t m 4332) (meaning t m 4347) (meaning t m 4877) source

theorem rule38279 (p2264 p2911 p3740 : Prop) (h : (¬ p3740) ∨ (¬ p2264) ∨ p2911) : (¬ p2264) ∨ (p2911) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial38279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (meaning t m 2911) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory27535 (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule38279 (meaning t m 2264) (meaning t m 2911) (meaning t m 3740) source

theorem rule38284 (p2027 p2138 p2518 p2928 p3389 p3758 p3989 p4079 p4596 p4736 : Prop) (h : (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2138) ∨ (¬ p4596) ∨ (¬ p2518) ∨ (¬ p3758) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4079) ∨ (¬ p4596) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27540 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule38284 (meaning t m 2027) (meaning t m 2138) (meaning t m 2518) (meaning t m 2928) (meaning t m 3389) (meaning t m 3758) (meaning t m 3989) (meaning t m 4079) (meaning t m 4596) (meaning t m 4736) source

theorem rule38285 (p2027 p2138 p2352 p2493 p3097 p3379 p3758 p4405 p4736 : Prop) (h : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2138) ∨ (¬ p4736) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3758) ∨ (¬ p4405) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27541 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule38285 (meaning t m 2027) (meaning t m 2138) (meaning t m 2352) (meaning t m 2493) (meaning t m 3097) (meaning t m 3379) (meaning t m 3758) (meaning t m 4405) (meaning t m 4736) source

theorem rule38290 (p3662 p3842 p4314 : Prop) (h : (¬ p4314) ∨ (¬ p3662) ∨ (¬ p3842)) : (¬ p3662) ∨ (¬ p3842) ∨ (¬ p4314) := by
  classical
  tauto

theorem initial38290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4314)) := by
  have source := ElevenTheory.theory27546 (m.theta 1 3) (m.theta 3 5) (m.theta 3 9)
  exact rule38290 (meaning t m 3662) (meaning t m 3842) (meaning t m 4314) source

theorem rule38293 (p2027 p2331 p2657 p2992 p4154 p4704 : Prop) (h : (¬ p4704) ∨ (¬ p2992) ∨ (¬ p2657) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4154)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial38293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory27549 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule38293 (meaning t m 2027) (meaning t m 2331) (meaning t m 2657) (meaning t m 2992) (meaning t m 4154) (meaning t m 4704) source

theorem rule38297 (p2284 p3957 p4282 p4512 : Prop) (h : (¬ p3957) ∨ (¬ p4282) ∨ (¬ p2284) ∨ (¬ p4512)) : (¬ p2284) ∨ (¬ p3957) ∨ (¬ p4282) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial38297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory27553 (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6)
  exact rule38297 (meaning t m 2284) (meaning t m 3957) (meaning t m 4282) (meaning t m 4512) source

theorem rule38298 (p2027 p2143 p2696 p2742 p3189 p3256 p3583 p3646 p3744 p4604 p4737 : Prop) (h : (¬ p3646) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2143) ∨ (¬ p2742) ∨ (¬ p4604) ∨ (¬ p3583) ∨ (¬ p3256) ∨ (¬ p4737) ∨ (¬ p3744) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4604) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27554 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule38298 (meaning t m 2027) (meaning t m 2143) (meaning t m 2696) (meaning t m 2742) (meaning t m 3189) (meaning t m 3256) (meaning t m 3583) (meaning t m 3646) (meaning t m 3744) (meaning t m 4604) (meaning t m 4737) source

theorem rule38300 (p3880 p4031 p4120 : Prop) (h : (¬ p4120) ∨ (¬ p4031) ∨ p3880) : (p3880) ∨ (¬ p4031) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial38300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3880) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory27556 (m.theta 0 5) (m.theta 4 5) (m.theta 5 8)
  exact rule38300 (meaning t m 3880) (meaning t m 4031) (meaning t m 4120) source

theorem rule38301 (p2138 p3366 p3688 p4193 : Prop) (h : (¬ p2138) ∨ (¬ p3366) ∨ (¬ p4193) ∨ p3688) : (¬ p2138) ∨ (¬ p3366) ∨ (p3688) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial38301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3366)) ∨ (meaning t m 3688) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory27557 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule38301 (meaning t m 2138) (meaning t m 3366) (meaning t m 3688) (meaning t m 4193) source

theorem rule38303 (p1978 p2027 p2169 p2870 p3556 p3758 p3989 : Prop) (h : (¬ p1978) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3989) ∨ p2169) : (¬ p1978) ∨ (p2027) ∨ (p2169) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial38303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory27559 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule38303 (meaning t m 1978) (meaning t m 2027) (meaning t m 2169) (meaning t m 2870) (meaning t m 3556) (meaning t m 3758) (meaning t m 3989) source

theorem rule38304 (p2027 p2341 p2656 p2992 p3031 p3548 p4704 p5201 : Prop) (h : (¬ p2656) ∨ (¬ p3031) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4704) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial38304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory27560 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 5) (m.theta 7 8)
  exact rule38304 (meaning t m 2027) (meaning t m 2341) (meaning t m 2656) (meaning t m 2992) (meaning t m 3031) (meaning t m 3548) (meaning t m 4704) (meaning t m 5201) source

theorem rule38305 (p2027 p2143 p3097 p3471 p3527 p3583 p3644 p3646 p4276 p4424 p4737 : Prop) (h : (¬ p3471) ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p4737) ∨ (¬ p4424) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p4276) ∨ (¬ p3097) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2143) ∨ (¬ p3097) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3583) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4276) ∨ (¬ p4424) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27561 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 2 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule38305 (meaning t m 2027) (meaning t m 2143) (meaning t m 3097) (meaning t m 3471) (meaning t m 3527) (meaning t m 3583) (meaning t m 3644) (meaning t m 3646) (meaning t m 4276) (meaning t m 4424) (meaning t m 4737) source

theorem rule38307 (p1979 p2027 p2946 p3414 p3434 p3437 p3947 : Prop) (h : (¬ p3947) ∨ (¬ p3434) ∨ (¬ p3414) ∨ p2027 ∨ p3437 ∨ (¬ p2946) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3434) ∨ (p3437) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial38307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3434)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory27563 t (m.theta 0 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule38307 (meaning t m 1979) (meaning t m 2027) (meaning t m 2946) (meaning t m 3414) (meaning t m 3434) (meaning t m 3437) (meaning t m 3947) source

theorem rule38309 (p2027 p2417 p2922 p3379 p3646 p3950 p3989 p4347 p4524 : Prop) (h : (¬ p2922) ∨ (¬ p3989) ∨ (¬ p3646) ∨ (¬ p2417) ∨ (¬ p3379) ∨ (¬ p3950) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial38309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory27565 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38309 (meaning t m 2027) (meaning t m 2417) (meaning t m 2922) (meaning t m 3379) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) (meaning t m 4524) source

theorem rule38315 (p1983 p2027 p2202 p2563 p2951 p3051 p3246 p3952 : Prop) (h : (¬ p2951) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p1983) ∨ (¬ p3952) ∨ p2027 ∨ p2202 ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial38315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory27571 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule38315 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2951) (meaning t m 3051) (meaning t m 3246) (meaning t m 3952) source

theorem rule38318 (p2027 p2104 p2363 p3366 p3399 p3452 p3527 p4340 p4376 p4503 : Prop) (h : (¬ p3366) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3452) ∨ (¬ p3399) ∨ (¬ p2104) ∨ (¬ p4503) ∨ (¬ p4340) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2363) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial38318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory27574 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38318 (meaning t m 2027) (meaning t m 2104) (meaning t m 2363) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3527) (meaning t m 4340) (meaning t m 4376) (meaning t m 4503) source

theorem rule38319 (p2027 p2299 p2881 p3549 p3872 p4514 : Prop) (h : (¬ p4514) ∨ (¬ p3872) ∨ (¬ p3549) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2881)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3549) ∨ (¬ p3872) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial38319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory27575 t (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule38319 (meaning t m 2027) (meaning t m 2299) (meaning t m 2881) (meaning t m 3549) (meaning t m 3872) (meaning t m 4514) source

theorem rule38321 (p1991 p2027 p2952 p3570 p3982 p4320 p5558 : Prop) (h : (¬ p4320) ∨ (¬ p3570) ∨ p3982 ∨ (¬ p2952) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p5558)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (p3982) ∨ (¬ p4320) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial38321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory27577 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10)
  exact rule38321 (meaning t m 1991) (meaning t m 2027) (meaning t m 2952) (meaning t m 3570) (meaning t m 3982) (meaning t m 4320) (meaning t m 5558) source

theorem rule38328 (p1977 p2027 p2437 p2764 p2928 p3359 p3402 p4381 p4636 : Prop) (h : (¬ p2437) ∨ (¬ p3402) ∨ (¬ p1977) ∨ (¬ p4381) ∨ p2764 ∨ p2027 ∨ (¬ p4636) ∨ (¬ p2928) ∨ (¬ p3359)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2437) ∨ (p2764) ∨ (¬ p2928) ∨ (¬ p3359) ∨ (¬ p3402) ∨ (¬ p4381) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial38328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory27584 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule38328 (meaning t m 1977) (meaning t m 2027) (meaning t m 2437) (meaning t m 2764) (meaning t m 2928) (meaning t m 3359) (meaning t m 3402) (meaning t m 4381) (meaning t m 4636) source

theorem rule38335 (p2027 p2241 p2750 p3319 p3461 p3555 p4363 p4444 p4869 p5059 : Prop) (h : p2027 ∨ (¬ p4869) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p4363) ∨ (¬ p3461) ∨ (¬ p3555) ∨ (¬ p3319) ∨ (¬ p5059) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p4444) ∨ (¬ p4869) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial38335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory27591 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38335 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 3319) (meaning t m 3461) (meaning t m 3555) (meaning t m 4363) (meaning t m 4444) (meaning t m 4869) (meaning t m 5059) source

theorem rule38338 (p2027 p3324 p3931 p4156 p4260 p4501 : Prop) (h : (¬ p4260) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4501) ∨ (¬ p4156) ∨ (¬ p3931)) : (p2027) ∨ (¬ p3324) ∨ (¬ p3931) ∨ (¬ p4156) ∨ (¬ p4260) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial38338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory27594 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule38338 (meaning t m 2027) (meaning t m 3324) (meaning t m 3931) (meaning t m 4156) (meaning t m 4260) (meaning t m 4501) source

theorem rule38339 (p2027 p2241 p2299 p2717 p2750 p2753 p3471 p3860 p4712 p5074 p5508 p5600 p5674 : Prop) (h : p2027 ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p5600) ∨ (¬ p5074) ∨ (¬ p3860) ∨ (¬ p2750) ∨ (¬ p5508) ∨ (¬ p2241) ∨ (¬ p3471) ∨ (¬ p2753) ∨ (¬ p4712) ∨ (¬ p5674)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3860) ∨ (¬ p4712) ∨ (¬ p5074) ∨ (¬ p5508) ∨ (¬ p5600) ∨ (¬ p5674) := by
  classical
  tauto

theorem initial38339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 5074)) ∨ (¬ (meaning t m 5508)) ∨ (¬ (meaning t m 5600)) ∨ (¬ (meaning t m 5674)) := by
  have source := ElevenTheory.theory27595 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 7) (m.theta 3 8) (m.theta 4 10) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule38339 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3860) (meaning t m 4712) (meaning t m 5074) (meaning t m 5508) (meaning t m 5600) (meaning t m 5674) source

theorem rule38341 (p2027 p2132 p2780 p2891 p4418 p4428 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p2132) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4418) ∨ (¬ p4428) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2891) ∨ (¬ p4418) ∨ (¬ p4428) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial38341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory27597 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7)
  exact rule38341 (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 2891) (meaning t m 4418) (meaning t m 4428) (meaning t m 4558) source

theorem rule38342 (p1992 p2027 p2331 p2545 p2657 p2743 p4195 : Prop) (h : (¬ p2657) ∨ p2545 ∨ (¬ p1992) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial38342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory27598 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule38342 (meaning t m 1992) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 2743) (meaning t m 4195) source

theorem rule38344 (p2027 p2383 p2499 p2584 p3956 p5194 : Prop) (h : (¬ p3956) ∨ (¬ p5194) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p2383) ∨ p2027) : (p2027) ∨ (¬ p2383) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p3956) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial38344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory27600 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8)
  exact rule38344 (meaning t m 2027) (meaning t m 2383) (meaning t m 2499) (meaning t m 2584) (meaning t m 3956) (meaning t m 5194) source

theorem rule38345 (p2027 p2088 p2252 p2657 p2750 p3644 p3742 p3954 p4133 p4347 p5242 : Prop) (h : (¬ p2750) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p2088) ∨ (¬ p2657) ∨ (¬ p3644) ∨ (¬ p2252) ∨ (¬ p3742) ∨ (¬ p5242) ∨ p2027 ∨ (¬ p3954)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p5242) := by
  classical
  tauto

theorem initial38345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5242)) := by
  have source := ElevenTheory.theory27601 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38345 (meaning t m 2027) (meaning t m 2088) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3644) (meaning t m 3742) (meaning t m 3954) (meaning t m 4133) (meaning t m 4347) (meaning t m 5242) source

theorem rule38347 (p2027 p2252 p2657 p2750 p3399 p3631 p3644 p3742 p3954 p4668 : Prop) (h : (¬ p3631) ∨ (¬ p3954) ∨ (¬ p3742) ∨ (¬ p2657) ∨ (¬ p2252) ∨ (¬ p3644) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial38347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory27603 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38347 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3399) (meaning t m 3631) (meaning t m 3644) (meaning t m 3742) (meaning t m 3954) (meaning t m 4668) source

theorem rule38349 (p1991 p2027 p2191 p2657 p2972 p3578 p3680 p3742 p4278 p4444 p4669 : Prop) (h : (¬ p2657) ∨ (¬ p1991) ∨ p2027 ∨ p3578 ∨ (¬ p3680) ∨ (¬ p4444) ∨ (¬ p4278) ∨ (¬ p3742) ∨ (¬ p2191) ∨ (¬ p4669) ∨ (¬ p2972)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2657) ∨ (¬ p2972) ∨ (p3578) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial38349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2972)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory27605 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38349 (meaning t m 1991) (meaning t m 2027) (meaning t m 2191) (meaning t m 2657) (meaning t m 2972) (meaning t m 3578) (meaning t m 3680) (meaning t m 3742) (meaning t m 4278) (meaning t m 4444) (meaning t m 4669) source

theorem rule38353 (p2027 p2144 p2220 p2963 p3146 p3266 p3568 p4260 p4789 p4831 : Prop) (h : (¬ p2220) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4789) ∨ (¬ p2144) ∨ (¬ p4260) ∨ (¬ p3568) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2963) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial38353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory27609 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule38353 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2963) (meaning t m 3146) (meaning t m 3266) (meaning t m 3568) (meaning t m 4260) (meaning t m 4789) (meaning t m 4831) source

theorem rule38354 (p2027 p2144 p2220 p2753 p3105 p3193 p3343 p3694 p3742 p4402 p4647 p5216 : Prop) (h : (¬ p3694) ∨ (¬ p3105) ∨ (¬ p2220) ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p4647) ∨ (¬ p2144) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p5216) ∨ (¬ p4402)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3694) ∨ (¬ p3742) ∨ (¬ p4402) ∨ (¬ p4647) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27610 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 5 8) (m.theta 5 9)
  exact rule38354 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2753) (meaning t m 3105) (meaning t m 3193) (meaning t m 3343) (meaning t m 3694) (meaning t m 3742) (meaning t m 4402) (meaning t m 4647) (meaning t m 5216) source

theorem rule38355 (p2210 p3830 p4351 p4496 : Prop) (h : (¬ p2210) ∨ (¬ p4496) ∨ (¬ p4351) ∨ p3830) : (¬ p2210) ∨ (p3830) ∨ (¬ p4351) ∨ (¬ p4496) := by
  classical
  tauto

theorem initial38355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (meaning t m 3830) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 4496)) := by
  have source := ElevenTheory.theory27611 (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 1 9)
  exact rule38355 (meaning t m 2210) (meaning t m 3830) (meaning t m 4351) (meaning t m 4496) source

theorem rule38357 (p2027 p2427 p2753 p2786 p3461 p3556 p3645 p3654 p4444 p4877 p4948 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p3645) ∨ (¬ p2427) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p4444) ∨ (¬ p4877) ∨ (¬ p3654) ∨ (¬ p2753) ∨ (¬ p4948) ∨ (¬ p2786)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p3461) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3654) ∨ (¬ p4444) ∨ (¬ p4877) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial38357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory27613 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38357 (meaning t m 2027) (meaning t m 2427) (meaning t m 2753) (meaning t m 2786) (meaning t m 3461) (meaning t m 3556) (meaning t m 3645) (meaning t m 3654) (meaning t m 4444) (meaning t m 4877) (meaning t m 4948) (meaning t m 5059) source

theorem rule38359 (p2027 p2284 p2946 p3414 p3699 p4555 : Prop) (h : (¬ p3699) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p2284) ∨ (¬ p4555)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial38359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory27615 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule38359 (meaning t m 2027) (meaning t m 2284) (meaning t m 2946) (meaning t m 3414) (meaning t m 3699) (meaning t m 4555) source

theorem rule38360 (p2027 p2870 p3516 p3543 p4382 p4385 p4914 : Prop) (h : (¬ p3543) ∨ (¬ p4914) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4385) ∨ (¬ p2870) ∨ (¬ p4382)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4382) ∨ (¬ p4385) ∨ (¬ p4914) := by
  classical
  tauto

theorem initial38360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4914)) := by
  have source := ElevenTheory.theory27616 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule38360 (meaning t m 2027) (meaning t m 2870) (meaning t m 3516) (meaning t m 3543) (meaning t m 4382) (meaning t m 4385) (meaning t m 4914) source

theorem rule38363 (p2027 p2252 p2459 p2534 p2655 p2750 p3093 p3319 p3322 p3540 p3954 p4133 p4186 : Prop) (h : (¬ p3093) ∨ (¬ p3322) ∨ (¬ p2534) ∨ (¬ p4133) ∨ (¬ p4186) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3540) ∨ (¬ p2252) ∨ (¬ p2655) ∨ (¬ p3319) ∨ (¬ p2459) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3322) ∨ (¬ p3540) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial38363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory27619 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38363 (meaning t m 2027) (meaning t m 2252) (meaning t m 2459) (meaning t m 2534) (meaning t m 2655) (meaning t m 2750) (meaning t m 3093) (meaning t m 3319) (meaning t m 3322) (meaning t m 3540) (meaning t m 3954) (meaning t m 4133) (meaning t m 4186) source

theorem rule38366 (p2027 p2252 p2657 p2750 p2753 p2786 p2819 p3644 p3654 p3742 p3917 p4133 : Prop) (h : (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2819) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3644) ∨ (¬ p3917) ∨ (¬ p2786) ∨ (¬ p3654)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3644) ∨ (¬ p3654) ∨ (¬ p3742) ∨ (¬ p3917) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial38366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory27622 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8)
  exact rule38366 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2786) (meaning t m 2819) (meaning t m 3644) (meaning t m 3654) (meaning t m 3742) (meaning t m 3917) (meaning t m 4133) source

theorem rule38369 (p2027 p2144 p2220 p2437 p2579 p2655 p3105 p3359 p3581 p3694 p4789 p4954 : Prop) (h : (¬ p4954) ∨ (¬ p3694) ∨ (¬ p3105) ∨ (¬ p2144) ∨ (¬ p4789) ∨ (¬ p2655) ∨ (¬ p3581) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3359) ∨ (¬ p2579) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2437) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3105) ∨ (¬ p3359) ∨ (¬ p3581) ∨ (¬ p3694) ∨ (¬ p4789) ∨ (¬ p4954) := by
  classical
  tauto

theorem initial38369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4954)) := by
  have source := ElevenTheory.theory27625 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9)
  exact rule38369 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2437) (meaning t m 2579) (meaning t m 2655) (meaning t m 3105) (meaning t m 3359) (meaning t m 3581) (meaning t m 3694) (meaning t m 4789) (meaning t m 4954) source

theorem rule38370 (p1975 p2027 p2274 p2352 p3008 p3979 p3988 p5568 : Prop) (h : (¬ p2274) ∨ (¬ p3988) ∨ p3008 ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2352) ∨ (¬ p3979) ∨ (¬ p5568)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2352) ∨ (p3008) ∨ (¬ p3979) ∨ (¬ p3988) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial38370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory27626 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule38370 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2352) (meaning t m 3008) (meaning t m 3979) (meaning t m 3988) (meaning t m 5568) source

theorem rule38376 (p2027 p2406 p2499 p3016 p3684 p4750 : Prop) (h : (¬ p4750) ∨ (¬ p3684) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3684) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial38376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory27632 t (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule38376 (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 3016) (meaning t m 3684) (meaning t m 4750) source

theorem rule38377 (p2027 p2098 p2780 p2952 p3361 p3497 p3692 p3979 p4326 p4842 p5122 : Prop) (h : (¬ p4842) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3979) ∨ (¬ p3497) ∨ (¬ p4326) ∨ (¬ p2952) ∨ (¬ p3361) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3979) ∨ (¬ p4326) ∨ (¬ p4842) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial38377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4842)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory27633 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule38377 (meaning t m 2027) (meaning t m 2098) (meaning t m 2780) (meaning t m 2952) (meaning t m 3361) (meaning t m 3497) (meaning t m 3692) (meaning t m 3979) (meaning t m 4326) (meaning t m 4842) (meaning t m 5122) source

theorem rule38380 (p2027 p2363 p2761 p2774 p2819 p3292 p4669 p4789 p5284 : Prop) (h : (¬ p2363) ∨ (¬ p2761) ∨ (¬ p4669) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4789) ∨ (¬ p2819) ∨ (¬ p3292) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2761) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3292) ∨ (¬ p4669) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial38380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory27636 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 9) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38380 (meaning t m 2027) (meaning t m 2363) (meaning t m 2761) (meaning t m 2774) (meaning t m 2819) (meaning t m 3292) (meaning t m 4669) (meaning t m 4789) (meaning t m 5284) source

theorem rule38382 (p2027 p2230 p2299 p2518 p2780 p3238 p3822 p4079 p4420 p4736 : Prop) (h : (¬ p4079) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p3822) ∨ (¬ p3238) ∨ (¬ p2230) ∨ (¬ p4736) ∨ (¬ p2299) ∨ (¬ p4420) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2518) ∨ (¬ p2780) ∨ (¬ p3238) ∨ (¬ p3822) ∨ (¬ p4079) ∨ (¬ p4420) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27638 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule38382 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2518) (meaning t m 2780) (meaning t m 3238) (meaning t m 3822) (meaning t m 4079) (meaning t m 4420) (meaning t m 4736) source

theorem rule38389 (p2027 p3741 p3868 p4110 p4558 p5660 : Prop) (h : p2027 ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4110) ∨ (¬ p5660) ∨ (¬ p4558)) : (p2027) ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4110) ∨ (¬ p4558) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial38389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory27645 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 10)
  exact rule38389 (meaning t m 2027) (meaning t m 3741) (meaning t m 3868) (meaning t m 4110) (meaning t m 4558) (meaning t m 5660) source

theorem rule38391 (p2027 p2252 p2750 p2963 p3568 p3707 p3830 p3954 p4260 p4831 : Prop) (h : (¬ p2963) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p3568) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial38391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory27647 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule38391 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 3568) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 4260) (meaning t m 4831) source

theorem rule38394 (p2027 p2144 p2437 p2579 p2655 p3212 p3359 p3581 p3680 p4022 p4444 p4604 p4789 : Prop) (h : (¬ p2437) ∨ (¬ p4022) ∨ (¬ p3359) ∨ (¬ p2655) ∨ (¬ p4444) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p3212) ∨ (¬ p4789) ∨ (¬ p3680) ∨ (¬ p3581) ∨ (¬ p2144) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2437) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3212) ∨ (¬ p3359) ∨ (¬ p3581) ∨ (¬ p3680) ∨ (¬ p4022) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial38394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory27650 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 4 9) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38394 (meaning t m 2027) (meaning t m 2144) (meaning t m 2437) (meaning t m 2579) (meaning t m 2655) (meaning t m 3212) (meaning t m 3359) (meaning t m 3581) (meaning t m 3680) (meaning t m 4022) (meaning t m 4444) (meaning t m 4604) (meaning t m 4789) source

theorem rule38396 (p2027 p2299 p2780 p3073 p3449 p3692 p3822 p4736 p4902 : Prop) (h : (¬ p3822) ∨ (¬ p2780) ∨ (¬ p4736) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p4902) ∨ (¬ p3449) ∨ (¬ p2299) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial38396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory27652 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule38396 (meaning t m 2027) (meaning t m 2299) (meaning t m 2780) (meaning t m 3073) (meaning t m 3449) (meaning t m 3692) (meaning t m 3822) (meaning t m 4736) (meaning t m 4902) source

theorem rule38397 (p1992 p2027 p2633 p3238 p3246 p3570 p3821 p4031 p4257 p4984 : Prop) (h : (¬ p4257) ∨ (¬ p4031) ∨ (¬ p3238) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4984) ∨ p2633 ∨ (¬ p3821) ∨ (¬ p3570) ∨ (¬ p3246)) : (¬ p1992) ∨ (p2027) ∨ (p2633) ∨ (¬ p3238) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4031) ∨ (¬ p4257) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial38397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory27653 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38397 (meaning t m 1992) (meaning t m 2027) (meaning t m 2633) (meaning t m 3238) (meaning t m 3246) (meaning t m 3570) (meaning t m 3821) (meaning t m 4031) (meaning t m 4257) (meaning t m 4984) source

theorem rule38400 (p2027 p2132 p2252 p2657 p2750 p2753 p2860 p3125 p3742 p4278 p4621 : Prop) (h : (¬ p4621) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p2132) ∨ (¬ p3742) ∨ (¬ p2753) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial38400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory27656 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule38400 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2860) (meaning t m 3125) (meaning t m 3742) (meaning t m 4278) (meaning t m 4621) source

theorem rule38402 (p2027 p2470 p2665 p2727 p4360 p4437 : Prop) (h : (¬ p2665) ∨ (¬ p4437) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial38402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory27658 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule38402 (meaning t m 2027) (meaning t m 2470) (meaning t m 2665) (meaning t m 2727) (meaning t m 4360) (meaning t m 4437) source

theorem rule38404 (p2027 p2132 p2187 p2192 p2743 p3361 p3414 p3553 p4133 p4418 p4737 : Prop) (h : p2027 ∨ (¬ p4737) ∨ (¬ p2743) ∨ (¬ p4418) ∨ (¬ p3414) ∨ (¬ p2192) ∨ (¬ p3361) ∨ (¬ p2132) ∨ (¬ p4133) ∨ (¬ p3553) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4418) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27660 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule38404 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2192) (meaning t m 2743) (meaning t m 3361) (meaning t m 3414) (meaning t m 3553) (meaning t m 4133) (meaning t m 4418) (meaning t m 4737) source

theorem rule38405 (p1975 p2027 p2274 p2344 p2383 p3979 p3988 p5568 : Prop) (h : (¬ p2383) ∨ p2344 ∨ (¬ p2274) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p3988) ∨ (¬ p3979) ∨ (¬ p5568)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2344) ∨ (¬ p2383) ∨ (¬ p3979) ∨ (¬ p3988) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial38405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory27661 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule38405 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2344) (meaning t m 2383) (meaning t m 3979) (meaning t m 3988) (meaning t m 5568) source

theorem rule38406 (p2027 p2132 p2252 p2750 p2753 p2963 p3105 p3568 p3680 p4260 p4831 : Prop) (h : (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p2963) ∨ (¬ p2132) ∨ (¬ p4831) ∨ (¬ p3680) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p4260)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3105) ∨ (¬ p3568) ∨ (¬ p3680) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial38406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory27662 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule38406 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2963) (meaning t m 3105) (meaning t m 3568) (meaning t m 3680) (meaning t m 4260) (meaning t m 4831) source

theorem rule38408 (p2027 p2254 p2299 p2608 p2619 p2839 p2963 p3568 p4902 : Prop) (h : (¬ p2299) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p4902) ∨ (¬ p2254) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial38408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory27664 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule38408 (meaning t m 2027) (meaning t m 2254) (meaning t m 2299) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 2963) (meaning t m 3568) (meaning t m 4902) source

theorem rule38409 (p2027 p2156 p2252 p2534 p2657 p2750 p3105 p3370 p3371 p3758 p4256 p4450 : Prop) (h : (¬ p3105) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p4256) ∨ (¬ p2156) ∨ (¬ p4450) ∨ (¬ p2252) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p3370) ∨ (¬ p3371)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p4256) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial38409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory27665 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule38409 (meaning t m 2027) (meaning t m 2156) (meaning t m 2252) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 3105) (meaning t m 3370) (meaning t m 3371) (meaning t m 3758) (meaning t m 4256) (meaning t m 4450) source

theorem rule38415 (p4399 p4984 p5201 : Prop) (h : (¬ p4984) ∨ (¬ p5201) ∨ p4399) : (p4399) ∨ (¬ p4984) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial38415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4399) ∨ (¬ (meaning t m 4984)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory27671 (m.theta 0 4) (m.theta 0 5) (m.theta 0 7)
  exact rule38415 (meaning t m 4399) (meaning t m 4984) (meaning t m 5201) source

theorem rule38418 (p2027 p2493 p3238 p3880 p4203 p4507 : Prop) (h : (¬ p3238) ∨ (¬ p4507) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p4203) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p4203) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial38418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory27674 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule38418 (meaning t m 2027) (meaning t m 2493) (meaning t m 3238) (meaning t m 3880) (meaning t m 4203) (meaning t m 4507) source

theorem rule38434 (p2027 p3146 p3156 p4340 p4359 p4906 : Prop) (h : (¬ p3146) ∨ (¬ p4359) ∨ (¬ p3156) ∨ (¬ p4906) ∨ p2027 ∨ (¬ p4340)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial38434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory27690 t (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule38434 (meaning t m 2027) (meaning t m 3146) (meaning t m 3156) (meaning t m 4340) (meaning t m 4359) (meaning t m 4906) source

theorem rule38435 (p2027 p2274 p2911 p3960 p3989 p4113 p4712 : Prop) (h : (¬ p3989) ∨ (¬ p3960) ∨ (¬ p2911) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p4113)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2911) ∨ (¬ p3960) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial38435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory27691 t (m.theta 0 8) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule38435 (meaning t m 2027) (meaning t m 2274) (meaning t m 2911) (meaning t m 3960) (meaning t m 3989) (meaning t m 4113) (meaning t m 4712) source

theorem rule38438 (p2027 p2363 p2437 p2774 p2819 p3359 p3540 p4697 p4729 : Prop) (h : (¬ p4729) ∨ (¬ p3540) ∨ (¬ p2774) ∨ (¬ p3359) ∨ (¬ p2437) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2437) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3359) ∨ (¬ p3540) ∨ (¬ p4697) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial38438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory27694 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule38438 (meaning t m 2027) (meaning t m 2363) (meaning t m 2437) (meaning t m 2774) (meaning t m 2819) (meaning t m 3359) (meaning t m 3540) (meaning t m 4697) (meaning t m 4729) source

theorem rule38441 (p2027 p2532 p3212 p4120 p4134 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p4120) ∨ (¬ p2532) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p3212)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4134) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial38441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory27697 t (m.theta 0 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule38441 (meaning t m 2027) (meaning t m 2532) (meaning t m 3212) (meaning t m 4120) (meaning t m 4134) (meaning t m 4347) source

theorem rule38445 (p2027 p2122 p2396 p2657 p2774 p3644 p3742 p4668 p4789 : Prop) (h : (¬ p2657) ∨ (¬ p4789) ∨ (¬ p3644) ∨ (¬ p4668) ∨ (¬ p3742) ∨ (¬ p2774) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4668) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial38445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory27701 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38445 (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2657) (meaning t m 2774) (meaning t m 3644) (meaning t m 3742) (meaning t m 4668) (meaning t m 4789) source

theorem rule38453 (p2027 p3694 p4149 p4355 p4882 p5568 : Prop) (h : (¬ p4149) ∨ (¬ p4882) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p4355)) : (p2027) ∨ (¬ p3694) ∨ (¬ p4149) ∨ (¬ p4355) ∨ (¬ p4882) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial38453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory27709 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule38453 (meaning t m 2027) (meaning t m 3694) (meaning t m 4149) (meaning t m 4355) (meaning t m 4882) (meaning t m 5568) source

theorem rule38454 (p2027 p2363 p2743 p2774 p3063 p3361 p3414 p3918 p3947 p4669 p4737 : Prop) (h : (¬ p3947) ∨ (¬ p4669) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p2774) ∨ (¬ p3918) ∨ (¬ p3063) ∨ (¬ p4737) ∨ (¬ p2363) ∨ (¬ p2743)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3063) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3918) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27710 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38454 (meaning t m 2027) (meaning t m 2363) (meaning t m 2743) (meaning t m 2774) (meaning t m 3063) (meaning t m 3361) (meaning t m 3414) (meaning t m 3918) (meaning t m 3947) (meaning t m 4669) (meaning t m 4737) source

theorem rule38457 (p2027 p2307 p2563 p3743 p3822 p4193 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p4193) ∨ (¬ p2307) ∨ (¬ p3822) ∨ (¬ p3743) ∨ p2027 ∨ (¬ p2563)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2563) ∨ (¬ p3743) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial38457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory27713 t (m.theta 0 6) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule38457 (meaning t m 2027) (meaning t m 2307) (meaning t m 2563) (meaning t m 3743) (meaning t m 3822) (meaning t m 4193) (meaning t m 4882) source

theorem rule38460 (p2027 p2230 p2352 p2387 p2577 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2577) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial38460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory27716 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule38460 (meaning t m 2027) (meaning t m 2230) (meaning t m 2352) (meaning t m 2387) (meaning t m 2577) (meaning t m 4715) source

theorem rule38463 (p1992 p2027 p2633 p2743 p2952 p3361 p3570 p4320 : Prop) (h : (¬ p2952) ∨ (¬ p1992) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p3361) ∨ p2633 ∨ (¬ p3570)) : (¬ p1992) ∨ (p2027) ∨ (p2633) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3570) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial38463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory27719 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule38463 (meaning t m 1992) (meaning t m 2027) (meaning t m 2633) (meaning t m 2743) (meaning t m 2952) (meaning t m 3361) (meaning t m 3570) (meaning t m 4320) source

theorem rule38468 (p1986 p2027 p2230 p2911 p2914 p3551 p3684 p5197 : Prop) (h : (¬ p1986) ∨ (¬ p2230) ∨ p2914 ∨ p2027 ∨ (¬ p3684) ∨ (¬ p2911) ∨ (¬ p5197) ∨ (¬ p3551)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3551) ∨ (¬ p3684) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial38468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory27724 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule38468 (meaning t m 1986) (meaning t m 2027) (meaning t m 2230) (meaning t m 2911) (meaning t m 2914) (meaning t m 3551) (meaning t m 3684) (meaning t m 5197) source

theorem rule38469 (p1990 p2027 p2210 p2699 p2860 p2972 p4385 : Prop) (h : (¬ p2210) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p2972) ∨ p2699 ∨ (¬ p1990) ∨ (¬ p2860)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2860) ∨ (¬ p2972) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial38469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory27725 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9)
  exact rule38469 (meaning t m 1990) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2860) (meaning t m 2972) (meaning t m 4385) source

theorem rule38472 (p2027 p2132 p2743 p2891 p3172 p3246 p3361 p3950 p4118 p4418 p4737 : Prop) (h : (¬ p3950) ∨ (¬ p4737) ∨ (¬ p2132) ∨ (¬ p3172) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p3246) ∨ (¬ p4418) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p2891) ∨ (¬ p3172) ∨ (¬ p3246) ∨ (¬ p3361) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4418) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27728 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule38472 (meaning t m 2027) (meaning t m 2132) (meaning t m 2743) (meaning t m 2891) (meaning t m 3172) (meaning t m 3246) (meaning t m 3361) (meaning t m 3950) (meaning t m 4118) (meaning t m 4418) (meaning t m 4737) source

theorem rule38475 (p2027 p2437 p2440 p3569 p4244 p4882 : Prop) (h : (¬ p2440) ∨ p2027 ∨ (¬ p3569) ∨ (¬ p4244) ∨ (¬ p4882) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3569) ∨ (¬ p4244) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial38475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory27731 t (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule38475 (meaning t m 2027) (meaning t m 2437) (meaning t m 2440) (meaning t m 3569) (meaning t m 4244) (meaning t m 4882) source

theorem rule38476 (p2027 p2437 p2440 p3486 p3569 p4629 : Prop) (h : (¬ p2440) ∨ (¬ p3569) ∨ (¬ p2437) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p4629)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial38476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory27732 t (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule38476 (meaning t m 2027) (meaning t m 2437) (meaning t m 2440) (meaning t m 3486) (meaning t m 3569) (meaning t m 4629) source

theorem rule38477 (p1990 p2027 p2192 p2766 p3486 p3570 p4348 : Prop) (h : (¬ p4348) ∨ p2766 ∨ (¬ p3570) ∨ (¬ p1990) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p3486)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2192) ∨ (p2766) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial38477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory27733 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule38477 (meaning t m 1990) (meaning t m 2027) (meaning t m 2192) (meaning t m 2766) (meaning t m 3486) (meaning t m 3570) (meaning t m 4348) source

theorem rule38479 (p2027 p2122 p2177 p2241 p2750 p2753 p2774 p3032 p3947 p4366 p4666 : Prop) (h : (¬ p2774) ∨ (¬ p2122) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p4366) ∨ (¬ p2241) ∨ (¬ p3032) ∨ (¬ p2177) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p3947)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial38479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory27735 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38479 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3032) (meaning t m 3947) (meaning t m 4366) (meaning t m 4666) source

theorem rule38484 (p2027 p2563 p2901 p3556 p3952 p4533 : Prop) (h : (¬ p3556) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4533) ∨ (¬ p3952) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial38484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory27740 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule38484 (meaning t m 2027) (meaning t m 2563) (meaning t m 2901) (meaning t m 3556) (meaning t m 3952) (meaning t m 4533) source

theorem rule38487 (p2027 p2254 p2563 p2952 p3063 p3093 p3952 p4193 p4358 p4882 : Prop) (h : (¬ p3093) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p4358) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p4193) ∨ (¬ p4882) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3952) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial38487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory27743 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule38487 (meaning t m 2027) (meaning t m 2254) (meaning t m 2563) (meaning t m 2952) (meaning t m 3063) (meaning t m 3093) (meaning t m 3952) (meaning t m 4193) (meaning t m 4358) (meaning t m 4882) source

theorem rule38493 (p2027 p2440 p2933 p3019 p3256 p3544 p4261 p4341 p4646 : Prop) (h : (¬ p2440) ∨ (¬ p4646) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p3256) ∨ (¬ p2933) ∨ (¬ p4341) ∨ (¬ p3019) ∨ p2027) : (p2027) ∨ (¬ p2440) ∨ (¬ p2933) ∨ (¬ p3019) ∨ (¬ p3256) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4341) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial38493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory27749 t (m.theta 1 7) (m.theta 1 8) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 4 7) (m.theta 8 9)
  exact rule38493 (meaning t m 2027) (meaning t m 2440) (meaning t m 2933) (meaning t m 3019) (meaning t m 3256) (meaning t m 3544) (meaning t m 4261) (meaning t m 4341) (meaning t m 4646) source

theorem rule38495 (p2027 p2138 p2406 p3379 p3698 p4736 : Prop) (h : (¬ p2406) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4736) ∨ (¬ p2138) ∨ (¬ p3698)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3698) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27751 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 5)
  exact rule38495 (meaning t m 2027) (meaning t m 2138) (meaning t m 2406) (meaning t m 3379) (meaning t m 3698) (meaning t m 4736) source

theorem rule38497 (p1992 p2027 p2138 p2696 p2743 p3043 p4385 : Prop) (h : (¬ p1992) ∨ (¬ p2743) ∨ p2027 ∨ p3043 ∨ (¬ p2696) ∨ (¬ p2138) ∨ (¬ p4385)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (p3043) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial38497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory27753 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 9)
  exact rule38497 (meaning t m 1992) (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2743) (meaning t m 3043) (meaning t m 4385) source

theorem rule38499 (p1987 p2027 p2545 p2579 p2737 p3016 p3363 p3585 : Prop) (h : (¬ p3585) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2737) ∨ p2545 ∨ (¬ p3363) ∨ (¬ p1987) ∨ (¬ p3016)) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p2737) ∨ (¬ p3016) ∨ (¬ p3363) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial38499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory27755 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule38499 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 2579) (meaning t m 2737) (meaning t m 3016) (meaning t m 3363) (meaning t m 3585) source

theorem rule38500 (p2819 p3822 p3955 : Prop) (h : (¬ p2819) ∨ (¬ p3955) ∨ (¬ p3822)) : (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial38500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory27756 (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule38500 (meaning t m 2819) (meaning t m 3822) (meaning t m 3955) source

theorem rule38501 (p1987 p2027 p2143 p2633 p2737 p3556 p3570 p3583 : Prop) (h : p2633 ∨ (¬ p2143) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p1987) ∨ (¬ p3556) ∨ (¬ p3570)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2143) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial38501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory27757 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule38501 (meaning t m 1987) (meaning t m 2027) (meaning t m 2143) (meaning t m 2633) (meaning t m 2737) (meaning t m 3556) (meaning t m 3570) (meaning t m 3583) source

theorem rule38505 (p2027 p2122 p2241 p2396 p2750 p2753 p2774 p3860 p3950 p4261 : Prop) (h : (¬ p2241) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p2753) ∨ (¬ p3860) ∨ (¬ p2750) ∨ (¬ p2774) ∨ (¬ p2396) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial38505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory27761 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule38505 (meaning t m 2027) (meaning t m 2122) (meaning t m 2241) (meaning t m 2396) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) source

theorem rule38506 (p2015 p2027 p2633 p3549 p3570 p4129 p4260 : Prop) (h : p2633 ∨ (¬ p3570) ∨ (¬ p2015) ∨ p2027 ∨ (¬ p4129) ∨ (¬ p4260) ∨ (¬ p3549)) : (¬ p2015) ∨ (p2027) ∨ (p2633) ∨ (¬ p3549) ∨ (¬ p3570) ∨ (¬ p4129) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial38506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory27762 t (m.theta 1 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule38506 (meaning t m 2015) (meaning t m 2027) (meaning t m 2633) (meaning t m 3549) (meaning t m 3570) (meaning t m 4129) (meaning t m 4260) source

theorem rule38516 (p1987 p2027 p2633 p2737 p3570 p3583 p4244 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p3570) ∨ (¬ p1987) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p4244)) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial38516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory27772 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule38516 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2737) (meaning t m 3570) (meaning t m 3583) (meaning t m 4244) source

theorem rule38520 (p2027 p2144 p2780 p3051 p4244 p4392 p4842 : Prop) (h : (¬ p4244) ∨ (¬ p4392) ∨ (¬ p2780) ∨ (¬ p3051) ∨ (¬ p4842) ∨ (¬ p2144) ∨ p2027) : (p2027) ∨ (¬ p2144) ∨ (¬ p2780) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4392) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial38520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory27776 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7)
  exact rule38520 (meaning t m 2027) (meaning t m 2144) (meaning t m 2780) (meaning t m 3051) (meaning t m 4244) (meaning t m 4392) (meaning t m 4842) source

theorem rule38522 (p2027 p2177 p2254 p2657 p3093 p3309 p3742 p4278 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p2657) ∨ (¬ p2254) ∨ (¬ p2177) ∨ (¬ p3309) ∨ (¬ p4278) ∨ (¬ p3093) ∨ (¬ p3742) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial38522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory27778 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38522 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2657) (meaning t m 3093) (meaning t m 3309) (meaning t m 3742) (meaning t m 4278) (meaning t m 4666) source

theorem rule38525 (p2027 p2254 p2952 p3379 p3537 p4019 p4208 p4257 p4322 p5119 : Prop) (h : (¬ p2254) ∨ (¬ p4257) ∨ (¬ p3379) ∨ (¬ p5119) ∨ (¬ p4322) ∨ (¬ p4019) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3537) ∨ (¬ p4019) ∨ (¬ p4208) ∨ (¬ p4257) ∨ (¬ p4322) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial38525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory27781 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 8) (m.theta 3 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule38525 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3379) (meaning t m 3537) (meaning t m 4019) (meaning t m 4208) (meaning t m 4257) (meaning t m 4322) (meaning t m 5119) source

theorem rule38526 (p3426 p3588 p3688 : Prop) (h : (¬ p3426) ∨ (¬ p3588) ∨ p3688) : (¬ p3426) ∨ (¬ p3588) ∨ (p3688) := by
  classical
  tauto

theorem initial38526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3588)) ∨ (meaning t m 3688) := by
  have source := ElevenTheory.theory27782 (m.theta 1 2) (m.theta 2 6) (m.theta 2 7)
  exact rule38526 (meaning t m 3426) (meaning t m 3588) (meaning t m 3688) source

theorem rule38532 (p1986 p2027 p2169 p2295 p2313 p3324 p3684 p4031 p4198 : Prop) (h : (¬ p4031) ∨ p2169 ∨ (¬ p3324) ∨ (¬ p4198) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p1986) ∨ (¬ p3684)) : (¬ p1986) ∨ (p2027) ∨ (p2169) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial38532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory27788 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 6 7) (m.theta 6 8)
  exact rule38532 (meaning t m 1986) (meaning t m 2027) (meaning t m 2169) (meaning t m 2295) (meaning t m 2313) (meaning t m 3324) (meaning t m 3684) (meaning t m 4031) (meaning t m 4198) source

theorem rule38534 (p2027 p2588 p3156 p3952 p3958 p4119 p4140 : Prop) (h : p2027 ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p3958) ∨ (¬ p3952) ∨ (¬ p3156) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3958) ∨ (¬ p4119) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial38534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory27790 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7)
  exact rule38534 (meaning t m 2027) (meaning t m 2588) (meaning t m 3156) (meaning t m 3952) (meaning t m 3958) (meaning t m 4119) (meaning t m 4140) source

theorem rule38538 (p2027 p2138 p2922 p3379 p3868 p4322 p4385 p4736 p4826 : Prop) (h : (¬ p4736) ∨ (¬ p4385) ∨ (¬ p2138) ∨ (¬ p3868) ∨ (¬ p3379) ∨ (¬ p4826) ∨ (¬ p2922) ∨ p2027 ∨ (¬ p4322)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3868) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4736) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial38538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory27794 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule38538 (meaning t m 2027) (meaning t m 2138) (meaning t m 2922) (meaning t m 3379) (meaning t m 3868) (meaning t m 4322) (meaning t m 4385) (meaning t m 4736) (meaning t m 4826) source

theorem rule38541 (p2027 p2657 p3005 p3506 p3683 p3876 p4278 p4444 p4669 p4787 p5111 : Prop) (h : (¬ p4278) ∨ (¬ p5111) ∨ (¬ p4444) ∨ (¬ p3683) ∨ (¬ p3506) ∨ (¬ p4787) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p4669) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3005) ∨ (¬ p3506) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4787) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial38541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory27797 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 3 9) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38541 (meaning t m 2027) (meaning t m 2657) (meaning t m 3005) (meaning t m 3506) (meaning t m 3683) (meaning t m 3876) (meaning t m 4278) (meaning t m 4444) (meaning t m 4669) (meaning t m 4787) (meaning t m 5111) source

theorem rule38543 (p1991 p2027 p2764 p2952 p3690 p4320 p4381 : Prop) (h : (¬ p2952) ∨ (¬ p4320) ∨ (¬ p3690) ∨ (¬ p1991) ∨ p2027 ∨ p2764 ∨ (¬ p4381)) : (¬ p1991) ∨ (p2027) ∨ (p2764) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial38543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory27799 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule38543 (meaning t m 1991) (meaning t m 2027) (meaning t m 2764) (meaning t m 2952) (meaning t m 3690) (meaning t m 4320) (meaning t m 4381) source

theorem rule38545 (p1991 p2027 p2810 p2952 p3008 p3136 p3574 : Prop) (h : (¬ p3574) ∨ p3008 ∨ p2027 ∨ (¬ p1991) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p3136)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (p3008) ∨ (¬ p3136) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial38545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory27801 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule38545 (meaning t m 1991) (meaning t m 2027) (meaning t m 2810) (meaning t m 2952) (meaning t m 3008) (meaning t m 3136) (meaning t m 3574) source

theorem rule38546 (p1991 p2027 p2685 p2810 p3008 p3414 p3574 : Prop) (h : (¬ p3574) ∨ p3008 ∨ (¬ p1991) ∨ (¬ p2810) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p2685)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (p3008) ∨ (¬ p3414) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial38546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory27802 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6)
  exact rule38546 (meaning t m 1991) (meaning t m 2027) (meaning t m 2685) (meaning t m 2810) (meaning t m 3008) (meaning t m 3414) (meaning t m 3574) source

theorem rule38548 (p2027 p3055 p3707 p3830 p3876 p4191 p4278 p4621 p4736 : Prop) (h : (¬ p3830) ∨ (¬ p4278) ∨ (¬ p4736) ∨ (¬ p3055) ∨ (¬ p3707) ∨ (¬ p3876) ∨ (¬ p4191) ∨ (¬ p4621) ∨ p2027) : (p2027) ∨ (¬ p3055) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3876) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27804 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 9) (m.theta 2 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule38548 (meaning t m 2027) (meaning t m 3055) (meaning t m 3707) (meaning t m 3830) (meaning t m 3876) (meaning t m 4191) (meaning t m 4278) (meaning t m 4621) (meaning t m 4736) source

theorem rule38551 (p1987 p2027 p2138 p2633 p2737 p3366 p3570 p4244 : Prop) (h : p2633 ∨ (¬ p3366) ∨ (¬ p2737) ∨ (¬ p1987) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2138)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p3570) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial38551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory27807 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule38551 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2633) (meaning t m 2737) (meaning t m 3366) (meaning t m 3570) (meaning t m 4244) source

theorem rule38552 (p3568 p4275 p4320 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p4320) ∨ (¬ p4275) ∨ p3568) : (p3568) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial38552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3568) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory27808 (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7)
  exact rule38552 (meaning t m 3568) (meaning t m 4275) (meaning t m 4320) (meaning t m 4336) source

theorem rule38553 (p2027 p2177 p2406 p2982 p3379 p3551 p4107 p4395 p5210 : Prop) (h : (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4395) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p5210) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5210) := by
  classical
  tauto

theorem initial38553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5210)) := by
  have source := ElevenTheory.theory27809 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38553 (meaning t m 2027) (meaning t m 2177) (meaning t m 2406) (meaning t m 2982) (meaning t m 3379) (meaning t m 3551) (meaning t m 4107) (meaning t m 4395) (meaning t m 5210) source

theorem rule38554 (p2027 p2441 p2563 p2933 p3246 p3817 p4555 : Prop) (h : (¬ p2441) ∨ (¬ p2933) ∨ (¬ p3817) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (¬ p2933) ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial38554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory27810 t (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule38554 (meaning t m 2027) (meaning t m 2441) (meaning t m 2563) (meaning t m 2933) (meaning t m 3246) (meaning t m 3817) (meaning t m 4555) source

theorem rule38555 (p1990 p2027 p2396 p2563 p2997 p3556 p3645 p3690 p4210 : Prop) (h : (¬ p3645) ∨ p2997 ∨ (¬ p3556) ∨ (¬ p2563) ∨ (¬ p4210) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p1990) ∨ (¬ p2396)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2563) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial38555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory27811 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule38555 (meaning t m 1990) (meaning t m 2027) (meaning t m 2396) (meaning t m 2563) (meaning t m 2997) (meaning t m 3556) (meaning t m 3645) (meaning t m 3690) (meaning t m 4210) source

theorem rule38557 (p2001 p2027 p2470 p2528 p2622 p2630 p2656 p3692 : Prop) (h : p2622 ∨ (¬ p2470) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2528) ∨ (¬ p2001) ∨ (¬ p3692)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial38557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory27813 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule38557 (meaning t m 2001) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3692) source

theorem rule38558 (p2027 p2406 p2780 p2982 p3379 p4347 p4358 p4450 p4736 : Prop) (h : (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4347) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p4450) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4450) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27814 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule38558 (meaning t m 2027) (meaning t m 2406) (meaning t m 2780) (meaning t m 2982) (meaning t m 3379) (meaning t m 4347) (meaning t m 4358) (meaning t m 4450) (meaning t m 4736) source

theorem rule38563 (p1997 p2027 p2192 p2233 p3193 p3355 p3948 p4110 : Prop) (h : (¬ p1997) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p3193) ∨ (¬ p3948) ∨ p2233 ∨ (¬ p3355)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2192) ∨ (p2233) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p3948) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial38563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory27819 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule38563 (meaning t m 1997) (meaning t m 2027) (meaning t m 2192) (meaning t m 2233) (meaning t m 3193) (meaning t m 3355) (meaning t m 3948) (meaning t m 4110) source

theorem rule38564 (p2027 p2156 p2166 p2254 p2685 p3414 p3877 p4043 p4172 p4173 : Prop) (h : (¬ p2156) ∨ (¬ p4043) ∨ (¬ p4172) ∨ (¬ p2685) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p2254) ∨ (¬ p2166) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p2254) ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4172) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial38564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory27820 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8)
  exact rule38564 (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 2254) (meaning t m 2685) (meaning t m 3414) (meaning t m 3877) (meaning t m 4043) (meaning t m 4172) (meaning t m 4173) source

theorem rule38568 (p2027 p2373 p2406 p2685 p3379 p3414 p3877 p4043 p4236 p4736 : Prop) (h : (¬ p2406) ∨ (¬ p4043) ∨ (¬ p2373) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p2685) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2685) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4236) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27824 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule38568 (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 2685) (meaning t m 3379) (meaning t m 3414) (meaning t m 3877) (meaning t m 4043) (meaning t m 4236) (meaning t m 4736) source

theorem rule38569 (p2027 p2220 p2284 p3646 p3880 p4705 : Prop) (h : (¬ p3880) ∨ (¬ p2284) ∨ (¬ p4705) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial38569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory27825 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule38569 (meaning t m 2027) (meaning t m 2220) (meaning t m 2284) (meaning t m 3646) (meaning t m 3880) (meaning t m 4705) source

theorem rule38570 (p2982 p3880 p4335 : Prop) (h : (¬ p4335) ∨ (¬ p3880) ∨ (¬ p2982)) : (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial38570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory27826 (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule38570 (meaning t m 2982) (meaning t m 3880) (meaning t m 4335) source

theorem rule38571 (p2027 p2284 p2619 p3758 p3880 p4705 : Prop) (h : (¬ p3880) ∨ (¬ p4705) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p3880) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial38571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory27827 t (m.theta 2 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule38571 (meaning t m 2027) (meaning t m 2284) (meaning t m 2619) (meaning t m 3758) (meaning t m 3880) (meaning t m 4705) source

theorem rule38572 (p2027 p2284 p3105 p3758 p3880 p4335 p4705 : Prop) (h : (¬ p3880) ∨ (¬ p4335) ∨ (¬ p4705) ∨ (¬ p2284) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3105)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p3880) ∨ (¬ p4335) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial38572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory27828 t (m.theta 2 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 5 9)
  exact rule38572 (meaning t m 2027) (meaning t m 2284) (meaning t m 3105) (meaning t m 3758) (meaning t m 3880) (meaning t m 4335) (meaning t m 4705) source

theorem rule38588 (p2027 p2449 p3324 p4107 p4156 p4501 : Prop) (h : (¬ p4501) ∨ p2027 ∨ (¬ p4156) ∨ (¬ p4107) ∨ (¬ p3324) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3324) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial38588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory27844 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule38588 (meaning t m 2027) (meaning t m 2449) (meaning t m 3324) (meaning t m 4107) (meaning t m 4156) (meaning t m 4501) source

theorem rule38596 (p2027 p2295 p2313 p2518 p2528 p3379 p4037 p4604 p5021 : Prop) (h : (¬ p2528) ∨ (¬ p3379) ∨ (¬ p2313) ∨ (¬ p4037) ∨ (¬ p5021) ∨ (¬ p2518) ∨ (¬ p2295) ∨ (¬ p4604) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial38596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory27852 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule38596 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2518) (meaning t m 2528) (meaning t m 3379) (meaning t m 4037) (meaning t m 4604) (meaning t m 5021) source

theorem rule38597 (p2027 p2737 p3055 p3471 p4400 p4424 p4749 : Prop) (h : (¬ p4749) ∨ (¬ p3055) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p4424) ∨ (¬ p3471) ∨ (¬ p4400)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p4400) ∨ (¬ p4424) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial38597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory27853 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7)
  exact rule38597 (meaning t m 2027) (meaning t m 2737) (meaning t m 3055) (meaning t m 3471) (meaning t m 4400) (meaning t m 4424) (meaning t m 4749) source

theorem rule38600 (p2027 p2387 p2668 p2785 p3055 p3434 p3471 p4037 p4625 p4749 p4841 : Prop) (h : (¬ p2785) ∨ (¬ p4841) ∨ (¬ p3434) ∨ (¬ p3055) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4749) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2785) ∨ (¬ p3055) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4037) ∨ (¬ p4625) ∨ (¬ p4749) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial38600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory27856 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule38600 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2785) (meaning t m 3055) (meaning t m 3434) (meaning t m 3471) (meaning t m 4037) (meaning t m 4625) (meaning t m 4749) (meaning t m 4841) source

theorem rule38601 (p2001 p2027 p2373 p3128 p3461 p4210 p4322 p4363 : Prop) (h : (¬ p2373) ∨ (¬ p4210) ∨ (¬ p2001) ∨ p3128 ∨ (¬ p4363) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p4322)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2373) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p4210) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial38601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory27857 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule38601 (meaning t m 2001) (meaning t m 2027) (meaning t m 2373) (meaning t m 3128) (meaning t m 3461) (meaning t m 4210) (meaning t m 4322) (meaning t m 4363) source

theorem rule38603 (p2027 p2254 p2518 p2963 p3379 p4037 p4149 p4191 p5119 : Prop) (h : (¬ p4191) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p5119) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p4149) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial38603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory27859 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule38603 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2963) (meaning t m 3379) (meaning t m 4037) (meaning t m 4149) (meaning t m 4191) (meaning t m 5119) source

theorem rule38604 (p2027 p2254 p2295 p2313 p2373 p2406 p3324 p3379 p3983 p4433 : Prop) (h : (¬ p2373) ∨ (¬ p2295) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3983) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3983) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial38604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory27860 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38604 (meaning t m 2027) (meaning t m 2254) (meaning t m 2295) (meaning t m 2313) (meaning t m 2373) (meaning t m 2406) (meaning t m 3324) (meaning t m 3379) (meaning t m 3983) (meaning t m 4433) source

theorem rule38605 (p2027 p2299 p2619 p4244 p4275 p4902 : Prop) (h : (¬ p4902) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p4275) ∨ (¬ p2619) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2619) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial38605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory27861 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule38605 (meaning t m 2027) (meaning t m 2299) (meaning t m 2619) (meaning t m 4244) (meaning t m 4275) (meaning t m 4902) source

theorem rule38606 (p2027 p2254 p2299 p2373 p2608 p2839 p2963 p3568 p3695 p4902 : Prop) (h : (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2839) ∨ (¬ p2608) ∨ (¬ p2254) ∨ (¬ p3695) ∨ (¬ p2963) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3568)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3695) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial38606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory27862 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule38606 (meaning t m 2027) (meaning t m 2254) (meaning t m 2299) (meaning t m 2373) (meaning t m 2608) (meaning t m 2839) (meaning t m 2963) (meaning t m 3568) (meaning t m 3695) (meaning t m 4902) source

theorem rule38608 (p2027 p2860 p3323 p4033 p4385 p4560 : Prop) (h : (¬ p3323) ∨ p2027 ∨ (¬ p4033) ∨ (¬ p2860) ∨ (¬ p4560) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2860) ∨ (¬ p3323) ∨ (¬ p4033) ∨ (¬ p4385) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial38608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory27864 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule38608 (meaning t m 2027) (meaning t m 2860) (meaning t m 3323) (meaning t m 4033) (meaning t m 4385) (meaning t m 4560) source

theorem rule38610 (p3371 p3541 p4202 : Prop) (h : (¬ p3371) ∨ (¬ p4202) ∨ p3541) : (¬ p3371) ∨ (p3541) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial38610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3371)) ∨ (meaning t m 3541) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory27866 (m.theta 1 2) (m.theta 1 4) (m.theta 1 5)
  exact rule38610 (meaning t m 3371) (meaning t m 3541) (meaning t m 4202) source

theorem rule38615 (p1987 p2027 p2138 p2284 p2388 p2696 p3758 : Prop) (h : (¬ p1987) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p2138) ∨ p2388 ∨ p2027 ∨ (¬ p3758)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2696) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial38615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory27871 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule38615 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2284) (meaning t m 2388) (meaning t m 2696) (meaning t m 3758) source

theorem rule38616 (p2027 p2138 p2341 p2417 p3644 p3744 p3758 p4419 p4625 p5201 : Prop) (h : p2027 ∨ (¬ p2138) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p3644) ∨ (¬ p2417) ∨ (¬ p4625) ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p4419)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4419) ∨ (¬ p4625) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial38616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory27872 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule38616 (meaning t m 2027) (meaning t m 2138) (meaning t m 2341) (meaning t m 2417) (meaning t m 3644) (meaning t m 3744) (meaning t m 3758) (meaning t m 4419) (meaning t m 4625) (meaning t m 5201) source

theorem rule38618 (p2027 p2459 p2579 p3363 p3471 p3527 p3585 p4137 p4424 p4604 p4737 : Prop) (h : p2027 ∨ (¬ p4604) ∨ (¬ p4424) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p2459) ∨ (¬ p3471) ∨ (¬ p4737) ∨ (¬ p3527) ∨ (¬ p2579) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2579) ∨ (¬ p3363) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3585) ∨ (¬ p4137) ∨ (¬ p4424) ∨ (¬ p4604) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27874 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38618 (meaning t m 2027) (meaning t m 2459) (meaning t m 2579) (meaning t m 3363) (meaning t m 3471) (meaning t m 3527) (meaning t m 3585) (meaning t m 4137) (meaning t m 4424) (meaning t m 4604) (meaning t m 4737) source

theorem rule38619 (p2027 p2459 p2743 p2963 p3361 p3471 p3527 p4037 p4424 p4604 p4737 : Prop) (h : (¬ p3471) ∨ (¬ p4737) ∨ (¬ p3527) ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p4424) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p4037) ∨ (¬ p4424) ∨ (¬ p4604) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27875 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38619 (meaning t m 2027) (meaning t m 2459) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 3471) (meaning t m 3527) (meaning t m 4037) (meaning t m 4424) (meaning t m 4604) (meaning t m 4737) source

theorem rule38621 (p2027 p2651 p3290 p3506 p3773 p5172 : Prop) (h : (¬ p2651) ∨ p2027 ∨ (¬ p5172) ∨ (¬ p3290) ∨ (¬ p3506) ∨ (¬ p3773)) : (p2027) ∨ (¬ p2651) ∨ (¬ p3290) ∨ (¬ p3506) ∨ (¬ p3773) ∨ (¬ p5172) := by
  classical
  tauto

theorem initial38621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3290)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 5172)) := by
  have source := ElevenTheory.theory27877 t (m.theta 0 3) (m.theta 0 9) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule38621 (meaning t m 2027) (meaning t m 2651) (meaning t m 3290) (meaning t m 3506) (meaning t m 3773) (meaning t m 5172) source

theorem rule38623 (p2441 p3644 p3880 p4042 : Prop) (h : (¬ p3644) ∨ (¬ p4042) ∨ (¬ p2441) ∨ p3880) : (¬ p2441) ∨ (¬ p3644) ∨ (p3880) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial38623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3644)) ∨ (meaning t m 3880) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory27879 (m.theta 4 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8)
  exact rule38623 (meaning t m 2441) (meaning t m 3644) (meaning t m 3880) (meaning t m 4042) source

theorem rule38626 (p2027 p2449 p2696 p2742 p3027 p3276 p3585 p4641 p4737 p5158 p5387 : Prop) (h : (¬ p3276) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p2742) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p5158) ∨ (¬ p5387) ∨ (¬ p3585) ∨ (¬ p4737) ∨ (¬ p4641)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3276) ∨ (¬ p3585) ∨ (¬ p4641) ∨ (¬ p4737) ∨ (¬ p5158) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial38626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5158)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory27882 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 3 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule38626 (meaning t m 2027) (meaning t m 2449) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3276) (meaning t m 3585) (meaning t m 4641) (meaning t m 4737) (meaning t m 5158) (meaning t m 5387) source

theorem rule38628 (p2027 p2274 p2860 p3694 p4501 p4506 : Prop) (h : p2027 ∨ (¬ p2860) ∨ (¬ p4506) ∨ (¬ p4501) ∨ (¬ p3694) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p4501) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial38628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory27884 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38628 (meaning t m 2027) (meaning t m 2274) (meaning t m 2860) (meaning t m 3694) (meaning t m 4501) (meaning t m 4506) source

theorem rule38629 (p2027 p2307 p2860 p3694 p3743 p4501 p4506 : Prop) (h : p2027 ∨ (¬ p4506) ∨ (¬ p2860) ∨ (¬ p4501) ∨ (¬ p3743) ∨ (¬ p3694) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p3743) ∨ (¬ p4501) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial38629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory27885 t (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38629 (meaning t m 2027) (meaning t m 2307) (meaning t m 2860) (meaning t m 3694) (meaning t m 3743) (meaning t m 4501) (meaning t m 4506) source

theorem rule38631 (p2027 p2295 p2641 p2696 p2742 p2911 p3363 p3551 p3585 p4712 p4737 p5197 : Prop) (h : (¬ p4712) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p2742) ∨ (¬ p2641) ∨ (¬ p4737) ∨ (¬ p2696) ∨ (¬ p3551) ∨ (¬ p5197) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2911) ∨ (¬ p3363) ∨ (¬ p3551) ∨ (¬ p3585) ∨ (¬ p4712) ∨ (¬ p4737) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial38631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory27887 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule38631 (meaning t m 2027) (meaning t m 2295) (meaning t m 2641) (meaning t m 2696) (meaning t m 2742) (meaning t m 2911) (meaning t m 3363) (meaning t m 3551) (meaning t m 3585) (meaning t m 4712) (meaning t m 4737) (meaning t m 5197) source

theorem rule38632 (p2027 p2352 p2363 p2573 p3365 p3366 p3519 p4208 p4315 p4376 p5059 : Prop) (h : (¬ p3519) ∨ (¬ p4208) ∨ (¬ p5059) ∨ (¬ p4315) ∨ (¬ p3365) ∨ (¬ p2352) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2573) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4376) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial38632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory27888 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule38632 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 4208) (meaning t m 4315) (meaning t m 4376) (meaning t m 5059) source

theorem rule38636 (p2027 p2241 p2727 p2870 p3083 p3556 p3694 p4158 p4524 : Prop) (h : (¬ p3556) ∨ (¬ p4524) ∨ (¬ p3694) ∨ (¬ p4158) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2241) ∨ (¬ p2870) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3694) ∨ (¬ p4158) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial38636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory27892 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule38636 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 2870) (meaning t m 3083) (meaning t m 3556) (meaning t m 3694) (meaning t m 4158) (meaning t m 4524) source

theorem rule38645 (p2027 p2132 p2187 p2192 p3363 p3540 p3585 p3644 p4133 p4418 p4737 : Prop) (h : (¬ p2187) ∨ (¬ p2192) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4737) ∨ (¬ p2132) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p4418) ∨ (¬ p3540) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4418) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27901 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule38645 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2192) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 3644) (meaning t m 4133) (meaning t m 4418) (meaning t m 4737) source

theorem rule38649 (p3063 p3319 p3990 : Prop) (h : (¬ p3063) ∨ (¬ p3990) ∨ p3319) : (¬ p3063) ∨ (p3319) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial38649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3063)) ∨ (meaning t m 3319) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory27905 (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule38649 (meaning t m 3063) (meaning t m 3319) (meaning t m 3990) source

theorem rule38650 (p2027 p2313 p2553 p2577 p2608 p2619 p2839 p3956 p4433 p5193 : Prop) (h : (¬ p4433) ∨ (¬ p2619) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p2608) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial38650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory27906 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38650 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 3956) (meaning t m 4433) (meaning t m 5193) source

theorem rule38652 (p1982 p2027 p2132 p2166 p2533 p2611 p3680 p4418 p4444 : Prop) (h : (¬ p1982) ∨ (¬ p2166) ∨ p2611 ∨ (¬ p4444) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p2132) ∨ (¬ p4418) ∨ (¬ p2533)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p2533) ∨ (p2611) ∨ (¬ p3680) ∨ (¬ p4418) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial38652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2533)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory27908 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38652 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2166) (meaning t m 2533) (meaning t m 2611) (meaning t m 3680) (meaning t m 4418) (meaning t m 4444) source

theorem rule38653 (p2860 p3645 p3646 p4243 : Prop) (h : (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4243) ∨ (¬ p2860)) : (¬ p2860) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial38653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory27909 (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule38653 (meaning t m 2860) (meaning t m 3645) (meaning t m 3646) (meaning t m 4243) source

theorem rule38655 (p2027 p2313 p2553 p2608 p2619 p2839 p3956 p4433 p5021 : Prop) (h : p2027 ∨ (¬ p5021) ∨ (¬ p2619) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2313) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial38655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory27911 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38655 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 3956) (meaning t m 4433) (meaning t m 5021) source

theorem rule38656 (p2685 p2748 p4111 p4112 : Prop) (h : (¬ p4111) ∨ (¬ p4112) ∨ (¬ p2748) ∨ (¬ p2685)) : (¬ p2685) ∨ (¬ p2748) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial38656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory27912 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule38656 (meaning t m 2685) (meaning t m 2748) (meaning t m 4111) (meaning t m 4112) source

theorem rule38657 (p2748 p3572 p4111 p4112 : Prop) (h : (¬ p4111) ∨ (¬ p4112) ∨ (¬ p2748) ∨ p3572) : (¬ p2748) ∨ (p3572) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial38657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (meaning t m 3572) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory27913 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule38657 (meaning t m 2748) (meaning t m 3572) (meaning t m 4111) (meaning t m 4112) source

theorem rule38660 (p2027 p2177 p2247 p2307 p3848 p3941 p5017 p5119 p5284 : Prop) (h : (¬ p5119) ∨ (¬ p2177) ∨ (¬ p3941) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p5017) ∨ (¬ p2307) ∨ (¬ p2247) ∨ (¬ p3848)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3848) ∨ (¬ p3941) ∨ (¬ p5017) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial38660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory27916 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule38660 (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2307) (meaning t m 3848) (meaning t m 3941) (meaning t m 5017) (meaning t m 5119) (meaning t m 5284) source

theorem rule38670 (p1990 p2027 p2608 p2699 p2819 p2839 p3985 p3989 : Prop) (h : p2027 ∨ (¬ p2839) ∨ p2699 ∨ (¬ p1990) ∨ (¬ p3989) ∨ (¬ p3985) ∨ (¬ p2608) ∨ (¬ p2819)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2819) ∨ (¬ p2839) ∨ (¬ p3985) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial38670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory27926 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule38670 (meaning t m 1990) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2819) (meaning t m 2839) (meaning t m 3985) (meaning t m 3989) source

theorem rule38671 (p2027 p2177 p2254 p2608 p2839 p2870 p3414 p3553 p4556 : Prop) (h : (¬ p2177) ∨ (¬ p3553) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p4556) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial38671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory27927 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule38671 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2608) (meaning t m 2839) (meaning t m 2870) (meaning t m 3414) (meaning t m 3553) (meaning t m 4556) source

theorem rule38672 (p1998 p2027 p2427 p2542 p2765 p2881 p3096 p3574 : Prop) (h : (¬ p1998) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2881) ∨ (¬ p3096) ∨ p2765 ∨ (¬ p3574)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p3096) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial38672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory27928 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule38672 (meaning t m 1998) (meaning t m 2027) (meaning t m 2427) (meaning t m 2542) (meaning t m 2765) (meaning t m 2881) (meaning t m 3096) (meaning t m 3574) source

theorem rule38673 (p2027 p2252 p2750 p3266 p3292 p3399 p3631 p3950 p3954 p5284 : Prop) (h : (¬ p3950) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p5284) ∨ (¬ p3631) ∨ (¬ p2750) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial38673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory27929 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38673 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 3266) (meaning t m 3292) (meaning t m 3399) (meaning t m 3631) (meaning t m 3950) (meaning t m 3954) (meaning t m 5284) source

theorem rule38680 (p3097 p3822 p4185 : Prop) (h : (¬ p3822) ∨ (¬ p4185) ∨ p3097) : (p3097) ∨ (¬ p3822) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial38680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3097) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory27936 (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule38680 (meaning t m 3097) (meaning t m 3822) (meaning t m 4185) source

theorem rule38681 (p2027 p2493 p2651 p2952 p3879 p4116 p4717 : Prop) (h : (¬ p4717) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2493) ∨ (¬ p4116) ∨ (¬ p2651) ∨ (¬ p3879)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4116) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial38681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory27937 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule38681 (meaning t m 2027) (meaning t m 2493) (meaning t m 2651) (meaning t m 2952) (meaning t m 3879) (meaning t m 4116) (meaning t m 4717) source

theorem rule38684 (p2027 p2138 p3471 p3571 p4320 p4424 p5053 : Prop) (h : p2027 ∨ (¬ p5053) ∨ (¬ p4424) ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4320) ∨ (¬ p3571)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3571) ∨ (¬ p4320) ∨ (¬ p4424) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial38684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory27940 t (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7)
  exact rule38684 (meaning t m 2027) (meaning t m 2138) (meaning t m 3471) (meaning t m 3571) (meaning t m 4320) (meaning t m 4424) (meaning t m 5053) source

theorem rule38687 (p2027 p2363 p3055 p3366 p3449 p3591 p3684 p4318 p4866 p4948 p5059 : Prop) (h : (¬ p4948) ∨ p2027 ∨ (¬ p5059) ∨ (¬ p3684) ∨ (¬ p3366) ∨ (¬ p3055) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p3449) ∨ (¬ p2363) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial38687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory27943 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule38687 (meaning t m 2027) (meaning t m 2363) (meaning t m 3055) (meaning t m 3366) (meaning t m 3449) (meaning t m 3591) (meaning t m 3684) (meaning t m 4318) (meaning t m 4866) (meaning t m 4948) (meaning t m 5059) source

theorem rule38693 (p2027 p2220 p2630 p2657 p3146 p3366 p3370 p3877 p4041 p4236 p4348 p4377 : Prop) (h : (¬ p2630) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4377) ∨ (¬ p3370) ∨ (¬ p2657) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial38693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory27949 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38693 (meaning t m 2027) (meaning t m 2220) (meaning t m 2630) (meaning t m 2657) (meaning t m 3146) (meaning t m 3366) (meaning t m 3370) (meaning t m 3877) (meaning t m 4041) (meaning t m 4236) (meaning t m 4348) (meaning t m 4377) source

theorem rule38699 (p2011 p2027 p2202 p2589 p3276 p3355 p4322 : Prop) (h : (¬ p3355) ∨ p2202 ∨ p2027 ∨ (¬ p2589) ∨ (¬ p3276) ∨ (¬ p4322) ∨ (¬ p2011)) : (¬ p2011) ∨ (p2027) ∨ (p2202) ∨ (¬ p2589) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial38699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory27955 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule38699 (meaning t m 2011) (meaning t m 2027) (meaning t m 2202) (meaning t m 2589) (meaning t m 3276) (meaning t m 3355) (meaning t m 4322) source

theorem rule38700 (p1991 p2027 p2202 p2657 p2922 p3238 p3742 : Prop) (h : (¬ p3238) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p1991) ∨ (¬ p3742) ∨ p2202 ∨ (¬ p2922)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2657) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial38700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory27956 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule38700 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2657) (meaning t m 2922) (meaning t m 3238) (meaning t m 3742) source

theorem rule38709 (p2027 p2264 p2459 p2807 p3346 p3461 p3905 p4425 p4604 p4786 : Prop) (h : (¬ p2459) ∨ (¬ p2807) ∨ (¬ p4786) ∨ (¬ p2264) ∨ (¬ p4425) ∨ (¬ p3346) ∨ (¬ p4604) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p3461)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p4604) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial38709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory27965 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule38709 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3346) (meaning t m 3461) (meaning t m 3905) (meaning t m 4425) (meaning t m 4604) (meaning t m 4786) source

theorem rule38715 (p2027 p2264 p2946 p3551 p4849 p4917 : Prop) (h : (¬ p2264) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p4917) ∨ (¬ p4849) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2946) ∨ (¬ p3551) ∨ (¬ p4849) ∨ (¬ p4917) := by
  classical
  tauto

theorem initial38715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4849)) ∨ (¬ (meaning t m 4917)) := by
  have source := ElevenTheory.theory27971 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule38715 (meaning t m 2027) (meaning t m 2264) (meaning t m 2946) (meaning t m 3551) (meaning t m 4849) (meaning t m 4917) source

theorem rule38718 (p2027 p2241 p2449 p3027 p3055 p3644 p3876 p4668 p4736 : Prop) (h : (¬ p2449) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27974 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38718 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3055) (meaning t m 3644) (meaning t m 3876) (meaning t m 4668) (meaning t m 4736) source

theorem rule38728 (p1982 p2027 p2220 p2287 p2951 p3136 p3146 p4195 : Prop) (h : (¬ p1982) ∨ (¬ p2220) ∨ (¬ p2951) ∨ (¬ p3146) ∨ (¬ p3136) ∨ p2027 ∨ p2287 ∨ (¬ p4195)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2220) ∨ (p2287) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial38728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory27984 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 8 9)
  exact rule38728 (meaning t m 1982) (meaning t m 2027) (meaning t m 2220) (meaning t m 2287) (meaning t m 2951) (meaning t m 3136) (meaning t m 3146) (meaning t m 4195) source

theorem rule38729 (p2027 p2946 p3055 p3115 p3680 p3876 p4786 p4831 p5503 : Prop) (h : (¬ p5503) ∨ (¬ p3055) ∨ (¬ p4786) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p2946) ∨ (¬ p4831) ∨ (¬ p3876) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3876) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial38729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory27985 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule38729 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 3115) (meaning t m 3680) (meaning t m 3876) (meaning t m 4786) (meaning t m 4831) (meaning t m 5503) source

theorem rule38736 (p1996 p2027 p2287 p2807 p2952 p3136 p4195 : Prop) (h : (¬ p2807) ∨ (¬ p1996) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3136) ∨ p2287 ∨ (¬ p4195)) : (¬ p1996) ∨ (p2027) ∨ (p2287) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial38736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory27992 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7)
  exact rule38736 (meaning t m 1996) (meaning t m 2027) (meaning t m 2287) (meaning t m 2807) (meaning t m 2952) (meaning t m 3136) (meaning t m 4195) source

theorem rule38737 (p2027 p3055 p3073 p3366 p3449 p3591 p3684 p4866 p4948 p5059 : Prop) (h : (¬ p4948) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p5059) ∨ (¬ p3073) ∨ (¬ p4866) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3591) ∨ (¬ p3055)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p4866) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial38737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory27993 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 8 9)
  exact rule38737 (meaning t m 2027) (meaning t m 3055) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3591) (meaning t m 3684) (meaning t m 4866) (meaning t m 4948) (meaning t m 5059) source

theorem rule38740 (p2027 p2246 p2534 p2744 p2958 p3051 p3055 p3115 p3366 p3874 p4320 p4450 : Prop) (h : (¬ p3051) ∨ (¬ p4320) ∨ (¬ p2958) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3115) ∨ (¬ p2744) ∨ (¬ p3874) ∨ (¬ p4450) ∨ (¬ p2534) ∨ (¬ p3366) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3874) ∨ (¬ p4320) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial38740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory27996 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule38740 (meaning t m 2027) (meaning t m 2246) (meaning t m 2534) (meaning t m 2744) (meaning t m 2958) (meaning t m 3051) (meaning t m 3055) (meaning t m 3115) (meaning t m 3366) (meaning t m 3874) (meaning t m 4320) (meaning t m 4450) source

theorem rule38741 (p2252 p2657 p3878 p4360 : Prop) (h : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3878) ∨ p4360) : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3878) ∨ (p4360) := by
  classical
  tauto

theorem initial38741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3878)) ∨ (meaning t m 4360) := by
  have source := ElevenTheory.theory27997 (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8)
  exact rule38741 (meaning t m 2252) (meaning t m 2657) (meaning t m 3878) (meaning t m 4360) source

theorem rule38743 (p2027 p2220 p2657 p2951 p3136 p3146 p3358 p3683 p4286 p4787 p5118 p5160 : Prop) (h : p2027 ∨ (¬ p5118) ∨ (¬ p2220) ∨ (¬ p2657) ∨ (¬ p4787) ∨ (¬ p3683) ∨ (¬ p3146) ∨ (¬ p3136) ∨ (¬ p4286) ∨ (¬ p2951) ∨ (¬ p3358) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2657) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3358) ∨ (¬ p3683) ∨ (¬ p4286) ∨ (¬ p4787) ∨ (¬ p5118) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial38743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory27999 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule38743 (meaning t m 2027) (meaning t m 2220) (meaning t m 2657) (meaning t m 2951) (meaning t m 3136) (meaning t m 3146) (meaning t m 3358) (meaning t m 3683) (meaning t m 4286) (meaning t m 4787) (meaning t m 5118) (meaning t m 5160) source

theorem rule38744 (p2010 p2027 p2287 p2499 p2668 p2922 p3956 : Prop) (h : p2027 ∨ (¬ p2499) ∨ p2287 ∨ (¬ p2010) ∨ (¬ p2922) ∨ (¬ p2668) ∨ (¬ p3956)) : (¬ p2010) ∨ (p2027) ∨ (p2287) ∨ (¬ p2499) ∨ (¬ p2668) ∨ (¬ p2922) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial38744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory28000 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule38744 (meaning t m 2010) (meaning t m 2027) (meaning t m 2287) (meaning t m 2499) (meaning t m 2668) (meaning t m 2922) (meaning t m 3956) source

theorem rule38745 (p2027 p2475 p3574 p3641 p3989 p4113 p4343 p4718 : Prop) (h : (¬ p4718) ∨ (¬ p3989) ∨ (¬ p2475) ∨ (¬ p3641) ∨ (¬ p3574) ∨ (¬ p4113) ∨ p2027 ∨ (¬ p4343)) : (p2027) ∨ (¬ p2475) ∨ (¬ p3574) ∨ (¬ p3641) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4343) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial38745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory28001 t (m.theta 0 8) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule38745 (meaning t m 2027) (meaning t m 2475) (meaning t m 3574) (meaning t m 3641) (meaning t m 3989) (meaning t m 4113) (meaning t m 4343) (meaning t m 4718) source

theorem rule38746 (p2027 p2951 p3051 p3136 p3745 p4195 p4558 : Prop) (h : (¬ p2951) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4558)) : (p2027) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial38746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory28002 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule38746 (meaning t m 2027) (meaning t m 2951) (meaning t m 3051) (meaning t m 3136) (meaning t m 3745) (meaning t m 4195) (meaning t m 4558) source

theorem rule38748 (p2027 p2995 p3497 p3931 p4901 p5660 : Prop) (h : (¬ p3931) ∨ (¬ p2995) ∨ p2027 ∨ (¬ p5660) ∨ (¬ p4901) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2995) ∨ (¬ p3497) ∨ (¬ p3931) ∨ (¬ p4901) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial38748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4901)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory28004 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10)
  exact rule38748 (meaning t m 2027) (meaning t m 2995) (meaning t m 3497) (meaning t m 3931) (meaning t m 4901) (meaning t m 5660) source

theorem rule38752 (p2027 p2139 p2156 p2274 p2396 p2810 p3359 p3365 p4641 : Prop) (h : (¬ p4641) ∨ (¬ p3359) ∨ (¬ p2274) ∨ (¬ p2810) ∨ (¬ p2156) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2810) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p4641) := by
  classical
  tauto

theorem initial38752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4641)) := by
  have source := ElevenTheory.theory28008 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule38752 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2810) (meaning t m 3359) (meaning t m 3365) (meaning t m 4641) source

theorem rule38755 (p3276 p3461 p4022 : Prop) (h : (¬ p3276) ∨ (¬ p4022) ∨ p3461) : (¬ p3276) ∨ (p3461) ∨ (¬ p4022) := by
  classical
  tauto

theorem initial38755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3276)) ∨ (meaning t m 3461) ∨ (¬ (meaning t m 4022)) := by
  have source := ElevenTheory.theory28011 (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule38755 (meaning t m 3276) (meaning t m 3461) (meaning t m 4022) source

theorem rule38758 (p2027 p3434 p3587 p3690 p3758 p4558 : Prop) (h : p2027 ∨ (¬ p3690) ∨ (¬ p4558) ∨ (¬ p3587) ∨ (¬ p3434) ∨ (¬ p3758)) : (p2027) ∨ (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3690) ∨ (¬ p3758) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial38758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory28014 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule38758 (meaning t m 2027) (meaning t m 3434) (meaning t m 3587) (meaning t m 3690) (meaning t m 3758) (meaning t m 4558) source

theorem rule38761 (p2027 p2295 p2331 p2396 p3346 p3680 p3905 p3951 p4786 p5164 p5387 : Prop) (h : (¬ p3346) ∨ (¬ p3905) ∨ (¬ p4786) ∨ (¬ p5164) ∨ (¬ p5387) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p3680) ∨ (¬ p2331) ∨ (¬ p3951)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p3905) ∨ (¬ p3951) ∨ (¬ p4786) ∨ (¬ p5164) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial38761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5164)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory28017 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 9) (m.theta 3 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule38761 (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 3346) (meaning t m 3680) (meaning t m 3905) (meaning t m 3951) (meaning t m 4786) (meaning t m 5164) (meaning t m 5387) source

theorem rule38768 (p1991 p2027 p2633 p2797 p2963 p3553 p3572 : Prop) (h : (¬ p1991) ∨ (¬ p3553) ∨ (¬ p2963) ∨ p2633 ∨ p2027 ∨ (¬ p2797) ∨ (¬ p3572)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial38768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory28024 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule38768 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 2797) (meaning t m 2963) (meaning t m 3553) (meaning t m 3572) source

theorem rule38771 (p2027 p2104 p2363 p2928 p3222 p3389 p3657 p4079 p4340 p4451 p4503 p4736 : Prop) (h : (¬ p3389) ∨ (¬ p4079) ∨ (¬ p2363) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2104) ∨ (¬ p4503) ∨ (¬ p3657) ∨ (¬ p4451) ∨ (¬ p3222) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2363) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3389) ∨ (¬ p3657) ∨ (¬ p4079) ∨ (¬ p4340) ∨ (¬ p4451) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28027 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 8) (m.theta 4 7) (m.theta 4 9) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38771 (meaning t m 2027) (meaning t m 2104) (meaning t m 2363) (meaning t m 2928) (meaning t m 3222) (meaning t m 3389) (meaning t m 3657) (meaning t m 4079) (meaning t m 4340) (meaning t m 4451) (meaning t m 4503) (meaning t m 4736) source

theorem rule38772 (p2010 p2027 p2388 p2449 p2685 p4278 p4315 : Prop) (h : (¬ p4278) ∨ (¬ p2010) ∨ p2388 ∨ (¬ p2685) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p2449)) : (¬ p2010) ∨ (p2027) ∨ (p2388) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p4278) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial38772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory28028 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule38772 (meaning t m 2010) (meaning t m 2027) (meaning t m 2388) (meaning t m 2449) (meaning t m 2685) (meaning t m 4278) (meaning t m 4315) source

theorem rule38778 (p1994 p2027 p2352 p2727 p3008 p3324 p4154 : Prop) (h : (¬ p2727) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p1994) ∨ p3008 ∨ (¬ p2352) ∨ (¬ p4154)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2727) ∨ (p3008) ∨ (¬ p3324) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial38778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory28034 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule38778 (meaning t m 1994) (meaning t m 2027) (meaning t m 2352) (meaning t m 2727) (meaning t m 3008) (meaning t m 3324) (meaning t m 4154) source

theorem rule38789 (p2027 p2187 p2192 p2210 p3365 p3553 p3572 p4133 p4736 : Prop) (h : (¬ p4133) ∨ (¬ p3365) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3553) ∨ (¬ p2187) ∨ (¬ p4736) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28045 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule38789 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 4133) (meaning t m 4736) source

theorem rule38792 (p1982 p2027 p2633 p2657 p2951 p3136 p3146 p3644 p3683 p3876 p3998 p4238 p4787 p5568 : Prop) (h : (¬ p1982) ∨ (¬ p3146) ∨ (¬ p4787) ∨ p2633 ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p3876) ∨ (¬ p3683) ∨ (¬ p4238) ∨ (¬ p3998) ∨ (¬ p5568)) : (¬ p1982) ∨ (p2027) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p3998) ∨ (¬ p4238) ∨ (¬ p4787) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial38792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory28048 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 8) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule38792 (meaning t m 1982) (meaning t m 2027) (meaning t m 2633) (meaning t m 2657) (meaning t m 2951) (meaning t m 3136) (meaning t m 3146) (meaning t m 3644) (meaning t m 3683) (meaning t m 3876) (meaning t m 3998) (meaning t m 4238) (meaning t m 4787) (meaning t m 5568) source

theorem rule38796 (p2005 p2027 p2388 p2493 p3193 p3755 p4315 p5175 : Prop) (h : (¬ p2005) ∨ (¬ p3755) ∨ p2388 ∨ (¬ p2493) ∨ (¬ p4315) ∨ (¬ p5175) ∨ (¬ p3193) ∨ p2027) : (¬ p2005) ∨ (p2027) ∨ (p2388) ∨ (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3755) ∨ (¬ p4315) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial38796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory28052 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9)
  exact rule38796 (meaning t m 2005) (meaning t m 2027) (meaning t m 2388) (meaning t m 2493) (meaning t m 3193) (meaning t m 3755) (meaning t m 4315) (meaning t m 5175) source

theorem rule38798 (p2027 p2717 p3414 p3553 p4781 p4787 : Prop) (h : (¬ p3553) ∨ (¬ p4781) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4781) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial38798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4781)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory28054 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule38798 (meaning t m 2027) (meaning t m 2717) (meaning t m 3414) (meaning t m 3553) (meaning t m 4781) (meaning t m 4787) source

theorem rule38800 (p2274 p3309 p4516 : Prop) (h : (¬ p2274) ∨ (¬ p4516) ∨ p3309) : (¬ p2274) ∨ (p3309) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial38800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (meaning t m 3309) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory28056 (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule38800 (meaning t m 2274) (meaning t m 3309) (meaning t m 4516) source

theorem rule38803 (p2027 p3005 p4009 p4035 p5107 p5122 : Prop) (h : (¬ p5122) ∨ (¬ p4035) ∨ (¬ p5107) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p4009)) : (p2027) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4035) ∨ (¬ p5107) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial38803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5107)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory28059 t (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 8 10) (m.theta 8 9)
  exact rule38803 (meaning t m 2027) (meaning t m 3005) (meaning t m 4009) (meaning t m 4035) (meaning t m 5107) (meaning t m 5122) source

theorem rule38806 (p2027 p2470 p2531 p2656 p3146 p3359 p4636 p4669 : Prop) (h : (¬ p3146) ∨ (¬ p2470) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p4636) ∨ (¬ p2656) ∨ (¬ p2531) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2656) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p4636) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial38806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory28062 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38806 (meaning t m 2027) (meaning t m 2470) (meaning t m 2531) (meaning t m 2656) (meaning t m 3146) (meaning t m 3359) (meaning t m 4636) (meaning t m 4669) source

theorem rule38807 (p2027 p2139 p2156 p2177 p2274 p2810 p3365 p4256 p4438 : Prop) (h : (¬ p2139) ∨ (¬ p2810) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4438) ∨ (¬ p2274) ∨ (¬ p2177) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4256) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial38807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory28063 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule38807 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2810) (meaning t m 3365) (meaning t m 4256) (meaning t m 4438) source

theorem rule38809 (p1975 p2027 p2233 p2470 p2493 p2509 p2553 : Prop) (h : (¬ p2470) ∨ p2233 ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (p2233) ∨ (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2553) := by
  classical
  tauto

theorem initial38809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2553)) := by
  have source := ElevenTheory.theory28065 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule38809 (meaning t m 1975) (meaning t m 2027) (meaning t m 2233) (meaning t m 2470) (meaning t m 2493) (meaning t m 2509) (meaning t m 2553) source

theorem rule38811 (p2027 p3291 p3755 p3877 p4348 p4437 p4438 p4460 : Prop) (h : (¬ p4348) ∨ (¬ p4438) ∨ (¬ p3755) ∨ (¬ p4460) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p4437) ∨ (¬ p3291)) : (p2027) ∨ (¬ p3291) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4348) ∨ (¬ p4437) ∨ (¬ p4438) ∨ (¬ p4460) := by
  classical
  tauto

theorem initial38811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3291)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4460)) := by
  have source := ElevenTheory.theory28067 t (m.theta 0 9) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38811 (meaning t m 2027) (meaning t m 3291) (meaning t m 3755) (meaning t m 3877) (meaning t m 4348) (meaning t m 4437) (meaning t m 4438) (meaning t m 4460) source

theorem rule38812 (p2027 p3755 p3877 p4347 p4350 p4774 : Prop) (h : (¬ p4347) ∨ (¬ p4350) ∨ (¬ p4774) ∨ (¬ p3755) ∨ (¬ p3877) ∨ p2027) : (p2027) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4347) ∨ (¬ p4350) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial38812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4350)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory28068 t (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 6 8) (m.theta 8 9)
  exact rule38812 (meaning t m 2027) (meaning t m 3755) (meaning t m 3877) (meaning t m 4347) (meaning t m 4350) (meaning t m 4774) source

theorem rule38813 (p2027 p2253 p2741 p3166 p3555 p4360 p4377 : Prop) (h : (¬ p4377) ∨ (¬ p2253) ∨ (¬ p3555) ∨ (¬ p4360) ∨ (¬ p2741) ∨ (¬ p3166) ∨ p2027) : (p2027) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p3166) ∨ (¬ p3555) ∨ (¬ p4360) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial38813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory28069 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 8)
  exact rule38813 (meaning t m 2027) (meaning t m 2253) (meaning t m 2741) (meaning t m 3166) (meaning t m 3555) (meaning t m 4360) (meaning t m 4377) source

theorem rule38815 (p2027 p2299 p3641 p3742 p4343 p4404 p4712 : Prop) (h : (¬ p3641) ∨ (¬ p4712) ∨ (¬ p4343) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p4404) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3641) ∨ (¬ p3742) ∨ (¬ p4343) ∨ (¬ p4404) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial38815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory28071 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule38815 (meaning t m 2027) (meaning t m 2299) (meaning t m 3641) (meaning t m 3742) (meaning t m 4343) (meaning t m 4404) (meaning t m 4712) source

theorem rule38821 (p2027 p2383 p2781 p3125 p3276 p3292 p3989 p4236 p5284 p5325 : Prop) (h : (¬ p5325) ∨ (¬ p3292) ∨ (¬ p3276) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3989) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3125) ∨ (¬ p3276) ∨ (¬ p3292) ∨ (¬ p3989) ∨ (¬ p4236) ∨ (¬ p5284) ∨ (¬ p5325) := by
  classical
  tauto

theorem initial38821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5325)) := by
  have source := ElevenTheory.theory28077 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 3 9) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule38821 (meaning t m 2027) (meaning t m 2383) (meaning t m 2781) (meaning t m 3125) (meaning t m 3276) (meaning t m 3292) (meaning t m 3989) (meaning t m 4236) (meaning t m 5284) (meaning t m 5325) source

theorem rule38825 (p2027 p2187 p2307 p2630 p2657 p2781 p3097 p3877 p4236 p4774 : Prop) (h : (¬ p3097) ∨ (¬ p4774) ∨ (¬ p2307) ∨ (¬ p3877) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p4236) ∨ (¬ p2781)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p3097) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial38825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory28081 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule38825 (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2630) (meaning t m 2657) (meaning t m 2781) (meaning t m 3097) (meaning t m 3877) (meaning t m 4236) (meaning t m 4774) source

theorem rule38829 (p4377 p4496 p5312 : Prop) (h : (¬ p4377) ∨ (¬ p4496) ∨ p5312) : (¬ p4377) ∨ (¬ p4496) ∨ (p5312) := by
  classical
  tauto

theorem initial38829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4496)) ∨ (meaning t m 5312) := by
  have source := ElevenTheory.theory28085 t (m.theta 1 2) (m.theta 1 5) (m.theta 1 8)
  exact rule38829 (meaning t m 4377) (meaning t m 4496) (meaning t m 5312) source

theorem rule38833 (p2027 p2630 p2657 p3212 p3366 p3370 p3680 p4035 p4236 p4377 p4444 p4697 p5171 : Prop) (h : (¬ p3680) ∨ (¬ p4697) ∨ (¬ p3212) ∨ (¬ p4236) ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p4035) ∨ (¬ p2630) ∨ (¬ p5171) ∨ (¬ p2657) ∨ (¬ p4377)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3680) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial38833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory28089 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38833 (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 3212) (meaning t m 3366) (meaning t m 3370) (meaning t m 3680) (meaning t m 4035) (meaning t m 4236) (meaning t m 4377) (meaning t m 4444) (meaning t m 4697) (meaning t m 5171) source

theorem rule38835 (p2027 p2459 p2881 p3051 p3365 p3366 p3370 p4037 p4195 p4377 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p2459) ∨ (¬ p3366) ∨ (¬ p4195) ∨ (¬ p3051) ∨ (¬ p4377) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p4037)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial38835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory28091 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38835 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3051) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 4037) (meaning t m 4195) (meaning t m 4377) (meaning t m 4604) source

theorem rule38836 (p2027 p2383 p2962 p3055 p3125 p3366 p3370 p3876 p3989 p4278 p4377 p4621 : Prop) (h : (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4377) ∨ (¬ p3370) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4278) ∨ (¬ p2962) ∨ (¬ p2383) ∨ (¬ p4621) ∨ (¬ p3366) ∨ p2027) : (p2027) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3055) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3876) ∨ (¬ p3989) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial38836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory28092 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule38836 (meaning t m 2027) (meaning t m 2383) (meaning t m 2962) (meaning t m 3055) (meaning t m 3125) (meaning t m 3366) (meaning t m 3370) (meaning t m 3876) (meaning t m 3989) (meaning t m 4278) (meaning t m 4377) (meaning t m 4621) source

theorem rule38842 (p3917 p4037 p4337 : Prop) (h : (¬ p4337) ∨ (¬ p4037) ∨ p3917) : (p3917) ∨ (¬ p4037) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial38842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3917) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory28098 (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule38842 (meaning t m 3917) (meaning t m 4037) (meaning t m 4337) source

theorem rule38844 (p2027 p3055 p3146 p3366 p3449 p3555 p3876 p4278 p4377 p4446 p4669 : Prop) (h : (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3146) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4446) ∨ (¬ p3449) ∨ (¬ p3555)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial38844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory28100 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38844 (meaning t m 2027) (meaning t m 3055) (meaning t m 3146) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3876) (meaning t m 4278) (meaning t m 4377) (meaning t m 4446) (meaning t m 4669) source

theorem rule38849 (p2027 p2139 p2630 p2657 p2962 p3461 p3654 p4035 p4236 p4381 p4663 : Prop) (h : (¬ p4663) ∨ (¬ p3461) ∨ (¬ p2139) ∨ (¬ p2657) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p2630) ∨ (¬ p4236)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2962) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4381) ∨ (¬ p4663) := by
  classical
  tauto

theorem initial38849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4663)) := by
  have source := ElevenTheory.theory28105 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule38849 (meaning t m 2027) (meaning t m 2139) (meaning t m 2630) (meaning t m 2657) (meaning t m 2962) (meaning t m 3461) (meaning t m 3654) (meaning t m 4035) (meaning t m 4236) (meaning t m 4381) (meaning t m 4663) source

end SunPrize.SMT
