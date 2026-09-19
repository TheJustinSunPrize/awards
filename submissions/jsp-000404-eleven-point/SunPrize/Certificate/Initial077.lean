import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory061
import SunPrize.Certificate.Theory062
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule35305 (p2027 p2230 p2274 p2284 p2717 p3548 p3879 p3954 p4400 p4477 p5190 : Prop) (h : (¬ p2717) ∨ (¬ p2230) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p2284) ∨ (¬ p2274) ∨ (¬ p4477) ∨ (¬ p4400) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2717) ∨ (¬ p3548) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4400) ∨ (¬ p4477) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial35305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory24561 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35305 (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2284) (meaning t m 2717) (meaning t m 3548) (meaning t m 3879) (meaning t m 3954) (meaning t m 4400) (meaning t m 4477) (meaning t m 5190) source

theorem rule35308 (p2027 p2104 p2230 p2274 p2284 p3537 p3588 p3873 p3879 p4477 p5190 : Prop) (h : (¬ p2230) ∨ (¬ p4477) ∨ (¬ p2274) ∨ (¬ p3588) ∨ (¬ p2284) ∨ (¬ p3537) ∨ (¬ p3879) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p2104) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3879) ∨ (¬ p4477) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial35308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory24564 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule35308 (meaning t m 2027) (meaning t m 2104) (meaning t m 2230) (meaning t m 2274) (meaning t m 2284) (meaning t m 3537) (meaning t m 3588) (meaning t m 3873) (meaning t m 3879) (meaning t m 4477) (meaning t m 5190) source

theorem rule35309 (p2027 p2230 p2373 p3146 p3588 p3954 p4324 p4669 p5190 : Prop) (h : (¬ p3146) ∨ (¬ p2373) ∨ (¬ p4669) ∨ (¬ p4324) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2230) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial35309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory24565 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule35309 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4669) (meaning t m 5190) source

theorem rule35312 (p2685 p3005 p3919 : Prop) (h : (¬ p3919) ∨ (¬ p3005) ∨ p2685) : (p2685) ∨ (¬ p3005) ∨ (¬ p3919) := by
  classical
  tauto

theorem initial35312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3919)) := by
  have source := ElevenTheory.theory24568 (m.theta 2 3) (m.theta 3 7) (m.theta 3 8)
  exact rule35312 (meaning t m 2685) (meaning t m 3005) (meaning t m 3919) source

theorem rule35315 (p2027 p2088 p2499 p2860 p3452 p3660 p4235 p4340 p4359 p4555 p4590 p5207 : Prop) (h : (¬ p4555) ∨ (¬ p5207) ∨ (¬ p4235) ∨ (¬ p2499) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4340) ∨ (¬ p3660) ∨ (¬ p4359) ∨ (¬ p4590) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3452) ∨ (¬ p3660) ∨ (¬ p4235) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4555) ∨ (¬ p4590) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial35315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4555)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory24571 t (m.theta 0 1) (m.theta 0 7) (m.theta 0 8) (m.theta 1 4) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule35315 (meaning t m 2027) (meaning t m 2088) (meaning t m 2499) (meaning t m 2860) (meaning t m 3452) (meaning t m 3660) (meaning t m 4235) (meaning t m 4340) (meaning t m 4359) (meaning t m 4555) (meaning t m 4590) (meaning t m 5207) source

theorem rule35316 (p2027 p2230 p2284 p3737 p3879 p3954 p4379 p5190 p5250 p5387 : Prop) (h : (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5190) ∨ (¬ p2284) ∨ (¬ p3879) ∨ (¬ p5250) ∨ (¬ p2230) ∨ (¬ p5387) ∨ p2027 ∨ (¬ p3737)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3737) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5190) ∨ (¬ p5250) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial35316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5250)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory24572 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 9) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 10) (m.theta 9 10)
  exact rule35316 (meaning t m 2027) (meaning t m 2230) (meaning t m 2284) (meaning t m 3737) (meaning t m 3879) (meaning t m 3954) (meaning t m 4379) (meaning t m 5190) (meaning t m 5250) (meaning t m 5387) source

theorem rule35317 (p1997 p2027 p2542 p2633 p3246 p3359 p3570 p4636 : Prop) (h : (¬ p1997) ∨ (¬ p4636) ∨ p2633 ∨ (¬ p2542) ∨ (¬ p3570) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p3246)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial35317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory24573 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35317 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2633) (meaning t m 3246) (meaning t m 3359) (meaning t m 3570) (meaning t m 4636) source

theorem rule35320 (p2027 p2136 p2573 p2870 p3083 p3556 p3574 p3694 p4158 p4419 : Prop) (h : (¬ p4158) ∨ (¬ p3556) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p2136) ∨ (¬ p4419) ∨ (¬ p3694) ∨ (¬ p2573) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2573) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3694) ∨ (¬ p4158) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial35320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory24576 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule35320 (meaning t m 2027) (meaning t m 2136) (meaning t m 2573) (meaning t m 2870) (meaning t m 3083) (meaning t m 3556) (meaning t m 3574) (meaning t m 3694) (meaning t m 4158) (meaning t m 4419) source

theorem rule35323 (p2027 p2230 p2274 p2284 p3609 p3860 p3879 p4261 p4477 p4805 p5190 : Prop) (h : (¬ p4261) ∨ (¬ p5190) ∨ (¬ p3609) ∨ (¬ p3860) ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p4477) ∨ (¬ p3879) ∨ (¬ p4805) ∨ p2027 ∨ (¬ p2274)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3609) ∨ (¬ p3860) ∨ (¬ p3879) ∨ (¬ p4261) ∨ (¬ p4477) ∨ (¬ p4805) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial35323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory24579 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule35323 (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2284) (meaning t m 3609) (meaning t m 3860) (meaning t m 3879) (meaning t m 4261) (meaning t m 4477) (meaning t m 4805) (meaning t m 5190) source

theorem rule35324 (p1997 p2027 p2633 p3105 p3570 p4244 p4948 : Prop) (h : (¬ p3570) ∨ p2633 ∨ (¬ p4244) ∨ (¬ p1997) ∨ (¬ p4948) ∨ p2027 ∨ (¬ p3105)) : (¬ p1997) ∨ (p2027) ∨ (p2633) ∨ (¬ p3105) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial35324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory24580 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule35324 (meaning t m 1997) (meaning t m 2027) (meaning t m 2633) (meaning t m 3105) (meaning t m 3570) (meaning t m 4244) (meaning t m 4948) source

theorem rule35325 (p2027 p2138 p2573 p3083 p3570 p3574 p4244 p4419 p4420 : Prop) (h : (¬ p4244) ∨ (¬ p4419) ∨ (¬ p2138) ∨ (¬ p3574) ∨ (¬ p3570) ∨ (¬ p2573) ∨ (¬ p4420) ∨ p2027 ∨ (¬ p3083)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial35325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory24581 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule35325 (meaning t m 2027) (meaning t m 2138) (meaning t m 2573) (meaning t m 3083) (meaning t m 3570) (meaning t m 3574) (meaning t m 4244) (meaning t m 4419) (meaning t m 4420) source

theorem rule35331 (p2027 p2230 p2440 p2531 p3083 p3588 p3659 p3954 p4902 p5190 : Prop) (h : (¬ p2531) ∨ (¬ p3954) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p5190) ∨ (¬ p3083) ∨ (¬ p4902) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3588)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4902) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial35331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory24587 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule35331 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2531) (meaning t m 3083) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4902) (meaning t m 5190) source

theorem rule35334 (p2027 p2341 p2459 p2499 p2707 p3055 p3577 p4030 p4137 p4604 p4734 : Prop) (h : (¬ p2499) ∨ (¬ p4030) ∨ (¬ p3577) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2459) ∨ (¬ p4604) ∨ (¬ p2341) ∨ (¬ p4734) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2707) ∨ (¬ p3055) ∨ (¬ p3577) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial35334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory24590 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule35334 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2499) (meaning t m 2707) (meaning t m 3055) (meaning t m 3577) (meaning t m 4030) (meaning t m 4137) (meaning t m 4604) (meaning t m 4734) source

theorem rule35335 (p2027 p2331 p2751 p3027 p3414 p4195 : Prop) (h : (¬ p3027) ∨ (¬ p4195) ∨ (¬ p2331) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p2751)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial35335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory24591 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule35335 (meaning t m 2027) (meaning t m 2331) (meaning t m 2751) (meaning t m 3027) (meaning t m 3414) (meaning t m 4195) source

theorem rule35339 (p2191 p3694 p4418 : Prop) (h : (¬ p4418) ∨ (¬ p3694) ∨ p2191) : (p2191) ∨ (¬ p3694) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial35339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2191) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory24595 (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule35339 (meaning t m 2191) (meaning t m 3694) (meaning t m 4418) source

theorem rule35344 (p2027 p2528 p3551 p3875 p4348 p5199 : Prop) (h : (¬ p5199) ∨ (¬ p3875) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3551) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p5199) := by
  classical
  tauto

theorem initial35344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5199)) := by
  have source := ElevenTheory.theory24600 t (m.theta 0 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35344 (meaning t m 2027) (meaning t m 2528) (meaning t m 3551) (meaning t m 3875) (meaning t m 4348) (meaning t m 5199) source

theorem rule35346 (p2027 p2246 p2573 p2608 p2663 p2744 p3343 p3574 p4324 p4366 p4424 p4638 : Prop) (h : (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p4638) ∨ (¬ p3574) ∨ (¬ p4424) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p2744) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4638) := by
  classical
  tauto

theorem initial35346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4638)) := by
  have source := ElevenTheory.theory24602 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 7 9)
  exact rule35346 (meaning t m 2027) (meaning t m 2246) (meaning t m 2573) (meaning t m 2608) (meaning t m 2663) (meaning t m 2744) (meaning t m 3343) (meaning t m 3574) (meaning t m 4324) (meaning t m 4366) (meaning t m 4424) (meaning t m 4638) source

theorem rule35354 (p1994 p2027 p2148 p2651 p2952 p3051 p4320 : Prop) (h : (¬ p2651) ∨ p2148 ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p1994) ∨ (¬ p2952)) : (¬ p1994) ∨ (p2027) ∨ (p2148) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3051) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial35354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory24610 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule35354 (meaning t m 1994) (meaning t m 2027) (meaning t m 2148) (meaning t m 2651) (meaning t m 2952) (meaning t m 3051) (meaning t m 4320) source

theorem rule35358 (p1984 p2027 p2881 p2928 p2938 p3452 p3644 : Prop) (h : (¬ p3452) ∨ (¬ p1984) ∨ p2027 ∨ p2938 ∨ (¬ p2881) ∨ (¬ p2928) ∨ (¬ p3644)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2881) ∨ (¬ p2928) ∨ (p2938) ∨ (¬ p3452) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial35358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory24614 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule35358 (meaning t m 1984) (meaning t m 2027) (meaning t m 2881) (meaning t m 2928) (meaning t m 2938) (meaning t m 3452) (meaning t m 3644) source

theorem rule35361 (p2027 p2136 p2241 p2299 p2727 p3083 p3097 p3646 p4420 p4736 : Prop) (h : (¬ p4420) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2136) ∨ (¬ p3083) ∨ (¬ p3646) ∨ (¬ p2299) ∨ (¬ p2241) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial35361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24617 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35361 (meaning t m 2027) (meaning t m 2136) (meaning t m 2241) (meaning t m 2299) (meaning t m 2727) (meaning t m 3083) (meaning t m 3097) (meaning t m 3646) (meaning t m 4420) (meaning t m 4736) source

theorem rule35365 (p1994 p2027 p2651 p2881 p2938 p3414 p3553 : Prop) (h : (¬ p2651) ∨ (¬ p3414) ∨ p2938 ∨ (¬ p2881) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3553)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial35365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory24621 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule35365 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2881) (meaning t m 2938) (meaning t m 3414) (meaning t m 3553) source

theorem rule35366 (p2027 p2774 p3238 p3452 p3609 p3880 p4134 p4347 p4733 p4861 : Prop) (h : (¬ p4733) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p4861) ∨ (¬ p3880) ∨ (¬ p3238) ∨ (¬ p2774) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2774) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4733) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial35366 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory24622 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule35366 (meaning t m 2027) (meaning t m 2774) (meaning t m 3238) (meaning t m 3452) (meaning t m 3609) (meaning t m 3880) (meaning t m 4134) (meaning t m 4347) (meaning t m 4733) (meaning t m 4861) source

theorem rule35375 (p2027 p2177 p2249 p2295 p2641 p2657 p3238 p3487 p3880 p4905 : Prop) (h : (¬ p3880) ∨ (¬ p2249) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p2295) ∨ (¬ p2657) ∨ (¬ p2641) ∨ (¬ p3238) ∨ (¬ p3487)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2249) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial35375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory24631 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule35375 (meaning t m 2027) (meaning t m 2177) (meaning t m 2249) (meaning t m 2295) (meaning t m 2641) (meaning t m 2657) (meaning t m 3238) (meaning t m 3487) (meaning t m 3880) (meaning t m 4905) source

theorem rule35378 (p1987 p2027 p2641 p2651 p2688 p2810 p2963 : Prop) (h : (¬ p2641) ∨ (¬ p1987) ∨ p2688 ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2651)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2641) ∨ (¬ p2651) ∨ (p2688) ∨ (¬ p2810) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial35378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory24634 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule35378 (meaning t m 1987) (meaning t m 2027) (meaning t m 2641) (meaning t m 2651) (meaning t m 2688) (meaning t m 2810) (meaning t m 2963) source

theorem rule35382 (p2440 p4256 p4607 : Prop) (h : (¬ p2440) ∨ (¬ p4607) ∨ p4256) : (¬ p2440) ∨ (p4256) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial35382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (meaning t m 4256) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory24638 (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule35382 (meaning t m 2440) (meaning t m 4256) (meaning t m 4607) source

theorem rule35383 (p3040 p4427 p4570 : Prop) (h : (¬ p4427) ∨ (¬ p4570) ∨ p3040) : (p3040) ∨ (¬ p4427) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial35383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3040) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory24639 t (m.theta 1 7) (m.theta 3 7) (m.theta 6 7)
  exact rule35383 (meaning t m 3040) (meaning t m 4427) (meaning t m 4570) source

theorem rule35384 (p4275 p4280 p4570 : Prop) (h : (¬ p4570) ∨ (¬ p4275) ∨ p4280) : (¬ p4275) ∨ (p4280) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial35384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4275)) ∨ (meaning t m 4280) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory24640 t (m.theta 3 7) (m.theta 5 7) (m.theta 6 7)
  exact rule35384 (meaning t m 4275) (meaning t m 4280) (meaning t m 4570) source

theorem rule35387 (p2264 p3960 p3961 p4155 : Prop) (h : (¬ p2264) ∨ (¬ p3961) ∨ (¬ p4155) ∨ (¬ p3960)) : (¬ p2264) ∨ (¬ p3960) ∨ (¬ p3961) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial35387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory24643 (m.theta 0 7) (m.theta 0 8) (m.theta 3 7) (m.theta 7 8)
  exact rule35387 (meaning t m 2264) (meaning t m 3960) (meaning t m 3961) (meaning t m 4155) source

theorem rule35388 (p2331 p2946 p4153 : Prop) (h : (¬ p4153) ∨ (¬ p2331) ∨ p2946) : (¬ p2331) ∨ (p2946) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial35388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (meaning t m 2946) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory24644 (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule35388 (meaning t m 2331) (meaning t m 2946) (meaning t m 4153) source

theorem rule35400 (p2027 p2751 p3309 p3568 p4195 p4759 : Prop) (h : (¬ p4759) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p2751) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial35400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory24656 t (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule35400 (meaning t m 2027) (meaning t m 2751) (meaning t m 3309) (meaning t m 3568) (meaning t m 4195) (meaning t m 4759) source

theorem rule35401 (p2027 p2248 p2499 p3166 p3256 p3266 p3452 p5254 p5514 : Prop) (h : (¬ p3266) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3256) ∨ (¬ p2248) ∨ (¬ p5254) ∨ (¬ p3166) ∨ (¬ p5514)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3452) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial35401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory24657 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule35401 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3452) (meaning t m 5254) (meaning t m 5514) source

theorem rule35403 (p2027 p2156 p3737 p3880 p4109 p4506 p5586 : Prop) (h : p2027 ∨ (¬ p3880) ∨ (¬ p4506) ∨ (¬ p3737) ∨ (¬ p4109) ∨ (¬ p5586) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4506) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial35403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory24659 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 8)
  exact rule35403 (meaning t m 2027) (meaning t m 2156) (meaning t m 3737) (meaning t m 3880) (meaning t m 4109) (meaning t m 4506) (meaning t m 5586) source

theorem rule35404 (p2027 p2341 p2459 p3919 p4118 p4854 : Prop) (h : (¬ p4854) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4854) := by
  classical
  tauto

theorem initial35404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4854)) := by
  have source := ElevenTheory.theory24660 t (m.theta 0 7) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35404 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 3919) (meaning t m 4118) (meaning t m 4854) source

theorem rule35417 (p2027 p2088 p2249 p2641 p2657 p2928 p3487 p3567 p3644 p4114 p4133 p4347 : Prop) (h : (¬ p4114) ∨ (¬ p3644) ∨ (¬ p2641) ∨ (¬ p4133) ∨ (¬ p2928) ∨ (¬ p2088) ∨ (¬ p3567) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p3487) ∨ (¬ p2657) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p3567) ∨ (¬ p3644) ∨ (¬ p4114) ∨ (¬ p4133) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial35417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory24673 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35417 (meaning t m 2027) (meaning t m 2088) (meaning t m 2249) (meaning t m 2641) (meaning t m 2657) (meaning t m 2928) (meaning t m 3487) (meaning t m 3567) (meaning t m 3644) (meaning t m 4114) (meaning t m 4133) (meaning t m 4347) source

theorem rule35422 (p2027 p2299 p2341 p2417 p3821 p4712 : Prop) (h : (¬ p2417) ∨ (¬ p4712) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial35422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory24678 t (m.theta 0 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35422 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2417) (meaning t m 3821) (meaning t m 4712) source

theorem rule35429 (p2027 p2191 p2753 p3166 p3256 p3379 p3555 p4117 p4134 p4347 p5216 : Prop) (h : (¬ p4134) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p4347) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4117) ∨ (¬ p3555) ∨ (¬ p2753) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4117) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial35429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory24685 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule35429 (meaning t m 2027) (meaning t m 2191) (meaning t m 2753) (meaning t m 3166) (meaning t m 3256) (meaning t m 3379) (meaning t m 3555) (meaning t m 4117) (meaning t m 4134) (meaning t m 4347) (meaning t m 5216) source

theorem rule35435 (p1988 p2027 p2202 p2563 p3115 p3680 p3952 : Prop) (h : (¬ p3952) ∨ (¬ p3680) ∨ p2202 ∨ p2027 ∨ (¬ p2563) ∨ (¬ p3115) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial35435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory24691 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule35435 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3115) (meaning t m 3680) (meaning t m 3952) source

theorem rule35437 (p2027 p2132 p2753 p2870 p2881 p2927 p3379 p4278 p4366 p4666 p5216 : Prop) (h : (¬ p2870) ∨ (¬ p2927) ∨ (¬ p2132) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p2881) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial35437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory24693 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35437 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2870) (meaning t m 2881) (meaning t m 2927) (meaning t m 3379) (meaning t m 4278) (meaning t m 4366) (meaning t m 4666) (meaning t m 5216) source

theorem rule35441 (p2027 p2295 p2313 p2630 p3361 p3983 p4972 : Prop) (h : p2027 ∨ (¬ p4972) ∨ (¬ p3361) ∨ (¬ p2313) ∨ (¬ p2295) ∨ (¬ p3983) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p3361) ∨ (¬ p3983) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial35441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory24697 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule35441 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2630) (meaning t m 3361) (meaning t m 3983) (meaning t m 4972) source

theorem rule35442 (p2027 p2295 p2727 p3549 p4245 p4972 : Prop) (h : (¬ p2727) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p4245) ∨ (¬ p4972) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial35442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory24698 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule35442 (meaning t m 2027) (meaning t m 2295) (meaning t m 2727) (meaning t m 3549) (meaning t m 4245) (meaning t m 4972) source

theorem rule35443 (p2027 p2727 p3323 p4026 p4245 p4972 : Prop) (h : p2027 ∨ (¬ p4972) ∨ (¬ p4245) ∨ (¬ p3323) ∨ (¬ p2727) ∨ (¬ p4026)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4245) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial35443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory24699 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9)
  exact rule35443 (meaning t m 2027) (meaning t m 2727) (meaning t m 3323) (meaning t m 4026) (meaning t m 4245) (meaning t m 4972) source

theorem rule35445 (p1984 p2027 p2114 p2829 p3238 p3452 p3461 p3483 p4444 p4948 p5059 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p2829) ∨ p2114 ∨ (¬ p3461) ∨ (¬ p5059) ∨ (¬ p3483) ∨ (¬ p4444)) : (¬ p1984) ∨ (p2027) ∨ (p2114) ∨ (¬ p2829) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial35445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory24701 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35445 (meaning t m 1984) (meaning t m 2027) (meaning t m 2114) (meaning t m 2829) (meaning t m 3238) (meaning t m 3452) (meaning t m 3461) (meaning t m 3483) (meaning t m 4444) (meaning t m 4948) (meaning t m 5059) source

theorem rule35449 (p2027 p2497 p3389 p3519 p3660 p3888 p4435 p4646 : Prop) (h : (¬ p4435) ∨ (¬ p3519) ∨ (¬ p2497) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3888) ∨ (¬ p4646) ∨ (¬ p3660)) : (p2027) ∨ (¬ p2497) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4435) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial35449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory24705 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule35449 (meaning t m 2027) (meaning t m 2497) (meaning t m 3389) (meaning t m 3519) (meaning t m 3660) (meaning t m 3888) (meaning t m 4435) (meaning t m 4646) source

theorem rule35450 (p2027 p2248 p2499 p2901 p2946 p3246 p3452 p4137 p4625 : Prop) (h : (¬ p2499) ∨ (¬ p2901) ∨ (¬ p4137) ∨ (¬ p3452) ∨ (¬ p2248) ∨ (¬ p4625) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2946)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial35450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory24706 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule35450 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3452) (meaning t m 4137) (meaning t m 4625) source

theorem rule35452 (p2027 p2850 p2927 p3379 p4030 p4366 p4644 : Prop) (h : (¬ p2927) ∨ (¬ p4030) ∨ (¬ p4366) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4644)) : (p2027) ∨ (¬ p2850) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4030) ∨ (¬ p4366) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial35452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory24708 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule35452 (meaning t m 2027) (meaning t m 2850) (meaning t m 2927) (meaning t m 3379) (meaning t m 4030) (meaning t m 4366) (meaning t m 4644) source

theorem rule35453 (p2027 p2104 p2246 p2264 p2363 p2598 p2742 p2807 p3550 p4752 p5118 p5612 : Prop) (h : (¬ p4752) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p2246) ∨ (¬ p5612) ∨ (¬ p5118) ∨ (¬ p2742) ∨ (¬ p2598) ∨ (¬ p2104) ∨ p3550) : (p2027) ∨ (¬ p2104) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2807) ∨ (p3550) ∨ (¬ p4752) ∨ (¬ p5118) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial35453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2807)) ∨ (meaning t m 3550) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory24709 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule35453 (meaning t m 2027) (meaning t m 2104) (meaning t m 2246) (meaning t m 2264) (meaning t m 2363) (meaning t m 2598) (meaning t m 2742) (meaning t m 2807) (meaning t m 3550) (meaning t m 4752) (meaning t m 5118) (meaning t m 5612) source

theorem rule35454 (p1988 p2027 p2589 p2662 p2842 p2850 p3276 p3343 : Prop) (h : (¬ p2662) ∨ (¬ p1988) ∨ (¬ p2589) ∨ (¬ p3276) ∨ p2842 ∨ p2027 ∨ (¬ p3343) ∨ (¬ p2850)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p3276) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial35454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory24710 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule35454 (meaning t m 1988) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2842) (meaning t m 2850) (meaning t m 3276) (meaning t m 3343) source

theorem rule35455 (p2027 p2313 p3212 p3309 p3957 p4198 p5046 : Prop) (h : (¬ p3212) ∨ p2027 ∨ (¬ p5046) ∨ (¬ p4198) ∨ (¬ p3957) ∨ (¬ p2313) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3212) ∨ (¬ p3309) ∨ (¬ p3957) ∨ (¬ p4198) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial35455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory24711 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule35455 (meaning t m 2027) (meaning t m 2313) (meaning t m 3212) (meaning t m 3309) (meaning t m 3957) (meaning t m 4198) (meaning t m 5046) source

theorem rule35461 (p2761 p3680 p4135 : Prop) (h : (¬ p2761) ∨ (¬ p4135) ∨ p3680) : (¬ p2761) ∨ (p3680) ∨ (¬ p4135) := by
  classical
  tauto

theorem initial35461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2761)) ∨ (meaning t m 3680) ∨ (¬ (meaning t m 4135)) := by
  have source := ElevenTheory.theory24717 (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule35461 (meaning t m 2761) (meaning t m 3680) (meaning t m 4135) source

theorem rule35465 (p3553 p3659 p4777 : Prop) (h : (¬ p4777) ∨ (¬ p3553) ∨ p3659) : (¬ p3553) ∨ (p3659) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial35465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3553)) ∨ (meaning t m 3659) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory24721 (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule35465 (meaning t m 3553) (meaning t m 3659) (meaning t m 4777) source

theorem rule35468 (p1994 p2027 p2230 p2440 p2579 p3128 p4137 : Prop) (h : (¬ p1994) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p4137) ∨ (¬ p2440) ∨ p3128 ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (p3128) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial35468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory24724 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule35468 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2579) (meaning t m 3128) (meaning t m 4137) source

theorem rule35473 (p2027 p2191 p2248 p2531 p2534 p3286 p3452 p3506 p3950 p4202 p4381 : Prop) (h : (¬ p3950) ∨ (¬ p4381) ∨ (¬ p3452) ∨ (¬ p2531) ∨ (¬ p2534) ∨ (¬ p2248) ∨ (¬ p2191) ∨ (¬ p3286) ∨ p2027 ∨ (¬ p4202) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2531) ∨ (¬ p2534) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p3950) ∨ (¬ p4202) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial35473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory24729 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 9) (m.theta 4 8) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35473 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2531) (meaning t m 2534) (meaning t m 3286) (meaning t m 3452) (meaning t m 3506) (meaning t m 3950) (meaning t m 4202) (meaning t m 4381) source

theorem rule35478 (p1981 p2027 p2202 p2427 p2819 p3707 p4337 p4909 p5274 p5284 p5363 : Prop) (h : (¬ p1981) ∨ (¬ p5274) ∨ p2027 ∨ (¬ p4337) ∨ p2202 ∨ (¬ p2819) ∨ (¬ p5284) ∨ (¬ p4909) ∨ (¬ p5363) ∨ (¬ p2427) ∨ (¬ p3707)) : (¬ p1981) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2819) ∨ (¬ p3707) ∨ (¬ p4337) ∨ (¬ p4909) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial35478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4909)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory24734 t (m.theta 1 7) (m.theta 1 9) (m.theta 2 6) (m.theta 3 6) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 9 10)
  exact rule35478 (meaning t m 1981) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2819) (meaning t m 3707) (meaning t m 4337) (meaning t m 4909) (meaning t m 5274) (meaning t m 5284) (meaning t m 5363) source

theorem rule35479 (p2027 p2144 p2630 p2742 p2957 p3425 p3662 p4650 p4777 : Prop) (h : (¬ p4650) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p4777) ∨ (¬ p2630) ∨ p2742 ∨ (¬ p2144) ∨ (¬ p3662) ∨ (¬ p2957)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2630) ∨ (p2742) ∨ (¬ p2957) ∨ (¬ p3425) ∨ (¬ p3662) ∨ (¬ p4650) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial35479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2742) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory24735 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule35479 (meaning t m 2027) (meaning t m 2144) (meaning t m 2630) (meaning t m 2742) (meaning t m 2957) (meaning t m 3425) (meaning t m 3662) (meaning t m 4650) (meaning t m 4777) source

theorem rule35480 (p2027 p2138 p2246 p2598 p2742 p3286 p3506 p3951 p4381 p4385 p4752 : Prop) (h : (¬ p4385) ∨ (¬ p4752) ∨ (¬ p2246) ∨ (¬ p4381) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3506) ∨ (¬ p3286) ∨ (¬ p3951)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3951) ∨ (¬ p4381) ∨ (¬ p4385) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial35480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory24736 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 3 9) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule35480 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2598) (meaning t m 2742) (meaning t m 3286) (meaning t m 3506) (meaning t m 3951) (meaning t m 4381) (meaning t m 4385) (meaning t m 4752) source

theorem rule35482 (p1988 p2027 p2373 p2938 p3146 p3266 p4235 : Prop) (h : (¬ p2373) ∨ (¬ p4235) ∨ (¬ p3146) ∨ (¬ p1988) ∨ p2027 ∨ p2938 ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2373) ∨ (p2938) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial35482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory24738 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule35482 (meaning t m 1988) (meaning t m 2027) (meaning t m 2373) (meaning t m 2938) (meaning t m 3146) (meaning t m 3266) (meaning t m 4235) source

theorem rule35486 (p2027 p2373 p3553 p4042 p4235 p4280 : Prop) (h : p2027 ∨ (¬ p4280) ∨ (¬ p3553) ∨ (¬ p2373) ∨ (¬ p4235) ∨ (¬ p4042)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3553) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p4280) := by
  classical
  tauto

theorem initial35486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4280)) := by
  have source := ElevenTheory.theory24742 t (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule35486 (meaning t m 2027) (meaning t m 2373) (meaning t m 3553) (meaning t m 4042) (meaning t m 4235) (meaning t m 4280) source

theorem rule35487 (p1982 p2027 p2388 p2619 p2901 p3146 p4244 : Prop) (h : (¬ p2901) ∨ p2388 ∨ (¬ p1982) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p4244)) : (¬ p1982) ∨ (p2027) ∨ (p2388) ∨ (¬ p2619) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial35487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory24743 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule35487 (meaning t m 1982) (meaning t m 2027) (meaning t m 2388) (meaning t m 2619) (meaning t m 2901) (meaning t m 3146) (meaning t m 4244) source

theorem rule35491 (p2027 p2088 p2630 p2951 p4238 p4340 p4364 p4701 : Prop) (h : (¬ p2630) ∨ (¬ p4238) ∨ (¬ p4701) ∨ (¬ p2951) ∨ (¬ p2088) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p4364)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p4238) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial35491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory24747 t (m.theta 0 5) (m.theta 0 8) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 5) (m.theta 8 9)
  exact rule35491 (meaning t m 2027) (meaning t m 2088) (meaning t m 2630) (meaning t m 2951) (meaning t m 4238) (meaning t m 4340) (meaning t m 4364) (meaning t m 4701) source

theorem rule35493 (p1987 p2027 p2651 p2810 p2963 p2997 p3568 : Prop) (h : (¬ p2651) ∨ p2027 ∨ p2997 ∨ (¬ p3568) ∨ (¬ p2963) ∨ (¬ p2810) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial35493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory24749 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule35493 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2810) (meaning t m 2963) (meaning t m 2997) (meaning t m 3568) source

theorem rule35494 (p2027 p2651 p2737 p2811 p3588 p4650 p4777 : Prop) (h : (¬ p2811) ∨ (¬ p2651) ∨ (¬ p3588) ∨ (¬ p2737) ∨ (¬ p4650) ∨ (¬ p4777) ∨ p2027) : (p2027) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3588) ∨ (¬ p4650) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial35494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory24750 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule35494 (meaning t m 2027) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 3588) (meaning t m 4650) (meaning t m 4777) source

theorem rule35498 (p1987 p2027 p2588 p2651 p2810 p2963 p2997 p4389 : Prop) (h : (¬ p2651) ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p4389) ∨ p2997 ∨ (¬ p2963)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial35498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory24754 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule35498 (meaning t m 1987) (meaning t m 2027) (meaning t m 2588) (meaning t m 2651) (meaning t m 2810) (meaning t m 2963) (meaning t m 2997) (meaning t m 4389) source

theorem rule35499 (p2027 p2341 p2589 p2922 p3097 p3553 p3575 p4173 p4210 p4570 p5191 : Prop) (h : (¬ p3553) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3097) ∨ (¬ p5191) ∨ (¬ p4210) ∨ (¬ p4570) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3097) ∨ (¬ p3553) ∨ (¬ p3575) ∨ (¬ p4173) ∨ (¬ p4210) ∨ (¬ p4570) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial35499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory24755 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 1 5) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35499 (meaning t m 2027) (meaning t m 2341) (meaning t m 2589) (meaning t m 2922) (meaning t m 3097) (meaning t m 3553) (meaning t m 3575) (meaning t m 4173) (meaning t m 4210) (meaning t m 4570) (meaning t m 5191) source

theorem rule35504 (p2027 p3319 p3692 p3923 p4433 p4460 p5379 : Prop) (h : (¬ p3319) ∨ (¬ p4433) ∨ (¬ p5379) ∨ (¬ p3923) ∨ (¬ p4460) ∨ (¬ p3692) ∨ p2027) : (p2027) ∨ (¬ p3319) ∨ (¬ p3692) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p4460) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial35504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4460)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory24760 t (m.theta 0 9) (m.theta 1 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule35504 (meaning t m 2027) (meaning t m 3319) (meaning t m 3692) (meaning t m 3923) (meaning t m 4433) (meaning t m 4460) (meaning t m 5379) source

theorem rule35505 (p2027 p2319 p2352 p2387 p3660 p4283 p4320 p4702 : Prop) (h : (¬ p2319) ∨ (¬ p3660) ∨ (¬ p4320) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p4702) ∨ p2027 ∨ (¬ p4283)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3660) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial35505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory24761 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8)
  exact rule35505 (meaning t m 2027) (meaning t m 2319) (meaning t m 2352) (meaning t m 2387) (meaning t m 3660) (meaning t m 4283) (meaning t m 4320) (meaning t m 4702) source

theorem rule35510 (p2027 p2373 p2533 p3680 p3773 p4380 p4533 : Prop) (h : p2027 ∨ (¬ p4533) ∨ (¬ p2373) ∨ (¬ p4380) ∨ (¬ p3680) ∨ (¬ p2533) ∨ (¬ p3773)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p4380) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial35510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4380)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory24766 t (m.theta 0 5) (m.theta 0 9) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 9 10)
  exact rule35510 (meaning t m 2027) (meaning t m 2373) (meaning t m 2533) (meaning t m 3680) (meaning t m 3773) (meaning t m 4380) (meaning t m 4533) source

theorem rule35513 (p1991 p2027 p2202 p2427 p2952 p2992 p2996 p3699 : Prop) (h : p2202 ∨ (¬ p2952) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p1991) ∨ (¬ p3699) ∨ (¬ p2996)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial35513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory24769 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule35513 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2952) (meaning t m 2992) (meaning t m 2996) (meaning t m 3699) source

theorem rule35514 (p2027 p2132 p2493 p2509 p2579 p2870 p2881 p4108 p4438 p4733 : Prop) (h : (¬ p2132) ∨ (¬ p2881) ∨ (¬ p2579) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p4438) ∨ (¬ p4733) ∨ (¬ p4108) ∨ (¬ p2493) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4108) ∨ (¬ p4438) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial35514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory24770 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule35514 (meaning t m 2027) (meaning t m 2132) (meaning t m 2493) (meaning t m 2509) (meaning t m 2579) (meaning t m 2870) (meaning t m 2881) (meaning t m 4108) (meaning t m 4438) (meaning t m 4733) source

theorem rule35519 (p2027 p2249 p2499 p2657 p3487 p3506 p3842 p4137 p4444 p4604 : Prop) (h : (¬ p2499) ∨ (¬ p4137) ∨ (¬ p3487) ∨ (¬ p2657) ∨ (¬ p3506) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p4444) ∨ (¬ p3842)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial35519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory24775 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35519 (meaning t m 2027) (meaning t m 2249) (meaning t m 2499) (meaning t m 2657) (meaning t m 3487) (meaning t m 3506) (meaning t m 3842) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) source

theorem rule35524 (p2027 p2341 p2499 p3434 p3452 p3659 p3819 p4137 p4625 p4733 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2499) ∨ (¬ p3434) ∨ (¬ p4625) ∨ (¬ p4733) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2499) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial35524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory24780 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule35524 (meaning t m 2027) (meaning t m 2341) (meaning t m 2499) (meaning t m 3434) (meaning t m 3452) (meaning t m 3659) (meaning t m 3819) (meaning t m 4137) (meaning t m 4625) (meaning t m 4733) source

theorem rule35531 (p2499 p2641 p3402 p3984 : Prop) (h : (¬ p3402) ∨ (¬ p3984) ∨ (¬ p2499) ∨ (¬ p2641)) : (¬ p2499) ∨ (¬ p2641) ∨ (¬ p3402) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial35531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory24787 (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6)
  exact rule35531 (meaning t m 2499) (meaning t m 2641) (meaning t m 3402) (meaning t m 3984) source

theorem rule35533 (p2027 p2313 p3309 p3361 p3583 p3983 p4869 p5049 : Prop) (h : (¬ p3983) ∨ p2027 ∨ (¬ p4869) ∨ (¬ p5049) ∨ (¬ p3583) ∨ (¬ p3309) ∨ (¬ p2313) ∨ (¬ p3361)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3583) ∨ (¬ p3983) ∨ (¬ p4869) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial35533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory24789 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 7)
  exact rule35533 (meaning t m 2027) (meaning t m 2313) (meaning t m 3309) (meaning t m 3361) (meaning t m 3583) (meaning t m 3983) (meaning t m 4869) (meaning t m 5049) source

theorem rule35535 (p2027 p2341 p2459 p2707 p2748 p3365 p3577 p4037 p4154 p4604 p4734 : Prop) (h : (¬ p3365) ∨ (¬ p2748) ∨ (¬ p2707) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p4037) ∨ (¬ p3577) ∨ (¬ p4154) ∨ (¬ p2459) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3577) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial35535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory24791 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule35535 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2707) (meaning t m 2748) (meaning t m 3365) (meaning t m 3577) (meaning t m 4037) (meaning t m 4154) (meaning t m 4604) (meaning t m 4734) source

theorem rule35538 (p2510 p2534 p3984 p4037 p4171 : Prop) (h : (¬ p4037) ∨ (¬ p3984) ∨ (¬ p4171) ∨ (¬ p2510) ∨ p2534) : (¬ p2510) ∨ (p2534) ∨ (¬ p3984) ∨ (¬ p4037) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial35538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (meaning t m 2534) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory24794 (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule35538 (meaning t m 2510) (meaning t m 2534) (meaning t m 3984) (meaning t m 4037) (meaning t m 4171) source

theorem rule35545 (p1984 p2027 p2245 p2657 p2727 p3128 p4037 p4154 : Prop) (h : (¬ p1984) ∨ (¬ p4154) ∨ (¬ p2727) ∨ p3128 ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2245) ∨ (¬ p4037)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (p3128) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial35545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory24801 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9)
  exact rule35545 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 3128) (meaning t m 4037) (meaning t m 4154) source

theorem rule35546 (p3193 p3359 p3487 : Prop) (h : (¬ p3487) ∨ (¬ p3193) ∨ p3359) : (¬ p3193) ∨ (p3359) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial35546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3193)) ∨ (meaning t m 3359) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory24802 (m.theta 1 4) (m.theta 3 4) (m.theta 4 9)
  exact rule35546 (meaning t m 3193) (meaning t m 3359) (meaning t m 3487) source

theorem rule35549 (p2498 p2553 p3309 : Prop) (h : (¬ p2498) ∨ (¬ p3309) ∨ p2553) : (¬ p2498) ∨ (p2553) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial35549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (meaning t m 2553) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory24805 (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule35549 (meaning t m 2498) (meaning t m 2553) (meaning t m 3309) source

theorem rule35557 (p3693 p4132 p4383 : Prop) (h : (¬ p4132) ∨ (¬ p3693) ∨ p4383) : (¬ p3693) ∨ (¬ p4132) ∨ (p4383) := by
  classical
  tauto

theorem initial35557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4132)) ∨ (meaning t m 4383) := by
  have source := ElevenTheory.theory24813 (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule35557 (meaning t m 3693) (meaning t m 4132) (meaning t m 4383) source

theorem rule35558 (p2027 p2437 p3564 p3660 p4037 p4194 p4646 : Prop) (h : p2027 ∨ (¬ p4646) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p3660) ∨ (¬ p3564) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial35558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory24814 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule35558 (meaning t m 2027) (meaning t m 2437) (meaning t m 3564) (meaning t m 3660) (meaning t m 4037) (meaning t m 4194) (meaning t m 4646) source

theorem rule35565 (p1982 p2027 p2622 p2797 p3461 p3567 p3654 p4444 : Prop) (h : (¬ p3654) ∨ (¬ p1982) ∨ (¬ p3461) ∨ (¬ p3567) ∨ p2027 ∨ p2622 ∨ (¬ p2797) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3461) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial35565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory24821 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35565 (meaning t m 1982) (meaning t m 2027) (meaning t m 2622) (meaning t m 2797) (meaning t m 3461) (meaning t m 3567) (meaning t m 3654) (meaning t m 4444) source

theorem rule35569 (p2027 p2252 p2750 p2952 p3063 p3093 p3097 p3952 p3954 p4405 : Prop) (h : (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3063) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4405) ∨ (¬ p2252) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial35569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory24825 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule35569 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3063) (meaning t m 3093) (meaning t m 3097) (meaning t m 3952) (meaning t m 3954) (meaning t m 4405) source

theorem rule35582 (p2027 p2252 p2264 p2750 p3093 p3319 p3551 p3947 p3954 p4621 p4849 : Prop) (h : (¬ p4621) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3954) ∨ (¬ p2264) ∨ (¬ p3947) ∨ (¬ p2252) ∨ (¬ p3551) ∨ (¬ p4849)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2264) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3551) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4621) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial35582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory24838 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule35582 (meaning t m 2027) (meaning t m 2252) (meaning t m 2264) (meaning t m 2750) (meaning t m 3093) (meaning t m 3319) (meaning t m 3551) (meaning t m 3947) (meaning t m 3954) (meaning t m 4621) (meaning t m 4849) source

theorem rule35586 (p2027 p2542 p2662 p3276 p3773 p4949 p5181 : Prop) (h : (¬ p2542) ∨ (¬ p4949) ∨ (¬ p5181) ∨ (¬ p2662) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p3773)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2662) ∨ (¬ p3276) ∨ (¬ p3773) ∨ (¬ p4949) ∨ (¬ p5181) := by
  classical
  tauto

theorem initial35586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4949)) ∨ (¬ (meaning t m 5181)) := by
  have source := ElevenTheory.theory24842 t (m.theta 0 4) (m.theta 0 9) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule35586 (meaning t m 2027) (meaning t m 2542) (meaning t m 2662) (meaning t m 3276) (meaning t m 3773) (meaning t m 4949) (meaning t m 5181) source

theorem rule35588 (p2027 p2577 p3389 p3564 p3946 p4711 : Prop) (h : (¬ p2577) ∨ p2027 ∨ (¬ p4711) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3946)) : (p2027) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial35588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory24844 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule35588 (meaning t m 2027) (meaning t m 2577) (meaning t m 3389) (meaning t m 3564) (meaning t m 3946) (meaning t m 4711) source

theorem rule35589 (p1990 p2027 p2295 p3008 p3097 p3564 p4037 : Prop) (h : (¬ p3564) ∨ p3008 ∨ (¬ p2295) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (p3008) ∨ (¬ p3097) ∨ (¬ p3564) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial35589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory24845 t (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule35589 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 3008) (meaning t m 3097) (meaning t m 3564) (meaning t m 4037) source

theorem rule35591 (p2027 p2960 p2962 p3654 p3744 p3952 : Prop) (h : p2027 ∨ (¬ p3952) ∨ (¬ p2962) ∨ (¬ p2960) ∨ (¬ p3654) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial35591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory24847 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9)
  exact rule35591 (meaning t m 2027) (meaning t m 2960) (meaning t m 2962) (meaning t m 3654) (meaning t m 3744) (meaning t m 3952) source

theorem rule35592 (p2027 p2589 p2922 p3347 p3569 p4320 p4702 : Prop) (h : p2027 ∨ (¬ p4702) ∨ (¬ p2589) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p2922) ∨ (¬ p3347)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial35592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory24848 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule35592 (meaning t m 2027) (meaning t m 2589) (meaning t m 2922) (meaning t m 3347) (meaning t m 3569) (meaning t m 4320) (meaning t m 4702) source

theorem rule35595 (p2406 p3193 p4449 : Prop) (h : (¬ p3193) ∨ (¬ p2406) ∨ (¬ p4449)) : (¬ p2406) ∨ (¬ p3193) ∨ (¬ p4449) := by
  classical
  tauto

theorem initial35595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4449)) := by
  have source := ElevenTheory.theory24851 (m.theta 1 4) (m.theta 4 5) (m.theta 4 9)
  exact rule35595 (meaning t m 2406) (meaning t m 3193) (meaning t m 4449) source

theorem rule35596 (p2027 p2498 p2542 p3319 p4037 p4194 p4715 : Prop) (h : (¬ p4715) ∨ p2027 ∨ (¬ p4194) ∨ (¬ p3319) ∨ (¬ p2498) ∨ (¬ p4037) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2498) ∨ (¬ p2542) ∨ (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial35596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory24852 t (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule35596 (meaning t m 2027) (meaning t m 2498) (meaning t m 2542) (meaning t m 3319) (meaning t m 4037) (meaning t m 4194) (meaning t m 4715) source

theorem rule35597 (p3319 p4037 p4319 : Prop) (h : (¬ p4037) ∨ (¬ p3319) ∨ (¬ p4319)) : (¬ p3319) ∨ (¬ p4037) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial35597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory24853 (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule35597 (meaning t m 3319) (meaning t m 4037) (meaning t m 4319) source

theorem rule35600 (p2027 p2406 p2427 p2499 p3096 p4558 : Prop) (h : (¬ p3096) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial35600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory24856 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule35600 (meaning t m 2027) (meaning t m 2406) (meaning t m 2427) (meaning t m 2499) (meaning t m 3096) (meaning t m 4558) source

theorem rule35605 (p2027 p2499 p2891 p3948 p4235 p4715 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p4235) ∨ (¬ p3948) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial35605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory24861 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule35605 (meaning t m 2027) (meaning t m 2499) (meaning t m 2891) (meaning t m 3948) (meaning t m 4235) (meaning t m 4715) source

theorem rule35607 (p2020 p2027 p2088 p2409 p2922 p3575 p3941 p4348 p4590 : Prop) (h : (¬ p2088) ∨ (¬ p2020) ∨ (¬ p3575) ∨ (¬ p4348) ∨ (¬ p2922) ∨ (¬ p4590) ∨ p2027 ∨ p2409 ∨ (¬ p3941)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2088) ∨ (p2409) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial35607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory24863 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule35607 (meaning t m 2020) (meaning t m 2027) (meaning t m 2088) (meaning t m 2409) (meaning t m 2922) (meaning t m 3575) (meaning t m 3941) (meaning t m 4348) (meaning t m 4590) source

theorem rule35611 (p2027 p2210 p2922 p3540 p4108 p4281 p4959 : Prop) (h : (¬ p3540) ∨ p2027 ∨ (¬ p4281) ∨ (¬ p2922) ∨ (¬ p4959) ∨ (¬ p4108) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4281) ∨ (¬ p4959) := by
  classical
  tauto

theorem initial35611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4959)) := by
  have source := ElevenTheory.theory24867 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7)
  exact rule35611 (meaning t m 2027) (meaning t m 2210) (meaning t m 2922) (meaning t m 3540) (meaning t m 4108) (meaning t m 4281) (meaning t m 4959) source

theorem rule35620 (p2010 p2027 p2497 p2622 p2797 p2922 p3567 p3654 p4026 : Prop) (h : (¬ p4026) ∨ (¬ p2010) ∨ p2622 ∨ (¬ p2797) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p2497) ∨ (¬ p3654) ∨ (¬ p2922)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2497) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p2922) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial35620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory24876 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9)
  exact rule35620 (meaning t m 2010) (meaning t m 2027) (meaning t m 2497) (meaning t m 2622) (meaning t m 2797) (meaning t m 2922) (meaning t m 3567) (meaning t m 3654) (meaning t m 4026) source

theorem rule35621 (p2027 p2252 p2750 p2952 p3093 p3309 p3952 p3954 p3989 p4501 : Prop) (h : (¬ p4501) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2252) ∨ (¬ p3954) ∨ (¬ p2750) ∨ (¬ p3989) ∨ (¬ p3952) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial35621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory24877 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule35621 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3093) (meaning t m 3309) (meaning t m 3952) (meaning t m 3954) (meaning t m 3989) (meaning t m 4501) source

theorem rule35625 (p3204 p4356 p4516 : Prop) (h : (¬ p4516) ∨ (¬ p3204) ∨ p4356) : (¬ p3204) ∨ (p4356) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial35625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3204)) ∨ (meaning t m 4356) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory24881 (m.theta 0 6) (m.theta 1 6) (m.theta 5 6)
  exact rule35625 (meaning t m 3204) (meaning t m 4356) (meaning t m 4516) source

theorem rule35628 (p3333 p3422 p3746 : Prop) (h : (¬ p3333) ∨ (¬ p3746) ∨ p3422) : (¬ p3333) ∨ (p3422) ∨ (¬ p3746) := by
  classical
  tauto

theorem initial35628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3333)) ∨ (meaning t m 3422) ∨ (¬ (meaning t m 3746)) := by
  have source := ElevenTheory.theory24884 (m.theta 2 4) (m.theta 4 6) (m.theta 4 9)
  exact rule35628 (meaning t m 3333) (meaning t m 3422) (meaning t m 3746) source

theorem rule35654 (p2027 p2440 p3016 p3958 p4110 : Prop) (h : (¬ p3016) ∨ (¬ p2440) ∨ (¬ p3958) ∨ p2027 ∨ (¬ p4110)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial35654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory24910 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule35654 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 3958) (meaning t m 4110) source

theorem rule35656 (p2027 p2440 p3016 p4173 p4203 p4629 : Prop) (h : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p4629) ∨ p2027 ∨ (¬ p4173)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4173) ∨ (¬ p4203) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial35656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory24912 t (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule35656 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 4173) (meaning t m 4203) (meaning t m 4629) source

theorem rule35663 (p2138 p2210 p3873 p4243 : Prop) (h : (¬ p3873) ∨ (¬ p2138) ∨ (¬ p2210) ∨ (¬ p4243)) : (¬ p2138) ∨ (¬ p2210) ∨ (¬ p3873) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial35663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory24919 (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 5)
  exact rule35663 (meaning t m 2138) (meaning t m 2210) (meaning t m 3873) (meaning t m 4243) source

theorem rule35668 (p2027 p2363 p2534 p2579 p3347 p3399 p3527 p3573 p3954 p4503 p5216 : Prop) (h : (¬ p3399) ∨ (¬ p4503) ∨ (¬ p2363) ∨ (¬ p5216) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p3573) ∨ (¬ p3527) ∨ (¬ p2579) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3573) ∨ (¬ p3954) ∨ (¬ p4503) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial35668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory24924 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35668 (meaning t m 2027) (meaning t m 2363) (meaning t m 2534) (meaning t m 2579) (meaning t m 3347) (meaning t m 3399) (meaning t m 3527) (meaning t m 3573) (meaning t m 3954) (meaning t m 4503) (meaning t m 5216) source

theorem rule35669 (p2027 p2088 p4066 p4348 p4391 p4590 p5559 : Prop) (h : (¬ p5559) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p4391) ∨ (¬ p4590) ∨ (¬ p4348) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p4066) ∨ (¬ p4348) ∨ (¬ p4391) ∨ (¬ p4590) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial35669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory24925 t (m.theta 0 7) (m.theta 0 8) (m.theta 3 7) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule35669 (meaning t m 2027) (meaning t m 2088) (meaning t m 4066) (meaning t m 4348) (meaning t m 4391) (meaning t m 4590) (meaning t m 5559) source

theorem rule35670 (p2027 p2241 p2579 p2641 p3125 p3347 p3954 p4137 p4564 p5216 : Prop) (h : (¬ p4564) ∨ (¬ p2641) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p5216) ∨ (¬ p2241) ∨ (¬ p3347) ∨ (¬ p4137) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p3125) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4564) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial35670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory24926 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule35670 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 2641) (meaning t m 3125) (meaning t m 3347) (meaning t m 3954) (meaning t m 4137) (meaning t m 4564) (meaning t m 5216) source

theorem rule35676 (p2027 p2299 p3097 p3399 p3631 p3645 p3646 p3954 p4668 p4877 : Prop) (h : (¬ p4877) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3097) ∨ (¬ p2299) ∨ (¬ p3631) ∨ (¬ p4668) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial35676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory24932 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35676 (meaning t m 2027) (meaning t m 2299) (meaning t m 3097) (meaning t m 3399) (meaning t m 3631) (meaning t m 3645) (meaning t m 3646) (meaning t m 3954) (meaning t m 4668) (meaning t m 4877) source

theorem rule35678 (p2027 p2156 p3954 p4172 p4173 p4877 : Prop) (h : (¬ p4172) ∨ (¬ p3954) ∨ (¬ p4173) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4877)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial35678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory24934 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6)
  exact rule35678 (meaning t m 2027) (meaning t m 2156) (meaning t m 3954) (meaning t m 4172) (meaning t m 4173) (meaning t m 4877) source

theorem rule35680 (p3226 p3399 p3452 p5363 : Prop) (h : (¬ p3452) ∨ (¬ p5363) ∨ (¬ p3399) ∨ (¬ p3226)) : (¬ p3226) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial35680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3226)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory24936 (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 1 9)
  exact rule35680 (meaning t m 3226) (meaning t m 3399) (meaning t m 3452) (meaning t m 5363) source

theorem rule35683 (p2352 p2504 p3923 : Prop) (h : (¬ p2504) ∨ (¬ p3923) ∨ (¬ p2352)) : (¬ p2352) ∨ (¬ p2504) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial35683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory24939 (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule35683 (meaning t m 2352) (meaning t m 2504) (meaning t m 3923) source

theorem rule35696 (p2027 p2532 p3115 p3497 p3857 p4529 : Prop) (h : p2027 ∨ (¬ p4529) ∨ (¬ p3857) ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3857) ∨ (¬ p4529) := by
  classical
  tauto

theorem initial35696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4529)) := by
  have source := ElevenTheory.theory24952 t (m.theta 0 8) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule35696 (meaning t m 2027) (meaning t m 2532) (meaning t m 3115) (meaning t m 3497) (meaning t m 3857) (meaning t m 4529) source

theorem rule35697 (p2003 p2027 p2387 p2668 p2764 p4037 p4191 : Prop) (h : (¬ p2003) ∨ (¬ p2668) ∨ p2027 ∨ p2764 ∨ (¬ p2387) ∨ (¬ p4037) ∨ (¬ p4191)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (p2764) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial35697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory24953 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule35697 (meaning t m 2003) (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2764) (meaning t m 4037) (meaning t m 4191) source

theorem rule35707 (p2027 p2387 p2581 p3083 p3574 p4157 : Prop) (h : (¬ p3574) ∨ p2027 ∨ (¬ p4157) ∨ (¬ p2581) ∨ (¬ p2387) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2581) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial35707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2581)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory24963 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule35707 (meaning t m 2027) (meaning t m 2387) (meaning t m 2581) (meaning t m 3083) (meaning t m 3574) (meaning t m 4157) source

theorem rule35708 (p2027 p2252 p2542 p2589 p2655 p2750 p3063 p3093 p3693 p3954 p4134 p4256 : Prop) (h : (¬ p3693) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p3093) ∨ (¬ p4256) ∨ (¬ p3063) ∨ (¬ p3954) ∨ (¬ p4134) ∨ (¬ p2750) ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p2655)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3693) ∨ (¬ p3954) ∨ (¬ p4134) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial35708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory24964 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8)
  exact rule35708 (meaning t m 2027) (meaning t m 2252) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2750) (meaning t m 3063) (meaning t m 3093) (meaning t m 3693) (meaning t m 3954) (meaning t m 4134) (meaning t m 4256) source

theorem rule35711 (p1983 p2027 p2765 p2982 p3680 p4110 p4381 : Prop) (h : (¬ p1983) ∨ p2765 ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3680) ∨ (¬ p2982) ∨ (¬ p4110)) : (¬ p1983) ∨ (p2027) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4110) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial35711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory24967 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule35711 (meaning t m 1983) (meaning t m 2027) (meaning t m 2765) (meaning t m 2982) (meaning t m 3680) (meaning t m 4110) (meaning t m 4381) source

theorem rule35718 (p1987 p2027 p2534 p2589 p2608 p2662 p2699 p2707 p2717 p2810 p3146 p4607 p4905 : Prop) (h : (¬ p2707) ∨ (¬ p2608) ∨ p2027 ∨ p2699 ∨ (¬ p2662) ∨ (¬ p3146) ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p2589) ∨ (¬ p4905) ∨ (¬ p4607) ∨ (¬ p2717) ∨ (¬ p2534)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2662) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial35718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory24974 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35718 (meaning t m 1987) (meaning t m 2027) (meaning t m 2534) (meaning t m 2589) (meaning t m 2608) (meaning t m 2662) (meaning t m 2699) (meaning t m 2707) (meaning t m 2717) (meaning t m 2810) (meaning t m 3146) (meaning t m 4607) (meaning t m 4905) source

theorem rule35722 (p2027 p2717 p3146 p4324 p4445 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p3146) ∨ (¬ p2717) ∨ (¬ p4445) ∨ p2027 ∨ (¬ p4324)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3146) ∨ (¬ p4324) ∨ (¬ p4445) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial35722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory24978 t (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule35722 (meaning t m 2027) (meaning t m 2717) (meaning t m 3146) (meaning t m 4324) (meaning t m 4445) (meaning t m 4905) source

theorem rule35723 (p1989 p2027 p2169 p2210 p2363 p3692 p3860 p3906 : Prop) (h : p2027 ∨ (¬ p2210) ∨ (¬ p1989) ∨ p2169 ∨ (¬ p3906) ∨ (¬ p3692) ∨ (¬ p2363) ∨ (¬ p3860)) : (¬ p1989) ∨ (p2027) ∨ (p2169) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) := by
  classical
  tauto

theorem initial35723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) := by
  have source := ElevenTheory.theory24979 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule35723 (meaning t m 1989) (meaning t m 2027) (meaning t m 2169) (meaning t m 2210) (meaning t m 2363) (meaning t m 3692) (meaning t m 3860) (meaning t m 3906) source

theorem rule35726 (p1987 p2027 p2589 p2662 p2764 p2810 p4322 p4948 : Prop) (h : (¬ p2810) ∨ p2764 ∨ (¬ p4948) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p4322) ∨ (¬ p2589)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial35726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory24982 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule35726 (meaning t m 1987) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2764) (meaning t m 2810) (meaning t m 4322) (meaning t m 4948) source

theorem rule35728 (p2630 p2748 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p2748) ∨ (¬ p2630)) : (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial35728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory24984 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule35728 (meaning t m 2630) (meaning t m 2748) (meaning t m 4111) source

theorem rule35729 (p2027 p2651 p2685 p2787 p2810 p3097 p3125 p3946 p4117 p4570 : Prop) (h : (¬ p4570) ∨ (¬ p4117) ∨ (¬ p3946) ∨ (¬ p2810) ∨ (¬ p2685) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2787) ∨ (¬ p3125) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2787) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4117) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial35729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory24985 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule35729 (meaning t m 2027) (meaning t m 2651) (meaning t m 2685) (meaning t m 2787) (meaning t m 2810) (meaning t m 3097) (meaning t m 3125) (meaning t m 3946) (meaning t m 4117) (meaning t m 4570) source

theorem rule35733 (p1977 p2027 p2299 p2633 p3097 p3662 p3952 : Prop) (h : (¬ p1977) ∨ (¬ p3952) ∨ (¬ p3662) ∨ p2633 ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2299)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial35733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory24989 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35733 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3097) (meaning t m 3662) (meaning t m 3952) source

theorem rule35737 (p2027 p2750 p3073 p3449 p3662 p3744 p3952 p3954 p4604 : Prop) (h : (¬ p3954) ∨ (¬ p2750) ∨ (¬ p3449) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3073) ∨ (¬ p4604) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3662) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial35737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory24993 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule35737 (meaning t m 2027) (meaning t m 2750) (meaning t m 3073) (meaning t m 3449) (meaning t m 3662) (meaning t m 3744) (meaning t m 3952) (meaning t m 3954) (meaning t m 4604) source

theorem rule35740 (p2003 p2027 p2187 p2284 p2387 p2938 p4320 : Prop) (h : (¬ p2003) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p2284) ∨ (¬ p4320) ∨ (¬ p2187) ∨ p2938) : (¬ p2003) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2387) ∨ (p2938) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial35740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory24996 t (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule35740 (meaning t m 2003) (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2387) (meaning t m 2938) (meaning t m 4320) source

theorem rule35745 (p2027 p2313 p2598 p2742 p2778 p3309 p4752 p4759 : Prop) (h : (¬ p2742) ∨ (¬ p2778) ∨ (¬ p2313) ∨ (¬ p4759) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3309) ∨ (¬ p4752) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial35745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory25001 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 6 7)
  exact rule35745 (meaning t m 2027) (meaning t m 2313) (meaning t m 2598) (meaning t m 2742) (meaning t m 2778) (meaning t m 3309) (meaning t m 4752) (meaning t m 4759) source

theorem rule35752 (p2027 p2373 p3347 p3399 p3631 p3904 p3951 p3954 p4120 p4948 p5216 : Prop) (h : (¬ p3631) ∨ (¬ p2373) ∨ (¬ p4120) ∨ (¬ p3904) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p4948) ∨ p2027 ∨ (¬ p3951)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3904) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p4120) ∨ (¬ p4948) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial35752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory25008 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule35752 (meaning t m 2027) (meaning t m 2373) (meaning t m 3347) (meaning t m 3399) (meaning t m 3631) (meaning t m 3904) (meaning t m 3951) (meaning t m 3954) (meaning t m 4120) (meaning t m 4948) (meaning t m 5216) source

theorem rule35755 (p2000 p2027 p2274 p2476 p2765 p3083 p3742 p3921 : Prop) (h : (¬ p3742) ∨ p2765 ∨ (¬ p2000) ∨ (¬ p3921) ∨ (¬ p3083) ∨ (¬ p2274) ∨ (¬ p2476) ∨ p2027) : (¬ p2000) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2476) ∨ (p2765) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial35755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory25011 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule35755 (meaning t m 2000) (meaning t m 2027) (meaning t m 2274) (meaning t m 2476) (meaning t m 2765) (meaning t m 3083) (meaning t m 3742) (meaning t m 3921) source

theorem rule35759 (p2027 p2274 p2313 p2563 p4198 p4533 : Prop) (h : (¬ p4533) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p4198) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial35759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory25015 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule35759 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2563) (meaning t m 4198) (meaning t m 4533) source

theorem rule35763 (p2027 p2459 p3055 p3399 p3527 p3684 p4736 p4948 p5059 : Prop) (h : (¬ p5059) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p4736) ∨ (¬ p2459) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p4948) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3684) ∨ (¬ p4736) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial35763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory25019 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule35763 (meaning t m 2027) (meaning t m 2459) (meaning t m 3055) (meaning t m 3399) (meaning t m 3527) (meaning t m 3684) (meaning t m 4736) (meaning t m 4948) (meaning t m 5059) source

theorem rule35764 (p2553 p3660 p4235 p4275 : Prop) (h : (¬ p4275) ∨ (¬ p2553) ∨ (¬ p3660) ∨ (¬ p4235)) : (¬ p2553) ∨ (¬ p3660) ∨ (¬ p4235) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial35764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory25020 (m.theta 4 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7)
  exact rule35764 (meaning t m 2553) (meaning t m 3660) (meaning t m 4235) (meaning t m 4275) source

theorem rule35767 (p2001 p2027 p2553 p3008 p3073 p3549 p3692 p4317 : Prop) (h : (¬ p3549) ∨ (¬ p2001) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3692) ∨ p3008 ∨ (¬ p3073) ∨ (¬ p4317)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3073) ∨ (¬ p3549) ∨ (¬ p3692) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial35767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory25023 t (m.theta 1 6) (m.theta 1 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 8 9)
  exact rule35767 (meaning t m 2001) (meaning t m 2027) (meaning t m 2553) (meaning t m 3008) (meaning t m 3073) (meaning t m 3549) (meaning t m 3692) (meaning t m 4317) source

theorem rule35768 (p4108 p5197 p5206 : Prop) (h : (¬ p5197) ∨ (¬ p4108) ∨ p5206) : (¬ p4108) ∨ (¬ p5197) ∨ (p5206) := by
  classical
  tauto

theorem initial35768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 5197)) ∨ (meaning t m 5206) := by
  have source := ElevenTheory.theory25024 (m.theta 0 1) (m.theta 0 4) (m.theta 0 7)
  exact rule35768 (meaning t m 4108) (meaning t m 5197) (meaning t m 5206) source

theorem rule35771 (p2027 p2210 p2254 p2630 p2657 p2881 p2891 p3877 p4041 : Prop) (h : (¬ p2254) ∨ (¬ p2210) ∨ (¬ p4041) ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p2881) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p3877)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3877) ∨ (¬ p4041) := by
  classical
  tauto

theorem initial35771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) := by
  have source := ElevenTheory.theory25027 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule35771 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2630) (meaning t m 2657) (meaning t m 2881) (meaning t m 2891) (meaning t m 3877) (meaning t m 4041) source

theorem rule35779 (p2027 p2284 p2497 p2553 p2696 p3136 p3452 p3549 p4718 p4733 : Prop) (h : (¬ p2497) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2553) ∨ (¬ p3549) ∨ (¬ p4718) ∨ (¬ p3136) ∨ (¬ p2696) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p4718) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial35779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4718)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory25035 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule35779 (meaning t m 2027) (meaning t m 2284) (meaning t m 2497) (meaning t m 2553) (meaning t m 2696) (meaning t m 3136) (meaning t m 3452) (meaning t m 3549) (meaning t m 4718) (meaning t m 4733) source

theorem rule35781 (p2027 p2264 p2312 p3309 p3570 p4155 p4204 p4518 : Prop) (h : p2027 ∨ (¬ p3570) ∨ (¬ p4155) ∨ (¬ p4518) ∨ (¬ p2312) ∨ (¬ p3309) ∨ (¬ p4204) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2312) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4155) ∨ (¬ p4204) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial35781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory25037 t (m.theta 0 7) (m.theta 1 6) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35781 (meaning t m 2027) (meaning t m 2264) (meaning t m 2312) (meaning t m 3309) (meaning t m 3570) (meaning t m 4155) (meaning t m 4204) (meaning t m 4518) source

theorem rule35784 (p2928 p3193 p4635 : Prop) (h : (¬ p2928) ∨ (¬ p4635) ∨ p3193) : (¬ p2928) ∨ (p3193) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial35784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2928)) ∨ (meaning t m 3193) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory25040 (m.theta 1 4) (m.theta 4 7) (m.theta 4 9)
  exact rule35784 (meaning t m 2928) (meaning t m 3193) (meaning t m 4635) source

theorem rule35797 (p2027 p2264 p2737 p2807 p2811 p2928 p3055 p4030 p4278 p4666 p4734 : Prop) (h : p2027 ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p2737) ∨ (¬ p4734) ∨ (¬ p2264) ∨ (¬ p2928) ∨ (¬ p4666) ∨ (¬ p4278) ∨ (¬ p4030) ∨ (¬ p2811)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial35797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory25053 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35797 (meaning t m 2027) (meaning t m 2264) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 2928) (meaning t m 3055) (meaning t m 4030) (meaning t m 4278) (meaning t m 4666) (meaning t m 4734) source

theorem rule35800 (p1976 p2027 p2534 p2589 p2914 p3609 p3876 p3905 p4354 p4607 : Prop) (h : (¬ p1976) ∨ p2027 ∨ p2914 ∨ (¬ p2589) ∨ (¬ p3905) ∨ (¬ p4607) ∨ (¬ p3876) ∨ (¬ p4354) ∨ (¬ p3609) ∨ (¬ p2534)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (p2914) ∨ (¬ p3609) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4354) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial35800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4354)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory25056 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule35800 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2589) (meaning t m 2914) (meaning t m 3609) (meaning t m 3876) (meaning t m 3905) (meaning t m 4354) (meaning t m 4607) source

theorem rule35801 (p1998 p2027 p2264 p2611 p2696 p3434 p3947 p4781 : Prop) (h : p2611 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2264) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial35801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory25057 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35801 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2611) (meaning t m 2696) (meaning t m 3434) (meaning t m 3947) (meaning t m 4781) source

theorem rule35806 (p1998 p2027 p2132 p2497 p2553 p2870 p3008 p3146 p3452 p3549 p3747 p4348 p4733 : Prop) (h : (¬ p2870) ∨ (¬ p2497) ∨ (¬ p2132) ∨ (¬ p3747) ∨ p3008 ∨ (¬ p4733) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3452) ∨ (¬ p2553) ∨ (¬ p4348) ∨ (¬ p3146)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2497) ∨ (¬ p2553) ∨ (¬ p2870) ∨ (p3008) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial35806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2870)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory25062 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule35806 (meaning t m 1998) (meaning t m 2027) (meaning t m 2132) (meaning t m 2497) (meaning t m 2553) (meaning t m 2870) (meaning t m 3008) (meaning t m 3146) (meaning t m 3452) (meaning t m 3549) (meaning t m 3747) (meaning t m 4348) (meaning t m 4733) source

theorem rule35808 (p2027 p2246 p2476 p2534 p2662 p2751 p2810 p2901 p2946 p3246 p3950 : Prop) (h : (¬ p2751) ∨ (¬ p2662) ∨ (¬ p3950) ∨ (¬ p3246) ∨ (¬ p2246) ∨ (¬ p2901) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p2476) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial35808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory25064 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule35808 (meaning t m 2027) (meaning t m 2246) (meaning t m 2476) (meaning t m 2534) (meaning t m 2662) (meaning t m 2751) (meaning t m 2810) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3950) source

theorem rule35812 (p2363 p2528 p4432 : Prop) (h : (¬ p4432) ∨ (¬ p2528) ∨ p2363) : (p2363) ∨ (¬ p2528) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial35812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2363) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory25068 (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule35812 (meaning t m 2363) (meaning t m 2528) (meaning t m 4432) source

theorem rule35814 (p2313 p3399 p3547 p5015 : Prop) (h : (¬ p2313) ∨ (¬ p3547) ∨ (¬ p5015) ∨ (¬ p3399)) : (¬ p2313) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial35814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory25070 (m.theta 0 1) (m.theta 0 6) (m.theta 1 7) (m.theta 6 7)
  exact rule35814 (meaning t m 2313) (meaning t m 3399) (meaning t m 3547) (meaning t m 5015) source

theorem rule35815 (p2027 p2284 p2352 p3497 p4506 p4718 : Prop) (h : (¬ p4718) ∨ (¬ p2284) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p4506) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2352) ∨ (¬ p3497) ∨ (¬ p4506) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial35815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory25071 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule35815 (meaning t m 2027) (meaning t m 2284) (meaning t m 2352) (meaning t m 3497) (meaning t m 4506) (meaning t m 4718) source

theorem rule35826 (p2027 p2829 p3583 p3952 p4185 p5053 : Prop) (h : (¬ p3952) ∨ p2027 ∨ (¬ p5053) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4185)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial35826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory25082 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6)
  exact rule35826 (meaning t m 2027) (meaning t m 2829) (meaning t m 3583) (meaning t m 3952) (meaning t m 4185) (meaning t m 5053) source

theorem rule35828 (p2004 p2027 p2191 p2202 p2373 p3399 p3555 : Prop) (h : p2202 ∨ (¬ p2373) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p3399) ∨ (¬ p2004) ∨ (¬ p3555)) : (¬ p2004) ∨ (p2027) ∨ (¬ p2191) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p3399) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial35828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory25084 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 5 8)
  exact rule35828 (meaning t m 2004) (meaning t m 2027) (meaning t m 2191) (meaning t m 2202) (meaning t m 2373) (meaning t m 3399) (meaning t m 3555) source

theorem rule35831 (p1984 p2027 p2622 p2743 p2780 p3063 p3873 p4358 p4869 : Prop) (h : (¬ p4869) ∨ (¬ p2743) ∨ (¬ p1984) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p3873) ∨ p2622 ∨ (¬ p3063) ∨ (¬ p4358)) : (¬ p1984) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p3063) ∨ (¬ p3873) ∨ (¬ p4358) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial35831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory25087 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule35831 (meaning t m 1984) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 2780) (meaning t m 3063) (meaning t m 3873) (meaning t m 4358) (meaning t m 4869) source

theorem rule35832 (p1976 p2027 p2765 p3055 p3367 p3583 p3698 p4110 : Prop) (h : (¬ p3367) ∨ p2765 ∨ (¬ p3698) ∨ (¬ p3055) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p4110)) : (¬ p1976) ∨ (p2027) ∨ (p2765) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial35832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory25088 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule35832 (meaning t m 1976) (meaning t m 2027) (meaning t m 2765) (meaning t m 3055) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 4110) source

theorem rule35840 (p2027 p2499 p3222 p3989 p4045 p4157 p4718 : Prop) (h : p2027 ∨ (¬ p3222) ∨ (¬ p4045) ∨ (¬ p4157) ∨ (¬ p2499) ∨ (¬ p4718) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3989) ∨ (¬ p4045) ∨ (¬ p4157) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial35840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory25096 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8)
  exact rule35840 (meaning t m 2027) (meaning t m 2499) (meaning t m 3222) (meaning t m 3989) (meaning t m 4045) (meaning t m 4157) (meaning t m 4718) source

theorem rule35842 (p2027 p2598 p3434 p3820 p3821 p4752 p4781 : Prop) (h : (¬ p4781) ∨ (¬ p3820) ∨ (¬ p3434) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p3821) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4752) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial35842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory25098 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9)
  exact rule35842 (meaning t m 2027) (meaning t m 2598) (meaning t m 3434) (meaning t m 3820) (meaning t m 3821) (meaning t m 4752) (meaning t m 4781) source

theorem rule35845 (p2027 p2518 p2531 p3238 p4120 p4533 : Prop) (h : (¬ p4120) ∨ (¬ p4533) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2531) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3238) ∨ (¬ p4120) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial35845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory25101 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule35845 (meaning t m 2027) (meaning t m 2518) (meaning t m 2531) (meaning t m 3238) (meaning t m 4120) (meaning t m 4533) source

theorem rule35849 (p1999 p2027 p2307 p2641 p2688 p3097 p3125 p3567 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2641) ∨ (¬ p2307) ∨ (¬ p1999) ∨ (¬ p3125) ∨ (¬ p3567)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial35849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory25105 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule35849 (meaning t m 1999) (meaning t m 2027) (meaning t m 2307) (meaning t m 2641) (meaning t m 2688) (meaning t m 3097) (meaning t m 3125) (meaning t m 3567) source

theorem rule35860 (p1979 p2027 p2132 p2619 p2622 p3365 p3497 : Prop) (h : p2622 ∨ (¬ p2619) ∨ (¬ p2132) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3497)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial35860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory25116 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule35860 (meaning t m 1979) (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2622) (meaning t m 3365) (meaning t m 3497) source

theorem rule35861 (p2027 p2252 p2657 p2881 p3399 p3555 p3571 p3742 p4278 p4448 p4666 : Prop) (h : (¬ p3571) ∨ (¬ p2881) ∨ (¬ p2252) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p4448) ∨ (¬ p2657) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4448) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial35861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4448)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory25117 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35861 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2881) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) (meaning t m 3742) (meaning t m 4278) (meaning t m 4448) (meaning t m 4666) source

theorem rule35863 (p1984 p2027 p2202 p2493 p2579 p3238 p3366 p3905 p3954 : Prop) (h : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3954) ∨ p2202 ∨ (¬ p3238)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3238) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial35863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory25119 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6)
  exact rule35863 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2493) (meaning t m 2579) (meaning t m 3238) (meaning t m 3366) (meaning t m 3905) (meaning t m 3954) source

theorem rule35864 (p2027 p2248 p2509 p2534 p2958 p3212 p3452 p3680 p3950 p4381 : Prop) (h : p2027 ∨ (¬ p2509) ∨ (¬ p4381) ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p2534) ∨ (¬ p3212) ∨ (¬ p2958) ∨ (¬ p3950) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p3950) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial35864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory25120 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 4 8) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35864 (meaning t m 2027) (meaning t m 2248) (meaning t m 2509) (meaning t m 2534) (meaning t m 2958) (meaning t m 3212) (meaning t m 3452) (meaning t m 3680) (meaning t m 3950) (meaning t m 4381) source

theorem rule35867 (p2027 p2156 p2187 p2247 p3848 p3979 p4521 p5119 p5284 : Prop) (h : p2027 ∨ (¬ p2247) ∨ (¬ p2187) ∨ (¬ p3979) ∨ (¬ p5119) ∨ (¬ p3848) ∨ (¬ p5284) ∨ (¬ p4521) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p3848) ∨ (¬ p3979) ∨ (¬ p4521) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial35867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory25123 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule35867 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2247) (meaning t m 3848) (meaning t m 3979) (meaning t m 4521) (meaning t m 5119) (meaning t m 5284) source

theorem rule35869 (p2027 p2210 p2254 p2657 p2881 p2891 p3742 p5503 p5559 : Prop) (h : (¬ p2881) ∨ (¬ p5559) ∨ (¬ p3742) ∨ (¬ p5503) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3742) ∨ (¬ p5503) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial35869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory25125 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule35869 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2881) (meaning t m 2891) (meaning t m 3742) (meaning t m 5503) (meaning t m 5559) source

theorem rule35871 (p2027 p2264 p2995 p3355 p3551 p3879 p4953 p5197 : Prop) (h : (¬ p3551) ∨ (¬ p2995) ∨ (¬ p3879) ∨ (¬ p5197) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p4953) ∨ (¬ p3355)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3355) ∨ (¬ p3551) ∨ (¬ p3879) ∨ (¬ p4953) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial35871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4953)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory25127 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 4 9) (m.theta 7 8)
  exact rule35871 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3355) (meaning t m 3551) (meaning t m 3879) (meaning t m 4953) (meaning t m 5197) source

theorem rule35874 (p2027 p2459 p2608 p2881 p3051 p3193 p3370 p3452 p4377 p4697 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3193) ∨ (¬ p4697) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4377) ∨ (¬ p2459) ∨ (¬ p3370)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3193) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4377) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial35874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory25130 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule35874 (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 2881) (meaning t m 3051) (meaning t m 3193) (meaning t m 3370) (meaning t m 3452) (meaning t m 4377) (meaning t m 4697) source

theorem rule35876 (p1981 p2027 p2190 p2307 p2344 p3097 p3146 p4347 : Prop) (h : (¬ p1981) ∨ (¬ p2190) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2307) ∨ (¬ p4347) ∨ p2344 ∨ (¬ p3097)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2190) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p3097) ∨ (¬ p3146) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial35876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory25132 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule35876 (meaning t m 1981) (meaning t m 2027) (meaning t m 2190) (meaning t m 2307) (meaning t m 2344) (meaning t m 3097) (meaning t m 3146) (meaning t m 4347) source

theorem rule35877 (p2027 p2717 p3097 p3426 p3551 p3552 p4155 p4401 : Prop) (h : (¬ p4155) ∨ (¬ p3097) ∨ (¬ p2717) ∨ (¬ p3552) ∨ (¬ p3426) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4401)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3097) ∨ (¬ p3426) ∨ (¬ p3551) ∨ (¬ p3552) ∨ (¬ p4155) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial35877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory25133 t (m.theta 0 7) (m.theta 2 6) (m.theta 2 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35877 (meaning t m 2027) (meaning t m 2717) (meaning t m 3097) (meaning t m 3426) (meaning t m 3551) (meaning t m 3552) (meaning t m 4155) (meaning t m 4401) source

theorem rule35884 (p1985 p2027 p2633 p2901 p2927 p3516 p3543 p3644 p4208 p4382 : Prop) (h : (¬ p3543) ∨ p2633 ∨ (¬ p1985) ∨ (¬ p2901) ∨ (¬ p3644) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p4382) ∨ (¬ p3516) ∨ (¬ p2927)) : (¬ p1985) ∨ (p2027) ∨ (p2633) ∨ (¬ p2901) ∨ (¬ p2927) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3644) ∨ (¬ p4208) ∨ (¬ p4382) := by
  classical
  tauto

theorem initial35884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4382)) := by
  have source := ElevenTheory.theory25140 t (m.theta 0 7) (m.theta 1 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule35884 (meaning t m 1985) (meaning t m 2027) (meaning t m 2633) (meaning t m 2901) (meaning t m 2927) (meaning t m 3516) (meaning t m 3543) (meaning t m 3644) (meaning t m 4208) (meaning t m 4382) source

theorem rule35890 (p2027 p2493 p3238 p3646 p4203 p4533 : Prop) (h : (¬ p4203) ∨ (¬ p4533) ∨ (¬ p3238) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2493)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial35890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory25146 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule35890 (meaning t m 2027) (meaning t m 2493) (meaning t m 3238) (meaning t m 3646) (meaning t m 4203) (meaning t m 4533) source

theorem rule35899 (p2027 p2187 p2230 p2563 p3365 p3366 p3519 p3553 p3572 p4133 p4376 : Prop) (h : (¬ p4133) ∨ (¬ p3572) ∨ (¬ p3366) ∨ (¬ p2187) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3519) ∨ (¬ p3365) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial35899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory25155 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule35899 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3553) (meaning t m 3572) (meaning t m 4133) (meaning t m 4376) source

theorem rule35912 (p3256 p3609 p4963 : Prop) (h : (¬ p4963) ∨ (¬ p3609) ∨ p3256) : (p3256) ∨ (¬ p3609) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial35912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3256) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory25168 (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule35912 (meaning t m 3256) (meaning t m 3609) (meaning t m 4963) source

theorem rule35914 (p2027 p2156 p2373 p2608 p3519 p3548 p4110 p4366 p4376 p4399 p4902 : Prop) (h : (¬ p2156) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p4902) ∨ (¬ p2608) ∨ (¬ p2373) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p4110) ∨ (¬ p3548) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3548) ∨ (¬ p4110) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial35914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory25170 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule35914 (meaning t m 2027) (meaning t m 2156) (meaning t m 2373) (meaning t m 2608) (meaning t m 3519) (meaning t m 3548) (meaning t m 4110) (meaning t m 4366) (meaning t m 4376) (meaning t m 4399) (meaning t m 4902) source

theorem rule35915 (p2027 p2210 p2254 p2657 p2891 p3359 p4129 p4425 p4826 : Prop) (h : p2027 ∨ (¬ p2657) ∨ (¬ p4425) ∨ (¬ p4129) ∨ (¬ p2254) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p4826) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3359) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial35915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory25171 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule35915 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2891) (meaning t m 3359) (meaning t m 4129) (meaning t m 4425) (meaning t m 4826) source

theorem rule35918 (p1983 p2027 p2191 p2388 p2891 p3156 p3246 : Prop) (h : (¬ p2891) ∨ (¬ p3156) ∨ (¬ p1983) ∨ p2388 ∨ (¬ p2191) ∨ (¬ p3246) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (¬ p2191) ∨ (p2388) ∨ (¬ p2891) ∨ (¬ p3156) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial35918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory25174 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule35918 (meaning t m 1983) (meaning t m 2027) (meaning t m 2191) (meaning t m 2388) (meaning t m 2891) (meaning t m 3156) (meaning t m 3246) source

theorem rule35921 (p2027 p2252 p2657 p2750 p3073 p3449 p3742 p3954 p4278 p4669 : Prop) (h : (¬ p2252) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p3954) ∨ (¬ p3449) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p3073) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial35921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25177 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule35921 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3073) (meaning t m 3449) (meaning t m 3742) (meaning t m 3954) (meaning t m 4278) (meaning t m 4669) source

theorem rule35922 (p2027 p2264 p2298 p2307 p3570 p4204 p4489 : Prop) (h : (¬ p2298) ∨ (¬ p2307) ∨ (¬ p2264) ∨ (¬ p3570) ∨ (¬ p4489) ∨ p2027 ∨ (¬ p4204)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2298) ∨ (¬ p2307) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial35922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory25178 t (m.theta 0 6) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35922 (meaning t m 2027) (meaning t m 2264) (meaning t m 2298) (meaning t m 2307) (meaning t m 3570) (meaning t m 4204) (meaning t m 4489) source

theorem rule35924 (p2027 p2138 p2598 p2743 p2839 p4752 : Prop) (h : (¬ p2138) ∨ (¬ p2839) ∨ (¬ p4752) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2598)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial35924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory25180 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule35924 (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 2743) (meaning t m 2839) (meaning t m 4752) source

theorem rule35931 (p2027 p2192 p2210 p3834 p4388 p5043 : Prop) (h : p2027 ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4388) ∨ (¬ p3834) ∨ (¬ p5043)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial35931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4388)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory25187 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 5 6) (m.theta 5 9)
  exact rule35931 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 3834) (meaning t m 4388) (meaning t m 5043) source

theorem rule35934 (p1982 p2027 p2202 p2220 p2427 p3146 p3556 : Prop) (h : (¬ p1982) ∨ p2202 ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3146) ∨ (¬ p2220)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial35934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory25190 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule35934 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2220) (meaning t m 2427) (meaning t m 3146) (meaning t m 3556) source

theorem rule35936 (p2891 p3698 p4235 p4418 : Prop) (h : (¬ p2891) ∨ (¬ p4418) ∨ (¬ p3698) ∨ (¬ p4235)) : (¬ p2891) ∨ (¬ p3698) ∨ (¬ p4235) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial35936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory25192 (m.theta 1 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule35936 (meaning t m 2891) (meaning t m 3698) (meaning t m 4235) (meaning t m 4418) source

theorem rule35940 (p2027 p2136 p2192 p2598 p3646 p4313 p4418 p4752 : Prop) (h : p2027 ∨ (¬ p4752) ∨ (¬ p2598) ∨ (¬ p4313) ∨ (¬ p2192) ∨ (¬ p4418) ∨ (¬ p2136) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2192) ∨ (¬ p2598) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4418) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial35940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory25196 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule35940 (meaning t m 2027) (meaning t m 2136) (meaning t m 2192) (meaning t m 2598) (meaning t m 3646) (meaning t m 4313) (meaning t m 4418) (meaning t m 4752) source

theorem rule35944 (p2027 p2144 p2220 p2295 p2313 p2577 p3105 p3694 p4037 p4397 p4729 : Prop) (h : (¬ p2577) ∨ (¬ p4397) ∨ (¬ p2313) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p3105) ∨ (¬ p4037) ∨ (¬ p2295) ∨ (¬ p2220) ∨ (¬ p2144) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4037) ∨ (¬ p4397) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial35944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory25200 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule35944 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2295) (meaning t m 2313) (meaning t m 2577) (meaning t m 3105) (meaning t m 3694) (meaning t m 4037) (meaning t m 4397) (meaning t m 4729) source

theorem rule35950 (p2027 p2307 p2797 p3567 p3877 p4501 p4769 : Prop) (h : (¬ p3567) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p4769) ∨ (¬ p3877) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3877) ∨ (¬ p4501) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial35950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory25206 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule35950 (meaning t m 2027) (meaning t m 2307) (meaning t m 2797) (meaning t m 3567) (meaning t m 3877) (meaning t m 4501) (meaning t m 4769) source

theorem rule35952 (p2220 p2951 p3497 : Prop) (h : (¬ p3497) ∨ (¬ p2951) ∨ (¬ p2220)) : (¬ p2220) ∨ (¬ p2951) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial35952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory25208 (m.theta 0 5) (m.theta 3 5) (m.theta 5 8)
  exact rule35952 (meaning t m 2220) (meaning t m 2951) (meaning t m 3497) source

theorem rule35953 (p1976 p2027 p2169 p2810 p3365 p3574 p3956 : Prop) (h : (¬ p2810) ∨ (¬ p3574) ∨ (¬ p3956) ∨ p2169 ∨ p2027 ∨ (¬ p1976) ∨ (¬ p3365)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3574) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial35953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory25209 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule35953 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2810) (meaning t m 3365) (meaning t m 3574) (meaning t m 3956) source

theorem rule35957 (p2027 p2252 p2657 p3399 p3527 p3555 p3742 p4448 p5503 p5559 : Prop) (h : (¬ p3742) ∨ (¬ p4448) ∨ (¬ p2252) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p5503) ∨ (¬ p3399) ∨ (¬ p5559) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3742) ∨ (¬ p4448) ∨ (¬ p5503) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial35957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4448)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory25213 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10) (m.theta 7 8)
  exact rule35957 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 3399) (meaning t m 3527) (meaning t m 3555) (meaning t m 3742) (meaning t m 4448) (meaning t m 5503) (meaning t m 5559) source

theorem rule35958 (p2177 p3552 p3644 p3740 : Prop) (h : (¬ p3644) ∨ (¬ p3740) ∨ (¬ p3552) ∨ (¬ p2177)) : (¬ p2177) ∨ (¬ p3552) ∨ (¬ p3644) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial35958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory25214 (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35958 (meaning t m 2177) (meaning t m 3552) (meaning t m 3644) (meaning t m 3740) source

theorem rule35965 (p2027 p2295 p2313 p2785 p3497 p4185 p4336 p4507 : Prop) (h : (¬ p3497) ∨ (¬ p2785) ∨ (¬ p2313) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p4185) ∨ (¬ p4336) ∨ (¬ p4507)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2785) ∨ (¬ p3497) ∨ (¬ p4185) ∨ (¬ p4336) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial35965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory25221 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule35965 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2785) (meaning t m 3497) (meaning t m 4185) (meaning t m 4336) (meaning t m 4507) source

theorem rule35974 (p2027 p2307 p3549 p3860 p4994 p5020 : Prop) (h : (¬ p3549) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4994) ∨ (¬ p5020) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3860) ∨ (¬ p4994) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial35974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4994)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory25230 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6) (m.theta 1 8) (m.theta 6 7)
  exact rule35974 (meaning t m 2027) (meaning t m 2307) (meaning t m 3549) (meaning t m 3860) (meaning t m 4994) (meaning t m 5020) source

theorem rule35980 (p3740 p3947 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3740) ∨ p3947) : (¬ p3740) ∨ (p3947) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial35980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3740)) ∨ (meaning t m 3947) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25236 (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule35980 (meaning t m 3740) (meaning t m 3947) (meaning t m 4278) source

theorem rule35989 (p1984 p2027 p2187 p2247 p2765 p3324 p3662 p4153 : Prop) (h : (¬ p1984) ∨ (¬ p3662) ∨ p2765 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2187) ∨ (¬ p3324) ∨ (¬ p4153)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (p2765) ∨ (¬ p3324) ∨ (¬ p3662) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial35989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory25245 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule35989 (meaning t m 1984) (meaning t m 2027) (meaning t m 2187) (meaning t m 2247) (meaning t m 2765) (meaning t m 3324) (meaning t m 3662) (meaning t m 4153) source

theorem rule35990 (p1984 p2027 p2202 p2247 p2563 p3662 p3952 : Prop) (h : p2202 ∨ (¬ p3662) ∨ (¬ p2247) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial35990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory25246 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule35990 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2247) (meaning t m 2563) (meaning t m 3662) (meaning t m 3952) source

theorem rule35991 (p2027 p2132 p2241 p2619 p2750 p2753 p3146 p3817 p4366 p4669 : Prop) (h : (¬ p2132) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p3817) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2241) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial35991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25247 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule35991 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3146) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) source

theorem rule35992 (p2027 p2274 p2563 p3549 p4512 p4629 : Prop) (h : (¬ p3549) ∨ (¬ p4512) ∨ p2027 ∨ (¬ p4629) ∨ (¬ p2563) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial35992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory25248 t (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule35992 (meaning t m 2027) (meaning t m 2274) (meaning t m 2563) (meaning t m 3549) (meaning t m 4512) (meaning t m 4629) source

theorem rule35999 (p2143 p4533 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p2143) ∨ p4533) : (¬ p2143) ∨ (p4533) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial35999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (meaning t m 4533) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory25255 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5)
  exact rule35999 (meaning t m 2143) (meaning t m 4533) (meaning t m 4882) source

theorem rule36001 (p2027 p2088 p2657 p3005 p3171 p3266 p3742 p4787 p4831 p5503 : Prop) (h : (¬ p3266) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2088) ∨ (¬ p4831) ∨ (¬ p3171) ∨ (¬ p5503) ∨ (¬ p3005) ∨ (¬ p4787)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2657) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p4787) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial36001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory25257 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule36001 (meaning t m 2027) (meaning t m 2088) (meaning t m 2657) (meaning t m 3005) (meaning t m 3171) (meaning t m 3266) (meaning t m 3742) (meaning t m 4787) (meaning t m 4831) (meaning t m 5503) source

theorem rule36007 (p2027 p2132 p2241 p2619 p2750 p2753 p3146 p3591 p4026 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p3146) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2241) ∨ (¬ p3591) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial36007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory25263 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule36007 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3146) (meaning t m 3591) (meaning t m 4026) (meaning t m 4604) source

theorem rule36009 (p2156 p2220 p3988 : Prop) (h : (¬ p3988) ∨ (¬ p2220) ∨ p2156) : (p2156) ∨ (¬ p2220) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial36009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory25265 (m.theta 0 5) (m.theta 5 6) (m.theta 5 8)
  exact rule36009 (meaning t m 2156) (meaning t m 2220) (meaning t m 3988) source

theorem rule36013 (p2027 p2657 p3093 p3309 p3366 p3742 p3860 p3920 p3956 p4236 p4501 p5312 : Prop) (h : p2027 ∨ (¬ p5312) ∨ (¬ p3366) ∨ (¬ p3956) ∨ (¬ p3742) ∨ (¬ p4236) ∨ (¬ p2657) ∨ (¬ p3920) ∨ (¬ p4501) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3742) ∨ (¬ p3860) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4236) ∨ (¬ p4501) ∨ (¬ p5312) := by
  classical
  tauto

theorem initial36013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5312)) := by
  have source := ElevenTheory.theory25269 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule36013 (meaning t m 2027) (meaning t m 2657) (meaning t m 3093) (meaning t m 3309) (meaning t m 3366) (meaning t m 3742) (meaning t m 3860) (meaning t m 3920) (meaning t m 3956) (meaning t m 4236) (meaning t m 4501) (meaning t m 5312) source

theorem rule36014 (p2027 p2144 p2220 p2241 p2750 p2753 p3105 p3591 p3694 p4026 p4397 : Prop) (h : (¬ p3694) ∨ (¬ p4397) ∨ (¬ p2144) ∨ (¬ p3591) ∨ (¬ p2750) ∨ (¬ p3105) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p2753) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3591) ∨ (¬ p3694) ∨ (¬ p4026) ∨ (¬ p4397) := by
  classical
  tauto

theorem initial36014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4397)) := by
  have source := ElevenTheory.theory25270 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9)
  exact rule36014 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3105) (meaning t m 3591) (meaning t m 3694) (meaning t m 4026) (meaning t m 4397) source

theorem rule36017 (p3574 p3584 p4343 : Prop) (h : (¬ p3574) ∨ (¬ p4343) ∨ p3584) : (¬ p3574) ∨ (p3584) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial36017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3574)) ∨ (meaning t m 3584) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory25273 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule36017 (meaning t m 3574) (meaning t m 3584) (meaning t m 4343) source

theorem rule36019 (p1987 p2027 p2169 p2696 p3055 p3574 p3956 p4343 : Prop) (h : (¬ p1987) ∨ (¬ p2696) ∨ p2169 ∨ p2027 ∨ (¬ p3956) ∨ (¬ p3574) ∨ (¬ p4343) ∨ (¬ p3055)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial36019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory25275 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule36019 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2696) (meaning t m 3055) (meaning t m 3574) (meaning t m 3956) (meaning t m 4343) source

theorem rule36025 (p1991 p2027 p2169 p2498 p2657 p3319 p3461 p3742 p3956 p4278 p4444 p4669 : Prop) (h : p2169 ∨ (¬ p2657) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p3956) ∨ (¬ p2498) ∨ (¬ p3461) ∨ (¬ p3319) ∨ (¬ p4278) ∨ (¬ p3742) ∨ (¬ p4669) ∨ (¬ p4444)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2498) ∨ (¬ p2657) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4278) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25281 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36025 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2498) (meaning t m 2657) (meaning t m 3319) (meaning t m 3461) (meaning t m 3742) (meaning t m 3956) (meaning t m 4278) (meaning t m 4444) (meaning t m 4669) source

theorem rule36042 (p1988 p2027 p2114 p2839 p2860 p3125 p3461 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p2839) ∨ (¬ p3125) ∨ (¬ p1988) ∨ (¬ p3461) ∨ (¬ p2860)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial36042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory25298 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule36042 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2839) (meaning t m 2860) (meaning t m 3125) (meaning t m 3461) source

theorem rule36044 (p2027 p3097 p3399 p3547 p3591 p4518 : Prop) (h : (¬ p3591) ∨ (¬ p3097) ∨ (¬ p3547) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p4518)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial36044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory25300 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7)
  exact rule36044 (meaning t m 2027) (meaning t m 3097) (meaning t m 3399) (meaning t m 3547) (meaning t m 3591) (meaning t m 4518) source

theorem rule36045 (p2027 p2254 p2363 p2952 p3063 p3093 p3497 p5118 p5568 : Prop) (h : (¬ p3497) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p5118) ∨ (¬ p3063) ∨ (¬ p2952) ∨ (¬ p2254) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial36045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory25301 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36045 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2952) (meaning t m 3063) (meaning t m 3093) (meaning t m 3497) (meaning t m 5118) (meaning t m 5568) source

theorem rule36047 (p2027 p2363 p2589 p3063 p3093 p3497 p4241 p5118 p5193 p5568 : Prop) (h : (¬ p2363) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p4241) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p3063) ∨ (¬ p5118)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p4241) ∨ (¬ p5118) ∨ (¬ p5193) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial36047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory25303 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36047 (meaning t m 2027) (meaning t m 2363) (meaning t m 2589) (meaning t m 3063) (meaning t m 3093) (meaning t m 3497) (meaning t m 4241) (meaning t m 5118) (meaning t m 5193) (meaning t m 5568) source

end SunPrize.SMT
