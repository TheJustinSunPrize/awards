import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory038
import SunPrize.Certificate.Theory039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule23570 (p2027 p2247 p2598 p3422 p3564 p4118 p4330 p4360 p4733 : Prop) (h : (¬ p4118) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4733) ∨ (¬ p3422) ∨ (¬ p4360) ∨ (¬ p2247) ∨ (¬ p4330) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12826 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule23570 (meaning t m 2027) (meaning t m 2247) (meaning t m 2598) (meaning t m 3422) (meaning t m 3564) (meaning t m 4118) (meaning t m 4330) (meaning t m 4360) (meaning t m 4733) source

theorem rule23571 (p2027 p2122 p2247 p2396 p2774 p3662 p3951 p4208 p4733 : Prop) (h : (¬ p3951) ∨ (¬ p2122) ∨ (¬ p4208) ∨ (¬ p2247) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2396) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2247) ∨ (¬ p2396) ∨ (¬ p2774) ∨ (¬ p3662) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12827 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule23571 (meaning t m 2027) (meaning t m 2122) (meaning t m 2247) (meaning t m 2396) (meaning t m 2774) (meaning t m 3662) (meaning t m 3951) (meaning t m 4208) (meaning t m 4733) source

theorem rule23573 (p2027 p2132 p2247 p2870 p2881 p2996 p3947 p4666 p4733 : Prop) (h : (¬ p4666) ∨ (¬ p2996) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2881) ∨ (¬ p3947) ∨ (¬ p4733) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12829 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23573 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2870) (meaning t m 2881) (meaning t m 2996) (meaning t m 3947) (meaning t m 4666) (meaning t m 4733) source

theorem rule23574 (p2027 p2318 p3027 p3097 p4066 p4154 p4560 : Prop) (h : (¬ p4066) ∨ (¬ p2318) ∨ (¬ p4560) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p4154) ∨ p2027) : (p2027) ∨ (¬ p2318) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p4066) ∨ (¬ p4154) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12830 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule23574 (meaning t m 2027) (meaning t m 2318) (meaning t m 3027) (meaning t m 3097) (meaning t m 4066) (meaning t m 4154) (meaning t m 4560) source

theorem rule23575 (p2027 p2247 p2307 p2363 p3325 p3497 p3662 p4348 p4905 p5017 : Prop) (h : (¬ p5017) ∨ (¬ p3662) ∨ (¬ p3497) ∨ (¬ p4348) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3325) ∨ (¬ p4905) ∨ (¬ p2307) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial23575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory12831 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23575 (meaning t m 2027) (meaning t m 2247) (meaning t m 2307) (meaning t m 2363) (meaning t m 3325) (meaning t m 3497) (meaning t m 3662) (meaning t m 4348) (meaning t m 4905) (meaning t m 5017) source

theorem rule23576 (p2027 p2132 p2247 p2264 p2274 p2860 p3031 p3548 p4361 p4733 : Prop) (h : (¬ p3031) ∨ (¬ p2264) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2860) ∨ (¬ p4361) ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2860) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4361) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12832 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23576 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2264) (meaning t m 2274) (meaning t m 2860) (meaning t m 3031) (meaning t m 3548) (meaning t m 4361) (meaning t m 4733) source

theorem rule23578 (p2027 p2132 p2860 p3125 p3548 p4330 p4348 p4366 p4733 : Prop) (h : (¬ p4348) ∨ (¬ p4330) ∨ (¬ p2132) ∨ (¬ p3548) ∨ (¬ p3125) ∨ (¬ p2860) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p4733)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12834 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23578 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3125) (meaning t m 3548) (meaning t m 4330) (meaning t m 4348) (meaning t m 4366) (meaning t m 4733) source

theorem rule23580 (p2027 p2598 p3422 p3548 p3564 p4330 p4348 p4366 p4733 : Prop) (h : (¬ p3422) ∨ (¬ p4330) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2598) ∨ (¬ p3548) ∨ (¬ p3564) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3548) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12836 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23580 (meaning t m 2027) (meaning t m 2598) (meaning t m 3422) (meaning t m 3548) (meaning t m 3564) (meaning t m 4330) (meaning t m 4348) (meaning t m 4366) (meaning t m 4733) source

theorem rule23583 (p3548 p3657 p3817 : Prop) (h : (¬ p3657) ∨ (¬ p3548) ∨ p3817) : (¬ p3548) ∨ (¬ p3657) ∨ (p3817) := by
  classical
  tauto

theorem initial23583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 3817) := by
  have source := ElevenTheory.theory12839 (m.theta 1 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23583 (meaning t m 3548) (meaning t m 3657) (meaning t m 3817) source

theorem rule23584 (p2027 p2598 p2850 p2982 p3548 p4348 p4366 p4450 p4733 : Prop) (h : (¬ p4348) ∨ (¬ p2598) ∨ (¬ p4366) ∨ (¬ p2850) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p4450) ∨ (¬ p2982) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4450) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12840 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23584 (meaning t m 2027) (meaning t m 2598) (meaning t m 2850) (meaning t m 2982) (meaning t m 3548) (meaning t m 4348) (meaning t m 4366) (meaning t m 4450) (meaning t m 4733) source

theorem rule23585 (p2027 p2177 p2230 p3201 p3362 p3548 p3684 p4276 p4366 p4733 : Prop) (h : (¬ p3201) ∨ (¬ p4366) ∨ (¬ p4276) ∨ (¬ p2177) ∨ (¬ p3548) ∨ (¬ p3362) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2230) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2230) ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3684) ∨ (¬ p4276) ∨ (¬ p4366) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12841 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23585 (meaning t m 2027) (meaning t m 2177) (meaning t m 2230) (meaning t m 3201) (meaning t m 3362) (meaning t m 3548) (meaning t m 3684) (meaning t m 4276) (meaning t m 4366) (meaning t m 4733) source

theorem rule23588 (p3548 p3631 p3657 : Prop) (h : (¬ p3657) ∨ (¬ p3548) ∨ (¬ p3631)) : (¬ p3548) ∨ (¬ p3631) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial23588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory12844 (m.theta 1 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23588 (meaning t m 3548) (meaning t m 3631) (meaning t m 3657) source

theorem rule23589 (p2027 p2140 p2870 p2881 p3551 p4984 : Prop) (h : (¬ p4984) ∨ (¬ p2881) ∨ (¬ p2140) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2140) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial23589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory12845 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule23589 (meaning t m 2027) (meaning t m 2140) (meaning t m 2870) (meaning t m 2881) (meaning t m 3551) (meaning t m 4984) source

theorem rule23591 (p2027 p2246 p2383 p3324 p3987 p4111 p4975 : Prop) (h : (¬ p3987) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p4975) ∨ (¬ p4111) ∨ (¬ p2383) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4111) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12847 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule23591 (meaning t m 2027) (meaning t m 2246) (meaning t m 2383) (meaning t m 3324) (meaning t m 3987) (meaning t m 4111) (meaning t m 4975) source

theorem rule23592 (p2027 p2187 p2387 p2427 p4031 p4198 p4558 : Prop) (h : p2027 ∨ (¬ p4031) ∨ (¬ p4558) ∨ (¬ p2427) ∨ (¬ p2387) ∨ (¬ p2187) ∨ (¬ p4198)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2427) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12848 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule23592 (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2427) (meaning t m 4031) (meaning t m 4198) (meaning t m 4558) source

theorem rule23594 (p2027 p2659 p3027 p3540 p3579 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p3579) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p3540) ∨ (¬ p2659)) : (p2027) ∨ (¬ p2659) ∨ (¬ p3027) ∨ (¬ p3540) ∨ (¬ p3579) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial23594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory12850 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule23594 (meaning t m 2027) (meaning t m 2659) (meaning t m 3027) (meaning t m 3540) (meaning t m 3579) (meaning t m 4111) source

theorem rule23595 (p2027 p2341 p3365 p3367 p3568 p3644 p3759 p4195 p4276 p4734 p5201 : Prop) (h : (¬ p3568) ∨ (¬ p2341) ∨ (¬ p5201) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4276) ∨ (¬ p4195) ∨ (¬ p3365) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3568) ∨ (¬ p3644) ∨ (¬ p3759) ∨ (¬ p4195) ∨ (¬ p4276) ∨ (¬ p4734) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial23595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory12851 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23595 (meaning t m 2027) (meaning t m 2341) (meaning t m 3365) (meaning t m 3367) (meaning t m 3568) (meaning t m 3644) (meaning t m 3759) (meaning t m 4195) (meaning t m 4276) (meaning t m 4734) (meaning t m 5201) source

theorem rule23596 (p2027 p2891 p4111 p4320 p4365 p4704 : Prop) (h : (¬ p4111) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p4365) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2891) ∨ (¬ p4111) ∨ (¬ p4320) ∨ (¬ p4365) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial23596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory12852 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule23596 (meaning t m 2027) (meaning t m 2891) (meaning t m 4111) (meaning t m 4320) (meaning t m 4365) (meaning t m 4704) source

theorem rule23597 (p2027 p2387 p2667 p2810 p2819 p4426 p4975 : Prop) (h : (¬ p4975) ∨ (¬ p4426) ∨ p2027 ∨ (¬ p2667) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p4426) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12853 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule23597 (meaning t m 2027) (meaning t m 2387) (meaning t m 2667) (meaning t m 2810) (meaning t m 2819) (meaning t m 4426) (meaning t m 4975) source

theorem rule23598 (p2027 p2138 p2192 p3541 p3758 p3948 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p3541) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p3948) ∨ (¬ p3758) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2192) ∨ (¬ p3541) ∨ (¬ p3758) ∨ (¬ p3948) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12854 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule23598 (meaning t m 2027) (meaning t m 2138) (meaning t m 2192) (meaning t m 3541) (meaning t m 3758) (meaning t m 3948) (meaning t m 4734) source

theorem rule23600 (p2027 p2166 p2331 p2950 p3948 p4116 p4120 p4975 : Prop) (h : (¬ p3948) ∨ (¬ p4975) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2166) ∨ (¬ p4116) ∨ (¬ p2950)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2331) ∨ (¬ p2950) ∨ (¬ p3948) ∨ (¬ p4116) ∨ (¬ p4120) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12856 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 8)
  exact rule23600 (meaning t m 2027) (meaning t m 2166) (meaning t m 2331) (meaning t m 2950) (meaning t m 3948) (meaning t m 4116) (meaning t m 4120) (meaning t m 4975) source

theorem rule23601 (p2027 p2122 p2313 p2667 p2810 p4426 p4975 : Prop) (h : (¬ p2122) ∨ (¬ p4426) ∨ p2027 ∨ (¬ p2667) ∨ (¬ p2810) ∨ (¬ p4975) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p2810) ∨ (¬ p4426) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12857 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule23601 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2667) (meaning t m 2810) (meaning t m 4426) (meaning t m 4975) source

theorem rule23602 (p2246 p2748 p2811 : Prop) (h : (¬ p2811) ∨ (¬ p2748) ∨ p2246) : (p2246) ∨ (¬ p2748) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial23602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2246) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory12858 (m.theta 0 3) (m.theta 1 3) (m.theta 2 3)
  exact rule23602 (meaning t m 2246) (meaning t m 2748) (meaning t m 2811) source

theorem rule23609 (p2331 p3172 p4349 p4421 : Prop) (h : (¬ p3172) ∨ (¬ p2331) ∨ (¬ p4349) ∨ (¬ p4421)) : (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4349) ∨ (¬ p4421) := by
  classical
  tauto

theorem initial23609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4421)) := by
  have source := ElevenTheory.theory12865 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 3 9)
  exact rule23609 (meaning t m 2331) (meaning t m 3172) (meaning t m 4349) (meaning t m 4421) source

theorem rule23610 (p2027 p2138 p2230 p3367 p3698 p3759 p4734 : Prop) (h : p2027 ∨ (¬ p2138) ∨ (¬ p4734) ∨ (¬ p2230) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12866 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule23610 (meaning t m 2027) (meaning t m 2138) (meaning t m 2230) (meaning t m 3367) (meaning t m 3698) (meaning t m 3759) (meaning t m 4734) source

theorem rule23611 (p2027 p2138 p2911 p3367 p3389 p3690 p3759 p4244 p4666 p4734 : Prop) (h : (¬ p4244) ∨ (¬ p4734) ∨ (¬ p3389) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p4666) ∨ (¬ p2138) ∨ (¬ p3759) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3690) ∨ (¬ p3759) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12867 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23611 (meaning t m 2027) (meaning t m 2138) (meaning t m 2911) (meaning t m 3367) (meaning t m 3389) (meaning t m 3690) (meaning t m 3759) (meaning t m 4244) (meaning t m 4666) (meaning t m 4734) source

theorem rule23612 (p2027 p2138 p2191 p2417 p3367 p3389 p3692 p3759 p3950 p4243 p4734 : Prop) (h : (¬ p4243) ∨ (¬ p2138) ∨ (¬ p3367) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p3950) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p3692) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2191) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3692) ∨ (¬ p3759) ∨ (¬ p3950) ∨ (¬ p4243) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12868 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23612 (meaning t m 2027) (meaning t m 2138) (meaning t m 2191) (meaning t m 2417) (meaning t m 3367) (meaning t m 3389) (meaning t m 3692) (meaning t m 3759) (meaning t m 3950) (meaning t m 4243) (meaning t m 4734) source

theorem rule23613 (p2027 p2459 p2668 p2737 p2797 p3425 p3544 p3576 p4133 p4261 p4734 : Prop) (h : (¬ p4133) ∨ (¬ p4261) ∨ (¬ p2797) ∨ (¬ p3544) ∨ (¬ p4734) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3425) ∨ (¬ p3576) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3425) ∨ (¬ p3544) ∨ (¬ p3576) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12869 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 1 8) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23613 (meaning t m 2027) (meaning t m 2459) (meaning t m 2668) (meaning t m 2737) (meaning t m 2797) (meaning t m 3425) (meaning t m 3544) (meaning t m 3576) (meaning t m 4133) (meaning t m 4261) (meaning t m 4734) source

theorem rule23615 (p1998 p2027 p2138 p2911 p2997 p3097 p3367 p3516 p3759 p4173 p4243 p4278 p4734 p5201 : Prop) (h : (¬ p3367) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p2138) ∨ (¬ p3759) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4734) ∨ (¬ p3516) ∨ (¬ p5201) ∨ (¬ p4278)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2911) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3367) ∨ (¬ p3516) ∨ (¬ p3759) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4278) ∨ (¬ p4734) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial23615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory12871 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23615 (meaning t m 1998) (meaning t m 2027) (meaning t m 2138) (meaning t m 2911) (meaning t m 2997) (meaning t m 3097) (meaning t m 3367) (meaning t m 3516) (meaning t m 3759) (meaning t m 4173) (meaning t m 4243) (meaning t m 4278) (meaning t m 4734) (meaning t m 5201) source

theorem rule23618 (p2027 p2668 p3097 p3309 p3923 p4560 : Prop) (h : (¬ p3309) ∨ (¬ p4560) ∨ (¬ p3097) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p3923)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12874 t (m.theta 1 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23618 (meaning t m 2027) (meaning t m 2668) (meaning t m 3097) (meaning t m 3309) (meaning t m 3923) (meaning t m 4560) source

theorem rule23619 (p2027 p2922 p3055 p3541 p3876 p4734 : Prop) (h : p2027 ∨ (¬ p3055) ∨ (¬ p4734) ∨ (¬ p3876) ∨ (¬ p2922) ∨ (¬ p3541)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3055) ∨ (¬ p3541) ∨ (¬ p3876) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12875 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule23619 (meaning t m 2027) (meaning t m 2922) (meaning t m 3055) (meaning t m 3541) (meaning t m 3876) (meaning t m 4734) source

theorem rule23620 (p2482 p2584 p4197 : Prop) (h : (¬ p4197) ∨ p2584 ∨ (¬ p2482)) : (¬ p2482) ∨ (p2584) ∨ (¬ p4197) := by
  classical
  tauto

theorem initial23620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2482)) ∨ (meaning t m 2584) ∨ (¬ (meaning t m 4197)) := by
  have source := ElevenTheory.theory12876 (m.theta 0 4) (m.theta 0 6) (m.theta 0 8)
  exact rule23620 (meaning t m 2482) (meaning t m 2584) (meaning t m 4197) source

theorem rule23622 (p3367 p3688 p4375 : Prop) (h : (¬ p4375) ∨ (¬ p3367) ∨ (¬ p3688)) : (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial23622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory12878 (m.theta 1 2) (m.theta 2 4) (m.theta 2 6)
  exact rule23622 (meaning t m 3367) (meaning t m 3688) (meaning t m 4375) source

theorem rule23624 (p2027 p2137 p2156 p2274 p2449 p2839 p3425 p4324 p4361 p4734 : Prop) (h : (¬ p2156) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p4361) ∨ (¬ p4324) ∨ (¬ p2449) ∨ (¬ p4734) ∨ (¬ p3425) ∨ (¬ p2274) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2449) ∨ (¬ p2839) ∨ (¬ p3425) ∨ (¬ p4324) ∨ (¬ p4361) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12880 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule23624 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2274) (meaning t m 2449) (meaning t m 2839) (meaning t m 3425) (meaning t m 4324) (meaning t m 4361) (meaning t m 4734) source

theorem rule23625 (p2748 p4154 p4195 : Prop) (h : (¬ p4154) ∨ (¬ p2748) ∨ p4195) : (¬ p2748) ∨ (¬ p4154) ∨ (p4195) := by
  classical
  tauto

theorem initial23625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 4154)) ∨ (meaning t m 4195) := by
  have source := ElevenTheory.theory12881 (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule23625 (meaning t m 2748) (meaning t m 4154) (meaning t m 4195) source

theorem rule23626 (p4383 p4434 p4902 : Prop) (h : (¬ p4383) ∨ (¬ p4902) ∨ p4434) : (¬ p4383) ∨ (p4434) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4383)) ∨ (meaning t m 4434) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12882 t (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule23626 (meaning t m 4383) (meaning t m 4434) (meaning t m 4902) source

theorem rule23630 (p1984 p2027 p2245 p2997 p3172 p3189 p3568 p4154 : Prop) (h : (¬ p2245) ∨ (¬ p1984) ∨ p2997 ∨ p2027 ∨ (¬ p3189) ∨ (¬ p3172) ∨ (¬ p4154) ∨ (¬ p3568)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2997) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial23630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory12886 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule23630 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2997) (meaning t m 3172) (meaning t m 3189) (meaning t m 3568) (meaning t m 4154) source

theorem rule23631 (p2027 p3063 p3324 p4111 p4759 p4975 : Prop) (h : (¬ p4975) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p4759) ∨ (¬ p4111) ∨ (¬ p3324)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3324) ∨ (¬ p4111) ∨ (¬ p4759) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12887 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule23631 (meaning t m 2027) (meaning t m 3063) (meaning t m 3324) (meaning t m 4111) (meaning t m 4759) (meaning t m 4975) source

theorem rule23635 (p1997 p2027 p2230 p2476 p2545 p3189 p4111 p4346 : Prop) (h : (¬ p3189) ∨ (¬ p1997) ∨ (¬ p2476) ∨ (¬ p2230) ∨ (¬ p4346) ∨ p2545 ∨ (¬ p4111) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (p2545) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial23635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory12891 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8)
  exact rule23635 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2545) (meaning t m 3189) (meaning t m 4111) (meaning t m 4346) source

theorem rule23640 (p2027 p2122 p2191 p2396 p2774 p3555 p3692 p3950 p4733 : Prop) (h : (¬ p2122) ∨ (¬ p3555) ∨ (¬ p2774) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2191) ∨ (¬ p2396) ∨ (¬ p2774) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12896 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23640 (meaning t m 2027) (meaning t m 2122) (meaning t m 2191) (meaning t m 2396) (meaning t m 2774) (meaning t m 3555) (meaning t m 3692) (meaning t m 3950) (meaning t m 4733) source

theorem rule23641 (p2027 p3201 p3367 p3540 p3905 p4734 : Prop) (h : (¬ p3540) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3905) ∨ (¬ p4734) ∨ p2027) : (p2027) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12897 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7)
  exact rule23641 (meaning t m 2027) (meaning t m 3201) (meaning t m 3367) (meaning t m 3540) (meaning t m 3905) (meaning t m 4734) source

theorem rule23642 (p2027 p2132 p2284 p2780 p4428 p4906 : Prop) (h : (¬ p2132) ∨ (¬ p2284) ∨ (¬ p4906) ∨ (¬ p4428) ∨ p2027 ∨ (¬ p2780)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2284) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial23642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory12898 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6)
  exact rule23642 (meaning t m 2027) (meaning t m 2132) (meaning t m 2284) (meaning t m 2780) (meaning t m 4428) (meaning t m 4906) source

theorem rule23643 (p3063 p3957 p3989 : Prop) (h : (¬ p3063) ∨ (¬ p3989) ∨ (¬ p3957)) : (¬ p3063) ∨ (¬ p3957) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial23643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory12899 (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule23643 (meaning t m 3063) (meaning t m 3957) (meaning t m 3989) source

theorem rule23646 (p2027 p2137 p2748 p2839 p3051 p3246 p3365 p3950 p4118 p4360 p4734 : Prop) (h : (¬ p4118) ∨ (¬ p4360) ∨ (¬ p2839) ∨ (¬ p3246) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p4734)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12902 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23646 (meaning t m 2027) (meaning t m 2137) (meaning t m 2748) (meaning t m 2839) (meaning t m 3051) (meaning t m 3246) (meaning t m 3365) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4734) source

theorem rule23651 (p2027 p2247 p2573 p3461 p3564 p4360 p5123 p5190 p5600 : Prop) (h : (¬ p2247) ∨ (¬ p2573) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p3564) ∨ (¬ p4360) ∨ (¬ p3461) ∨ (¬ p5600)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4360) ∨ (¬ p5123) ∨ (¬ p5190) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial23651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory12907 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule23651 (meaning t m 2027) (meaning t m 2247) (meaning t m 2573) (meaning t m 3461) (meaning t m 3564) (meaning t m 4360) (meaning t m 5123) (meaning t m 5190) (meaning t m 5600) source

theorem rule23652 (p2027 p2427 p3434 p4382 p4898 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4898) ∨ p2027 ∨ (¬ p4382) ∨ (¬ p2427) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3434) ∨ (¬ p4382) ∨ (¬ p4898) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial23652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4898)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory12908 t (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule23652 (meaning t m 2027) (meaning t m 2427) (meaning t m 3434) (meaning t m 4382) (meaning t m 4898) (meaning t m 4948) source

theorem rule23655 (p2027 p2396 p2553 p2573 p3583 p3951 p3954 p4385 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p3951) ∨ (¬ p3583) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p2553) ∨ (¬ p2396) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3583) ∨ (¬ p3951) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial23655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory12911 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule23655 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3583) (meaning t m 3951) (meaning t m 3954) (meaning t m 4385) (meaning t m 5190) source

theorem rule23657 (p2027 p2177 p2247 p2553 p2573 p2996 p3947 p4666 p5190 : Prop) (h : (¬ p2553) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2573) ∨ (¬ p5190) ∨ (¬ p4666) ∨ (¬ p2996) ∨ (¬ p2177) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial23657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory12913 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23657 (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2553) (meaning t m 2573) (meaning t m 2996) (meaning t m 3947) (meaning t m 4666) (meaning t m 5190) source

theorem rule23658 (p1998 p2027 p2177 p2553 p2573 p2622 p2630 p2656 : Prop) (h : (¬ p2656) ∨ (¬ p1998) ∨ p2622 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2573) ∨ (¬ p2553)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) := by
  classical
  tauto

theorem initial23658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) := by
  have source := ElevenTheory.theory12914 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23658 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) source

theorem rule23660 (p2027 p2630 p3172 p3189 p4111 p4787 : Prop) (h : (¬ p3189) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p4787) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12916 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule23660 (meaning t m 2027) (meaning t m 2630) (meaning t m 3172) (meaning t m 3189) (meaning t m 4111) (meaning t m 4787) source

theorem rule23662 (p2000 p2247 p2688 p4187 p4620 p5190 : Prop) (h : p2688 ∨ (¬ p2247) ∨ (¬ p4187) ∨ p4620 ∨ (¬ p2000) ∨ (¬ p5190)) : (¬ p2000) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p4187) ∨ (p4620) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial23662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 4187)) ∨ (meaning t m 4620) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory12918 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 6 7) (m.theta 6 9)
  exact rule23662 (meaning t m 2000) (meaning t m 2247) (meaning t m 2688) (meaning t m 4187) (meaning t m 4620) (meaning t m 5190) source

theorem rule23663 (p2027 p2437 p2659 p2911 p3551 p5197 : Prop) (h : (¬ p3551) ∨ (¬ p5197) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2659) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2659) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial23663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory12919 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule23663 (meaning t m 2027) (meaning t m 2437) (meaning t m 2659) (meaning t m 2911) (meaning t m 3551) (meaning t m 5197) source

theorem rule23666 (p2027 p2630 p2641 p2963 p3402 p4116 p4787 : Prop) (h : (¬ p3402) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p4116) ∨ (¬ p2963) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p3402) ∨ (¬ p4116) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12922 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule23666 (meaning t m 2027) (meaning t m 2630) (meaning t m 2641) (meaning t m 2963) (meaning t m 3402) (meaning t m 4116) (meaning t m 4787) source

theorem rule23667 (p2027 p2493 p2579 p2630 p2655 p4116 p4787 : Prop) (h : (¬ p2655) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2493) ∨ (¬ p4787)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p4116) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12923 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule23667 (meaning t m 2027) (meaning t m 2493) (meaning t m 2579) (meaning t m 2630) (meaning t m 2655) (meaning t m 4116) (meaning t m 4787) source

theorem rule23669 (p2027 p2963 p3483 p3922 p4026 p4426 p4787 : Prop) (h : (¬ p3922) ∨ (¬ p2963) ∨ (¬ p4787) ∨ (¬ p4026) ∨ (¬ p4426) ∨ (¬ p3483) ∨ p2027) : (p2027) ∨ (¬ p2963) ∨ (¬ p3483) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4426) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12925 t (m.theta 0 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule23669 (meaning t m 2027) (meaning t m 2963) (meaning t m 3483) (meaning t m 3922) (meaning t m 4026) (meaning t m 4426) (meaning t m 4787) source

theorem rule23675 (p3019 p3413 p4336 : Prop) (h : (¬ p3413) ∨ (¬ p4336) ∨ p3019) : (p3019) ∨ (¬ p3413) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial23675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3019) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory12931 (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule23675 (meaning t m 3019) (meaning t m 3413) (meaning t m 4336) source

theorem rule23676 (p2027 p3189 p3989 p4154 p4417 p4560 : Prop) (h : (¬ p4154) ∨ p2027 ∨ (¬ p4417) ∨ (¬ p3189) ∨ (¬ p3989) ∨ (¬ p4560)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3989) ∨ (¬ p4154) ∨ (¬ p4417) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12932 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule23676 (meaning t m 2027) (meaning t m 3189) (meaning t m 3989) (meaning t m 4154) (meaning t m 4417) (meaning t m 4560) source

theorem rule23677 (p2027 p2386 p2641 p3567 p3584 p4111 p4750 : Prop) (h : (¬ p3567) ∨ (¬ p4111) ∨ (¬ p2386) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p3584) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p3584) ∨ (¬ p4111) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12933 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule23677 (meaning t m 2027) (meaning t m 2386) (meaning t m 2641) (meaning t m 3567) (meaning t m 3584) (meaning t m 4111) (meaning t m 4750) source

theorem rule23678 (p2027 p2132 p2870 p3246 p3591 p3923 p3950 p4347 p4733 : Prop) (h : p2027 ∨ (¬ p3591) ∨ (¬ p3950) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3923) ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12934 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23678 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 3246) (meaning t m 3591) (meaning t m 3923) (meaning t m 3950) (meaning t m 4347) (meaning t m 4733) source

theorem rule23680 (p2027 p2264 p2331 p3551 p3580 p4849 p4975 : Prop) (h : (¬ p4975) ∨ (¬ p4849) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3580) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2331) ∨ (¬ p3551) ∨ (¬ p3580) ∨ (¬ p4849) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4849)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12936 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule23680 (meaning t m 2027) (meaning t m 2264) (meaning t m 2331) (meaning t m 3551) (meaning t m 3580) (meaning t m 4849) (meaning t m 4975) source

theorem rule23681 (p2027 p2417 p2598 p3201 p3591 p3923 p3950 p4347 p4733 : Prop) (h : (¬ p2598) ∨ (¬ p4733) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p4347) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12937 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23681 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3591) (meaning t m 3923) (meaning t m 3950) (meaning t m 4347) (meaning t m 4733) source

theorem rule23683 (p2027 p2598 p2911 p3201 p3486 p3555 p3690 p4666 p4733 : Prop) (h : p2027 ∨ (¬ p4666) ∨ (¬ p4733) ∨ (¬ p3690) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12939 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23683 (meaning t m 2027) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4666) (meaning t m 4733) source

theorem rule23684 (p1998 p2027 p2427 p2598 p2766 p2850 p2881 p3591 p3923 p4347 p4733 : Prop) (h : (¬ p3591) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p1998) ∨ p2766 ∨ (¬ p4347) ∨ (¬ p3923) ∨ (¬ p4733) ∨ (¬ p2850) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p2850) ∨ (¬ p2881) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12940 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23684 (meaning t m 1998) (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2766) (meaning t m 2850) (meaning t m 2881) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) (meaning t m 4733) source

theorem rule23685 (p3880 p3988 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p3988) ∨ p3880) : (p3880) ∨ (¬ p3988) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial23685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3880) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory12941 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule23685 (meaning t m 3880) (meaning t m 3988) (meaning t m 4110) source

theorem rule23686 (p2027 p3449 p3452 p4256 p4687 p4814 : Prop) (h : (¬ p4687) ∨ (¬ p4814) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p3452)) : (p2027) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4256) ∨ (¬ p4687) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4687)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12942 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 8)
  exact rule23686 (meaning t m 2027) (meaning t m 3449) (meaning t m 3452) (meaning t m 4256) (meaning t m 4687) (meaning t m 4814) source

theorem rule23687 (p2027 p2563 p2850 p3876 p4001 p4555 : Prop) (h : p2027 ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p2850) ∨ (¬ p4555) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial23687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory12943 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule23687 (meaning t m 2027) (meaning t m 2563) (meaning t m 2850) (meaning t m 3876) (meaning t m 4001) (meaning t m 4555) source

theorem rule23689 (p2027 p2542 p2573 p2589 p3584 p4750 : Prop) (h : (¬ p2589) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3584) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3584) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12945 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule23689 (meaning t m 2027) (meaning t m 2542) (meaning t m 2573) (meaning t m 2589) (meaning t m 3584) (meaning t m 4750) source

theorem rule23690 (p2027 p2505 p3063 p3584 p3956 p5217 : Prop) (h : (¬ p5217) ∨ (¬ p3063) ∨ (¬ p2505) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p3956)) : (p2027) ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial23690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory12946 t (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule23690 (meaning t m 2027) (meaning t m 2505) (meaning t m 3063) (meaning t m 3584) (meaning t m 3956) (meaning t m 5217) source

theorem rule23692 (p2027 p2449 p3580 p3876 p4278 p4750 : Prop) (h : (¬ p3876) ∨ (¬ p3580) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p2449) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12948 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule23692 (meaning t m 2027) (meaning t m 2449) (meaning t m 3580) (meaning t m 3876) (meaning t m 4278) (meaning t m 4750) source

theorem rule23695 (p2027 p2284 p3370 p3413 p3684 p4031 p4173 p4750 : Prop) (h : (¬ p4173) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p2284) ∨ (¬ p4750) ∨ (¬ p3413) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3370) ∨ (¬ p3413) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4173) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12951 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule23695 (meaning t m 2027) (meaning t m 2284) (meaning t m 3370) (meaning t m 3413) (meaning t m 3684) (meaning t m 4031) (meaning t m 4173) (meaning t m 4750) source

theorem rule23696 (p2027 p3201 p3569 p3646 p3684 p4031 p4558 : Prop) (h : (¬ p4031) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4558) ∨ (¬ p3646)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3569) ∨ (¬ p3646) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12952 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule23696 (meaning t m 2027) (meaning t m 3201) (meaning t m 3569) (meaning t m 3646) (meaning t m 3684) (meaning t m 4031) (meaning t m 4558) source

theorem rule23697 (p2027 p2230 p2437 p3540 p3684 p4750 : Prop) (h : (¬ p3684) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p2230) ∨ (¬ p2437) ∨ (¬ p4750)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2437) ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12953 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule23697 (meaning t m 2027) (meaning t m 2230) (meaning t m 2437) (meaning t m 3540) (meaning t m 3684) (meaning t m 4750) source

theorem rule23698 (p3875 p4608 p4644 : Prop) (h : (¬ p4644) ∨ (¬ p3875) ∨ p4608) : (¬ p3875) ∨ (p4608) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3875)) ∨ (meaning t m 4608) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12954 t (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule23698 (meaning t m 3875) (meaning t m 4608) (meaning t m 4644) source

theorem rule23699 (p2027 p3413 p3574 p4272 p4715 p5433 : Prop) (h : (¬ p3574) ∨ (¬ p3413) ∨ (¬ p4715) ∨ (¬ p4272) ∨ (¬ p5433) ∨ p2027) : (p2027) ∨ (¬ p3413) ∨ (¬ p3574) ∨ (¬ p4272) ∨ (¬ p4715) ∨ (¬ p5433) := by
  classical
  tauto

theorem initial23699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5433)) := by
  have source := ElevenTheory.theory12955 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 10)
  exact rule23699 (meaning t m 2027) (meaning t m 3413) (meaning t m 3574) (meaning t m 4272) (meaning t m 4715) (meaning t m 5433) source

theorem rule23700 (p2027 p2166 p2427 p3486 p4120 p4533 : Prop) (h : (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p4533)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3486) ∨ (¬ p4120) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial23700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory12956 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule23700 (meaning t m 2027) (meaning t m 2166) (meaning t m 2427) (meaning t m 3486) (meaning t m 4120) (meaning t m 4533) source

theorem rule23701 (p2027 p2295 p2396 p3690 p4204 p4560 : Prop) (h : (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4560) ∨ (¬ p2396) ∨ (¬ p2295) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12957 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule23701 (meaning t m 2027) (meaning t m 2295) (meaning t m 2396) (meaning t m 3690) (meaning t m 4204) (meaning t m 4560) source

theorem rule23704 (p2027 p3527 p3581 p3644 p4203 p4363 p4431 p5043 : Prop) (h : (¬ p3581) ∨ (¬ p4203) ∨ (¬ p4363) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4431) ∨ (¬ p5043)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4203) ∨ (¬ p4363) ∨ (¬ p4431) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial23704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory12960 t (m.theta 1 5) (m.theta 1 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8)
  exact rule23704 (meaning t m 2027) (meaning t m 3527) (meaning t m 3581) (meaning t m 3644) (meaning t m 4203) (meaning t m 4363) (meaning t m 4431) (meaning t m 5043) source

theorem rule23705 (p2027 p2247 p2982 p3051 p4037 p4154 p4235 p4397 p4399 p5190 : Prop) (h : (¬ p4235) ∨ (¬ p4037) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p2247) ∨ (¬ p3051) ∨ (¬ p4397) ∨ (¬ p5190) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4235) ∨ (¬ p4397) ∨ (¬ p4399) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial23705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory12961 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9)
  exact rule23705 (meaning t m 2027) (meaning t m 2247) (meaning t m 2982) (meaning t m 3051) (meaning t m 4037) (meaning t m 4154) (meaning t m 4235) (meaning t m 4397) (meaning t m 4399) (meaning t m 5190) source

theorem rule23707 (p2027 p3527 p3551 p4244 p4283 p4431 p4878 : Prop) (h : (¬ p4431) ∨ (¬ p4283) ∨ (¬ p3527) ∨ (¬ p4244) ∨ (¬ p3551) ∨ (¬ p4878) ∨ p2027) : (p2027) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4431) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial23707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory12963 t (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule23707 (meaning t m 2027) (meaning t m 3527) (meaning t m 3551) (meaning t m 4244) (meaning t m 4283) (meaning t m 4431) (meaning t m 4878) source

theorem rule23712 (p1990 p2027 p2284 p2611 p2651 p2810 p3136 p4117 : Prop) (h : (¬ p2810) ∨ (¬ p4117) ∨ p2027 ∨ p2611 ∨ (¬ p1990) ∨ (¬ p2284) ∨ (¬ p2651) ∨ (¬ p3136)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial23712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory12968 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule23712 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2611) (meaning t m 2651) (meaning t m 2810) (meaning t m 3136) (meaning t m 4117) source

theorem rule23713 (p2027 p2440 p2891 p3695 p3948 p4244 p4814 : Prop) (h : (¬ p4244) ∨ (¬ p3695) ∨ (¬ p4814) ∨ (¬ p2891) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3948)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2891) ∨ (¬ p3695) ∨ (¬ p3948) ∨ (¬ p4244) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12969 t (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule23713 (meaning t m 2027) (meaning t m 2440) (meaning t m 2891) (meaning t m 3695) (meaning t m 3948) (meaning t m 4244) (meaning t m 4814) source

theorem rule23716 (p2027 p2313 p2505 p2785 p3309 p3574 p4390 p4814 : Prop) (h : (¬ p4390) ∨ (¬ p2785) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p2505) ∨ (¬ p4814) ∨ p2027 ∨ (¬ p3574)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2505) ∨ (¬ p2785) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p4390) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12972 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule23716 (meaning t m 2027) (meaning t m 2313) (meaning t m 2505) (meaning t m 2785) (meaning t m 3309) (meaning t m 3574) (meaning t m 4390) (meaning t m 4814) source

theorem rule23717 (p2027 p2264 p2685 p2696 p3486 p3555 p3690 p4666 p4733 : Prop) (h : (¬ p3690) ∨ (¬ p2685) ∨ (¬ p3555) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4733) ∨ (¬ p2264) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12973 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23717 (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4666) (meaning t m 4733) source

theorem rule23719 (p2027 p2191 p2449 p2685 p2696 p3555 p3692 p3950 p4733 : Prop) (h : (¬ p2696) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2191) ∨ (¬ p4733) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p2685) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12975 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23719 (meaning t m 2027) (meaning t m 2191) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 3555) (meaning t m 3692) (meaning t m 3950) (meaning t m 4733) source

theorem rule23720 (p2027 p2696 p3115 p3136 p3591 p3923 p4347 p4450 p4733 : Prop) (h : (¬ p3923) ∨ (¬ p4450) ∨ (¬ p3591) ∨ (¬ p3136) ∨ (¬ p3115) ∨ (¬ p2696) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12976 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule23720 (meaning t m 2027) (meaning t m 2696) (meaning t m 3115) (meaning t m 3136) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) (meaning t m 4450) (meaning t m 4733) source

theorem rule23721 (p2027 p3201 p3370 p3684 p3742 p3948 p4031 p4814 : Prop) (h : (¬ p4814) ∨ (¬ p3948) ∨ (¬ p3742) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p3684) ∨ (¬ p3201)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3370) ∨ (¬ p3684) ∨ (¬ p3742) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12977 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule23721 (meaning t m 2027) (meaning t m 3201) (meaning t m 3370) (meaning t m 3684) (meaning t m 3742) (meaning t m 3948) (meaning t m 4031) (meaning t m 4814) source

theorem rule23722 (p2027 p2476 p2534 p2696 p2753 p2797 p3347 p4228 p4444 p5216 p5250 : Prop) (h : (¬ p2696) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p4228) ∨ (¬ p2797) ∨ (¬ p2476) ∨ (¬ p4444) ∨ (¬ p2534) ∨ (¬ p5250)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3347) ∨ (¬ p4228) ∨ (¬ p4444) ∨ (¬ p5216) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial23722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory12978 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23722 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3347) (meaning t m 4228) (meaning t m 4444) (meaning t m 5216) (meaning t m 5250) source

theorem rule23723 (p2027 p3758 p4053 p4338 p4393 p4878 : Prop) (h : p2027 ∨ (¬ p4878) ∨ (¬ p4393) ∨ (¬ p4338) ∨ (¬ p3758) ∨ (¬ p4053)) : (p2027) ∨ (¬ p3758) ∨ (¬ p4053) ∨ (¬ p4338) ∨ (¬ p4393) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial23723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory12979 t (m.theta 1 5) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 10)
  exact rule23723 (meaning t m 2027) (meaning t m 3758) (meaning t m 4053) (meaning t m 4338) (meaning t m 4393) (meaning t m 4878) source

theorem rule23725 (p2027 p2685 p2696 p3555 p3931 p4322 p4363 p4733 p4826 : Prop) (h : (¬ p4322) ∨ (¬ p2696) ∨ (¬ p2685) ∨ (¬ p4363) ∨ (¬ p4733) ∨ (¬ p3555) ∨ (¬ p3931) ∨ (¬ p4826) ∨ p2027) : (p2027) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3555) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4733) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory12981 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule23725 (meaning t m 2027) (meaning t m 2685) (meaning t m 2696) (meaning t m 3555) (meaning t m 3931) (meaning t m 4322) (meaning t m 4363) (meaning t m 4733) (meaning t m 4826) source

theorem rule23726 (p2027 p2313 p2505 p3309 p3684 p4031 p4198 p5217 : Prop) (h : (¬ p2313) ∨ (¬ p4198) ∨ (¬ p2505) ∨ (¬ p3309) ∨ (¬ p4031) ∨ (¬ p3684) ∨ (¬ p5217) ∨ p2027) : (p2027) ∨ (¬ p2313) ∨ (¬ p2505) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial23726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory12982 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 6 7)
  exact rule23726 (meaning t m 2027) (meaning t m 2313) (meaning t m 2505) (meaning t m 3309) (meaning t m 3684) (meaning t m 4031) (meaning t m 4198) (meaning t m 5217) source

theorem rule23727 (p2027 p2088 p3180 p3266 p4349 p5284 : Prop) (h : (¬ p3180) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p3266) ∨ (¬ p4349) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3180) ∨ (¬ p3266) ∨ (¬ p4349) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial23727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3180)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory12983 t (m.theta 0 8) (m.theta 3 8) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23727 (meaning t m 2027) (meaning t m 2088) (meaning t m 3180) (meaning t m 3266) (meaning t m 4349) (meaning t m 5284) source

theorem rule23728 (p2027 p2696 p2797 p3323 p3548 p4330 p4348 p4366 p4733 : Prop) (h : (¬ p4330) ∨ (¬ p2696) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p4366) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12984 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23728 (meaning t m 2027) (meaning t m 2696) (meaning t m 2797) (meaning t m 3323) (meaning t m 3548) (meaning t m 4330) (meaning t m 4348) (meaning t m 4366) (meaning t m 4733) source

theorem rule23730 (p2220 p2373 p4031 : Prop) (h : (¬ p4031) ∨ (¬ p2373) ∨ p2220) : (p2220) ∨ (¬ p2373) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial23730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2220) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory12986 (m.theta 0 5) (m.theta 4 5) (m.theta 5 8)
  exact rule23730 (meaning t m 2220) (meaning t m 2373) (meaning t m 4031) source

theorem rule23731 (p2145 p2753 p3645 p4877 : Prop) (h : (¬ p4877) ∨ (¬ p3645) ∨ (¬ p2753) ∨ p2145) : (p2145) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2145) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12987 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5)
  exact rule23731 (meaning t m 2145) (meaning t m 2753) (meaning t m 3645) (meaning t m 4877) source

theorem rule23733 (p2027 p2696 p2753 p2797 p3556 p3645 p3690 p4228 p4381 p4877 p5250 : Prop) (h : (¬ p4228) ∨ (¬ p5250) ∨ (¬ p2797) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p3556) ∨ (¬ p4877) ∨ (¬ p4381) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4228) ∨ (¬ p4381) ∨ (¬ p4877) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial23733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory12989 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule23733 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3556) (meaning t m 3645) (meaning t m 3690) (meaning t m 4228) (meaning t m 4381) (meaning t m 4877) (meaning t m 5250) source

theorem rule23734 (p2027 p2210 p3222 p3346 p3541 p4108 p4877 : Prop) (h : (¬ p4108) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p3541) ∨ (¬ p3346) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12990 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 9)
  exact rule23734 (meaning t m 2027) (meaning t m 2210) (meaning t m 3222) (meaning t m 3346) (meaning t m 3541) (meaning t m 4108) (meaning t m 4877) source

theorem rule23735 (p2027 p2331 p2589 p3005 p3570 p4117 p4195 p4235 p4550 p4729 : Prop) (h : (¬ p2589) ∨ (¬ p4550) ∨ (¬ p4729) ∨ (¬ p4195) ∨ (¬ p4235) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3005) ∨ (¬ p3570) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4235) ∨ (¬ p4550) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory12991 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule23735 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 3005) (meaning t m 3570) (meaning t m 4117) (meaning t m 4195) (meaning t m 4235) (meaning t m 4550) (meaning t m 4729) source

theorem rule23736 (p2027 p2132 p2860 p3551 p3737 p4348 p4444 p4729 p5197 p5250 : Prop) (h : (¬ p4444) ∨ (¬ p4348) ∨ (¬ p3551) ∨ (¬ p4729) ∨ (¬ p2860) ∨ (¬ p5197) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p5250) ∨ (¬ p3737)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3551) ∨ (¬ p3737) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4729) ∨ (¬ p5197) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial23736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5197)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory12992 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 2 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule23736 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3551) (meaning t m 3737) (meaning t m 4348) (meaning t m 4444) (meaning t m 4729) (meaning t m 5197) (meaning t m 5250) source

theorem rule23737 (p2027 p2132 p2860 p2911 p3125 p3551 p4278 p4621 p4729 p5197 : Prop) (h : (¬ p4729) ∨ (¬ p3551) ∨ (¬ p5197) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p3125) ∨ (¬ p4621) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2911) ∨ (¬ p3125) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4729) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial23737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory12993 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule23737 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 2911) (meaning t m 3125) (meaning t m 3551) (meaning t m 4278) (meaning t m 4621) (meaning t m 4729) (meaning t m 5197) source

theorem rule23738 (p2027 p2132 p2860 p3125 p3540 p3644 p4330 p4348 p4729 : Prop) (h : (¬ p4729) ∨ (¬ p3644) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p4330) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory12994 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23738 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3125) (meaning t m 3540) (meaning t m 3644) (meaning t m 4330) (meaning t m 4348) (meaning t m 4729) source

theorem rule23739 (p2001 p2027 p2247 p2688 p3256 p3449 p3692 p4288 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2247) ∨ (¬ p2001) ∨ (¬ p4288) ∨ (¬ p3256) ∨ (¬ p3449)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3256) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p4288) := by
  classical
  tauto

theorem initial23739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4288)) := by
  have source := ElevenTheory.theory12995 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule23739 (meaning t m 2001) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3256) (meaning t m 3449) (meaning t m 3692) (meaning t m 4288) source

theorem rule23741 (p2027 p2331 p2427 p3005 p3556 p3880 p3904 p4117 p4195 p4729 p5063 : Prop) (h : (¬ p4117) ∨ (¬ p3005) ∨ (¬ p5063) ∨ (¬ p4195) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p3880) ∨ (¬ p2427) ∨ (¬ p4729)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2427) ∨ (¬ p3005) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4729) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial23741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory12997 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule23741 (meaning t m 2027) (meaning t m 2331) (meaning t m 2427) (meaning t m 3005) (meaning t m 3556) (meaning t m 3880) (meaning t m 3904) (meaning t m 4117) (meaning t m 4195) (meaning t m 4729) (meaning t m 5063) source

theorem rule23742 (p2027 p2427 p2533 p3166 p3256 p3556 p3904 p4117 p4134 p4347 p4729 p4948 : Prop) (h : (¬ p4729) ∨ (¬ p4134) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4347) ∨ (¬ p2427) ∨ (¬ p3904) ∨ p2027 ∨ (¬ p2533) ∨ (¬ p3556) ∨ (¬ p4948) ∨ (¬ p4117)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2533) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4117) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4729) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial23742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory12998 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule23742 (meaning t m 2027) (meaning t m 2427) (meaning t m 2533) (meaning t m 3166) (meaning t m 3256) (meaning t m 3556) (meaning t m 3904) (meaning t m 4117) (meaning t m 4134) (meaning t m 4347) (meaning t m 4729) (meaning t m 4948) source

theorem rule23745 (p2027 p2331 p2589 p2753 p3347 p3690 p3755 p4117 p4195 p4235 p4658 p5216 : Prop) (h : (¬ p4235) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4658) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p3690) ∨ (¬ p3347) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3690) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4235) ∨ (¬ p4658) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4658)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13001 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule23745 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 2753) (meaning t m 3347) (meaning t m 3690) (meaning t m 3755) (meaning t m 4117) (meaning t m 4195) (meaning t m 4235) (meaning t m 4658) (meaning t m 5216) source

theorem rule23746 (p2027 p2807 p2963 p3324 p3552 p4501 : Prop) (h : (¬ p2963) ∨ (¬ p3552) ∨ (¬ p3324) ∨ (¬ p2807) ∨ (¬ p4501) ∨ p2027) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3552) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial23746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory13002 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8)
  exact rule23746 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3324) (meaning t m 3552) (meaning t m 4501) source

theorem rule23747 (p1994 p2027 p2299 p2630 p2633 p2963 p3361 p3568 : Prop) (h : p2633 ∨ (¬ p2630) ∨ (¬ p2963) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p2299) ∨ (¬ p3568)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial23747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory13003 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23747 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2630) (meaning t m 2633) (meaning t m 2963) (meaning t m 3361) (meaning t m 3568) source

theorem rule23748 (p2027 p2156 p3954 p4172 p4173 p4877 : Prop) (h : (¬ p4172) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4877) ∨ (¬ p3954) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13004 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6)
  exact rule23748 (meaning t m 2027) (meaning t m 2156) (meaning t m 3954) (meaning t m 4172) (meaning t m 4173) (meaning t m 4877) source

theorem rule23749 (p2027 p2192 p2210 p3860 p3906 p4507 : Prop) (h : (¬ p3860) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3906) ∨ p2027 ∨ (¬ p4507)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory13005 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 8)
  exact rule23749 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 3860) (meaning t m 3906) (meaning t m 4507) source

theorem rule23750 (p2027 p2579 p2588 p3347 p3399 p3527 p3954 p4107 p4666 p5216 : Prop) (h : p2027 ∨ (¬ p3399) ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p4666) ∨ (¬ p3527) ∨ (¬ p4107) ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13006 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23750 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3347) (meaning t m 3399) (meaning t m 3527) (meaning t m 3954) (meaning t m 4107) (meaning t m 4666) (meaning t m 5216) source

theorem rule23751 (p2027 p2143 p2373 p3969 p4197 p4198 p4882 p5590 : Prop) (h : (¬ p2143) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p4882) ∨ (¬ p2373) ∨ (¬ p4198) ∨ (¬ p5590) ∨ (¬ p4197)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2373) ∨ (¬ p3969) ∨ (¬ p4197) ∨ (¬ p4198) ∨ (¬ p4882) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial23751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory13007 t (m.theta 0 5) (m.theta 0 6) (m.theta 0 8) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10)
  exact rule23751 (meaning t m 2027) (meaning t m 2143) (meaning t m 2373) (meaning t m 3969) (meaning t m 4197) (meaning t m 4198) (meaning t m 4882) (meaning t m 5590) source

theorem rule23755 (p2027 p2579 p2588 p3166 p3755 p3877 p4107 p4117 p4658 p4729 : Prop) (h : (¬ p2588) ∨ (¬ p4658) ∨ (¬ p3877) ∨ (¬ p3166) ∨ (¬ p3755) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2579) ∨ (¬ p4117)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3166) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4658) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4658)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory13011 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule23755 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3166) (meaning t m 3755) (meaning t m 3877) (meaning t m 4107) (meaning t m 4117) (meaning t m 4658) (meaning t m 4729) source

theorem rule23756 (p2027 p3343 p4256 p4286 p4695 p5118 : Prop) (h : (¬ p4695) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p3343) ∨ (¬ p4286)) : (p2027) ∨ (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4695) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial23756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4695)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory13012 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 10) (m.theta 8 9)
  exact rule23756 (meaning t m 2027) (meaning t m 3343) (meaning t m 4256) (meaning t m 4286) (meaning t m 4695) (meaning t m 5118) source

theorem rule23757 (p2027 p2696 p2753 p3005 p3556 p3645 p3690 p4009 p4381 p4877 p5119 : Prop) (h : (¬ p3005) ∨ (¬ p4381) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p3645) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p4009) ∨ (¬ p2753) ∨ (¬ p4877)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4009) ∨ (¬ p4381) ∨ (¬ p4877) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial23757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory13013 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule23757 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3556) (meaning t m 3645) (meaning t m 3690) (meaning t m 4009) (meaning t m 4381) (meaning t m 4877) (meaning t m 5119) source

theorem rule23758 (p2027 p2459 p2630 p2696 p2753 p3083 p3556 p3645 p3692 p4119 p4420 p4877 : Prop) (h : (¬ p2753) ∨ (¬ p3083) ∨ (¬ p4119) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4877) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p2459) ∨ (¬ p4420)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4420) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13014 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23758 (meaning t m 2027) (meaning t m 2459) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 3083) (meaning t m 3556) (meaning t m 3645) (meaning t m 3692) (meaning t m 4119) (meaning t m 4420) (meaning t m 4877) source

theorem rule23759 (p2027 p2630 p2696 p2753 p3097 p3343 p3645 p3646 p4107 p4638 p4877 : Prop) (h : (¬ p4638) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3097) ∨ (¬ p2630) ∨ (¬ p3646) ∨ (¬ p2696) ∨ (¬ p3645) ∨ (¬ p4107) ∨ (¬ p4877)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3343) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13015 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule23759 (meaning t m 2027) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 3097) (meaning t m 3343) (meaning t m 3645) (meaning t m 3646) (meaning t m 4107) (meaning t m 4638) (meaning t m 4877) source

theorem rule23760 (p1997 p2027 p2441 p2462 p3097 p3399 p3527 p3644 p3645 p3646 p3954 p4107 p4877 : Prop) (h : (¬ p3644) ∨ (¬ p1997) ∨ (¬ p3954) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2441) ∨ p2462 ∨ (¬ p3645) ∨ (¬ p4877) ∨ (¬ p3097) ∨ (¬ p4107) ∨ (¬ p3399) ∨ (¬ p3527)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2441) ∨ (p2462) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13016 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23760 (meaning t m 1997) (meaning t m 2027) (meaning t m 2441) (meaning t m 2462) (meaning t m 3097) (meaning t m 3399) (meaning t m 3527) (meaning t m 3644) (meaning t m 3645) (meaning t m 3646) (meaning t m 3954) (meaning t m 4107) (meaning t m 4877) source

theorem rule23762 (p2027 p2299 p2313 p3083 p3204 p3683 p4024 p4420 p5220 : Prop) (h : (¬ p3683) ∨ (¬ p4420) ∨ (¬ p3083) ∨ (¬ p2299) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3204) ∨ (¬ p4024) ∨ (¬ p5220)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p3083) ∨ (¬ p3204) ∨ (¬ p3683) ∨ (¬ p4024) ∨ (¬ p4420) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial23762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory13018 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23762 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 3083) (meaning t m 3204) (meaning t m 3683) (meaning t m 4024) (meaning t m 4420) (meaning t m 5220) source

theorem rule23763 (p3922 p4024 p4328 : Prop) (h : p3922 ∨ (¬ p4328) ∨ (¬ p4024)) : (p3922) ∨ (¬ p4024) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial23763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3922) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory13019 (m.theta 1 6) (m.theta 2 6) (m.theta 3 6)
  exact rule23763 (meaning t m 3922) (meaning t m 4024) (meaning t m 4328) source

theorem rule23764 (p2027 p2589 p2696 p2753 p3347 p3570 p3609 p4118 p4235 p4373 p4550 p5216 : Prop) (h : p2027 ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p5216) ∨ (¬ p4118) ∨ (¬ p2696) ∨ (¬ p4373) ∨ (¬ p2753) ∨ (¬ p4550) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3570) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4235) ∨ (¬ p4373) ∨ (¬ p4550) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4373)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13020 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule23764 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 2753) (meaning t m 3347) (meaning t m 3570) (meaning t m 3609) (meaning t m 4118) (meaning t m 4235) (meaning t m 4373) (meaning t m 4550) (meaning t m 5216) source

theorem rule23766 (p2027 p2245 p2696 p3005 p3292 p4733 p5111 : Prop) (h : p2027 ∨ (¬ p2245) ∨ (¬ p5111) ∨ (¬ p3292) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3292) ∨ (¬ p4733) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial23766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory13022 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9)
  exact rule23766 (meaning t m 2027) (meaning t m 2245) (meaning t m 2696) (meaning t m 3005) (meaning t m 3292) (meaning t m 4733) (meaning t m 5111) source

theorem rule23767 (p4243 p4629 p4882 : Prop) (h : (¬ p4243) ∨ (¬ p4882) ∨ p4629) : (¬ p4243) ∨ (p4629) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial23767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4243)) ∨ (meaning t m 4629) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory13023 t (m.theta 1 5) (m.theta 2 5) (m.theta 4 5)
  exact rule23767 (meaning t m 4243) (meaning t m 4629) (meaning t m 4882) source

theorem rule23768 (p2027 p2579 p2696 p3005 p3256 p3956 p4729 p5118 p5580 : Prop) (h : (¬ p5118) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p5580) ∨ (¬ p2579) ∨ (¬ p3956) ∨ (¬ p4729) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3956) ∨ (¬ p4729) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13024 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23768 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3956) (meaning t m 4729) (meaning t m 5118) (meaning t m 5580) source

theorem rule23769 (p2027 p2098 p2299 p2534 p2753 p3097 p3609 p3645 p3646 p4420 p4877 : Prop) (h : (¬ p2753) ∨ (¬ p3646) ∨ (¬ p4877) ∨ (¬ p3609) ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p4420) ∨ (¬ p3645) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2534)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p2534) ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3609) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13025 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule23769 (meaning t m 2027) (meaning t m 2098) (meaning t m 2299) (meaning t m 2534) (meaning t m 2753) (meaning t m 3097) (meaning t m 3609) (meaning t m 3645) (meaning t m 3646) (meaning t m 4420) (meaning t m 4877) source

theorem rule23770 (p2027 p2246 p2651 p2749 p3276 p3333 p3645 p3646 p3989 p4343 p4877 p5123 p5580 : Prop) (h : (¬ p5123) ∨ (¬ p4343) ∨ (¬ p3645) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p2749) ∨ (¬ p2651) ∨ (¬ p4877) ∨ (¬ p2246) ∨ (¬ p3333) ∨ (¬ p3989) ∨ (¬ p5580) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4343) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory13026 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23770 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2749) (meaning t m 3276) (meaning t m 3333) (meaning t m 3645) (meaning t m 3646) (meaning t m 3989) (meaning t m 4343) (meaning t m 4877) (meaning t m 5123) (meaning t m 5580) source

theorem rule23771 (p2027 p2651 p2753 p2810 p3204 p3266 p3755 p3946 p4117 p4191 p4512 p4877 p5109 : Prop) (h : (¬ p4191) ∨ (¬ p4512) ∨ (¬ p5109) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p2651) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p3204) ∨ (¬ p3946) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2753) ∨ (¬ p2810) ∨ (¬ p3204) ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p3946) ∨ (¬ p4117) ∨ (¬ p4191) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial23771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory13027 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23771 (meaning t m 2027) (meaning t m 2651) (meaning t m 2753) (meaning t m 2810) (meaning t m 3204) (meaning t m 3266) (meaning t m 3755) (meaning t m 3946) (meaning t m 4117) (meaning t m 4191) (meaning t m 4512) (meaning t m 4877) (meaning t m 5109) source

theorem rule23772 (p2027 p3093 p3319 p4366 p4427 p4624 : Prop) (h : p2027 ∨ (¬ p4427) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4624) ∨ (¬ p3319)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13028 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9)
  exact rule23772 (meaning t m 2027) (meaning t m 3093) (meaning t m 3319) (meaning t m 4366) (meaning t m 4427) (meaning t m 4624) source

theorem rule23773 (p2598 p3379 p3873 p4030 : Prop) (h : (¬ p3379) ∨ (¬ p3873) ∨ (¬ p4030) ∨ p2598) : (p2598) ∨ (¬ p3379) ∨ (¬ p3873) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial23773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2598) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory13029 (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 4)
  exact rule23773 (meaning t m 2598) (meaning t m 3379) (meaning t m 3873) (meaning t m 4030) source

theorem rule23776 (p2027 p2406 p2437 p2928 p3684 p4750 : Prop) (h : (¬ p2437) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p2928) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2437) ∨ (¬ p2928) ∨ (¬ p3684) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory13032 t (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule23776 (meaning t m 2027) (meaning t m 2406) (meaning t m 2437) (meaning t m 2928) (meaning t m 3684) (meaning t m 4750) source

theorem rule23777 (p2027 p2810 p2951 p3136 p3742 p4031 p4644 : Prop) (h : (¬ p2951) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p2810) ∨ (¬ p4644) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3742) ∨ (¬ p4031) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13033 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule23777 (meaning t m 2027) (meaning t m 2810) (meaning t m 2951) (meaning t m 3136) (meaning t m 3742) (meaning t m 4031) (meaning t m 4644) source

theorem rule23778 (p2027 p2850 p3367 p3588 p4106 p4644 : Prop) (h : (¬ p4106) ∨ (¬ p3588) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p4644) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13034 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7)
  exact rule23778 (meaning t m 2027) (meaning t m 2850) (meaning t m 3367) (meaning t m 3588) (meaning t m 4106) (meaning t m 4644) source

theorem rule23779 (p2027 p3325 p3654 p3979 p4197 p4624 p5590 : Prop) (h : (¬ p3325) ∨ (¬ p5590) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p3654) ∨ (¬ p4624) ∨ (¬ p4197)) : (p2027) ∨ (¬ p3325) ∨ (¬ p3654) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p4624) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial23779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory13035 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule23779 (meaning t m 2027) (meaning t m 3325) (meaning t m 3654) (meaning t m 3979) (meaning t m 4197) (meaning t m 4624) (meaning t m 5590) source

theorem rule23780 (p2027 p2685 p2761 p2952 p3516 p3694 p4066 p4787 p5051 p5123 p5568 : Prop) (h : (¬ p3516) ∨ (¬ p2761) ∨ (¬ p5051) ∨ (¬ p2952) ∨ (¬ p3694) ∨ (¬ p4066) ∨ (¬ p4787) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3516) ∨ (¬ p3694) ∨ (¬ p4066) ∨ (¬ p4787) ∨ (¬ p5051) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial23780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5051)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13036 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule23780 (meaning t m 2027) (meaning t m 2685) (meaning t m 2761) (meaning t m 2952) (meaning t m 3516) (meaning t m 3694) (meaning t m 4066) (meaning t m 4787) (meaning t m 5051) (meaning t m 5123) (meaning t m 5568) source

theorem rule23781 (p2027 p2177 p2311 p3551 p3654 p4624 : Prop) (h : (¬ p3654) ∨ (¬ p4624) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2311) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3551) ∨ (¬ p3654) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13037 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule23781 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 3551) (meaning t m 3654) (meaning t m 4624) source

theorem rule23782 (p2027 p2254 p2922 p2950 p3379 p3868 p4118 p4120 p4311 p4444 p4826 : Prop) (h : (¬ p3379) ∨ (¬ p3868) ∨ (¬ p2922) ∨ (¬ p4118) ∨ (¬ p4120) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2950) ∨ (¬ p4311) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3868) ∨ (¬ p4118) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13038 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 8) (m.theta 4 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23782 (meaning t m 2027) (meaning t m 2254) (meaning t m 2922) (meaning t m 2950) (meaning t m 3379) (meaning t m 3868) (meaning t m 4118) (meaning t m 4120) (meaning t m 4311) (meaning t m 4444) (meaning t m 4826) source

theorem rule23783 (p2027 p2254 p2963 p3222 p3276 p3379 p3568 p4260 p4831 : Prop) (h : (¬ p3568) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4260) ∨ (¬ p3379) ∨ (¬ p3222) ∨ (¬ p2254) ∨ (¬ p3276) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial23783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory13039 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule23783 (meaning t m 2027) (meaning t m 2254) (meaning t m 2963) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 3568) (meaning t m 4260) (meaning t m 4831) source

theorem rule23785 (p2027 p2254 p2963 p3233 p3324 p3379 p3707 p4332 p4347 p4425 : Prop) (h : (¬ p2963) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4332) ∨ (¬ p2254) ∨ (¬ p3233) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3233) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3707) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial23785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory13041 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 1 9) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule23785 (meaning t m 2027) (meaning t m 2254) (meaning t m 2963) (meaning t m 3233) (meaning t m 3324) (meaning t m 3379) (meaning t m 3707) (meaning t m 4332) (meaning t m 4347) (meaning t m 4425) source

theorem rule23787 (p2027 p2598 p3172 p3201 p3868 p4118 p4444 p4789 p4826 : Prop) (h : (¬ p4444) ∨ (¬ p4789) ∨ (¬ p3868) ∨ (¬ p3201) ∨ (¬ p4118) ∨ (¬ p2598) ∨ (¬ p3172) ∨ (¬ p4826) ∨ p2027) : (p2027) ∨ (¬ p2598) ∨ (¬ p3172) ∨ (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13043 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23787 (meaning t m 2027) (meaning t m 2598) (meaning t m 3172) (meaning t m 3201) (meaning t m 3868) (meaning t m 4118) (meaning t m 4444) (meaning t m 4789) (meaning t m 4826) source

theorem rule23788 (p2027 p2220 p2534 p3146 p4539 p4607 : Prop) (h : (¬ p3146) ∨ (¬ p4539) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2534) ∨ (¬ p4607)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p4539) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial23788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4539)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory13044 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule23788 (meaning t m 2027) (meaning t m 2220) (meaning t m 2534) (meaning t m 3146) (meaning t m 4539) (meaning t m 4607) source

theorem rule23789 (p2027 p2220 p2850 p3693 p3874 p4539 : Prop) (h : (¬ p2850) ∨ (¬ p3693) ∨ (¬ p2220) ∨ (¬ p4539) ∨ (¬ p3874) ∨ p2027) : (p2027) ∨ (¬ p2220) ∨ (¬ p2850) ∨ (¬ p3693) ∨ (¬ p3874) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial23789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13045 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule23789 (meaning t m 2027) (meaning t m 2220) (meaning t m 2850) (meaning t m 3693) (meaning t m 3874) (meaning t m 4539) source

theorem rule23790 (p2027 p2156 p2406 p2499 p3096 p4539 : Prop) (h : (¬ p3096) ∨ (¬ p2406) ∨ (¬ p4539) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2499)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial23790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13046 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule23790 (meaning t m 2027) (meaning t m 2156) (meaning t m 2406) (meaning t m 2499) (meaning t m 3096) (meaning t m 4539) source

theorem rule23795 (p1976 p2027 p2589 p2619 p2914 p3582 p3876 p3880 p3905 : Prop) (h : p2027 ∨ (¬ p3876) ∨ (¬ p3582) ∨ (¬ p2619) ∨ (¬ p1976) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3905) ∨ p2914) : (¬ p1976) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2619) ∨ (p2914) ∨ (¬ p3582) ∨ (¬ p3876) ∨ (¬ p3880) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial23795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory13051 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8)
  exact rule23795 (meaning t m 1976) (meaning t m 2027) (meaning t m 2589) (meaning t m 2619) (meaning t m 2914) (meaning t m 3582) (meaning t m 3876) (meaning t m 3880) (meaning t m 3905) source

theorem rule23796 (p1976 p2027 p2589 p2633 p2850 p3644 p3876 p3905 : Prop) (h : (¬ p1976) ∨ (¬ p2850) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2589) ∨ p2633 ∨ (¬ p3876)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p2850) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial23796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory13052 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule23796 (meaning t m 1976) (meaning t m 2027) (meaning t m 2589) (meaning t m 2633) (meaning t m 2850) (meaning t m 3644) (meaning t m 3876) (meaning t m 3905) source

theorem rule23797 (p2027 p2264 p2441 p3580 p3644 p3684 p4750 : Prop) (h : (¬ p4750) ∨ (¬ p3684) ∨ (¬ p3580) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2441) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2441) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p3684) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory13053 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule23797 (meaning t m 2027) (meaning t m 2264) (meaning t m 2441) (meaning t m 3580) (meaning t m 3644) (meaning t m 3684) (meaning t m 4750) source

theorem rule23799 (p2441 p3684 p3876 : Prop) (h : (¬ p2441) ∨ (¬ p3684) ∨ p3876) : (¬ p2441) ∨ (¬ p3684) ∨ (p3876) := by
  classical
  tauto

theorem initial23799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3684)) ∨ (meaning t m 3876) := by
  have source := ElevenTheory.theory13055 (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule23799 (meaning t m 2441) (meaning t m 3684) (meaning t m 3876) source

theorem rule23801 (p3362 p3873 p4079 : Prop) (h : (¬ p3873) ∨ p3362 ∨ (¬ p4079)) : (p3362) ∨ (¬ p3873) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial23801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3362) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory13057 (m.theta 0 1) (m.theta 0 2) (m.theta 0 4)
  exact rule23801 (meaning t m 3362) (meaning t m 3873) (meaning t m 4079) source

theorem rule23802 (p2027 p2299 p2373 p4042 p4235 p4559 : Prop) (h : (¬ p2373) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p2299) ∨ (¬ p4042)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p4042) ∨ (¬ p4235) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial23802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory13058 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23802 (meaning t m 2027) (meaning t m 2299) (meaning t m 2373) (meaning t m 4042) (meaning t m 4235) (meaning t m 4559) source

theorem rule23803 (p2027 p2138 p2493 p2553 p3379 p3758 p3989 p4501 p4736 : Prop) (h : (¬ p3758) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3989) ∨ (¬ p4736) ∨ (¬ p2553) ∨ (¬ p4501) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3379) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4501) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13059 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23803 (meaning t m 2027) (meaning t m 2138) (meaning t m 2493) (meaning t m 2553) (meaning t m 3379) (meaning t m 3758) (meaning t m 3989) (meaning t m 4501) (meaning t m 4736) source

theorem rule23804 (p1987 p2611 p2696 p4117 p4786 : Prop) (h : p2611 ∨ (¬ p2696) ∨ (¬ p1987) ∨ p4786 ∨ (¬ p4117)) : (¬ p1987) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p4117) ∨ (p4786) := by
  classical
  tauto

theorem initial23804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4117)) ∨ (meaning t m 4786) := by
  have source := ElevenTheory.theory13060 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3)
  exact rule23804 (meaning t m 1987) (meaning t m 2611) (meaning t m 2696) (meaning t m 4117) (meaning t m 4786) source

theorem rule23807 (p2027 p2493 p3379 p3425 p3564 p3659 p4330 p4348 p4736 : Prop) (h : (¬ p4348) ∨ (¬ p3379) ∨ (¬ p4330) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p3564) ∨ (¬ p2493)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3564) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13063 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23807 (meaning t m 2027) (meaning t m 2493) (meaning t m 3379) (meaning t m 3425) (meaning t m 3564) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) (meaning t m 4736) source

theorem rule23808 (p2027 p2440 p2665 p3051 p4235 p4399 : Prop) (h : (¬ p2665) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2440) ∨ (¬ p4235) ∨ (¬ p4399)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2665) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial23808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory13064 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule23808 (meaning t m 2027) (meaning t m 2440) (meaning t m 2665) (meaning t m 3051) (meaning t m 4235) (meaning t m 4399) source

theorem rule23810 (p2027 p2542 p2563 p3359 p4947 p5043 : Prop) (h : p2027 ∨ (¬ p4947) ∨ (¬ p2563) ∨ (¬ p3359) ∨ (¬ p5043) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3359) ∨ (¬ p4947) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial23810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4947)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory13066 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9)
  exact rule23810 (meaning t m 2027) (meaning t m 2542) (meaning t m 2563) (meaning t m 3359) (meaning t m 4947) (meaning t m 5043) source

theorem rule23811 (p2027 p3516 p3690 p4235 p4539 p4988 : Prop) (h : (¬ p4539) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4988) ∨ (¬ p4235) ∨ (¬ p3690)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4539) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial23811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4539)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory13067 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule23811 (meaning t m 2027) (meaning t m 3516) (meaning t m 3690) (meaning t m 4235) (meaning t m 4539) (meaning t m 4988) source

theorem rule23814 (p2027 p2132 p2187 p2509 p2860 p2922 p3540 p4108 p4384 p4733 : Prop) (h : (¬ p2509) ∨ (¬ p4384) ∨ (¬ p2132) ∨ (¬ p2922) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2860) ∨ (¬ p4108) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2509) ∨ (¬ p2860) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4384) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13070 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule23814 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2509) (meaning t m 2860) (meaning t m 2922) (meaning t m 3540) (meaning t m 4108) (meaning t m 4384) (meaning t m 4733) source

theorem rule23816 (p2027 p2598 p3276 p3333 p3548 p4366 p4733 p5123 p5558 : Prop) (h : (¬ p3333) ∨ (¬ p4366) ∨ (¬ p2598) ∨ (¬ p3548) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p5558) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4733) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial23816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13072 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23816 (meaning t m 2027) (meaning t m 2598) (meaning t m 3276) (meaning t m 3333) (meaning t m 3548) (meaning t m 4366) (meaning t m 4733) (meaning t m 5123) (meaning t m 5558) source

theorem rule23817 (p2027 p2132 p2870 p3860 p4129 p4261 p4444 p4733 p4826 : Prop) (h : (¬ p4826) ∨ (¬ p2870) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p2132) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4129)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3860) ∨ (¬ p4129) ∨ (¬ p4261) ∨ (¬ p4444) ∨ (¬ p4733) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13073 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23817 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 3860) (meaning t m 4129) (meaning t m 4261) (meaning t m 4444) (meaning t m 4733) (meaning t m 4826) source

theorem rule23818 (p2027 p3707 p4039 p4110 p4205 p4632 p4942 p5284 : Prop) (h : (¬ p4039) ∨ (¬ p4110) ∨ (¬ p3707) ∨ (¬ p4205) ∨ (¬ p5284) ∨ (¬ p4942) ∨ p2027 ∨ (¬ p4632)) : (p2027) ∨ (¬ p3707) ∨ (¬ p4039) ∨ (¬ p4110) ∨ (¬ p4205) ∨ (¬ p4632) ∨ (¬ p4942) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial23818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4205)) ∨ (¬ (meaning t m 4632)) ∨ (¬ (meaning t m 4942)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory13074 t (m.theta 1 5) (m.theta 1 9) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule23818 (meaning t m 2027) (meaning t m 3707) (meaning t m 4039) (meaning t m 4110) (meaning t m 4205) (meaning t m 4632) (meaning t m 4942) (meaning t m 5284) source

theorem rule23819 (p2027 p2598 p2911 p3201 p3549 p3591 p4107 p4666 p4733 : Prop) (h : (¬ p3549) ∨ (¬ p3201) ∨ (¬ p3591) ∨ (¬ p4733) ∨ (¬ p2598) ∨ (¬ p4666) ∨ (¬ p4107) ∨ (¬ p2911) ∨ p2027) : (p2027) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13075 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23819 (meaning t m 2027) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4666) (meaning t m 4733) source

theorem rule23820 (p2027 p2248 p2299 p2901 p2946 p3246 p3549 p3591 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial23820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13076 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23820 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3549) (meaning t m 3591) (meaning t m 4668) source

theorem rule23822 (p2027 p2299 p2417 p2437 p2651 p2780 p3822 p4668 p4786 : Prop) (h : (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p4668) ∨ (¬ p2780) ∨ (¬ p4786) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4668) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial23822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory13078 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23822 (meaning t m 2027) (meaning t m 2299) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2780) (meaning t m 3822) (meaning t m 4668) (meaning t m 4786) source

theorem rule23824 (p2027 p2383 p2962 p3872 p3989 p4235 p4539 : Prop) (h : p2027 ∨ (¬ p4539) ∨ (¬ p4235) ∨ (¬ p2962) ∨ (¬ p2383) ∨ (¬ p3989) ∨ (¬ p3872)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4235) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial23824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13080 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule23824 (meaning t m 2027) (meaning t m 2383) (meaning t m 2962) (meaning t m 3872) (meaning t m 3989) (meaning t m 4235) (meaning t m 4539) source

theorem rule23825 (p2027 p2579 p3051 p4235 p4399 p4715 : Prop) (h : (¬ p4399) ∨ (¬ p4235) ∨ (¬ p3051) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4715)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory13081 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule23825 (meaning t m 2027) (meaning t m 2579) (meaning t m 3051) (meaning t m 4235) (meaning t m 4399) (meaning t m 4715) source

theorem rule23826 (p2027 p2220 p2542 p3693 p4256 p4539 : Prop) (h : (¬ p4539) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p3693) ∨ (¬ p2220) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial23826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13082 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule23826 (meaning t m 2027) (meaning t m 2220) (meaning t m 2542) (meaning t m 3693) (meaning t m 4256) (meaning t m 4539) source

theorem rule23827 (p1997 p2027 p2284 p2299 p2633 p2696 p3136 p3549 p3591 p4110 p4733 : Prop) (h : (¬ p3549) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2299) ∨ (¬ p1997) ∨ (¬ p2696) ∨ p2633 ∨ (¬ p3591) ∨ (¬ p3136) ∨ (¬ p4733)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4110) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13083 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23827 (meaning t m 1997) (meaning t m 2027) (meaning t m 2284) (meaning t m 2299) (meaning t m 2633) (meaning t m 2696) (meaning t m 3136) (meaning t m 3549) (meaning t m 3591) (meaning t m 4110) (meaning t m 4733) source

theorem rule23828 (p2027 p3767 p4207 p4235 p4322 p4402 p4539 : Prop) (h : (¬ p4207) ∨ (¬ p4402) ∨ (¬ p3767) ∨ (¬ p4539) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3767) ∨ (¬ p4207) ∨ (¬ p4235) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial23828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4207)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13084 t (m.theta 0 5) (m.theta 0 9) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule23828 (meaning t m 2027) (meaning t m 3767) (meaning t m 4207) (meaning t m 4235) (meaning t m 4322) (meaning t m 4402) (meaning t m 4539) source

theorem rule23829 (p2027 p2241 p2274 p2313 p3189 p3645 p3954 p3989 p4198 p4771 p4877 : Prop) (h : (¬ p4198) ∨ (¬ p3645) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4877) ∨ (¬ p2313) ∨ (¬ p4771) ∨ (¬ p2274) ∨ (¬ p3189) ∨ (¬ p3989) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3189) ∨ (¬ p3645) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4771) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13085 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23829 (meaning t m 2027) (meaning t m 2241) (meaning t m 2274) (meaning t m 2313) (meaning t m 3189) (meaning t m 3645) (meaning t m 3954) (meaning t m 3989) (meaning t m 4198) (meaning t m 4771) (meaning t m 4877) source

theorem rule23830 (p2027 p2122 p2140 p3097 p3646 p3985 : Prop) (h : p2027 ∨ (¬ p2140) ∨ (¬ p3646) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2140) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial23830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory13086 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule23830 (meaning t m 2027) (meaning t m 2122) (meaning t m 2140) (meaning t m 3097) (meaning t m 3646) (meaning t m 3985) source

theorem rule23834 (p2027 p2143 p2493 p2598 p3564 p3583 p3590 p3692 p4120 p4330 p4737 : Prop) (h : (¬ p3564) ∨ (¬ p3590) ∨ (¬ p4330) ∨ (¬ p2598) ∨ (¬ p4120) ∨ (¬ p4737) ∨ (¬ p3692) ∨ (¬ p2143) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p2493)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p3564) ∨ (¬ p3583) ∨ (¬ p3590) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4330) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory13090 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule23834 (meaning t m 2027) (meaning t m 2143) (meaning t m 2493) (meaning t m 2598) (meaning t m 3564) (meaning t m 3583) (meaning t m 3590) (meaning t m 3692) (meaning t m 4120) (meaning t m 4330) (meaning t m 4737) source

theorem rule23836 (p2027 p2140 p2187 p2387 p2860 p4198 : Prop) (h : p2027 ∨ (¬ p2187) ∨ (¬ p4198) ∨ (¬ p2387) ∨ (¬ p2860) ∨ (¬ p2140)) : (p2027) ∨ (¬ p2140) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2860) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial23836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory13092 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8)
  exact rule23836 (meaning t m 2027) (meaning t m 2140) (meaning t m 2187) (meaning t m 2387) (meaning t m 2860) (meaning t m 4198) source

theorem rule23838 (p2027 p2406 p3227 p3379 p3834 p4949 : Prop) (h : (¬ p3379) ∨ (¬ p2406) ∨ (¬ p3227) ∨ (¬ p4949) ∨ p2027 ∨ (¬ p3834)) : (p2027) ∨ (¬ p2406) ∨ (¬ p3227) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial23838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory13094 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 4 5) (m.theta 4 9)
  exact rule23838 (meaning t m 2027) (meaning t m 2406) (meaning t m 3227) (meaning t m 3379) (meaning t m 3834) (meaning t m 4949) source

theorem rule23842 (p3657 p3659 p4324 : Prop) (h : (¬ p3657) ∨ (¬ p3659) ∨ p4324) : (¬ p3657) ∨ (¬ p3659) ∨ (p4324) := by
  classical
  tauto

theorem initial23842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3659)) ∨ (meaning t m 4324) := by
  have source := ElevenTheory.theory13098 (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23842 (meaning t m 3657) (meaning t m 3659) (meaning t m 4324) source

theorem rule23844 (p2027 p2780 p2911 p2922 p3379 p3822 p4107 p4666 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p3822) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p4107) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13100 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23844 (meaning t m 2027) (meaning t m 2780) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3822) (meaning t m 4107) (meaning t m 4666) (meaning t m 4736) source

theorem rule23845 (p2027 p2284 p3177 p3661 p3969 p4507 p5590 : Prop) (h : p2027 ∨ (¬ p3177) ∨ (¬ p3661) ∨ (¬ p5590) ∨ (¬ p4507) ∨ (¬ p2284) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3177) ∨ (¬ p3661) ∨ (¬ p3969) ∨ (¬ p4507) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial23845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory13101 t (m.theta 0 8) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule23845 (meaning t m 2027) (meaning t m 2284) (meaning t m 3177) (meaning t m 3661) (meaning t m 3969) (meaning t m 4507) (meaning t m 5590) source

theorem rule23846 (p2027 p2166 p2210 p2313 p2553 p2577 p3347 p3954 p3956 p4433 p5216 : Prop) (h : (¬ p2210) ∨ (¬ p4433) ∨ (¬ p2577) ∨ (¬ p2166) ∨ (¬ p2313) ∨ (¬ p3956) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3347) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory13102 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule23846 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 3347) (meaning t m 3954) (meaning t m 3956) (meaning t m 4433) (meaning t m 5216) source

theorem rule23847 (p2027 p3093 p3555 p4363 p4516 p5043 : Prop) (h : (¬ p3093) ∨ (¬ p4516) ∨ (¬ p3555) ∨ (¬ p5043) ∨ (¬ p4363) ∨ p2027) : (p2027) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p4516) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial23847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory13103 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 9)
  exact rule23847 (meaning t m 2027) (meaning t m 3093) (meaning t m 3555) (meaning t m 4363) (meaning t m 4516) (meaning t m 5043) source

theorem rule23848 (p2027 p2138 p2933 p3366 p3399 p3452 p3868 p4322 p4376 p4385 p4826 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p2933) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p4385) ∨ (¬ p4322) ∨ (¬ p4826) ∨ (¬ p3399) ∨ (¬ p3868) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2933) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3868) ∨ (¬ p4322) ∨ (¬ p4376) ∨ (¬ p4385) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13104 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule23848 (meaning t m 2027) (meaning t m 2138) (meaning t m 2933) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3868) (meaning t m 4322) (meaning t m 4376) (meaning t m 4385) (meaning t m 4826) source

theorem rule23849 (p2027 p2210 p2743 p3954 p4243 p5052 : Prop) (h : p2027 ∨ (¬ p3954) ∨ (¬ p2743) ∨ (¬ p5052) ∨ (¬ p2210) ∨ (¬ p4243)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory13105 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5)
  exact rule23849 (meaning t m 2027) (meaning t m 2210) (meaning t m 2743) (meaning t m 3954) (meaning t m 4243) (meaning t m 5052) source

theorem rule23850 (p2027 p2248 p2299 p2946 p3256 p3549 p3591 p3692 p4237 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p3256) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p4237) ∨ (¬ p3549) ∨ (¬ p2946) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3692) ∨ (¬ p4237) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13106 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule23850 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2946) (meaning t m 3256) (meaning t m 3549) (meaning t m 3591) (meaning t m 3692) (meaning t m 4237) (meaning t m 4902) source

theorem rule23851 (p2027 p2630 p2696 p3343 p3549 p3591 p4107 p4638 p4733 : Prop) (h : (¬ p3343) ∨ (¬ p4638) ∨ (¬ p2696) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p4733) ∨ (¬ p3591) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3343) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13107 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule23851 (meaning t m 2027) (meaning t m 2630) (meaning t m 2696) (meaning t m 3343) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4638) (meaning t m 4733) source

theorem rule23852 (p1995 p2027 p2299 p2499 p2573 p2633 p3540 p3921 : Prop) (h : (¬ p2499) ∨ (¬ p1995) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p3921) ∨ (¬ p2573)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial23852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory13108 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23852 (meaning t m 1995) (meaning t m 2027) (meaning t m 2299) (meaning t m 2499) (meaning t m 2573) (meaning t m 2633) (meaning t m 3540) (meaning t m 3921) source

theorem rule23853 (p2027 p2253 p2331 p2881 p3027 p3425 p3659 p4154 p4280 p4736 : Prop) (h : p2027 ∨ (¬ p3659) ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p4154) ∨ (¬ p2881) ∨ (¬ p4280) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2881) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4154) ∨ (¬ p4280) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13109 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule23853 (meaning t m 2027) (meaning t m 2253) (meaning t m 2331) (meaning t m 2881) (meaning t m 3027) (meaning t m 3425) (meaning t m 3659) (meaning t m 4154) (meaning t m 4280) (meaning t m 4736) source

theorem rule23854 (p2881 p3246 p3945 : Prop) (h : (¬ p2881) ∨ (¬ p3945) ∨ p3246) : (¬ p2881) ∨ (p3246) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial23854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (meaning t m 3246) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory13110 (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23854 (meaning t m 2881) (meaning t m 3246) (meaning t m 3945) source

theorem rule23855 (p2027 p2138 p2241 p2641 p2668 p3570 p4133 p4244 p4736 : Prop) (h : (¬ p2241) ∨ (¬ p3570) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2138) ∨ (¬ p2668) ∨ (¬ p2641) ∨ (¬ p4133)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13111 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23855 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2641) (meaning t m 2668) (meaning t m 3570) (meaning t m 4133) (meaning t m 4244) (meaning t m 4736) source

theorem rule23856 (p2027 p2136 p2870 p3166 p3256 p3556 p3694 p4134 p4347 p4786 : Prop) (h : (¬ p3556) ∨ (¬ p3256) ∨ (¬ p4786) ∨ (¬ p3166) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p2136) ∨ (¬ p2870) ∨ (¬ p4347) ∨ (¬ p4134)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2870) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3556) ∨ (¬ p3694) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial23856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory13112 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23856 (meaning t m 2027) (meaning t m 2136) (meaning t m 2870) (meaning t m 3166) (meaning t m 3256) (meaning t m 3556) (meaning t m 3694) (meaning t m 4134) (meaning t m 4347) (meaning t m 4786) source

theorem rule23857 (p2027 p2138 p2241 p2449 p3027 p3570 p4244 p4668 p4736 : Prop) (h : (¬ p3570) ∨ (¬ p2449) ∨ (¬ p2241) ∨ (¬ p4244) ∨ (¬ p4668) ∨ (¬ p4736) ∨ (¬ p3027) ∨ (¬ p2138) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13113 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23857 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3570) (meaning t m 4244) (meaning t m 4668) (meaning t m 4736) source

theorem rule23859 (p2027 p2210 p2499 p3452 p4210 p4715 : Prop) (h : p2027 ∨ (¬ p2210) ∨ (¬ p4210) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory13115 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6)
  exact rule23859 (meaning t m 2027) (meaning t m 2210) (meaning t m 2499) (meaning t m 3452) (meaning t m 4210) (meaning t m 4715) source

theorem rule23861 (p2027 p2860 p2952 p3952 p4313 p4787 : Prop) (h : p2027 ∨ (¬ p2952) ∨ (¬ p4787) ∨ (¬ p4313) ∨ (¬ p2860) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2860) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4313) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory13117 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule23861 (meaning t m 2027) (meaning t m 2860) (meaning t m 2952) (meaning t m 3952) (meaning t m 4313) (meaning t m 4787) source

theorem rule23862 (p2027 p2210 p2928 p3452 p4210 p4644 : Prop) (h : p2027 ∨ (¬ p4210) ∨ (¬ p2210) ∨ (¬ p4644) ∨ (¬ p3452) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory13118 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7)
  exact rule23862 (meaning t m 2027) (meaning t m 2210) (meaning t m 2928) (meaning t m 3452) (meaning t m 4210) (meaning t m 4644) source

theorem rule23863 (p2027 p3051 p3684 p4235 p4399 p4730 : Prop) (h : (¬ p4730) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p3051)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial23863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory13119 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule23863 (meaning t m 2027) (meaning t m 3051) (meaning t m 3684) (meaning t m 4235) (meaning t m 4399) (meaning t m 4730) source

theorem rule23864 (p2027 p3051 p3452 p3486 p4172 p4376 p4874 : Prop) (h : (¬ p4874) ∨ (¬ p4376) ∨ (¬ p3051) ∨ (¬ p4172) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p3452)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3452) ∨ (¬ p3486) ∨ (¬ p4172) ∨ (¬ p4376) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial23864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory13120 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 5 7)
  exact rule23864 (meaning t m 2027) (meaning t m 3051) (meaning t m 3452) (meaning t m 3486) (meaning t m 4172) (meaning t m 4376) (meaning t m 4874) source

theorem rule23865 (p2027 p3073 p3365 p3449 p3553 p3572 p4133 p4347 p4736 : Prop) (h : (¬ p4347) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3449) ∨ (¬ p3572) ∨ (¬ p3365) ∨ (¬ p4736) ∨ (¬ p3073)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory13121 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23865 (meaning t m 2027) (meaning t m 3073) (meaning t m 3365) (meaning t m 3449) (meaning t m 3553) (meaning t m 3572) (meaning t m 4133) (meaning t m 4347) (meaning t m 4736) source

theorem rule23869 (p2027 p2396 p2553 p2573 p2608 p3519 p3659 p4366 p4376 p4424 p4668 : Prop) (h : (¬ p3519) ∨ (¬ p4424) ∨ (¬ p4376) ∨ (¬ p4366) ∨ (¬ p3659) ∨ (¬ p2573) ∨ (¬ p4668) ∨ (¬ p2553) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3659) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4424) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial23869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory13125 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23869 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 2608) (meaning t m 3519) (meaning t m 3659) (meaning t m 4366) (meaning t m 4376) (meaning t m 4424) (meaning t m 4668) source

theorem rule23872 (p3990 p4501 p4620 : Prop) (h : (¬ p4501) ∨ (¬ p3990) ∨ p4620) : (¬ p3990) ∨ (¬ p4501) ∨ (p4620) := by
  classical
  tauto

theorem initial23872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4501)) ∨ (meaning t m 4620) := by
  have source := ElevenTheory.theory13128 t (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule23872 (meaning t m 3990) (meaning t m 4501) (meaning t m 4620) source

theorem rule23873 (p1992 p2027 p2598 p2622 p2952 p3136 p3585 p4236 : Prop) (h : (¬ p2598) ∨ (¬ p1992) ∨ p2622 ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p2952)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3585) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial23873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory13129 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule23873 (meaning t m 1992) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 2952) (meaning t m 3136) (meaning t m 3585) (meaning t m 4236) source

theorem rule23874 (p2027 p3568 p3755 p4195 p4367 p4624 : Prop) (h : (¬ p3755) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p3568) ∨ (¬ p4367) ∨ (¬ p4195)) : (p2027) ∨ (¬ p3568) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4367) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13130 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 7) (m.theta 6 9)
  exact rule23874 (meaning t m 2027) (meaning t m 3568) (meaning t m 3755) (meaning t m 4195) (meaning t m 4367) (meaning t m 4624) source

theorem rule23875 (p2027 p2459 p2608 p2911 p3389 p3519 p3860 p4353 p4376 p5118 p5612 : Prop) (h : (¬ p4353) ∨ (¬ p3860) ∨ (¬ p3389) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2608) ∨ (¬ p5612)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p4353) ∨ (¬ p4376) ∨ (¬ p5118) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial23875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4353)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory13131 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23875 (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 2911) (meaning t m 3389) (meaning t m 3519) (meaning t m 3860) (meaning t m 4353) (meaning t m 4376) (meaning t m 5118) (meaning t m 5612) source

theorem rule23880 (p1977 p2027 p2177 p2241 p2997 p3553 p3591 p4067 p4319 : Prop) (h : (¬ p2177) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3591) ∨ p2997 ∨ (¬ p4319) ∨ (¬ p2241) ∨ (¬ p1977) ∨ (¬ p4067)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (p2997) ∨ (¬ p3553) ∨ (¬ p3591) ∨ (¬ p4067) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial23880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory13136 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23880 (meaning t m 1977) (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2997) (meaning t m 3553) (meaning t m 3591) (meaning t m 4067) (meaning t m 4319) source

theorem rule23881 (p2027 p3324 p3325 p3599 p3688 p4337 p4624 p5269 : Prop) (h : (¬ p4624) ∨ (¬ p3325) ∨ (¬ p4337) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p5269) ∨ (¬ p3688) ∨ (¬ p3599)) : (p2027) ∨ (¬ p3324) ∨ (¬ p3325) ∨ (¬ p3599) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4624) ∨ (¬ p5269) := by
  classical
  tauto

theorem initial23881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5269)) := by
  have source := ElevenTheory.theory13137 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 9) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule23881 (meaning t m 2027) (meaning t m 3324) (meaning t m 3325) (meaning t m 3599) (meaning t m 3688) (meaning t m 4337) (meaning t m 4624) (meaning t m 5269) source

theorem rule23885 (p2774 p3365 p4841 : Prop) (h : (¬ p4841) ∨ (¬ p3365) ∨ (¬ p2774)) : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial23885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory13141 (m.theta 0 2) (m.theta 2 3) (m.theta 2 6)
  exact rule23885 (meaning t m 2774) (meaning t m 3365) (meaning t m 4841) source

theorem rule23888 (p2027 p2247 p2396 p2553 p2573 p2996 p3553 p4668 p5190 : Prop) (h : (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p5190) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4668) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial23888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13144 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23888 (meaning t m 2027) (meaning t m 2247) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 2996) (meaning t m 3553) (meaning t m 4668) (meaning t m 5190) source

theorem rule23889 (p2027 p2608 p2911 p3389 p3519 p3860 p3941 p4261 p4376 p5122 : Prop) (h : (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2608) ∨ (¬ p3860) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p5122) ∨ (¬ p3941) ∨ (¬ p4261) ∨ p2027) : (p2027) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p4376) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial23889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory13145 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23889 (meaning t m 2027) (meaning t m 2608) (meaning t m 2911) (meaning t m 3389) (meaning t m 3519) (meaning t m 3860) (meaning t m 3941) (meaning t m 4261) (meaning t m 4376) (meaning t m 5122) source

end SunPrize.SMT
