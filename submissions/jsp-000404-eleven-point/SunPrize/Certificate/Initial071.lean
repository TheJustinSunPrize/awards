import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory055
import SunPrize.Certificate.Theory056
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule31552 (p2027 p2210 p2651 p2753 p2810 p3005 p3548 p4117 p4366 p4550 p4877 : Prop) (h : (¬ p2810) ∨ (¬ p2651) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p4550) ∨ (¬ p2753) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2651) ∨ (¬ p2753) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3548) ∨ (¬ p4117) ∨ (¬ p4366) ∨ (¬ p4550) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial31552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory20808 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 7 8)
  exact rule31552 (meaning t m 2027) (meaning t m 2210) (meaning t m 2651) (meaning t m 2753) (meaning t m 2810) (meaning t m 3005) (meaning t m 3548) (meaning t m 4117) (meaning t m 4366) (meaning t m 4550) (meaning t m 4877) source

theorem rule31555 (p2027 p2417 p2598 p2963 p3201 p3324 p3950 p4347 p4789 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p4789) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p3324) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial31555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory20811 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule31555 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 2963) (meaning t m 3201) (meaning t m 3324) (meaning t m 3950) (meaning t m 4347) (meaning t m 4789) source

theorem rule31557 (p2027 p2122 p2252 p2396 p2750 p2829 p2952 p3497 p3692 p3950 : Prop) (h : (¬ p2829) ∨ (¬ p3950) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial31557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory20813 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule31557 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2396) (meaning t m 2750) (meaning t m 2829) (meaning t m 2952) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule31558 (p2027 p2252 p2534 p2657 p2750 p3399 p3631 p3950 p3954 p4256 : Prop) (h : (¬ p2252) ∨ (¬ p4256) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p2534) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial31558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory20814 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule31558 (meaning t m 2027) (meaning t m 2252) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 3399) (meaning t m 3631) (meaning t m 3950) (meaning t m 3954) (meaning t m 4256) source

theorem rule31559 (p2027 p2144 p2156 p2252 p2459 p2534 p2619 p2655 p2750 p2753 p3540 p3758 p4133 p4186 p4441 : Prop) (h : (¬ p2619) ∨ (¬ p2156) ∨ (¬ p4441) ∨ (¬ p4133) ∨ (¬ p4186) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p3540) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3758) ∨ (¬ p2144) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2619) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3540) ∨ (¬ p3758) ∨ (¬ p4133) ∨ (¬ p4186) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial31559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory20815 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31559 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2252) (meaning t m 2459) (meaning t m 2534) (meaning t m 2619) (meaning t m 2655) (meaning t m 2750) (meaning t m 2753) (meaning t m 3540) (meaning t m 3758) (meaning t m 4133) (meaning t m 4186) (meaning t m 4441) source

theorem rule31560 (p2027 p2122 p2774 p4232 p4620 p5265 : Prop) (h : (¬ p2774) ∨ (¬ p2122) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p5265) ∨ (¬ p4232)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4232) ∨ (¬ p4620) ∨ (¬ p5265) := by
  classical
  tauto

theorem initial31560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5265)) := by
  have source := ElevenTheory.theory20816 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 9) (m.theta 6 7) (m.theta 6 9)
  exact rule31560 (meaning t m 2027) (meaning t m 2122) (meaning t m 2774) (meaning t m 4232) (meaning t m 4620) (meaning t m 5265) source

theorem rule31561 (p2027 p2254 p2707 p2774 p2881 p3414 p3553 p3589 p3688 p4895 : Prop) (h : (¬ p2707) ∨ (¬ p3688) ∨ (¬ p3553) ∨ (¬ p3414) ∨ (¬ p4895) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2774) ∨ (¬ p2254) ∨ (¬ p3589)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p2774) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3589) ∨ (¬ p3688) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial31561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory20817 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule31561 (meaning t m 2027) (meaning t m 2254) (meaning t m 2707) (meaning t m 2774) (meaning t m 2881) (meaning t m 3414) (meaning t m 3553) (meaning t m 3589) (meaning t m 3688) (meaning t m 4895) source

theorem rule31564 (p2027 p2373 p3256 p4043 p4209 p4456 p4948 : Prop) (h : (¬ p4456) ∨ (¬ p4043) ∨ p2027 ∨ (¬ p4209) ∨ (¬ p2373) ∨ (¬ p4948) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3256) ∨ (¬ p4043) ∨ (¬ p4209) ∨ (¬ p4456) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial31564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4209)) ∨ (¬ (meaning t m 4456)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory20820 t (m.theta 0 9) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule31564 (meaning t m 2027) (meaning t m 2373) (meaning t m 3256) (meaning t m 4043) (meaning t m 4209) (meaning t m 4456) (meaning t m 4948) source

theorem rule31565 (p2027 p2737 p3193 p3355 p3759 p4257 p4749 : Prop) (h : (¬ p3759) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p4749) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p4257)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial31565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory20821 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 9)
  exact rule31565 (meaning t m 2027) (meaning t m 2737) (meaning t m 3193) (meaning t m 3355) (meaning t m 3759) (meaning t m 4257) (meaning t m 4749) source

theorem rule31566 (p2027 p2518 p2528 p2685 p3366 p3414 p3877 p4236 p4347 p4376 p4774 : Prop) (h : (¬ p2528) ∨ (¬ p4347) ∨ (¬ p2518) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p4236) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p4774) ∨ (¬ p2685) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2685) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial31566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory20822 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31566 (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2685) (meaning t m 3366) (meaning t m 3414) (meaning t m 3877) (meaning t m 4236) (meaning t m 4347) (meaning t m 4376) (meaning t m 4774) source

theorem rule31568 (p2911 p3945 p4278 : Prop) (h : (¬ p2911) ∨ (¬ p3945) ∨ (¬ p4278)) : (¬ p2911) ∨ (¬ p3945) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial31568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory20824 (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31568 (meaning t m 2911) (meaning t m 3945) (meaning t m 4278) source

theorem rule31570 (p2027 p2295 p2331 p2396 p2534 p3055 p3874 p3950 p4786 : Prop) (h : (¬ p2331) ∨ (¬ p3950) ∨ (¬ p2396) ∨ (¬ p3055) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p4786) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial31570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory20826 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule31570 (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 2534) (meaning t m 3055) (meaning t m 3874) (meaning t m 3950) (meaning t m 4786) source

theorem rule31573 (p2027 p2247 p2387 p2744 p2778 p3083 p3366 p3379 p3487 p3609 p4347 p5375 : Prop) (h : (¬ p3083) ∨ (¬ p4347) ∨ (¬ p2387) ∨ (¬ p5375) ∨ (¬ p3487) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3379) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p5375) := by
  classical
  tauto

theorem initial31573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5375)) := by
  have source := ElevenTheory.theory20829 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 8) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31573 (meaning t m 2027) (meaning t m 2247) (meaning t m 2387) (meaning t m 2744) (meaning t m 2778) (meaning t m 3083) (meaning t m 3366) (meaning t m 3379) (meaning t m 3487) (meaning t m 3609) (meaning t m 4347) (meaning t m 5375) source

theorem rule31574 (p2027 p2707 p3688 p4358 p4475 p4501 : Prop) (h : (¬ p4501) ∨ (¬ p4475) ∨ (¬ p4358) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p2707)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3688) ∨ (¬ p4358) ∨ (¬ p4475) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial31574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory20830 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8)
  exact rule31574 (meaning t m 2027) (meaning t m 2707) (meaning t m 3688) (meaning t m 4358) (meaning t m 4475) (meaning t m 4501) source

theorem rule31575 (p2007 p2027 p2247 p2534 p2688 p3073 p3449 : Prop) (h : p2688 ∨ (¬ p2007) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p2534) ∨ (¬ p2247)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2534) ∨ (p2688) ∨ (¬ p3073) ∨ (¬ p3449) := by
  classical
  tauto

theorem initial31575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) := by
  have source := ElevenTheory.theory20831 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 4 8) (m.theta 8 9)
  exact rule31575 (meaning t m 2007) (meaning t m 2027) (meaning t m 2247) (meaning t m 2534) (meaning t m 2688) (meaning t m 3073) (meaning t m 3449) source

theorem rule31580 (p2166 p2619 p4418 : Prop) (h : (¬ p4418) ∨ (¬ p2166) ∨ p2619) : (¬ p2166) ∨ (p2619) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial31580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (meaning t m 2619) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory20836 (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule31580 (meaning t m 2166) (meaning t m 2619) (meaning t m 4418) source

theorem rule31586 (p2027 p2230 p2246 p2373 p2741 p2963 p3519 p3969 p4037 p4191 p4376 p5119 : Prop) (h : (¬ p2741) ∨ (¬ p2373) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p2963) ∨ p2246 ∨ (¬ p4376) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p3519) ∨ (¬ p5119) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (p2246) ∨ (¬ p2373) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4376) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2246) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20842 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31586 (meaning t m 2027) (meaning t m 2230) (meaning t m 2246) (meaning t m 2373) (meaning t m 2741) (meaning t m 2963) (meaning t m 3519) (meaning t m 3969) (meaning t m 4037) (meaning t m 4191) (meaning t m 4376) (meaning t m 5119) source

theorem rule31587 (p3758 p4173 p4418 : Prop) (h : (¬ p3758) ∨ (¬ p4418) ∨ p4173) : (¬ p3758) ∨ (p4173) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial31587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3758)) ∨ (meaning t m 4173) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory20843 (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule31587 (meaning t m 3758) (meaning t m 4173) (meaning t m 4418) source

theorem rule31590 (p2027 p2341 p2528 p2608 p3266 p3519 p3591 p4376 p4383 p4435 p5201 p5254 : Prop) (h : (¬ p5201) ∨ (¬ p4435) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3591) ∨ (¬ p5254) ∨ (¬ p2341) ∨ (¬ p4383) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p3266) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3266) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p4376) ∨ (¬ p4383) ∨ (¬ p4435) ∨ (¬ p5201) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial31590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5201)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory20846 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 8) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule31590 (meaning t m 2027) (meaning t m 2341) (meaning t m 2528) (meaning t m 2608) (meaning t m 3266) (meaning t m 3519) (meaning t m 3591) (meaning t m 4376) (meaning t m 4383) (meaning t m 4435) (meaning t m 5201) (meaning t m 5254) source

theorem rule31594 (p2027 p2248 p2651 p3276 p3343 p3366 p3371 p3425 p3555 p4423 p4831 : Prop) (h : (¬ p4423) ∨ (¬ p3425) ∨ (¬ p4831) ∨ (¬ p3555) ∨ (¬ p3276) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3425) ∨ (¬ p3555) ∨ (¬ p4423) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial31594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory20850 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 10) (m.theta 9 10)
  exact rule31594 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 3366) (meaning t m 3371) (meaning t m 3425) (meaning t m 3555) (meaning t m 4423) (meaning t m 4831) source

theorem rule31600 (p2027 p2579 p2588 p3363 p3365 p3619 p3670 p4260 p4752 p4831 : Prop) (h : (¬ p3670) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p4831) ∨ (¬ p2579) ∨ (¬ p3365) ∨ (¬ p2588) ∨ (¬ p4752) ∨ (¬ p3619) ∨ (¬ p4260)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3363) ∨ (¬ p3365) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4260) ∨ (¬ p4752) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial31600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory20856 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule31600 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3363) (meaning t m 3365) (meaning t m 3619) (meaning t m 3670) (meaning t m 4260) (meaning t m 4752) (meaning t m 4831) source

theorem rule31601 (p1990 p2027 p2169 p2284 p3564 p3956 p4033 p4385 p5051 : Prop) (h : (¬ p4385) ∨ p2169 ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4033) ∨ (¬ p5051) ∨ (¬ p3956) ∨ (¬ p3564)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2284) ∨ (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4033) ∨ (¬ p4385) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial31601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory20857 t (m.theta 2 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9)
  exact rule31601 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2284) (meaning t m 3564) (meaning t m 3956) (meaning t m 4033) (meaning t m 4385) (meaning t m 5051) source

theorem rule31604 (p2027 p2248 p2881 p2901 p2946 p3483 p3946 p4358 p4503 p5015 : Prop) (h : (¬ p5015) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3946) ∨ p2027 ∨ (¬ p3483) ∨ (¬ p4503) ∨ (¬ p2248) ∨ (¬ p4358) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3483) ∨ (¬ p3946) ∨ (¬ p4358) ∨ (¬ p4503) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial31604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory20860 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8)
  exact rule31604 (meaning t m 2027) (meaning t m 2248) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3483) (meaning t m 3946) (meaning t m 4358) (meaning t m 4503) (meaning t m 5015) source

theorem rule31605 (p2027 p2248 p2363 p2881 p2901 p2946 p3860 p4261 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p3860) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial31605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory20861 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31605 (meaning t m 2027) (meaning t m 2248) (meaning t m 2363) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3860) (meaning t m 4261) (meaning t m 4503) source

theorem rule31606 (p2027 p2753 p2807 p3379 p3506 p3591 p4026 p4117 p4381 p4625 p4661 p5216 : Prop) (h : (¬ p4625) ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p4026) ∨ (¬ p4381) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p4117) ∨ (¬ p4661) ∨ (¬ p2807) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2753) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p3506) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4117) ∨ (¬ p4381) ∨ (¬ p4625) ∨ (¬ p4661) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4661)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory20862 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 7) (m.theta 3 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31606 (meaning t m 2027) (meaning t m 2753) (meaning t m 2807) (meaning t m 3379) (meaning t m 3506) (meaning t m 3591) (meaning t m 4026) (meaning t m 4117) (meaning t m 4381) (meaning t m 4625) (meaning t m 4661) (meaning t m 5216) source

theorem rule31608 (p2001 p2027 p2247 p2387 p2577 p2744 p2819 p2997 p3156 p3347 p3822 p3830 p4208 p4257 p4387 : Prop) (h : p2997 ∨ (¬ p3822) ∨ (¬ p2819) ∨ (¬ p2744) ∨ (¬ p4257) ∨ (¬ p3347) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2247) ∨ (¬ p4387) ∨ (¬ p2001) ∨ (¬ p3156) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4208)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2744) ∨ (¬ p2819) ∨ (p2997) ∨ (¬ p3156) ∨ (¬ p3347) ∨ (¬ p3822) ∨ (¬ p3830) ∨ (¬ p4208) ∨ (¬ p4257) ∨ (¬ p4387) := by
  classical
  tauto

theorem initial31608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4387)) := by
  have source := ElevenTheory.theory20864 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 9) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 6 8)
  exact rule31608 (meaning t m 2001) (meaning t m 2027) (meaning t m 2247) (meaning t m 2387) (meaning t m 2577) (meaning t m 2744) (meaning t m 2819) (meaning t m 2997) (meaning t m 3156) (meaning t m 3347) (meaning t m 3822) (meaning t m 3830) (meaning t m 4208) (meaning t m 4257) (meaning t m 4387) source

theorem rule31612 (p3573 p3574 p4256 : Prop) (h : (¬ p3573) ∨ (¬ p3574) ∨ p4256) : (¬ p3573) ∨ (¬ p3574) ∨ (p4256) := by
  classical
  tauto

theorem initial31612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3574)) ∨ (meaning t m 4256) := by
  have source := ElevenTheory.theory20868 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule31612 (meaning t m 3573) (meaning t m 3574) (meaning t m 4256) source

theorem rule31613 (p2027 p2187 p2241 p2387 p2727 p3343 p3744 p4198 p4524 p5322 : Prop) (h : p2027 ∨ (¬ p5322) ∨ (¬ p2187) ∨ (¬ p3343) ∨ (¬ p3744) ∨ (¬ p2387) ∨ (¬ p4524) ∨ (¬ p4198) ∨ (¬ p2241) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3744) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial31613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory20869 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule31613 (meaning t m 2027) (meaning t m 2187) (meaning t m 2241) (meaning t m 2387) (meaning t m 2727) (meaning t m 3343) (meaning t m 3744) (meaning t m 4198) (meaning t m 4524) (meaning t m 5322) source

theorem rule31614 (p3549 p3822 p3918 : Prop) (h : (¬ p3822) ∨ (¬ p3918) ∨ p3549) : (p3549) ∨ (¬ p3822) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial31614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3549) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory20870 (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule31614 (meaning t m 3549) (meaning t m 3822) (meaning t m 3918) source

theorem rule31620 (p2027 p2246 p2307 p2608 p2744 p3323 p3555 p3568 p3987 p4363 p4368 : Prop) (h : (¬ p3987) ∨ (¬ p3323) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p3568) ∨ (¬ p2246) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4368) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2307) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3555) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4363) ∨ (¬ p4368) := by
  classical
  tauto

theorem initial31620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4368)) := by
  have source := ElevenTheory.theory20876 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule31620 (meaning t m 2027) (meaning t m 2246) (meaning t m 2307) (meaning t m 2608) (meaning t m 2744) (meaning t m 3323) (meaning t m 3555) (meaning t m 3568) (meaning t m 3987) (meaning t m 4363) (meaning t m 4368) source

theorem rule31621 (p2027 p2246 p2619 p2749 p2946 p3347 p3540 p3969 p4278 p4316 p4381 p5119 p5216 : Prop) (h : (¬ p3347) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p4381) ∨ (¬ p3540) ∨ (¬ p3969) ∨ (¬ p2946) ∨ (¬ p4278) ∨ (¬ p4316) ∨ (¬ p2619) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2619) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3969) ∨ (¬ p4278) ∨ (¬ p4316) ∨ (¬ p4381) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory20877 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31621 (meaning t m 2027) (meaning t m 2246) (meaning t m 2619) (meaning t m 2749) (meaning t m 2946) (meaning t m 3347) (meaning t m 3540) (meaning t m 3969) (meaning t m 4278) (meaning t m 4316) (meaning t m 4381) (meaning t m 5119) (meaning t m 5216) source

theorem rule31623 (p2027 p2098 p2245 p3027 p3414 p3609 p4347 p4360 p4733 p4774 : Prop) (h : (¬ p4347) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4733) ∨ (¬ p4774) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2245) ∨ (¬ p2098) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2245) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p4360) ∨ (¬ p4733) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial31623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory20879 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 8) (m.theta 3 7) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31623 (meaning t m 2027) (meaning t m 2098) (meaning t m 2245) (meaning t m 3027) (meaning t m 3414) (meaning t m 3609) (meaning t m 4347) (meaning t m 4360) (meaning t m 4733) (meaning t m 4774) source

theorem rule31627 (p2027 p2387 p2668 p2787 p3276 p3355 p3362 p4037 p4381 p4625 : Prop) (h : (¬ p4037) ∨ (¬ p2787) ∨ (¬ p4625) ∨ (¬ p2387) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p2668) ∨ (¬ p4381) ∨ (¬ p3362) ∨ p2027) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p4037) ∨ (¬ p4381) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial31627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory20883 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31627 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2787) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 4037) (meaning t m 4381) (meaning t m 4625) source

theorem rule31629 (p1990 p2027 p2611 p2696 p2743 p2839 p2860 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p1990) ∨ (¬ p2860) ∨ (¬ p2839)) : (¬ p1990) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial31629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory20885 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule31629 (meaning t m 1990) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2743) (meaning t m 2839) (meaning t m 2860) source

theorem rule31643 (p2027 p2248 p2331 p3323 p3461 p3588 p3954 p4106 p4831 p5503 : Prop) (h : p2027 ∨ (¬ p2331) ∨ (¬ p5503) ∨ (¬ p4831) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p3588) ∨ (¬ p3323) ∨ (¬ p2248) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4106) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial31643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory20899 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule31643 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 3323) (meaning t m 3461) (meaning t m 3588) (meaning t m 3954) (meaning t m 4106) (meaning t m 4831) (meaning t m 5503) source

theorem rule31647 (p2027 p2248 p2264 p2459 p2807 p3583 p3954 p4385 p5059 : Prop) (h : (¬ p3954) ∨ (¬ p5059) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p2248) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial31647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory20903 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule31647 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2459) (meaning t m 2807) (meaning t m 3583) (meaning t m 3954) (meaning t m 4385) (meaning t m 5059) source

theorem rule31650 (p2027 p2248 p2509 p2946 p3146 p3156 p3452 p4286 p5118 : Prop) (h : (¬ p3452) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p5118) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4286)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4286) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial31650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory20906 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31650 (meaning t m 2027) (meaning t m 2248) (meaning t m 2509) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3452) (meaning t m 4286) (meaning t m 5118) source

theorem rule31653 (p2662 p4727 p4753 : Prop) (h : (¬ p2662) ∨ (¬ p4753) ∨ p4727) : (¬ p2662) ∨ (p4727) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial31653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2662)) ∨ (meaning t m 4727) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory20909 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4)
  exact rule31653 (meaning t m 2662) (meaning t m 4727) (meaning t m 4753) source

theorem rule31657 (p1987 p2027 p2542 p2545 p2696 p3055 p3684 : Prop) (h : (¬ p2696) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p1987) ∨ p2545 ∨ (¬ p3684)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial31657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory20913 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule31657 (meaning t m 1987) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2696) (meaning t m 3055) (meaning t m 3684) source

theorem rule31665 (p2027 p3189 p3568 p4154 p4405 p4417 : Prop) (h : (¬ p3568) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4417) ∨ p2027 ∨ (¬ p4405)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial31665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory20921 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule31665 (meaning t m 2027) (meaning t m 3189) (meaning t m 3568) (meaning t m 4154) (meaning t m 4405) (meaning t m 4417) source

theorem rule31666 (p2027 p2363 p2598 p2911 p3201 p3591 p4261 p4371 p4503 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4261) ∨ (¬ p2363) ∨ (¬ p4371) ∨ (¬ p2911) ∨ (¬ p4503) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3591) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory20922 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31666 (meaning t m 2027) (meaning t m 2363) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3591) (meaning t m 4261) (meaning t m 4371) (meaning t m 4503) (meaning t m 4733) source

theorem rule31667 (p2027 p3093 p3527 p3551 p3687 p4870 p5206 : Prop) (h : (¬ p4870) ∨ (¬ p3687) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p5206) ∨ (¬ p3093) ∨ (¬ p3551)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3687) ∨ (¬ p4870) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial31667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory20923 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 7 8)
  exact rule31667 (meaning t m 2027) (meaning t m 3093) (meaning t m 3527) (meaning t m 3551) (meaning t m 3687) (meaning t m 4870) (meaning t m 5206) source

theorem rule31668 (p2017 p2027 p2323 p2437 p2470 p2663 p3868 p4256 : Prop) (h : (¬ p2017) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3868) ∨ (¬ p4256) ∨ p2323 ∨ (¬ p2470) ∨ (¬ p2663)) : (¬ p2017) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p3868) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial31668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory20924 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 10)
  exact rule31668 (meaning t m 2017) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2470) (meaning t m 2663) (meaning t m 3868) (meaning t m 4256) source

theorem rule31669 (p2749 p3541 p4281 : Prop) (h : (¬ p4281) ∨ (¬ p2749) ∨ p3541) : (¬ p2749) ∨ (p3541) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial31669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2749)) ∨ (meaning t m 3541) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory20925 (m.theta 1 2) (m.theta 1 3) (m.theta 1 4)
  exact rule31669 (meaning t m 2749) (meaning t m 3541) (meaning t m 4281) source

theorem rule31670 (p2749 p3371 p4365 : Prop) (h : (¬ p2749) ∨ (¬ p4365) ∨ p3371) : (¬ p2749) ∨ (p3371) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial31670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2749)) ∨ (meaning t m 3371) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory20926 (m.theta 1 2) (m.theta 1 3) (m.theta 1 5)
  exact rule31670 (meaning t m 2749) (meaning t m 3371) (meaning t m 4365) source

theorem rule31673 (p1990 p2027 p2166 p2284 p2611 p2696 p2742 p3497 p4365 : Prop) (h : (¬ p2742) ∨ p2611 ∨ (¬ p2284) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4365) ∨ (¬ p3497) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2284) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3497) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial31673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory20929 t (m.theta 0 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule31673 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2284) (meaning t m 2611) (meaning t m 2696) (meaning t m 2742) (meaning t m 3497) (meaning t m 4365) source

theorem rule31676 (p2187 p2819 p4428 : Prop) (h : (¬ p2819) ∨ (¬ p4428) ∨ p2187) : (p2187) ∨ (¬ p2819) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial31676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory20932 (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule31676 (meaning t m 2187) (meaning t m 2819) (meaning t m 4428) source

theorem rule31681 (p2027 p2191 p2248 p2331 p2363 p2819 p3555 p4337 p5118 p5568 : Prop) (h : (¬ p2363) ∨ (¬ p2191) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4337) ∨ (¬ p2331) ∨ (¬ p2248) ∨ (¬ p2819) ∨ (¬ p5118) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p4337) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial31681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory20937 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31681 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2819) (meaning t m 3555) (meaning t m 4337) (meaning t m 5118) (meaning t m 5568) source

theorem rule31683 (p2027 p2417 p3660 p3690 p3920 p4320 p4702 : Prop) (h : p2027 ∨ (¬ p2417) ∨ (¬ p3920) ∨ (¬ p4320) ∨ (¬ p3660) ∨ (¬ p4702) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3660) ∨ (¬ p3690) ∨ (¬ p3920) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial31683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory20939 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule31683 (meaning t m 2027) (meaning t m 2417) (meaning t m 3660) (meaning t m 3690) (meaning t m 3920) (meaning t m 4320) (meaning t m 4702) source

theorem rule31684 (p2027 p2132 p2579 p2588 p3363 p3527 p3570 p3585 p4418 p4431 p4556 p4737 : Prop) (h : (¬ p3527) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p4431) ∨ (¬ p4556) ∨ (¬ p2132) ∨ (¬ p3570) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4737) ∨ (¬ p4418)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3363) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3585) ∨ (¬ p4418) ∨ (¬ p4431) ∨ (¬ p4556) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial31684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20940 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule31684 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 2588) (meaning t m 3363) (meaning t m 3527) (meaning t m 3570) (meaning t m 3585) (meaning t m 4418) (meaning t m 4431) (meaning t m 4556) (meaning t m 4737) source

theorem rule31685 (p1976 p2027 p2997 p3055 p3367 p3688 p3822 : Prop) (h : (¬ p1976) ∨ (¬ p3822) ∨ p2997 ∨ (¬ p3688) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p2997) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial31685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory20941 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule31685 (meaning t m 1976) (meaning t m 2027) (meaning t m 2997) (meaning t m 3055) (meaning t m 3367) (meaning t m 3688) (meaning t m 3822) source

theorem rule31686 (p2027 p2166 p2210 p2254 p2657 p3359 p3969 p4425 p5119 : Prop) (h : (¬ p3359) ∨ (¬ p3969) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p5119) ∨ (¬ p2254) ∨ (¬ p2166) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3359) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20942 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31686 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 3359) (meaning t m 3969) (meaning t m 4425) (meaning t m 5119) source

theorem rule31690 (p2027 p3319 p3365 p3366 p3461 p3877 p3950 p4118 p4338 p4377 p4381 : Prop) (h : (¬ p3366) ∨ (¬ p4338) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p4118) ∨ (¬ p4381) ∨ (¬ p3950) ∨ (¬ p3461) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3319)) : (p2027) ∨ (¬ p3319) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4338) ∨ (¬ p4377) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial31690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory20946 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule31690 (meaning t m 2027) (meaning t m 3319) (meaning t m 3365) (meaning t m 3366) (meaning t m 3461) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4338) (meaning t m 4377) (meaning t m 4381) source

theorem rule31691 (p4344 p4473 p4556 : Prop) (h : (¬ p4344) ∨ (¬ p4556) ∨ p4473) : (¬ p4344) ∨ (p4473) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial31691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4344)) ∨ (meaning t m 4473) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory20947 t (m.theta 2 7) (m.theta 5 7) (m.theta 6 7)
  exact rule31691 (meaning t m 4344) (meaning t m 4473) (meaning t m 4556) source

theorem rule31695 (p2027 p2132 p2982 p4232 p4882 p5026 : Prop) (h : (¬ p4882) ∨ (¬ p5026) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p2132) ∨ (¬ p4232)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2982) ∨ (¬ p4232) ∨ (¬ p4882) ∨ (¬ p5026) := by
  classical
  tauto

theorem initial31695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 5026)) := by
  have source := ElevenTheory.theory20951 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 9) (m.theta 4 5) (m.theta 5 9)
  exact rule31695 (meaning t m 2027) (meaning t m 2132) (meaning t m 2982) (meaning t m 4232) (meaning t m 4882) (meaning t m 5026) source

theorem rule31697 (p2027 p2396 p2870 p4382 p4385 p4556 : Prop) (h : (¬ p4382) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p4385) ∨ (¬ p4556)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p4382) ∨ (¬ p4385) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial31697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory20953 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule31697 (meaning t m 2027) (meaning t m 2396) (meaning t m 2870) (meaning t m 4382) (meaning t m 4385) (meaning t m 4556) source

theorem rule31698 (p2027 p2641 p3051 p3368 p3486 p3759 p4343 p4399 p4975 : Prop) (h : (¬ p2641) ∨ p2027 ∨ (¬ p3368) ∨ (¬ p4975) ∨ (¬ p3051) ∨ (¬ p4399) ∨ (¬ p3759) ∨ (¬ p4343) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2641) ∨ (¬ p3051) ∨ (¬ p3368) ∨ (¬ p3486) ∨ (¬ p3759) ∨ (¬ p4343) ∨ (¬ p4399) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial31698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory20954 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 5 7)
  exact rule31698 (meaning t m 2027) (meaning t m 2641) (meaning t m 3051) (meaning t m 3368) (meaning t m 3486) (meaning t m 3759) (meaning t m 4343) (meaning t m 4399) (meaning t m 4975) source

theorem rule31699 (p1976 p2027 p2169 p2295 p3324 p3365 p3822 p4841 : Prop) (h : (¬ p1976) ∨ (¬ p3365) ∨ p2169 ∨ (¬ p3324) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p2295)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3822) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial31699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory20955 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31699 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2295) (meaning t m 3324) (meaning t m 3365) (meaning t m 3822) (meaning t m 4841) source

theorem rule31700 (p2027 p2138 p2528 p3367 p3641 p3690 p4244 p4669 p4734 : Prop) (h : (¬ p3641) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2528) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4734) ∨ (¬ p4669) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2528) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial31700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory20956 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule31700 (meaning t m 2027) (meaning t m 2138) (meaning t m 2528) (meaning t m 3367) (meaning t m 3641) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) (meaning t m 4734) source

theorem rule31701 (p2027 p2641 p3662 p3986 p4110 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p3986) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4110) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial31701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory20957 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule31701 (meaning t m 2027) (meaning t m 2641) (meaning t m 3662) (meaning t m 3986) (meaning t m 4110) (meaning t m 4705) source

theorem rule31705 (p2005 p2027 p2307 p2588 p2779 p2829 p2842 p3585 : Prop) (h : (¬ p2005) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2829) ∨ (¬ p2779) ∨ p2842 ∨ (¬ p2307) ∨ (¬ p2588)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial31705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory20961 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule31705 (meaning t m 2005) (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 2779) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) source

theorem rule31706 (p1984 p2027 p2764 p3688 p3917 p3954 p4191 : Prop) (h : (¬ p3917) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3688) ∨ p2764 ∨ (¬ p3954) ∨ (¬ p4191)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial31706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory20962 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 9) (m.theta 9 10)
  exact rule31706 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4191) source

theorem rule31707 (p2819 p3917 p3990 : Prop) (h : (¬ p3917) ∨ (¬ p3990) ∨ (¬ p2819)) : (¬ p2819) ∨ (¬ p3917) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial31707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory20963 (m.theta 2 6) (m.theta 6 8) (m.theta 6 9)
  exact rule31707 (meaning t m 2819) (meaning t m 3917) (meaning t m 3990) source

theorem rule31711 (p2027 p2098 p2145 p2588 p3266 p3609 p3646 p4203 p4260 p4831 : Prop) (h : (¬ p3609) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p3266) ∨ (¬ p4831) ∨ (¬ p2145) ∨ (¬ p3646) ∨ (¬ p4260) ∨ (¬ p4203) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2145) ∨ (¬ p2588) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial31711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory20967 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule31711 (meaning t m 2027) (meaning t m 2098) (meaning t m 2145) (meaning t m 2588) (meaning t m 3266) (meaning t m 3609) (meaning t m 3646) (meaning t m 4203) (meaning t m 4260) (meaning t m 4831) source

theorem rule31716 (p1977 p2027 p2764 p2957 p3646 p3662 p3744 p4191 : Prop) (h : p2764 ∨ (¬ p1977) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p2957) ∨ (¬ p4191)) : (¬ p1977) ∨ (p2027) ∨ (p2764) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3744) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial31716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory20972 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule31716 (meaning t m 1977) (meaning t m 2027) (meaning t m 2764) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) (meaning t m 3744) (meaning t m 4191) source

theorem rule31724 (p1979 p2027 p3136 p3146 p3578 p3877 p4118 : Prop) (h : (¬ p3136) ∨ (¬ p1979) ∨ (¬ p3877) ∨ p3578 ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4118)) : (¬ p1979) ∨ (p2027) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p3877) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial31724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory20980 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule31724 (meaning t m 1979) (meaning t m 2027) (meaning t m 3136) (meaning t m 3146) (meaning t m 3578) (meaning t m 3877) (meaning t m 4118) source

theorem rule31725 (p2027 p2295 p2313 p4110 p4336 p4356 p4705 : Prop) (h : (¬ p4336) ∨ (¬ p4705) ∨ (¬ p4110) ∨ (¬ p2313) ∨ (¬ p4356) ∨ p2027 ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial31725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory20981 t (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule31725 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 4110) (meaning t m 4336) (meaning t m 4356) (meaning t m 4705) source

theorem rule31727 (p1992 p2027 p2462 p2608 p3591 p3822 p3918 p4107 : Prop) (h : (¬ p1992) ∨ (¬ p3918) ∨ (¬ p3822) ∨ p2462 ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2608) ∨ (¬ p3591) ∨ (¬ p3822) ∨ (¬ p3918) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial31727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory20983 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule31727 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2608) (meaning t m 3591) (meaning t m 3822) (meaning t m 3918) (meaning t m 4107) source

theorem rule31728 (p2027 p2139 p2373 p2797 p2963 p3051 p3877 p4043 p4235 p4236 : Prop) (h : (¬ p4043) ∨ (¬ p3051) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p3877) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p2139) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2373) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4235) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial31728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory20984 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule31728 (meaning t m 2027) (meaning t m 2139) (meaning t m 2373) (meaning t m 2797) (meaning t m 2963) (meaning t m 3051) (meaning t m 3877) (meaning t m 4043) (meaning t m 4235) (meaning t m 4236) source

theorem rule31730 (p2027 p2252 p2750 p2753 p2774 p2819 p2952 p3979 p4208 p4322 p5119 : Prop) (h : (¬ p2753) ∨ (¬ p2952) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p3979) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p4208) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3979) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20986 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31730 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 2952) (meaning t m 3979) (meaning t m 4208) (meaning t m 4322) (meaning t m 5119) source

theorem rule31731 (p1991 p2027 p2633 p2655 p3343 p3346 p3644 p3742 : Prop) (h : (¬ p1991) ∨ (¬ p3644) ∨ p2027 ∨ p2633 ∨ (¬ p3742) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p2655)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p2655) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial31731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory20987 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8)
  exact rule31731 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 2655) (meaning t m 3343) (meaning t m 3346) (meaning t m 3644) (meaning t m 3742) source

theorem rule31733 (p2027 p2098 p2748 p2901 p3055 p3368 p3556 p3609 p3645 p4208 p4749 p5059 : Prop) (h : (¬ p3645) ∨ (¬ p2748) ∨ (¬ p3368) ∨ (¬ p3556) ∨ (¬ p3055) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p3609) ∨ (¬ p2098) ∨ (¬ p5059) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2748) ∨ (¬ p2901) ∨ (¬ p3055) ∨ (¬ p3368) ∨ (¬ p3556) ∨ (¬ p3609) ∨ (¬ p3645) ∨ (¬ p4208) ∨ (¬ p4749) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial31733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory20989 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule31733 (meaning t m 2027) (meaning t m 2098) (meaning t m 2748) (meaning t m 2901) (meaning t m 3055) (meaning t m 3368) (meaning t m 3556) (meaning t m 3609) (meaning t m 3645) (meaning t m 4208) (meaning t m 4749) (meaning t m 5059) source

theorem rule31734 (p1982 p2027 p2252 p2363 p2633 p2657 p2745 p2797 p3567 p3570 p3683 p3876 p3998 p4001 p4114 p5580 : Prop) (h : (¬ p2745) ∨ (¬ p2657) ∨ (¬ p3567) ∨ (¬ p2363) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p3683) ∨ p2633 ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p3570) ∨ (¬ p2252) ∨ (¬ p5580) ∨ (¬ p4114) ∨ (¬ p3998)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3570) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p3998) ∨ (¬ p4001) ∨ (¬ p4114) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial31734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory20990 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31734 (meaning t m 1982) (meaning t m 2027) (meaning t m 2252) (meaning t m 2363) (meaning t m 2633) (meaning t m 2657) (meaning t m 2745) (meaning t m 2797) (meaning t m 3567) (meaning t m 3570) (meaning t m 3683) (meaning t m 3876) (meaning t m 3998) (meaning t m 4001) (meaning t m 4114) (meaning t m 5580) source

theorem rule31735 (p1989 p2027 p2406 p2427 p2699 p3379 p3486 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3486) ∨ (¬ p1989)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial31735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory20991 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule31735 (meaning t m 1989) (meaning t m 2027) (meaning t m 2406) (meaning t m 2427) (meaning t m 2699) (meaning t m 3379) (meaning t m 3486) source

theorem rule31736 (p2027 p2737 p3105 p4363 p4874 p5049 : Prop) (h : (¬ p5049) ∨ (¬ p4874) ∨ (¬ p4363) ∨ (¬ p3105) ∨ p2027 ∨ (¬ p2737)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3105) ∨ (¬ p4363) ∨ (¬ p4874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial31736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory20992 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 9)
  exact rule31736 (meaning t m 2027) (meaning t m 2737) (meaning t m 3105) (meaning t m 4363) (meaning t m 4874) (meaning t m 5049) source

theorem rule31737 (p2027 p2156 p3323 p4032 p4033 p4560 : Prop) (h : (¬ p2156) ∨ (¬ p4560) ∨ p2027 ∨ (¬ p4032) ∨ (¬ p3323) ∨ (¬ p4033)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3323) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial31737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory20993 t (m.theta 0 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule31737 (meaning t m 2027) (meaning t m 2156) (meaning t m 3323) (meaning t m 4032) (meaning t m 4033) (meaning t m 4560) source

theorem rule31741 (p2027 p2138 p2449 p2761 p2807 p3758 p4393 p4786 p5254 : Prop) (h : (¬ p4786) ∨ (¬ p2449) ∨ (¬ p5254) ∨ (¬ p2138) ∨ (¬ p2807) ∨ (¬ p2761) ∨ (¬ p4393) ∨ p2027 ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4786) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial31741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory20997 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule31741 (meaning t m 2027) (meaning t m 2138) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3758) (meaning t m 4393) (meaning t m 4786) (meaning t m 5254) source

theorem rule31742 (p2027 p2246 p2744 p2946 p3115 p3366 p3425 p3659 p3680 p5123 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p2946) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial31742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20998 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31742 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2946) (meaning t m 3115) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 3680) (meaning t m 5123) (meaning t m 5558) source

theorem rule31743 (p2027 p2156 p3697 p3969 p4507 p5590 : Prop) (h : (¬ p2156) ∨ (¬ p3697) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p4507) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3697) ∨ (¬ p3969) ∨ (¬ p4507) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial31743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory20999 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule31743 (meaning t m 2027) (meaning t m 2156) (meaning t m 3697) (meaning t m 3969) (meaning t m 4507) (meaning t m 5590) source

theorem rule31746 (p2027 p2156 p2534 p2958 p3055 p3115 p3874 p3952 p4450 p4786 : Prop) (h : (¬ p3055) ∨ (¬ p2534) ∨ (¬ p3952) ∨ (¬ p2156) ∨ (¬ p4786) ∨ (¬ p2958) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2534) ∨ (¬ p2958) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3874) ∨ (¬ p3952) ∨ (¬ p4450) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial31746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory21002 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule31746 (meaning t m 2027) (meaning t m 2156) (meaning t m 2534) (meaning t m 2958) (meaning t m 3055) (meaning t m 3115) (meaning t m 3874) (meaning t m 3952) (meaning t m 4450) (meaning t m 4786) source

theorem rule31748 (p2027 p2299 p2780 p3246 p3366 p3399 p3452 p3571 p3822 p4376 p4668 : Prop) (h : (¬ p3571) ∨ (¬ p3822) ∨ (¬ p3246) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p2780) ∨ (¬ p2299) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3571) ∨ (¬ p3822) ∨ (¬ p4376) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial31748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory21004 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31748 (meaning t m 2027) (meaning t m 2299) (meaning t m 2780) (meaning t m 3246) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3571) (meaning t m 3822) (meaning t m 4376) (meaning t m 4668) source

theorem rule31752 (p2027 p2230 p2252 p2373 p2741 p2963 p3519 p3969 p4037 p4191 p4376 p5119 : Prop) (h : (¬ p4037) ∨ (¬ p2252) ∨ (¬ p4191) ∨ (¬ p4376) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p5119) ∨ (¬ p2373) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4376) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory21008 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31752 (meaning t m 2027) (meaning t m 2230) (meaning t m 2252) (meaning t m 2373) (meaning t m 2741) (meaning t m 2963) (meaning t m 3519) (meaning t m 3969) (meaning t m 4037) (meaning t m 4191) (meaning t m 4376) (meaning t m 5119) source

theorem rule31756 (p2027 p2248 p2284 p2946 p3737 p3954 p4379 p5250 p5387 : Prop) (h : (¬ p3737) ∨ (¬ p4379) ∨ (¬ p5250) ∨ (¬ p5387) ∨ (¬ p2946) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3737) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5250) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial31756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5250)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory21012 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 9) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 9 10)
  exact rule31756 (meaning t m 2027) (meaning t m 2248) (meaning t m 2284) (meaning t m 2946) (meaning t m 3737) (meaning t m 3954) (meaning t m 4379) (meaning t m 5250) (meaning t m 5387) source

theorem rule31760 (p2027 p2156 p2247 p2996 p3125 p3461 p4391 p4521 p4831 : Prop) (h : (¬ p2996) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p4831) ∨ (¬ p2156) ∨ (¬ p4391) ∨ (¬ p3461) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4391) ∨ (¬ p4521) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial31760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory21016 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule31760 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2996) (meaning t m 3125) (meaning t m 3461) (meaning t m 4391) (meaning t m 4521) (meaning t m 4831) source

theorem rule31763 (p1994 p2027 p2406 p2440 p2764 p3346 p3347 p4425 : Prop) (h : p2027 ∨ (¬ p4425) ∨ p2764 ∨ (¬ p3347) ∨ (¬ p3346) ∨ (¬ p1994) ∨ (¬ p2440) ∨ (¬ p2406)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2764) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial31763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory21019 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule31763 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2764) (meaning t m 3346) (meaning t m 3347) (meaning t m 4425) source

theorem rule31765 (p2027 p2470 p3343 p3461 p3519 p3645 p4032 p4256 p4322 p4376 p4874 p5322 : Prop) (h : (¬ p3519) ∨ (¬ p4256) ∨ (¬ p3343) ∨ (¬ p4032) ∨ (¬ p4376) ∨ (¬ p4322) ∨ (¬ p3461) ∨ (¬ p3645) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p4874) ∨ (¬ p5322)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3343) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4256) ∨ (¬ p4322) ∨ (¬ p4376) ∨ (¬ p4874) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial31765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory21021 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule31765 (meaning t m 2027) (meaning t m 2470) (meaning t m 3343) (meaning t m 3461) (meaning t m 3519) (meaning t m 3645) (meaning t m 4032) (meaning t m 4256) (meaning t m 4322) (meaning t m 4376) (meaning t m 4874) (meaning t m 5322) source

theorem rule31768 (p2027 p2246 p2608 p2744 p3166 p3506 p3591 p4026 p4444 p4604 p5111 : Prop) (h : (¬ p5111) ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p3166) ∨ (¬ p2246) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3506) ∨ (¬ p4444) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3506) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial31768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory21024 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 8) (m.theta 3 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule31768 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3166) (meaning t m 3506) (meaning t m 3591) (meaning t m 4026) (meaning t m 4444) (meaning t m 4604) (meaning t m 5111) source

theorem rule31769 (p1976 p2027 p2619 p2765 p3055 p3146 p3644 p3698 p3876 p4110 p4133 p4347 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p2619) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p4347) ∨ (¬ p3698) ∨ (¬ p3146)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2619) ∨ (p2765) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3698) ∨ (¬ p3876) ∨ (¬ p4110) ∨ (¬ p4133) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial31769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory21025 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31769 (meaning t m 1976) (meaning t m 2027) (meaning t m 2619) (meaning t m 2765) (meaning t m 3055) (meaning t m 3146) (meaning t m 3644) (meaning t m 3698) (meaning t m 3876) (meaning t m 4110) (meaning t m 4133) (meaning t m 4347) source

theorem rule31770 (p1984 p2027 p2202 p3434 p3684 p3817 p4366 p5085 : Prop) (h : (¬ p5085) ∨ (¬ p4366) ∨ (¬ p1984) ∨ (¬ p3817) ∨ (¬ p3684) ∨ (¬ p3434) ∨ p2027 ∨ p2202) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p3434) ∨ (¬ p3684) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial31770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory21026 t (m.theta 0 1) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 7 9)
  exact rule31770 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 3434) (meaning t m 3684) (meaning t m 3817) (meaning t m 4366) (meaning t m 5085) source

theorem rule31775 (p1988 p2027 p2611 p2946 p3680 p3755 p4039 p4117 p4315 : Prop) (h : (¬ p1988) ∨ (¬ p2946) ∨ (¬ p4117) ∨ p2611 ∨ (¬ p4315) ∨ (¬ p4039) ∨ (¬ p3755) ∨ (¬ p3680) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (p2611) ∨ (¬ p2946) ∨ (¬ p3680) ∨ (¬ p3755) ∨ (¬ p4039) ∨ (¬ p4117) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial31775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory21031 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule31775 (meaning t m 1988) (meaning t m 2027) (meaning t m 2611) (meaning t m 2946) (meaning t m 3680) (meaning t m 3755) (meaning t m 4039) (meaning t m 4117) (meaning t m 4315) source

theorem rule31776 (p2027 p2246 p2352 p2387 p2749 p2807 p3096 p3506 p3645 p3744 p4198 p4202 p4381 p4625 p4661 p5216 : Prop) (h : (¬ p4202) ∨ (¬ p2387) ∨ (¬ p4198) ∨ (¬ p2352) ∨ (¬ p3096) ∨ (¬ p5216) ∨ (¬ p3744) ∨ (¬ p4661) ∨ (¬ p2246) ∨ (¬ p4625) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2749) ∨ (¬ p4381) ∨ (¬ p3645) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3096) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3744) ∨ (¬ p4198) ∨ (¬ p4202) ∨ (¬ p4381) ∨ (¬ p4625) ∨ (¬ p4661) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4661)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21032 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31776 (meaning t m 2027) (meaning t m 2246) (meaning t m 2352) (meaning t m 2387) (meaning t m 2749) (meaning t m 2807) (meaning t m 3096) (meaning t m 3506) (meaning t m 3645) (meaning t m 3744) (meaning t m 4198) (meaning t m 4202) (meaning t m 4381) (meaning t m 4625) (meaning t m 4661) (meaning t m 5216) source

theorem rule31781 (p2027 p2589 p2807 p3572 p3744 p3755 p4110 p4117 p4729 p5276 : Prop) (h : (¬ p3572) ∨ (¬ p5276) ∨ (¬ p3755) ∨ (¬ p3744) ∨ (¬ p4117) ∨ (¬ p2807) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5276) := by
  classical
  tauto

theorem initial31781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5276)) := by
  have source := ElevenTheory.theory21037 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule31781 (meaning t m 2027) (meaning t m 2589) (meaning t m 2807) (meaning t m 3572) (meaning t m 3744) (meaning t m 3755) (meaning t m 4110) (meaning t m 4117) (meaning t m 4729) (meaning t m 5276) source

theorem rule31788 (p1994 p2027 p2406 p2440 p2476 p2534 p2766 p3347 : Prop) (h : p2766 ∨ (¬ p2440) ∨ (¬ p1994) ∨ (¬ p2476) ∨ (¬ p3347) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2534)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3347) := by
  classical
  tauto

theorem initial31788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3347)) := by
  have source := ElevenTheory.theory21044 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule31788 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2476) (meaning t m 2534) (meaning t m 2766) (meaning t m 3347) source

theorem rule31789 (p2027 p2241 p2641 p3323 p3425 p3659 p4330 p4348 p4736 : Prop) (h : (¬ p3323) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial31789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory21045 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule31789 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3323) (meaning t m 3425) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) (meaning t m 4736) source

theorem rule31791 (p2027 p2122 p2396 p2753 p2774 p3379 p3860 p3950 p4261 p5216 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p4261) ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p3860) ∨ (¬ p2753) ∨ (¬ p2122) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21047 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule31791 (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2753) (meaning t m 2774) (meaning t m 3379) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 5216) source

theorem rule31796 (p2027 p2307 p2819 p3238 p3452 p3822 p3880 p4134 p5017 : Prop) (h : (¬ p3238) ∨ (¬ p3880) ∨ (¬ p3452) ∨ (¬ p4134) ∨ (¬ p5017) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2819) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial31796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory21052 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule31796 (meaning t m 2027) (meaning t m 2307) (meaning t m 2819) (meaning t m 3238) (meaning t m 3452) (meaning t m 3822) (meaning t m 3880) (meaning t m 4134) (meaning t m 5017) source

theorem rule31798 (p1987 p2027 p2417 p2737 p2914 p3366 p3425 p3947 p4777 : Prop) (h : (¬ p1987) ∨ p2914 ∨ p2027 ∨ (¬ p3425) ∨ (¬ p2417) ∨ (¬ p2737) ∨ (¬ p4777) ∨ (¬ p3947) ∨ (¬ p3366)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2737) ∨ (p2914) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3947) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial31798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory21054 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule31798 (meaning t m 1987) (meaning t m 2027) (meaning t m 2417) (meaning t m 2737) (meaning t m 2914) (meaning t m 3366) (meaning t m 3425) (meaning t m 3947) (meaning t m 4777) source

theorem rule31799 (p2027 p2192 p2210 p3125 p3365 p3877 p4118 p4330 p4736 : Prop) (h : (¬ p2192) ∨ (¬ p4118) ∨ (¬ p2210) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4330) ∨ (¬ p3877) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial31799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory21055 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule31799 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 3125) (meaning t m 3365) (meaning t m 3877) (meaning t m 4118) (meaning t m 4330) (meaning t m 4736) source

theorem rule31804 (p1976 p2027 p2622 p2741 p3055 p3136 p3367 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p2741) ∨ (¬ p1976) ∨ p2622) : (¬ p1976) ∨ (p2027) ∨ (p2622) ∨ (¬ p2741) ∨ (¬ p3055) ∨ (¬ p3136) ∨ (¬ p3367) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial31804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory21060 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule31804 (meaning t m 1976) (meaning t m 2027) (meaning t m 2622) (meaning t m 2741) (meaning t m 3055) (meaning t m 3136) (meaning t m 3367) (meaning t m 3662) source

theorem rule31806 (p2027 p3588 p3599 p3947 p4783 p5233 : Prop) (h : p2027 ∨ (¬ p4783) ∨ (¬ p5233) ∨ (¬ p3947) ∨ (¬ p3588) ∨ (¬ p3599)) : (p2027) ∨ (¬ p3588) ∨ (¬ p3599) ∨ (¬ p3947) ∨ (¬ p4783) ∨ (¬ p5233) := by
  classical
  tauto

theorem initial31806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4783)) ∨ (¬ (meaning t m 5233)) := by
  have source := ElevenTheory.theory21062 t (m.theta 1 2) (m.theta 2 7) (m.theta 2 9) (m.theta 3 7) (m.theta 7 9)
  exact rule31806 (meaning t m 2027) (meaning t m 3588) (meaning t m 3599) (meaning t m 3947) (meaning t m 4783) (meaning t m 5233) source

theorem rule31811 (p2027 p2534 p3755 p3877 p4350 p5012 : Prop) (h : (¬ p5012) ∨ (¬ p4350) ∨ (¬ p3877) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p2534)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4350) ∨ (¬ p5012) := by
  classical
  tauto

theorem initial31811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4350)) ∨ (¬ (meaning t m 5012)) := by
  have source := ElevenTheory.theory21067 t (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 8) (m.theta 8 9)
  exact rule31811 (meaning t m 2027) (meaning t m 2534) (meaning t m 3755) (meaning t m 3877) (meaning t m 4350) (meaning t m 5012) source

theorem rule31818 (p2363 p3256 p4769 : Prop) (h : (¬ p4769) ∨ (¬ p3256) ∨ p2363) : (p2363) ∨ (¬ p3256) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial31818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2363) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory21074 (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31818 (meaning t m 2363) (meaning t m 3256) (meaning t m 4769) source

theorem rule31821 (p2027 p2860 p2946 p3414 p3699 p4316 p4555 : Prop) (h : (¬ p2860) ∨ (¬ p4555) ∨ (¬ p4316) ∨ (¬ p2946) ∨ (¬ p3699) ∨ (¬ p3414) ∨ p2027) : (p2027) ∨ (¬ p2860) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4316) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial31821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory21077 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule31821 (meaning t m 2027) (meaning t m 2860) (meaning t m 2946) (meaning t m 3414) (meaning t m 3699) (meaning t m 4316) (meaning t m 4555) source

theorem rule31822 (p2027 p2249 p2509 p2657 p2761 p3027 p3487 p3516 p4066 p4286 p5123 : Prop) (h : (¬ p3027) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p3487) ∨ (¬ p4066) ∨ (¬ p2657) ∨ (¬ p3516) ∨ (¬ p2761) ∨ (¬ p2249) ∨ (¬ p2509) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2509) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3487) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial31822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory21078 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31822 (meaning t m 2027) (meaning t m 2249) (meaning t m 2509) (meaning t m 2657) (meaning t m 2761) (meaning t m 3027) (meaning t m 3487) (meaning t m 3516) (meaning t m 4066) (meaning t m 4286) (meaning t m 5123) source

theorem rule31827 (p1988 p2027 p2114 p2737 p2811 p3166 p3256 p3266 : Prop) (h : (¬ p3256) ∨ p2114 ∨ (¬ p2737) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2811) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial31827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory21083 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule31827 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2811) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) source

theorem rule31836 (p1983 p2027 p2323 p2685 p2946 p3246 p4315 p4333 : Prop) (h : (¬ p1983) ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p4333) ∨ (¬ p2685)) : (¬ p1983) ∨ (p2027) ∨ (p2323) ∨ (¬ p2685) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p4315) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial31836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory21092 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule31836 (meaning t m 1983) (meaning t m 2027) (meaning t m 2323) (meaning t m 2685) (meaning t m 2946) (meaning t m 3246) (meaning t m 4315) (meaning t m 4333) source

theorem rule31837 (p2027 p2190 p2534 p3146 p3922 p3923 p4157 p4564 : Prop) (h : (¬ p4564) ∨ (¬ p3922) ∨ (¬ p2190) ∨ (¬ p4157) ∨ (¬ p3146) ∨ (¬ p2534) ∨ (¬ p3923) ∨ p2027) : (p2027) ∨ (¬ p2190) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p4157) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial31837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory21093 t (m.theta 1 6) (m.theta 3 6) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31837 (meaning t m 2027) (meaning t m 2190) (meaning t m 2534) (meaning t m 3146) (meaning t m 3922) (meaning t m 3923) (meaning t m 4157) (meaning t m 4564) source

theorem rule31838 (p2027 p2132 p2509 p2534 p2860 p3125 p3452 p4330 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2860) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p2132) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4330) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory21094 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule31838 (meaning t m 2027) (meaning t m 2132) (meaning t m 2509) (meaning t m 2534) (meaning t m 2860) (meaning t m 3125) (meaning t m 3452) (meaning t m 4330) (meaning t m 4733) source

theorem rule31840 (p2027 p2696 p3527 p3551 p3820 p4418 p4431 p5049 : Prop) (h : (¬ p2696) ∨ (¬ p3820) ∨ (¬ p3551) ∨ (¬ p3527) ∨ (¬ p5049) ∨ (¬ p4431) ∨ p2027 ∨ (¬ p4418)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4418) ∨ (¬ p4431) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial31840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory21096 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 2 5) (m.theta 7 8)
  exact rule31840 (meaning t m 2027) (meaning t m 2696) (meaning t m 3527) (meaning t m 3551) (meaning t m 3820) (meaning t m 4418) (meaning t m 4431) (meaning t m 5049) source

theorem rule31846 (p2010 p2027 p2114 p3399 p3527 p3644 p3954 : Prop) (h : (¬ p3644) ∨ (¬ p2010) ∨ (¬ p3399) ∨ p2027 ∨ p2114 ∨ (¬ p3954) ∨ (¬ p3527)) : (¬ p2010) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial31846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory21102 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule31846 (meaning t m 2010) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3527) (meaning t m 3644) (meaning t m 3954) source

theorem rule31848 (p1980 p2027 p2331 p2396 p2997 p3414 p3947 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p3947) ∨ (¬ p1980) ∨ (¬ p3414) ∨ (¬ p2396) ∨ (¬ p2331)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial31848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory21104 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule31848 (meaning t m 1980) (meaning t m 2027) (meaning t m 2331) (meaning t m 2396) (meaning t m 2997) (meaning t m 3414) (meaning t m 3947) source

theorem rule31850 (p1980 p2027 p2148 p2220 p2331 p2952 p3497 : Prop) (h : p2148 ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2331) ∨ (¬ p1980) ∨ (¬ p3497)) : (¬ p1980) ∨ (p2027) ∨ (p2148) ∨ (¬ p2220) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial31850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory21106 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule31850 (meaning t m 1980) (meaning t m 2027) (meaning t m 2148) (meaning t m 2220) (meaning t m 2331) (meaning t m 2952) (meaning t m 3497) source

theorem rule31856 (p2027 p2254 p2911 p2922 p2963 p3379 p3568 p3690 p4140 p4666 : Prop) (h : (¬ p3690) ∨ (¬ p2254) ∨ (¬ p4140) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p2963) ∨ (¬ p2911) ∨ (¬ p4666) ∨ (¬ p2922) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4140) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial31856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory21112 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31856 (meaning t m 2027) (meaning t m 2254) (meaning t m 2911) (meaning t m 2922) (meaning t m 2963) (meaning t m 3379) (meaning t m 3568) (meaning t m 3690) (meaning t m 4140) (meaning t m 4666) source

theorem rule31860 (p2000 p2027 p2579 p2997 p3323 p3568 p4137 : Prop) (h : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ p2997 ∨ (¬ p4137) ∨ (¬ p3568) ∨ (¬ p3323)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2579) ∨ (p2997) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial31860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory21116 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule31860 (meaning t m 2000) (meaning t m 2027) (meaning t m 2579) (meaning t m 2997) (meaning t m 3323) (meaning t m 3568) (meaning t m 4137) source

theorem rule31864 (p1988 p2027 p2651 p2766 p3276 p3333 p3661 p3692 p3969 p4315 p4343 p4790 p5600 : Prop) (h : p2766 ∨ (¬ p1988) ∨ (¬ p3276) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p3661) ∨ (¬ p4315) ∨ (¬ p5600) ∨ (¬ p3692) ∨ (¬ p4790) ∨ (¬ p3333) ∨ (¬ p2651) ∨ (¬ p4343)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3661) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p4315) ∨ (¬ p4343) ∨ (¬ p4790) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial31864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory21120 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule31864 (meaning t m 1988) (meaning t m 2027) (meaning t m 2651) (meaning t m 2766) (meaning t m 3276) (meaning t m 3333) (meaning t m 3661) (meaning t m 3692) (meaning t m 3969) (meaning t m 4315) (meaning t m 4343) (meaning t m 4790) (meaning t m 5600) source

theorem rule31867 (p2027 p2254 p2299 p2952 p3093 p3136 p3527 p3572 p4361 p4452 : Prop) (h : (¬ p2299) ∨ (¬ p3527) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p4361) ∨ (¬ p3093) ∨ (¬ p4452) ∨ (¬ p2952) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3527) ∨ (¬ p3572) ∨ (¬ p4361) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial31867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory21123 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule31867 (meaning t m 2027) (meaning t m 2254) (meaning t m 2299) (meaning t m 2952) (meaning t m 3093) (meaning t m 3136) (meaning t m 3527) (meaning t m 3572) (meaning t m 4361) (meaning t m 4452) source

theorem rule31872 (p2027 p2307 p2578 p3016 p4256 p4432 p4501 : Prop) (h : (¬ p4501) ∨ (¬ p3016) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p4432) ∨ (¬ p2578) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial31872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory21128 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule31872 (meaning t m 2027) (meaning t m 2307) (meaning t m 2578) (meaning t m 3016) (meaning t m 4256) (meaning t m 4432) (meaning t m 4501) source

theorem rule31873 (p2027 p2132 p2177 p2254 p2707 p3414 p3553 p3583 p3589 p4473 : Prop) (h : (¬ p3553) ∨ (¬ p3414) ∨ (¬ p3583) ∨ (¬ p2254) ∨ (¬ p3589) ∨ (¬ p2707) ∨ (¬ p2132) ∨ (¬ p4473) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial31873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory21129 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule31873 (meaning t m 2027) (meaning t m 2132) (meaning t m 2177) (meaning t m 2254) (meaning t m 2707) (meaning t m 3414) (meaning t m 3553) (meaning t m 3583) (meaning t m 3589) (meaning t m 4473) source

theorem rule31874 (p1998 p2027 p2352 p2588 p2997 p3979 p5558 : Prop) (h : (¬ p5558) ∨ p2997 ∨ (¬ p2588) ∨ (¬ p3979) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2352)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial31874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory21130 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule31874 (meaning t m 1998) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2997) (meaning t m 3979) (meaning t m 5558) source

theorem rule31875 (p1978 p2027 p2563 p2764 p3646 p4033 p4191 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p1978) ∨ p2027 ∨ p2764 ∨ (¬ p3646) ∨ (¬ p2563) ∨ (¬ p4191) ∨ (¬ p4033)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2563) ∨ (p2764) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial31875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory21131 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule31875 (meaning t m 1978) (meaning t m 2027) (meaning t m 2563) (meaning t m 2764) (meaning t m 3646) (meaning t m 4033) (meaning t m 4191) (meaning t m 4948) source

theorem rule31876 (p2027 p2098 p2138 p4188 p4385 p5056 : Prop) (h : p2027 ∨ (¬ p4188) ∨ (¬ p2138) ∨ (¬ p5056) ∨ (¬ p2098) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p4188) ∨ (¬ p4385) ∨ (¬ p5056) := by
  classical
  tauto

theorem initial31876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5056)) := by
  have source := ElevenTheory.theory21132 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 5 9)
  exact rule31876 (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 4188) (meaning t m 4385) (meaning t m 5056) source

theorem rule31880 (p4158 p4506 p4596 : Prop) (h : (¬ p4506) ∨ (¬ p4596) ∨ p4158) : (p4158) ∨ (¬ p4506) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial31880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4158) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory21136 t (m.theta 4 8) (m.theta 5 8) (m.theta 6 8)
  exact rule31880 (meaning t m 4158) (meaning t m 4506) (meaning t m 4596) source

theorem rule31887 (p1979 p2027 p2252 p2764 p2963 p2992 p4037 p4191 : Prop) (h : (¬ p2992) ∨ (¬ p2252) ∨ (¬ p1979) ∨ p2027 ∨ p2764 ∨ (¬ p2963) ∨ (¬ p4191) ∨ (¬ p4037)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2252) ∨ (p2764) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial31887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory21143 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule31887 (meaning t m 1979) (meaning t m 2027) (meaning t m 2252) (meaning t m 2764) (meaning t m 2963) (meaning t m 2992) (meaning t m 4037) (meaning t m 4191) source

theorem rule31888 (p2027 p2230 p2476 p3156 p3693 p4705 : Prop) (h : (¬ p3156) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p4705) ∨ (¬ p3693) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p3156) ∨ (¬ p3693) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial31888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory21144 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule31888 (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 3156) (meaning t m 3693) (meaning t m 4705) source

theorem rule31892 (p3554 p4400 p4874 : Prop) (h : (¬ p4874) ∨ (¬ p3554) ∨ p4400) : (¬ p3554) ∨ (p4400) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial31892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3554)) ∨ (meaning t m 4400) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory21148 (m.theta 1 2) (m.theta 1 5) (m.theta 1 7)
  exact rule31892 (meaning t m 3554) (meaning t m 4400) (meaning t m 4874) source

theorem rule31893 (p2027 p2143 p2352 p2493 p2598 p3097 p3583 p3590 p3646 p4405 p4737 : Prop) (h : (¬ p4405) ∨ (¬ p3646) ∨ (¬ p2143) ∨ (¬ p3590) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2598) ∨ (¬ p2493) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3590) ∨ (¬ p3646) ∨ (¬ p4405) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial31893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory21149 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31893 (meaning t m 2027) (meaning t m 2143) (meaning t m 2352) (meaning t m 2493) (meaning t m 2598) (meaning t m 3097) (meaning t m 3583) (meaning t m 3590) (meaning t m 3646) (meaning t m 4405) (meaning t m 4737) source

theorem rule31897 (p1984 p2027 p2166 p2247 p2533 p2873 p3662 p4208 : Prop) (h : (¬ p3662) ∨ (¬ p1984) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2533) ∨ (¬ p4208) ∨ p2873 ∨ (¬ p2166)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2247) ∨ (¬ p2533) ∨ (p2873) ∨ (¬ p3662) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial31897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2533)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory21153 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9)
  exact rule31897 (meaning t m 1984) (meaning t m 2027) (meaning t m 2166) (meaning t m 2247) (meaning t m 2533) (meaning t m 2873) (meaning t m 3662) (meaning t m 4208) source

theorem rule31898 (p3483 p3822 p4025 : Prop) (h : (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4025)) : (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial31898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory21154 (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule31898 (meaning t m 3483) (meaning t m 3822) (meaning t m 4025) source

theorem rule31903 (p2003 p2027 p2387 p2462 p2819 p3822 p4107 : Prop) (h : (¬ p2003) ∨ (¬ p2387) ∨ (¬ p3822) ∨ (¬ p2819) ∨ p2027 ∨ p2462 ∨ (¬ p4107)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2387) ∨ (p2462) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial31903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory21159 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule31903 (meaning t m 2003) (meaning t m 2027) (meaning t m 2387) (meaning t m 2462) (meaning t m 2819) (meaning t m 3822) (meaning t m 4107) source

theorem rule31904 (p1989 p2027 p2938 p3497 p3747 p4173 p4228 p4336 p4393 : Prop) (h : (¬ p4393) ∨ (¬ p3747) ∨ (¬ p4228) ∨ (¬ p4336) ∨ (¬ p3497) ∨ p2938 ∨ (¬ p1989) ∨ (¬ p4173) ∨ p2027) : (¬ p1989) ∨ (p2027) ∨ (p2938) ∨ (¬ p3497) ∨ (¬ p3747) ∨ (¬ p4173) ∨ (¬ p4228) ∨ (¬ p4336) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial31904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory21160 t (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 10)
  exact rule31904 (meaning t m 1989) (meaning t m 2027) (meaning t m 2938) (meaning t m 3497) (meaning t m 3747) (meaning t m 4173) (meaning t m 4228) (meaning t m 4336) (meaning t m 4393) source

theorem rule31905 (p2138 p4232 p5025 : Prop) (h : (¬ p2138) ∨ (¬ p5025) ∨ p4232) : (¬ p2138) ∨ (p4232) ∨ (¬ p5025) := by
  classical
  tauto

theorem initial31905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (meaning t m 4232) ∨ (¬ (meaning t m 5025)) := by
  have source := ElevenTheory.theory21161 (m.theta 0 2) (m.theta 2 5) (m.theta 2 9)
  exact rule31905 (meaning t m 2138) (meaning t m 4232) (meaning t m 5025) source

theorem rule31907 (p2027 p3537 p3688 p3822 p4326 p4405 : Prop) (h : (¬ p4326) ∨ (¬ p3822) ∨ (¬ p4405) ∨ (¬ p3537) ∨ (¬ p3688) ∨ p2027) : (p2027) ∨ (¬ p3537) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4326) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial31907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory21163 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8)
  exact rule31907 (meaning t m 2027) (meaning t m 3537) (meaning t m 3688) (meaning t m 3822) (meaning t m 4326) (meaning t m 4405) source

theorem rule31913 (p1975 p2027 p2230 p2274 p2563 p2622 p2630 p2656 : Prop) (h : (¬ p2563) ∨ p2027 ∨ (¬ p2656) ∨ p2622 ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2274) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) := by
  classical
  tauto

theorem initial31913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) := by
  have source := ElevenTheory.theory21169 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule31913 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2563) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) source

theorem rule31919 (p2027 p2363 p2534 p2553 p3573 p4501 : Prop) (h : (¬ p4501) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2363) ∨ (¬ p3573) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2553) ∨ (¬ p3573) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial31919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory21175 t (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule31919 (meaning t m 2027) (meaning t m 2363) (meaning t m 2534) (meaning t m 2553) (meaning t m 3573) (meaning t m 4501) source

theorem rule31920 (p1997 p2027 p2169 p2319 p2542 p3125 p3742 p3946 p3989 p4279 : Prop) (h : (¬ p2542) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4279) ∨ (¬ p2319) ∨ p2169 ∨ (¬ p3742) ∨ (¬ p3989) ∨ (¬ p3125) ∨ (¬ p3946)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2319) ∨ (¬ p2542) ∨ (¬ p3125) ∨ (¬ p3742) ∨ (¬ p3946) ∨ (¬ p3989) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial31920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory21176 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule31920 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2319) (meaning t m 2542) (meaning t m 3125) (meaning t m 3742) (meaning t m 3946) (meaning t m 3989) (meaning t m 4279) source

theorem rule31924 (p2027 p2143 p2829 p3365 p3366 p3556 p3690 p3914 p4381 p5052 p5250 : Prop) (h : (¬ p3914) ∨ (¬ p3556) ∨ (¬ p4381) ∨ (¬ p5250) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3365) ∨ (¬ p2829) ∨ (¬ p3690) ∨ (¬ p5052) ∨ (¬ p2143)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3914) ∨ (¬ p4381) ∨ (¬ p5052) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial31924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5052)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory21180 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule31924 (meaning t m 2027) (meaning t m 2143) (meaning t m 2829) (meaning t m 3365) (meaning t m 3366) (meaning t m 3556) (meaning t m 3690) (meaning t m 3914) (meaning t m 4381) (meaning t m 5052) (meaning t m 5250) source

theorem rule31928 (p2027 p2264 p2589 p2807 p3941 p4117 p4322 p4729 p4948 p5119 : Prop) (h : (¬ p2589) ∨ (¬ p4117) ∨ (¬ p3941) ∨ (¬ p4729) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p4948) ∨ (¬ p2264) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p4117) ∨ (¬ p4322) ∨ (¬ p4729) ∨ (¬ p4948) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory21184 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31928 (meaning t m 2027) (meaning t m 2264) (meaning t m 2589) (meaning t m 2807) (meaning t m 3941) (meaning t m 4117) (meaning t m 4322) (meaning t m 4729) (meaning t m 4948) (meaning t m 5119) source

theorem rule31930 (p2027 p2248 p2534 p3166 p3256 p3555 p3989 p4173 p4596 : Prop) (h : (¬ p4596) ∨ (¬ p3989) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3555) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2534) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial31930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory21186 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule31930 (meaning t m 2027) (meaning t m 2248) (meaning t m 2534) (meaning t m 3166) (meaning t m 3256) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) (meaning t m 4596) source

theorem rule31937 (p1979 p2027 p2563 p2764 p3952 p4322 p4948 : Prop) (h : (¬ p3952) ∨ (¬ p1979) ∨ (¬ p4322) ∨ p2764 ∨ p2027 ∨ (¬ p4948) ∨ (¬ p2563)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2563) ∨ (p2764) ∨ (¬ p3952) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial31937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory21193 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule31937 (meaning t m 1979) (meaning t m 2027) (meaning t m 2563) (meaning t m 2764) (meaning t m 3952) (meaning t m 4322) (meaning t m 4948) source

theorem rule31939 (p2027 p2579 p2946 p3115 p3680 p3905 p3956 p4786 p5123 p5580 : Prop) (h : (¬ p2579) ∨ (¬ p2946) ∨ (¬ p5123) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p3115) ∨ (¬ p3956) ∨ (¬ p4786) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial31939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory21195 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31939 (meaning t m 2027) (meaning t m 2579) (meaning t m 2946) (meaning t m 3115) (meaning t m 3680) (meaning t m 3905) (meaning t m 3956) (meaning t m 4786) (meaning t m 5123) (meaning t m 5580) source

theorem rule31942 (p2000 p2027 p2765 p2922 p3238 p3540 p4110 : Prop) (h : (¬ p2000) ∨ p2765 ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p2922)) : (¬ p2000) ∨ (p2027) ∨ (p2765) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial31942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory21198 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule31942 (meaning t m 2000) (meaning t m 2027) (meaning t m 2765) (meaning t m 2922) (meaning t m 3238) (meaning t m 3540) (meaning t m 4110) source

theorem rule31943 (p2027 p2246 p2749 p2946 p3005 p3379 p3548 p4315 p4366 p4550 p5216 : Prop) (h : (¬ p3379) ∨ (¬ p5216) ∨ (¬ p4366) ∨ (¬ p2946) ∨ (¬ p4550) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p3548) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4315) ∨ (¬ p4366) ∨ (¬ p4550) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21199 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 7 8)
  exact rule31943 (meaning t m 2027) (meaning t m 2246) (meaning t m 2749) (meaning t m 2946) (meaning t m 3005) (meaning t m 3379) (meaning t m 3548) (meaning t m 4315) (meaning t m 4366) (meaning t m 4550) (meaning t m 5216) source

theorem rule31946 (p1975 p2027 p2132 p2245 p2274 p2545 p2860 p3073 p3172 p3859 p4111 p4118 p4733 : Prop) (h : (¬ p2274) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p4111) ∨ p2545 ∨ (¬ p2245) ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p1975) ∨ (¬ p3859) ∨ (¬ p4118) ∨ (¬ p3073)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2274) ∨ (p2545) ∨ (¬ p2860) ∨ (¬ p3073) ∨ (¬ p3172) ∨ (¬ p3859) ∨ (¬ p4111) ∨ (¬ p4118) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory21202 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 3 4) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule31946 (meaning t m 1975) (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2274) (meaning t m 2545) (meaning t m 2860) (meaning t m 3073) (meaning t m 3172) (meaning t m 3859) (meaning t m 4111) (meaning t m 4118) (meaning t m 4733) source

theorem rule31961 (p2005 p2027 p2230 p2323 p2663 p2972 p3016 p4034 p4208 p4700 : Prop) (h : p2323 ∨ (¬ p3016) ∨ (¬ p2663) ∨ (¬ p2230) ∨ (¬ p2005) ∨ (¬ p4034) ∨ p2027 ∨ (¬ p4208) ∨ (¬ p4700) ∨ (¬ p2972)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (p2323) ∨ (¬ p2663) ∨ (¬ p2972) ∨ (¬ p3016) ∨ (¬ p4034) ∨ (¬ p4208) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial31961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory21217 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule31961 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2323) (meaning t m 2663) (meaning t m 2972) (meaning t m 3016) (meaning t m 4034) (meaning t m 4208) (meaning t m 4700) source

theorem rule31964 (p1991 p2027 p2765 p2797 p2963 p3952 p4315 : Prop) (h : (¬ p4315) ∨ (¬ p2797) ∨ p2765 ∨ p2027 ∨ (¬ p3952) ∨ (¬ p1991) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (p2765) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3952) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial31964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory21220 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule31964 (meaning t m 1991) (meaning t m 2027) (meaning t m 2765) (meaning t m 2797) (meaning t m 2963) (meaning t m 3952) (meaning t m 4315) source

theorem rule31965 (p2027 p2518 p2928 p3821 p4279 p4404 p4666 : Prop) (h : (¬ p4404) ∨ (¬ p3821) ∨ (¬ p4666) ∨ (¬ p4279) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4404) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial31965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory21221 t (m.theta 0 7) (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9)
  exact rule31965 (meaning t m 2027) (meaning t m 2518) (meaning t m 2928) (meaning t m 3821) (meaning t m 4279) (meaning t m 4404) (meaning t m 4666) source

theorem rule31970 (p1984 p2027 p2190 p2202 p2563 p3583 p3694 p3954 : Prop) (h : (¬ p3583) ∨ (¬ p1984) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2190) ∨ p2202 ∨ (¬ p2563)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2190) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial31970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory21226 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule31970 (meaning t m 1984) (meaning t m 2027) (meaning t m 2190) (meaning t m 2202) (meaning t m 2563) (meaning t m 3583) (meaning t m 3694) (meaning t m 3954) source

theorem rule31978 (p2027 p2098 p2499 p3452 p3609 p3956 p4348 p4503 p4733 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p4503) ∨ (¬ p4348) ∨ (¬ p3452) ∨ (¬ p2098) ∨ (¬ p4733) ∨ (¬ p3956) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory21234 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31978 (meaning t m 2027) (meaning t m 2098) (meaning t m 2499) (meaning t m 3452) (meaning t m 3609) (meaning t m 3956) (meaning t m 4348) (meaning t m 4503) (meaning t m 4733) source

theorem rule31980 (p2352 p3096 p3988 p4506 : Prop) (h : (¬ p3096) ∨ (¬ p2352) ∨ (¬ p3988) ∨ (¬ p4506)) : (¬ p2352) ∨ (¬ p3096) ∨ (¬ p3988) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial31980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory21236 (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule31980 (meaning t m 2352) (meaning t m 3096) (meaning t m 3988) (meaning t m 4506) source

theorem rule31981 (p2027 p2383 p2528 p3438 p3946 p4384 p5152 : Prop) (h : (¬ p5152) ∨ (¬ p3946) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3438) ∨ (¬ p2528) ∨ (¬ p4384)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2528) ∨ (¬ p3438) ∨ (¬ p3946) ∨ (¬ p4384) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial31981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory21237 t (m.theta 0 6) (m.theta 1 9) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule31981 (meaning t m 2027) (meaning t m 2383) (meaning t m 2528) (meaning t m 3438) (meaning t m 3946) (meaning t m 4384) (meaning t m 5152) source

theorem rule31982 (p2656 p3519 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p3519) ∨ p2656) : (p2656) ∨ (¬ p3519) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial31982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2656) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory21238 (m.theta 0 4) (m.theta 1 4) (m.theta 3 4)
  exact rule31982 (meaning t m 2656) (meaning t m 3519) (meaning t m 4116) source

theorem rule31983 (p2027 p2252 p2657 p2750 p3359 p3371 p3399 p3555 p4075 p4425 p4826 : Prop) (h : (¬ p4826) ∨ (¬ p3555) ∨ (¬ p4075) ∨ (¬ p3371) ∨ (¬ p4425) ∨ (¬ p3399) ∨ (¬ p2657) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3359) ∨ (¬ p3371) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p4075) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial31983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory21239 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 10) (m.theta 9 10)
  exact rule31983 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3359) (meaning t m 3371) (meaning t m 3399) (meaning t m 3555) (meaning t m 4075) (meaning t m 4425) (meaning t m 4826) source

theorem rule31987 (p2027 p2230 p2249 p2656 p2727 p2963 p2982 p3324 p4347 p4450 : Prop) (h : (¬ p2656) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p2727) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial31987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory21243 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule31987 (meaning t m 2027) (meaning t m 2230) (meaning t m 2249) (meaning t m 2656) (meaning t m 2727) (meaning t m 2963) (meaning t m 2982) (meaning t m 3324) (meaning t m 4347) (meaning t m 4450) source

theorem rule31988 (p2027 p2274 p2396 p3581 p3658 p3958 p4324 : Prop) (h : (¬ p3958) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3658) ∨ (¬ p3581) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3581) ∨ (¬ p3658) ∨ (¬ p3958) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial31988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory21244 t (m.theta 2 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule31988 (meaning t m 2027) (meaning t m 2274) (meaning t m 2396) (meaning t m 3581) (meaning t m 3658) (meaning t m 3958) (meaning t m 4324) source

theorem rule31989 (p1987 p2027 p2169 p3125 p3989 p4037 p4153 p4315 : Prop) (h : p2169 ∨ (¬ p3989) ∨ (¬ p4153) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p3125) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4037) ∨ (¬ p4153) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial31989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory21245 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule31989 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 3125) (meaning t m 3989) (meaning t m 4037) (meaning t m 4153) (meaning t m 4315) source

theorem rule31996 (p3919 p4652 p5011 : Prop) (h : (¬ p3919) ∨ (¬ p4652) ∨ p5011) : (¬ p3919) ∨ (¬ p4652) ∨ (p5011) := by
  classical
  tauto

theorem initial31996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4652)) ∨ (meaning t m 5011) := by
  have source := ElevenTheory.theory21252 t (m.theta 3 4) (m.theta 3 7) (m.theta 3 8)
  exact rule31996 (meaning t m 3919) (meaning t m 4652) (meaning t m 5011) source

theorem rule31997 (p1990 p2027 p2295 p2331 p2545 p2657 p3097 : Prop) (h : (¬ p1990) ∨ p2545 ∨ (¬ p2295) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2657) ∨ (¬ p2331)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial31997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory21253 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule31997 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 3097) source

theorem rule31998 (p2027 p2441 p3156 p3696 p3767 p4425 p4461 p4635 p4705 : Prop) (h : p2027 ∨ (¬ p3696) ∨ (¬ p4425) ∨ (¬ p3767) ∨ (¬ p4705) ∨ (¬ p2441) ∨ (¬ p4635) ∨ (¬ p3156) ∨ (¬ p4461)) : (p2027) ∨ (¬ p2441) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p3767) ∨ (¬ p4425) ∨ (¬ p4461) ∨ (¬ p4635) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial31998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4461)) ∨ (¬ (meaning t m 4635)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory21254 t (m.theta 0 8) (m.theta 0 9) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 9 10)
  exact rule31998 (meaning t m 2027) (meaning t m 2441) (meaning t m 3156) (meaning t m 3696) (meaning t m 3767) (meaning t m 4425) (meaning t m 4461) (meaning t m 4635) (meaning t m 4705) source

theorem rule32001 (p2027 p2589 p2659 p2850 p3019 p3584 p3984 : Prop) (h : (¬ p3984) ∨ (¬ p3019) ∨ (¬ p2589) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2850) ∨ (¬ p3019) ∨ (¬ p3584) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial32001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory21257 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule32001 (meaning t m 2027) (meaning t m 2589) (meaning t m 2659) (meaning t m 2850) (meaning t m 3019) (meaning t m 3584) (meaning t m 3984) source

theorem rule32004 (p2027 p2579 p3516 p3947 p4241 p4386 p4715 p5201 : Prop) (h : (¬ p4241) ∨ (¬ p4386) ∨ (¬ p4715) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p5201) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4241) ∨ (¬ p4386) ∨ (¬ p4715) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial32004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory21260 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 9)
  exact rule32004 (meaning t m 2027) (meaning t m 2579) (meaning t m 3516) (meaning t m 3947) (meaning t m 4241) (meaning t m 4386) (meaning t m 4715) (meaning t m 5201) source

theorem rule32012 (p2027 p2138 p2911 p2922 p3146 p3379 p4340 p4359 p4736 p4905 : Prop) (h : (¬ p2911) ∨ (¬ p2922) ∨ (¬ p4905) ∨ (¬ p4736) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p4359) ∨ (¬ p3146) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial32012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory21268 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 2 8) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32012 (meaning t m 2027) (meaning t m 2138) (meaning t m 2911) (meaning t m 2922) (meaning t m 3146) (meaning t m 3379) (meaning t m 4340) (meaning t m 4359) (meaning t m 4736) (meaning t m 4905) source

theorem rule32013 (p1979 p2027 p2192 p2688 p3051 p3646 p4320 p4365 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p1979) ∨ (¬ p2192) ∨ (¬ p4365) ∨ (¬ p4320) ∨ (¬ p3646) ∨ (¬ p3051)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2192) ∨ (p2688) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial32013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory21269 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule32013 (meaning t m 1979) (meaning t m 2027) (meaning t m 2192) (meaning t m 2688) (meaning t m 3051) (meaning t m 3646) (meaning t m 4320) (meaning t m 4365) source

theorem rule32019 (p3032 p3552 p4427 : Prop) (h : p3032 ∨ (¬ p3552) ∨ (¬ p4427)) : (p3032) ∨ (¬ p3552) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial32019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3032) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory21275 (m.theta 1 7) (m.theta 3 7) (m.theta 6 7)
  exact rule32019 (meaning t m 3032) (meaning t m 3552) (meaning t m 4427) source

theorem rule32020 (p2027 p2246 p2651 p2685 p2749 p2810 p3032 p4796 : Prop) (h : (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p4796) ∨ (¬ p2685) ∨ (¬ p3032)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3032) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial32020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory21276 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule32020 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2685) (meaning t m 2749) (meaning t m 2810) (meaning t m 3032) (meaning t m 4796) source

theorem rule32021 (p2027 p2807 p2952 p2992 p4111 p4652 : Prop) (h : (¬ p4111) ∨ (¬ p2952) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p4652) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial32021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory21277 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule32021 (meaning t m 2027) (meaning t m 2807) (meaning t m 2952) (meaning t m 2992) (meaning t m 4111) (meaning t m 4652) source

theorem rule32022 (p2027 p2449 p2737 p2780 p2807 p2811 p3950 p4347 p4358 p4734 : Prop) (h : (¬ p4347) ∨ (¬ p4734) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3950) ∨ (¬ p4358) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial32022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory21278 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32022 (meaning t m 2027) (meaning t m 2449) (meaning t m 2737) (meaning t m 2780) (meaning t m 2807) (meaning t m 2811) (meaning t m 3950) (meaning t m 4347) (meaning t m 4358) (meaning t m 4734) source

theorem rule32023 (p2027 p2230 p2780 p2982 p3367 p3759 p3822 p4107 p4395 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p3759) ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p4395) ∨ (¬ p2780) ∨ (¬ p4107) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial32023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory21279 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule32023 (meaning t m 2027) (meaning t m 2230) (meaning t m 2780) (meaning t m 2982) (meaning t m 3367) (meaning t m 3759) (meaning t m 3822) (meaning t m 4107) (meaning t m 4395) (meaning t m 4734) source

theorem rule32027 (p2027 p2274 p2972 p3549 p4512 p5046 : Prop) (h : p2027 ∨ (¬ p3549) ∨ (¬ p2274) ∨ (¬ p4512) ∨ (¬ p5046) ∨ (¬ p2972)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2972) ∨ (¬ p3549) ∨ (¬ p4512) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial32027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory21283 t (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule32027 (meaning t m 2027) (meaning t m 2274) (meaning t m 2972) (meaning t m 3549) (meaning t m 4512) (meaning t m 5046) source

theorem rule32030 (p2027 p2247 p2470 p2528 p2608 p3519 p4041 p4348 p4360 p4376 : Prop) (h : (¬ p4360) ∨ (¬ p4348) ∨ (¬ p4041) ∨ (¬ p3519) ∨ (¬ p2470) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2528) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial32030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory21286 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32030 (meaning t m 2027) (meaning t m 2247) (meaning t m 2470) (meaning t m 2528) (meaning t m 2608) (meaning t m 3519) (meaning t m 4041) (meaning t m 4348) (meaning t m 4360) (meaning t m 4376) source

theorem rule32031 (p4154 p4196 p4360 : Prop) (h : (¬ p4154) ∨ (¬ p4196) ∨ p4360) : (¬ p4154) ∨ (¬ p4196) ∨ (p4360) := by
  classical
  tauto

theorem initial32031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4196)) ∨ (meaning t m 4360) := by
  have source := ElevenTheory.theory21287 (m.theta 1 3) (m.theta 3 6) (m.theta 3 8)
  exact rule32031 (meaning t m 4154) (meaning t m 4196) (meaning t m 4360) source

theorem rule32032 (p2027 p2230 p2427 p2737 p3246 p3365 p3873 p4379 p5190 p5236 : Prop) (h : (¬ p3365) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p5236) ∨ (¬ p5190) ∨ (¬ p3246) ∨ (¬ p4379) ∨ (¬ p2737) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2737) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4379) ∨ (¬ p5190) ∨ (¬ p5236) := by
  classical
  tauto

theorem initial32032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5236)) := by
  have source := ElevenTheory.theory21288 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule32032 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2737) (meaning t m 3246) (meaning t m 3365) (meaning t m 3873) (meaning t m 4379) (meaning t m 5190) (meaning t m 5236) source

theorem rule32034 (p2027 p2295 p2313 p2386 p3019 p3584 p4750 : Prop) (h : (¬ p2313) ∨ (¬ p3019) ∨ (¬ p2386) ∨ (¬ p4750) ∨ (¬ p3584) ∨ (¬ p2295) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3019) ∨ (¬ p3584) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial32034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory21290 t (m.theta 0 6) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule32034 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2386) (meaning t m 3019) (meaning t m 3584) (meaning t m 4750) source

theorem rule32035 (p2027 p2247 p2427 p2598 p2850 p3568 p4154 p4556 p4733 : Prop) (h : (¬ p4556) ∨ (¬ p4733) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2850)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4556) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial32035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory21291 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7)
  exact rule32035 (meaning t m 2027) (meaning t m 2247) (meaning t m 2427) (meaning t m 2598) (meaning t m 2850) (meaning t m 3568) (meaning t m 4154) (meaning t m 4556) (meaning t m 4733) source

theorem rule32038 (p2027 p2427 p2753 p3166 p3347 p3556 p3880 p3904 p4009 p4117 p4134 p5216 p5580 : Prop) (h : (¬ p4117) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p3880) ∨ (¬ p2427) ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p4134) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p5580) ∨ (¬ p4009) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3347) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p3904) ∨ (¬ p4009) ∨ (¬ p4117) ∨ (¬ p4134) ∨ (¬ p5216) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial32038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory21294 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10)
  exact rule32038 (meaning t m 2027) (meaning t m 2427) (meaning t m 2753) (meaning t m 3166) (meaning t m 3347) (meaning t m 3556) (meaning t m 3880) (meaning t m 3904) (meaning t m 4009) (meaning t m 4117) (meaning t m 4134) (meaning t m 5216) (meaning t m 5580) source

theorem rule32042 (p1991 p2027 p2274 p2542 p2588 p2589 p2655 p2765 p3574 : Prop) (h : (¬ p2655) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2588) ∨ (¬ p1991) ∨ (¬ p2274) ∨ p2765 ∨ p2027 ∨ (¬ p3574)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (p2765) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial32042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory21298 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule32042 (meaning t m 1991) (meaning t m 2027) (meaning t m 2274) (meaning t m 2542) (meaning t m 2588) (meaning t m 2589) (meaning t m 2655) (meaning t m 2765) (meaning t m 3574) source

theorem rule32048 (p2027 p2437 p2651 p2780 p3868 p3917 p4191 p4786 p4826 : Prop) (h : (¬ p2437) ∨ (¬ p4826) ∨ (¬ p3868) ∨ (¬ p4786) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4191) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3868) ∨ (¬ p3917) ∨ (¬ p4191) ∨ (¬ p4786) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial32048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory21304 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule32048 (meaning t m 2027) (meaning t m 2437) (meaning t m 2651) (meaning t m 2780) (meaning t m 3868) (meaning t m 3917) (meaning t m 4191) (meaning t m 4786) (meaning t m 4826) source

theorem rule32057 (p1989 p2027 p2284 p2545 p3212 p3413 p3646 p4363 : Prop) (h : (¬ p3413) ∨ (¬ p1989) ∨ (¬ p2284) ∨ (¬ p4363) ∨ (¬ p3212) ∨ p2027 ∨ p2545 ∨ (¬ p3646)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p3212) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial32057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory21313 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule32057 (meaning t m 1989) (meaning t m 2027) (meaning t m 2284) (meaning t m 2545) (meaning t m 3212) (meaning t m 3413) (meaning t m 3646) (meaning t m 4363) source

theorem rule32058 (p2001 p2027 p2233 p2373 p2406 p2499 p2573 : Prop) (h : (¬ p2001) ∨ p2233 ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p2406)) : (¬ p2001) ∨ (p2027) ∨ (p2233) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2573) := by
  classical
  tauto

theorem initial32058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) := by
  have source := ElevenTheory.theory21314 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule32058 (meaning t m 2001) (meaning t m 2027) (meaning t m 2233) (meaning t m 2373) (meaning t m 2406) (meaning t m 2499) (meaning t m 2573) source

theorem rule32059 (p1985 p2027 p2144 p2427 p2842 p3055 p3212 p4948 : Prop) (h : (¬ p1985) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p3055) ∨ (¬ p2427) ∨ (¬ p2144) ∨ (¬ p3212) ∨ p2842) : (¬ p1985) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2427) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3212) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial32059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory21315 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule32059 (meaning t m 1985) (meaning t m 2027) (meaning t m 2144) (meaning t m 2427) (meaning t m 2842) (meaning t m 3055) (meaning t m 3212) (meaning t m 4948) source

theorem rule32060 (p2027 p2254 p2911 p2922 p2952 p3379 p3690 p4320 p4666 : Prop) (h : (¬ p2254) ∨ (¬ p3379) ∨ (¬ p2922) ∨ (¬ p3690) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p4320) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial32060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory21316 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32060 (meaning t m 2027) (meaning t m 2254) (meaning t m 2911) (meaning t m 2922) (meaning t m 2952) (meaning t m 3379) (meaning t m 3690) (meaning t m 4320) (meaning t m 4666) source

theorem rule32061 (p2027 p2138 p2352 p2363 p2573 p3690 p4244 p4419 p4669 : Prop) (h : (¬ p2138) ∨ (¬ p4669) ∨ (¬ p4244) ∨ (¬ p2363) ∨ (¬ p4419) ∨ (¬ p2573) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2352)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4419) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21317 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule32061 (meaning t m 2027) (meaning t m 2138) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 3690) (meaning t m 4244) (meaning t m 4419) (meaning t m 4669) source

theorem rule32065 (p2027 p2187 p2230 p2563 p2608 p3519 p3548 p4133 p4366 p4376 : Prop) (h : (¬ p4366) ∨ (¬ p2563) ∨ (¬ p4133) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p3548) ∨ (¬ p3519) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4376)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4366) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial32065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory21321 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule32065 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 2608) (meaning t m 3519) (meaning t m 3548) (meaning t m 4133) (meaning t m 4366) (meaning t m 4376) source

theorem rule32066 (p2027 p2417 p2901 p4208 p4209 p4647 p5295 : Prop) (h : p2027 ∨ (¬ p5295) ∨ (¬ p4209) ∨ (¬ p4647) ∨ (¬ p2417) ∨ (¬ p2901) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4209) ∨ (¬ p4647) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial32066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4209)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory21322 t (m.theta 0 9) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule32066 (meaning t m 2027) (meaning t m 2417) (meaning t m 2901) (meaning t m 4208) (meaning t m 4209) (meaning t m 4647) (meaning t m 5295) source

theorem rule32067 (p2027 p3755 p3946 p4195 p4367 p4581 : Prop) (h : p2027 ∨ (¬ p4581) ∨ (¬ p4195) ∨ (¬ p3946) ∨ (¬ p3755) ∨ (¬ p4367)) : (p2027) ∨ (¬ p3755) ∨ (¬ p3946) ∨ (¬ p4195) ∨ (¬ p4367) ∨ (¬ p4581) := by
  classical
  tauto

theorem initial32067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 4581)) := by
  have source := ElevenTheory.theory21323 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule32067 (meaning t m 2027) (meaning t m 3755) (meaning t m 3946) (meaning t m 4195) (meaning t m 4367) (meaning t m 4581) source

theorem rule32071 (p2027 p2253 p3055 p3166 p3256 p3644 p3876 p4133 p4347 p4736 : Prop) (h : (¬ p3644) ∨ (¬ p4133) ∨ (¬ p3876) ∨ (¬ p4347) ∨ (¬ p4736) ∨ (¬ p2253) ∨ (¬ p3055) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p3256)) : (p2027) ∨ (¬ p2253) ∨ (¬ p3055) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial32071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory21327 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32071 (meaning t m 2027) (meaning t m 2253) (meaning t m 3055) (meaning t m 3166) (meaning t m 3256) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) (meaning t m 4347) (meaning t m 4736) source

theorem rule32072 (p2027 p2246 p2264 p2459 p2579 p2744 p2807 p3366 p3422 p3905 p4022 p4604 p5160 : Prop) (h : (¬ p3905) ∨ (¬ p3422) ∨ (¬ p3366) ∨ (¬ p4022) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p4604) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3366) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4022) ∨ (¬ p4604) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial32072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory21328 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule32072 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2459) (meaning t m 2579) (meaning t m 2744) (meaning t m 2807) (meaning t m 3366) (meaning t m 3422) (meaning t m 3905) (meaning t m 4022) (meaning t m 4604) (meaning t m 5160) source

theorem rule32073 (p2027 p2248 p2528 p2651 p3083 p3486 p3555 p3690 p4669 : Prop) (h : (¬ p2248) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3555) ∨ (¬ p4669) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial32073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory21329 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule32073 (meaning t m 2027) (meaning t m 2248) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4669) source

theorem rule32074 (p3573 p3581 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p3581) ∨ p3573) : (p3573) ∨ (¬ p3581) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial32074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3573) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory21330 (m.theta 4 6) (m.theta 4 7) (m.theta 4 8)
  exact rule32074 (meaning t m 3573) (meaning t m 3581) (meaning t m 4186) source

theorem rule32076 (p2027 p2437 p2499 p3487 p3956 p4501 p4710 : Prop) (h : p2027 ∨ (¬ p4501) ∨ (¬ p4710) ∨ (¬ p2437) ∨ (¬ p2499) ∨ (¬ p3487) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2499) ∨ (¬ p3487) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial32076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory21332 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule32076 (meaning t m 2027) (meaning t m 2437) (meaning t m 2499) (meaning t m 3487) (meaning t m 3956) (meaning t m 4501) (meaning t m 4710) source

theorem rule32084 (p1999 p2027 p2409 p2518 p3016 p3564 p4256 : Prop) (h : (¬ p4256) ∨ p2409 ∨ (¬ p3016) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p1999) ∨ (¬ p3564)) : (¬ p1999) ∨ (p2027) ∨ (p2409) ∨ (¬ p2518) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial32084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory21340 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 9)
  exact rule32084 (meaning t m 1999) (meaning t m 2027) (meaning t m 2409) (meaning t m 2518) (meaning t m 3016) (meaning t m 3564) (meaning t m 4256) source

theorem rule32085 (p2505 p4281 p4759 : Prop) (h : p4759 ∨ (¬ p2505) ∨ (¬ p4281)) : (¬ p2505) ∨ (¬ p4281) ∨ (p4759) := by
  classical
  tauto

theorem initial32085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 4281)) ∨ (meaning t m 4759) := by
  have source := ElevenTheory.theory21341 (m.theta 1 3) (m.theta 1 4) (m.theta 1 6)
  exact rule32085 (meaning t m 2505) (meaning t m 4281) (meaning t m 4759) source

theorem rule32087 (p2027 p2248 p2449 p2807 p3688 p3690 p3822 p3954 p4556 : Prop) (h : (¬ p3690) ∨ (¬ p3954) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3688) ∨ (¬ p3690) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial32087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory21343 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule32087 (meaning t m 2027) (meaning t m 2248) (meaning t m 2449) (meaning t m 2807) (meaning t m 3688) (meaning t m 3690) (meaning t m 3822) (meaning t m 3954) (meaning t m 4556) source

theorem rule32089 (p2011 p2027 p2132 p2202 p2493 p2579 p2870 p3115 p3238 p4108 p4320 p4733 : Prop) (h : (¬ p2132) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4733) ∨ (¬ p2579) ∨ (¬ p4108) ∨ (¬ p2011) ∨ p2202 ∨ (¬ p2870) ∨ (¬ p4320) ∨ (¬ p3115)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2132) ∨ (p2202) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p3115) ∨ (¬ p3238) ∨ (¬ p4108) ∨ (¬ p4320) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial32089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory21345 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 9)
  exact rule32089 (meaning t m 2011) (meaning t m 2027) (meaning t m 2132) (meaning t m 2202) (meaning t m 2493) (meaning t m 2579) (meaning t m 2870) (meaning t m 3115) (meaning t m 3238) (meaning t m 4108) (meaning t m 4320) (meaning t m 4733) source

theorem rule32091 (p2027 p2145 p2563 p2696 p3005 p3256 p3646 p4948 p5059 : Prop) (h : (¬ p3005) ∨ (¬ p4948) ∨ (¬ p5059) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2145) ∨ (¬ p3256) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3646) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial32091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory21347 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule32091 (meaning t m 2027) (meaning t m 2145) (meaning t m 2563) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3646) (meaning t m 4948) (meaning t m 5059) source

theorem rule32096 (p2027 p2881 p3105 p3659 p4136 p5104 : Prop) (h : (¬ p3105) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p5104) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3105) ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p5104) := by
  classical
  tauto

theorem initial32096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 5104)) := by
  have source := ElevenTheory.theory21352 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule32096 (meaning t m 2027) (meaning t m 2881) (meaning t m 3105) (meaning t m 3659) (meaning t m 4136) (meaning t m 5104) source

theorem rule32102 (p2027 p2246 p2307 p2668 p2744 p3055 p3366 p3568 p3684 p3880 p3987 p4134 : Prop) (h : (¬ p2307) ∨ (¬ p2246) ∨ (¬ p2668) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4134) ∨ (¬ p3987) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3055) ∨ (¬ p3568) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2307) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3568) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p3987) ∨ (¬ p4134) := by
  classical
  tauto

theorem initial32102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4134)) := by
  have source := ElevenTheory.theory21358 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule32102 (meaning t m 2027) (meaning t m 2246) (meaning t m 2307) (meaning t m 2668) (meaning t m 2744) (meaning t m 3055) (meaning t m 3366) (meaning t m 3568) (meaning t m 3684) (meaning t m 3880) (meaning t m 3987) (meaning t m 4134) source

theorem rule32104 (p2027 p2132 p2187 p2459 p2509 p2534 p2753 p2860 p4133 p5216 : Prop) (h : (¬ p2459) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p2132) ∨ (¬ p2509) ∨ (¬ p2753) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p4133) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory21360 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32104 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2459) (meaning t m 2509) (meaning t m 2534) (meaning t m 2753) (meaning t m 2860) (meaning t m 4133) (meaning t m 5216) source

theorem rule32106 (p1999 p2027 p2307 p2584 p2588 p2656 p2688 p2727 p3564 : Prop) (h : (¬ p1999) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p2588) ∨ p2688 ∨ (¬ p2584) ∨ (¬ p2307) ∨ (¬ p3564)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial32106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory21362 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule32106 (meaning t m 1999) (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3564) source

theorem rule32113 (p2027 p2459 p3365 p3399 p3527 p4208 p4315 p4736 p5059 : Prop) (h : (¬ p4736) ∨ (¬ p5059) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3527) ∨ (¬ p3399) ∨ (¬ p2459) ∨ (¬ p4208) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4736) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial32113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory21369 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule32113 (meaning t m 2027) (meaning t m 2459) (meaning t m 3365) (meaning t m 3399) (meaning t m 3527) (meaning t m 4208) (meaning t m 4315) (meaning t m 4736) (meaning t m 5059) source

theorem rule32119 (p2027 p2299 p2774 p3426 p3527 p3585 p3684 p4235 p4424 p4559 p4737 : Prop) (h : (¬ p4424) ∨ (¬ p2774) ∨ (¬ p3585) ∨ (¬ p3426) ∨ (¬ p4737) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p2299) ∨ (¬ p3684) ∨ (¬ p3527) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p2774) ∨ (¬ p3426) ∨ (¬ p3527) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4424) ∨ (¬ p4559) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial32119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory21375 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule32119 (meaning t m 2027) (meaning t m 2299) (meaning t m 2774) (meaning t m 3426) (meaning t m 3527) (meaning t m 3585) (meaning t m 3684) (meaning t m 4235) (meaning t m 4424) (meaning t m 4559) (meaning t m 4737) source

end SunPrize.SMT
