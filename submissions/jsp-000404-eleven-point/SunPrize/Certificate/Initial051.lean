import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory035
import SunPrize.Certificate.Theory036
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule22500 (p2027 p2122 p2313 p2778 p2829 p4734 : Prop) (h : (¬ p4734) ∨ p2027 ∨ (¬ p2778) ∨ (¬ p2829) ∨ (¬ p2313) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p2829) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11756 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7)
  exact rule22500 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2778) (meaning t m 2829) (meaning t m 4734) source

theorem rule22501 (p2027 p2470 p2531 p2589 p4110 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p4110) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2531)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p4110) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory11757 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule22501 (meaning t m 2027) (meaning t m 2470) (meaning t m 2531) (meaning t m 2589) (meaning t m 4110) (meaning t m 4509) source

theorem rule22502 (p2027 p2220 p2313 p2553 p3096 p4198 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p4198) ∨ (¬ p2553) ∨ (¬ p2313) ∨ (¬ p3096) ∨ (¬ p2220) ∨ p2027) : (p2027) ∨ (¬ p2220) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3096) ∨ (¬ p4198) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory11758 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule22502 (meaning t m 2027) (meaning t m 2220) (meaning t m 2313) (meaning t m 2553) (meaning t m 3096) (meaning t m 4198) (meaning t m 4509) source

theorem rule22503 (p2027 p2737 p3365 p3379 p3873 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3873) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory11759 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3)
  exact rule22503 (meaning t m 2027) (meaning t m 2737) (meaning t m 3365) (meaning t m 3379) (meaning t m 3873) (meaning t m 5216) source

theorem rule22504 (p2027 p3319 p3585 p3917 p4869 p5224 : Prop) (h : (¬ p5224) ∨ (¬ p3917) ∨ (¬ p3319) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p4869)) : (p2027) ∨ (¬ p3319) ∨ (¬ p3585) ∨ (¬ p3917) ∨ (¬ p4869) ∨ (¬ p5224) := by
  classical
  tauto

theorem initial22504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5224)) := by
  have source := ElevenTheory.theory11760 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 9)
  exact rule22504 (meaning t m 2027) (meaning t m 3319) (meaning t m 3585) (meaning t m 3917) (meaning t m 4869) (meaning t m 5224) source

theorem rule22505 (p2027 p2192 p3125 p3486 p4275 p4624 : Prop) (h : (¬ p4624) ∨ p2027 ∨ (¬ p4275) ∨ (¬ p3125) ∨ (¬ p2192) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3125) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11761 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22505 (meaning t m 2027) (meaning t m 2192) (meaning t m 3125) (meaning t m 3486) (meaning t m 4275) (meaning t m 4624) source

theorem rule22506 (p2027 p2589 p2608 p2707 p2717 p3690 p4235 p4666 p5193 : Prop) (h : (¬ p4235) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p3690) ∨ (¬ p2717) ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p2707) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4666) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory11762 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22506 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3690) (meaning t m 4235) (meaning t m 4666) (meaning t m 5193) source

theorem rule22508 (p2657 p2963 p4194 : Prop) (h : (¬ p4194) ∨ (¬ p2657) ∨ p2963) : (¬ p2657) ∨ (p2963) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial22508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (meaning t m 2963) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory11764 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule22508 (meaning t m 2657) (meaning t m 2963) (meaning t m 4194) source

theorem rule22509 (p2027 p2387 p3063 p3379 p4869 p5015 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p4869) ∨ (¬ p3379) ∨ (¬ p5015) ∨ (¬ p3063) ∨ (¬ p2387) ∨ p2027) : (p2027) ∨ (¬ p2387) ∨ (¬ p3063) ∨ (¬ p3379) ∨ (¬ p4869) ∨ (¬ p5015) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5015)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory11765 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 6 8)
  exact rule22509 (meaning t m 2027) (meaning t m 2387) (meaning t m 3063) (meaning t m 3379) (meaning t m 4869) (meaning t m 5015) (meaning t m 5216) source

theorem rule22510 (p2027 p2589 p2696 p3005 p3256 p3690 p4235 p4669 p4729 : Prop) (h : (¬ p2696) ∨ (¬ p4669) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4729) ∨ (¬ p3690) ∨ (¬ p3005) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial22510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory11766 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22510 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3690) (meaning t m 4235) (meaning t m 4669) (meaning t m 4729) source

theorem rule22512 (p2027 p2210 p2247 p4243 p4360 p4700 p5008 p5051 : Prop) (h : (¬ p4243) ∨ (¬ p5008) ∨ (¬ p4360) ∨ (¬ p4700) ∨ (¬ p5051) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4243) ∨ (¬ p4360) ∨ (¬ p4700) ∨ (¬ p5008) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial22512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 5008)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory11768 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule22512 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 4243) (meaning t m 4360) (meaning t m 4700) (meaning t m 5008) (meaning t m 5051) source

theorem rule22513 (p1986 p2027 p2441 p2633 p3246 p3570 p3684 p4278 : Prop) (h : (¬ p3570) ∨ p2633 ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2441) ∨ (¬ p1986) ∨ (¬ p3684) ∨ (¬ p4278)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2441) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3684) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial22513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory11769 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22513 (meaning t m 1986) (meaning t m 2027) (meaning t m 2441) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 3684) (meaning t m 4278) source

theorem rule22514 (p2027 p2241 p2449 p2589 p3027 p3570 p4235 p4668 p5193 : Prop) (h : (¬ p4235) ∨ (¬ p2449) ∨ (¬ p5193) ∨ (¬ p4668) ∨ (¬ p3570) ∨ (¬ p2589) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3027)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4668) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory11770 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22514 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2589) (meaning t m 3027) (meaning t m 3570) (meaning t m 4235) (meaning t m 4668) (meaning t m 5193) source

theorem rule22515 (p2027 p2241 p2630 p2748 p3860 p5008 p5074 : Prop) (h : (¬ p5008) ∨ p2027 ∨ (¬ p5074) ∨ (¬ p3860) ∨ (¬ p2748) ∨ (¬ p2241) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p3860) ∨ (¬ p5008) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial22515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5008)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory11771 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule22515 (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2748) (meaning t m 3860) (meaning t m 5008) (meaning t m 5074) source

theorem rule22516 (p2027 p2589 p3073 p3266 p3449 p4235 p4831 p5193 p5660 : Prop) (h : (¬ p3449) ∨ (¬ p4831) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p5660) ∨ (¬ p2589) ∨ (¬ p4235) ∨ (¬ p3266) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p4235) ∨ (¬ p4831) ∨ (¬ p5193) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial22516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory11772 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule22516 (meaning t m 2027) (meaning t m 2589) (meaning t m 3073) (meaning t m 3266) (meaning t m 3449) (meaning t m 4235) (meaning t m 4831) (meaning t m 5193) (meaning t m 5660) source

theorem rule22517 (p2027 p2449 p2589 p2685 p2696 p3570 p4235 p4668 p4729 : Prop) (h : p2027 ∨ (¬ p2696) ∨ (¬ p4729) ∨ (¬ p4235) ∨ (¬ p2685) ∨ (¬ p2449) ∨ (¬ p3570) ∨ (¬ p4668) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4668) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial22517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory11773 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22517 (meaning t m 2027) (meaning t m 2449) (meaning t m 2589) (meaning t m 2685) (meaning t m 2696) (meaning t m 3570) (meaning t m 4235) (meaning t m 4668) (meaning t m 4729) source

theorem rule22518 (p2027 p2352 p2850 p4358 p4715 p5220 : Prop) (h : (¬ p5220) ∨ (¬ p2850) ∨ (¬ p2352) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p4715)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2850) ∨ (¬ p4358) ∨ (¬ p4715) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial22518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory11774 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule22518 (meaning t m 2027) (meaning t m 2352) (meaning t m 2850) (meaning t m 4358) (meaning t m 4715) (meaning t m 5220) source

theorem rule22519 (p2027 p2352 p2387 p3051 p3096 p4198 p4558 : Prop) (h : (¬ p2352) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p3051) ∨ (¬ p2387) ∨ (¬ p4198)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3051) ∨ (¬ p3096) ∨ (¬ p4198) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11775 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule22519 (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 3051) (meaning t m 3096) (meaning t m 4198) (meaning t m 4558) source

theorem rule22520 (p2655 p2807 p3540 p3579 : Prop) (h : (¬ p2655) ∨ (¬ p3540) ∨ (¬ p2807) ∨ (¬ p3579)) : (¬ p2655) ∨ (¬ p2807) ∨ (¬ p3540) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial22520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory11776 (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 7)
  exact rule22520 (meaning t m 2655) (meaning t m 2807) (meaning t m 3540) (meaning t m 3579) source

theorem rule22521 (p2027 p2498 p3399 p3547 p3591 p3956 p4501 : Prop) (h : (¬ p3399) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p3547) ∨ (¬ p2498) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2498) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11777 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22521 (meaning t m 2027) (meaning t m 2498) (meaning t m 3399) (meaning t m 3547) (meaning t m 3591) (meaning t m 3956) (meaning t m 4501) source

theorem rule22523 (p2027 p2651 p2950 p3156 p4120 p4701 : Prop) (h : (¬ p4120) ∨ (¬ p2950) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4701)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2950) ∨ (¬ p3156) ∨ (¬ p4120) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11779 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule22523 (meaning t m 2027) (meaning t m 2651) (meaning t m 2950) (meaning t m 3156) (meaning t m 4120) (meaning t m 4701) source

theorem rule22525 (p2027 p2417 p3690 p3741 p4110 p4558 : Prop) (h : (¬ p4110) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p3741) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11781 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule22525 (meaning t m 2027) (meaning t m 2417) (meaning t m 3690) (meaning t m 3741) (meaning t m 4110) (meaning t m 4558) source

theorem rule22526 (p2027 p2088 p3568 p3955 p4114 p4347 p4584 : Prop) (h : (¬ p4114) ∨ (¬ p3955) ∨ (¬ p4584) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3568) ∨ (¬ p3955) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4584) := by
  classical
  tauto

theorem initial22526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4584)) := by
  have source := ElevenTheory.theory11782 t (m.theta 0 6) (m.theta 0 8) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule22526 (meaning t m 2027) (meaning t m 2088) (meaning t m 3568) (meaning t m 3955) (meaning t m 4114) (meaning t m 4347) (meaning t m 4584) source

theorem rule22528 (p2589 p3238 p3519 : Prop) (h : (¬ p3238) ∨ (¬ p3519) ∨ p2589) : (p2589) ∨ (¬ p3238) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial22528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2589) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory11784 (m.theta 0 4) (m.theta 1 4) (m.theta 4 5)
  exact rule22528 (meaning t m 2589) (meaning t m 3238) (meaning t m 3519) source

theorem rule22529 (p2027 p2190 p2528 p2901 p3661 p3693 p4118 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p3661) ∨ (¬ p2901) ∨ (¬ p4118) ∨ (¬ p3693) ∨ (¬ p2190) ∨ p2027 ∨ (¬ p2528)) : (p2027) ∨ (¬ p2190) ∨ (¬ p2528) ∨ (¬ p2901) ∨ (¬ p3661) ∨ (¬ p3693) ∨ (¬ p4118) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11785 t (m.theta 3 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule22529 (meaning t m 2027) (meaning t m 2190) (meaning t m 2528) (meaning t m 2901) (meaning t m 3661) (meaning t m 3693) (meaning t m 4118) (meaning t m 4558) source

theorem rule22530 (p2027 p2307 p2363 p3857 p4197 p4501 : Prop) (h : (¬ p2307) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4197) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11786 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule22530 (meaning t m 2027) (meaning t m 2307) (meaning t m 2363) (meaning t m 3857) (meaning t m 4197) (meaning t m 4501) source

theorem rule22531 (p2027 p2510 p2528 p3051 p3096 p3697 p3857 p4558 : Prop) (h : (¬ p2510) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p3051) ∨ (¬ p4558) ∨ (¬ p3697) ∨ (¬ p3096)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3051) ∨ (¬ p3096) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11787 t (m.theta 0 5) (m.theta 0 8) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule22531 (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 3051) (meaning t m 3096) (meaning t m 3697) (meaning t m 3857) (meaning t m 4558) source

theorem rule22532 (p2027 p2532 p2982 p3880 p4118 p5063 : Prop) (h : p2027 ∨ (¬ p3880) ∨ (¬ p5063) ∨ (¬ p2532) ∨ (¬ p4118) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4118) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial22532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory11788 t (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule22532 (meaning t m 2027) (meaning t m 2532) (meaning t m 2982) (meaning t m 3880) (meaning t m 4118) (meaning t m 5063) source

theorem rule22533 (p2027 p2136 p2839 p2870 p3556 p4734 : Prop) (h : (¬ p2136) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2870) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11789 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7)
  exact rule22533 (meaning t m 2027) (meaning t m 2136) (meaning t m 2839) (meaning t m 2870) (meaning t m 3556) (meaning t m 4734) source

theorem rule22534 (p2027 p2753 p3471 p3583 p3758 p4344 p4558 : Prop) (h : (¬ p2753) ∨ (¬ p4344) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p3758) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p4344) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11790 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22534 (meaning t m 2027) (meaning t m 2753) (meaning t m 3471) (meaning t m 3583) (meaning t m 3758) (meaning t m 4344) (meaning t m 4558) source

theorem rule22535 (p2190 p3694 p3758 : Prop) (h : (¬ p2190) ∨ (¬ p3694) ∨ p3758) : (¬ p2190) ∨ (¬ p3694) ∨ (p3758) := by
  classical
  tauto

theorem initial22535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3694)) ∨ (meaning t m 3758) := by
  have source := ElevenTheory.theory11791 (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule22535 (meaning t m 2190) (meaning t m 3694) (meaning t m 3758) source

theorem rule22536 (p2027 p2589 p2850 p3367 p3905 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p2850) ∨ (¬ p2589) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p3367)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3905) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11792 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5)
  exact rule22536 (meaning t m 2027) (meaning t m 2589) (meaning t m 2850) (meaning t m 3367) (meaning t m 3905) (meaning t m 4734) source

theorem rule22537 (p2190 p2860 p3694 : Prop) (h : (¬ p2190) ∨ (¬ p3694) ∨ (¬ p2860)) : (¬ p2190) ∨ (¬ p2860) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial22537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory11793 (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule22537 (meaning t m 2190) (meaning t m 2860) (meaning t m 3694) source

theorem rule22538 (p2027 p2144 p3051 p3583 p4244 p4737 : Prop) (h : (¬ p2144) ∨ (¬ p4244) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11794 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7)
  exact rule22538 (meaning t m 2027) (meaning t m 2144) (meaning t m 3051) (meaning t m 3583) (meaning t m 4244) (meaning t m 4737) source

theorem rule22540 (p2027 p2891 p3097 p4173 p4556 : Prop) (h : (¬ p4173) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3097) ∨ (¬ p4173) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory11796 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule22540 (meaning t m 2027) (meaning t m 2891) (meaning t m 3097) (meaning t m 4173) (meaning t m 4556) source

theorem rule22542 (p3644 p3741 p3880 p4132 : Prop) (h : (¬ p3880) ∨ (¬ p3741) ∨ (¬ p4132) ∨ p3644) : (p3644) ∨ (¬ p3741) ∨ (¬ p3880) ∨ (¬ p4132) := by
  classical
  tauto

theorem initial22542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3644) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4132)) := by
  have source := ElevenTheory.theory11798 (m.theta 4 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8)
  exact rule22542 (meaning t m 3644) (meaning t m 3741) (meaning t m 3880) (meaning t m 4132) source

theorem rule22543 (p2027 p2427 p3246 p3880 p4132 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p3880) ∨ (¬ p2427) ∨ (¬ p4132) ∨ p2027 ∨ (¬ p3246)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11799 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule22543 (meaning t m 2027) (meaning t m 2427) (meaning t m 3246) (meaning t m 3880) (meaning t m 4132) (meaning t m 4668) source

theorem rule22544 (p1991 p2027 p2563 p2938 p2952 p3952 p4235 : Prop) (h : p2938 ∨ p2027 ∨ (¬ p1991) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p4235) ∨ (¬ p3952)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial22544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory11800 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule22544 (meaning t m 1991) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 2952) (meaning t m 3952) (meaning t m 4235) source

theorem rule22545 (p2027 p2459 p2499 p2717 p3452 p3471 p4137 p4604 p4733 : Prop) (h : (¬ p3471) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2717) ∨ (¬ p4733) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2717) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11801 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22545 (meaning t m 2027) (meaning t m 2459) (meaning t m 2499) (meaning t m 2717) (meaning t m 3452) (meaning t m 3471) (meaning t m 4137) (meaning t m 4604) (meaning t m 4733) source

theorem rule22547 (p1988 p2027 p2295 p2396 p2641 p2688 p2761 : Prop) (h : (¬ p2295) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2641) ∨ p2688 ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial22547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory11803 t (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule22547 (meaning t m 1988) (meaning t m 2027) (meaning t m 2295) (meaning t m 2396) (meaning t m 2641) (meaning t m 2688) (meaning t m 2761) source

theorem rule22548 (p2027 p2951 p3051 p3246 p3497 p4132 p4668 : Prop) (h : (¬ p3246) ∨ (¬ p4132) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3497) ∨ (¬ p4132) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11804 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule22548 (meaning t m 2027) (meaning t m 2951) (meaning t m 3051) (meaning t m 3246) (meaning t m 3497) (meaning t m 4132) (meaning t m 4668) source

theorem rule22549 (p2027 p2807 p2952 p3952 p4333 p4558 : Prop) (h : (¬ p4333) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4333) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11805 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22549 (meaning t m 2027) (meaning t m 2807) (meaning t m 2952) (meaning t m 3952) (meaning t m 4333) (meaning t m 4558) source

theorem rule22550 (p2027 p2098 p2928 p3452 p3609 p3741 p3880 p4134 p4347 p4733 : Prop) (h : (¬ p4347) ∨ (¬ p2928) ∨ (¬ p4134) ∨ (¬ p3452) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p4733) ∨ (¬ p3609) ∨ (¬ p3741)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3741) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11806 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule22550 (meaning t m 2027) (meaning t m 2098) (meaning t m 2928) (meaning t m 3452) (meaning t m 3609) (meaning t m 3741) (meaning t m 3880) (meaning t m 4134) (meaning t m 4347) (meaning t m 4733) source

theorem rule22554 (p1994 p2027 p2387 p2641 p2651 p2668 p2688 p3983 : Prop) (h : p2027 ∨ (¬ p2641) ∨ (¬ p2387) ∨ (¬ p1994) ∨ p2688 ∨ (¬ p3983) ∨ (¬ p2651) ∨ (¬ p2668)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2668) ∨ (p2688) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial22554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory11810 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule22554 (meaning t m 1994) (meaning t m 2027) (meaning t m 2387) (meaning t m 2641) (meaning t m 2651) (meaning t m 2668) (meaning t m 2688) (meaning t m 3983) source

theorem rule22555 (p3567 p3922 p5016 : Prop) (h : (¬ p3922) ∨ (¬ p3567) ∨ p5016) : (¬ p3567) ∨ (¬ p3922) ∨ (p5016) := by
  classical
  tauto

theorem initial22555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3922)) ∨ (meaning t m 5016) := by
  have source := ElevenTheory.theory11811 (m.theta 0 6) (m.theta 1 6) (m.theta 3 6)
  exact rule22555 (meaning t m 3567) (meaning t m 3922) (meaning t m 5016) source

theorem rule22559 (p3238 p3487 p4256 p4607 : Prop) (h : (¬ p4607) ∨ (¬ p3487) ∨ (¬ p3238) ∨ p4256) : (¬ p3238) ∨ (¬ p3487) ∨ (p4256) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial22559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3487)) ∨ (meaning t m 4256) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory11815 (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule22559 (meaning t m 3238) (meaning t m 3487) (meaning t m 4256) (meaning t m 4607) source

theorem rule22562 (p2657 p2952 p4700 : Prop) (h : (¬ p2657) ∨ (¬ p4700) ∨ p2952) : (¬ p2657) ∨ (p2952) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial22562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (meaning t m 2952) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory11818 (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule22562 (meaning t m 2657) (meaning t m 2952) (meaning t m 4700) source

theorem rule22563 (p1994 p2027 p2323 p2630 p3166 p3256 p4340 p4364 : Prop) (h : (¬ p3256) ∨ p2323 ∨ (¬ p4364) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p3166) ∨ (¬ p2630) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2323) ∨ (¬ p2630) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4340) ∨ (¬ p4364) := by
  classical
  tauto

theorem initial22563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) := by
  have source := ElevenTheory.theory11819 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule22563 (meaning t m 1994) (meaning t m 2027) (meaning t m 2323) (meaning t m 2630) (meaning t m 3166) (meaning t m 3256) (meaning t m 4340) (meaning t m 4364) source

theorem rule22564 (p2027 p3323 p3324 p4345 p5118 p5580 : Prop) (h : (¬ p4345) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p3323) ∨ (¬ p5118)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial22564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory11820 t (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule22564 (meaning t m 2027) (meaning t m 3323) (meaning t m 3324) (meaning t m 4345) (meaning t m 5118) (meaning t m 5580) source

theorem rule22565 (p2264 p2298 p3945 p4107 : Prop) (h : (¬ p2264) ∨ (¬ p3945) ∨ (¬ p2298) ∨ (¬ p4107)) : (¬ p2264) ∨ (¬ p2298) ∨ (¬ p3945) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial22565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory11821 (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22565 (meaning t m 2264) (meaning t m 2298) (meaning t m 3945) (meaning t m 4107) source

theorem rule22568 (p2509 p3238 p4607 : Prop) (h : (¬ p3238) ∨ (¬ p4607) ∨ p2509) : (p2509) ∨ (¬ p3238) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial22568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2509) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory11824 (m.theta 1 4) (m.theta 4 5) (m.theta 4 8)
  exact rule22568 (meaning t m 2509) (meaning t m 3238) (meaning t m 4607) source

theorem rule22570 (p2027 p2542 p2563 p3363 p3646 p3904 p4750 : Prop) (h : (¬ p3904) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p3363) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3363) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11826 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule22570 (meaning t m 2027) (meaning t m 2542) (meaning t m 2563) (meaning t m 3363) (meaning t m 3646) (meaning t m 3904) (meaning t m 4750) source

theorem rule22571 (p2027 p2136 p2839 p2860 p3646 p4734 : Prop) (h : (¬ p2839) ∨ (¬ p3646) ∨ (¬ p2860) ∨ (¬ p2136) ∨ (¬ p4734) ∨ p2027) : (p2027) ∨ (¬ p2136) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11827 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6)
  exact rule22571 (meaning t m 2027) (meaning t m 2136) (meaning t m 2839) (meaning t m 2860) (meaning t m 3646) (meaning t m 4734) source

theorem rule22572 (p2027 p2499 p2696 p3005 p3256 p3452 p4137 p4604 p4733 : Prop) (h : (¬ p2499) ∨ (¬ p4733) ∨ (¬ p2696) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p4137) ∨ (¬ p3005) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11828 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22572 (meaning t m 2027) (meaning t m 2499) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3452) (meaning t m 4137) (meaning t m 4604) (meaning t m 4733) source

theorem rule22575 (p2027 p2098 p3238 p3452 p3609 p3880 p4348 p4733 p4905 : Prop) (h : (¬ p2098) ∨ (¬ p3238) ∨ (¬ p4733) ∨ (¬ p4348) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p3609) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2098) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial22575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory11831 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22575 (meaning t m 2027) (meaning t m 2098) (meaning t m 3238) (meaning t m 3452) (meaning t m 3609) (meaning t m 3880) (meaning t m 4348) (meaning t m 4733) (meaning t m 4905) source

theorem rule22576 (p2027 p2449 p2509 p2534 p2685 p2696 p3452 p3950 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p2685) ∨ (¬ p3452) ∨ (¬ p2534) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p2449) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11832 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22576 (meaning t m 2027) (meaning t m 2449) (meaning t m 2509) (meaning t m 2534) (meaning t m 2685) (meaning t m 2696) (meaning t m 3452) (meaning t m 3950) (meaning t m 4733) source

theorem rule22577 (p2027 p2528 p3692 p3694 p4355 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p4355) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4355) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial22577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11833 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule22577 (meaning t m 2027) (meaning t m 2528) (meaning t m 3692) (meaning t m 3694) (meaning t m 4355) (meaning t m 4882) source

theorem rule22580 (p2027 p2406 p2499 p2982 p3096 p5046 : Prop) (h : p2027 ∨ (¬ p2406) ∨ (¬ p5046) ∨ (¬ p2499) ∨ (¬ p3096) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11836 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9)
  exact rule22580 (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 2982) (meaning t m 3096) (meaning t m 5046) source

theorem rule22581 (p2027 p2247 p2459 p2717 p3471 p3662 p4208 p4733 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2247) ∨ (¬ p3471) ∨ (¬ p2717) ∨ (¬ p4733) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4733) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial22581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory11837 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22581 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2717) (meaning t m 3471) (meaning t m 3662) (meaning t m 4208) (meaning t m 4733) (meaning t m 5059) source

theorem rule22585 (p2027 p2230 p2264 p3551 p4156 p4389 p4715 p5197 : Prop) (h : p2027 ∨ (¬ p4715) ∨ (¬ p2230) ∨ (¬ p4389) ∨ (¬ p5197) ∨ (¬ p2264) ∨ (¬ p4156) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2264) ∨ (¬ p3551) ∨ (¬ p4156) ∨ (¬ p4389) ∨ (¬ p4715) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial22585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory11841 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 8)
  exact rule22585 (meaning t m 2027) (meaning t m 2230) (meaning t m 2264) (meaning t m 3551) (meaning t m 4156) (meaning t m 4389) (meaning t m 4715) (meaning t m 5197) source

theorem rule22586 (p2027 p3868 p3920 p3956 p4260 p4501 : Prop) (h : (¬ p3868) ∨ (¬ p3920) ∨ (¬ p4260) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p4501)) : (p2027) ∨ (¬ p3868) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4260) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11842 t (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule22586 (meaning t m 2027) (meaning t m 3868) (meaning t m 3920) (meaning t m 3956) (meaning t m 4260) (meaning t m 4501) source

theorem rule22588 (p2027 p2132 p2499 p2619 p3146 p3452 p4137 p4604 p4733 : Prop) (h : (¬ p2619) ∨ (¬ p4733) ∨ (¬ p3146) ∨ (¬ p4137) ∨ (¬ p2499) ∨ (¬ p2132) ∨ (¬ p4604) ∨ (¬ p3452) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2499) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11844 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule22588 (meaning t m 2027) (meaning t m 2132) (meaning t m 2499) (meaning t m 2619) (meaning t m 3146) (meaning t m 3452) (meaning t m 4137) (meaning t m 4604) (meaning t m 4733) source

theorem rule22589 (p2027 p2298 p2331 p3323 p3414 p4624 : Prop) (h : (¬ p3323) ∨ (¬ p2298) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p3414) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3414) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11845 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22589 (meaning t m 2027) (meaning t m 2298) (meaning t m 2331) (meaning t m 3323) (meaning t m 3414) (meaning t m 4624) source

theorem rule22590 (p2027 p2311 p2667 p2911 p3323 p3551 p3921 p4624 : Prop) (h : (¬ p2667) ∨ (¬ p3921) ∨ (¬ p4624) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p2911) ∨ (¬ p2311) ∨ p2027) : (p2027) ∨ (¬ p2311) ∨ (¬ p2667) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p3921) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11846 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule22590 (meaning t m 2027) (meaning t m 2311) (meaning t m 2667) (meaning t m 2911) (meaning t m 3323) (meaning t m 3551) (meaning t m 3921) (meaning t m 4624) source

theorem rule22591 (p1984 p2027 p2331 p2499 p2588 p2688 p2952 p2992 p3323 p3452 p4624 : Prop) (h : (¬ p1984) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p4624) ∨ (¬ p2952) ∨ (¬ p2588) ∨ (¬ p2992) ∨ p2688) : (¬ p1984) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (p2688) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11847 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule22591 (meaning t m 1984) (meaning t m 2027) (meaning t m 2331) (meaning t m 2499) (meaning t m 2588) (meaning t m 2688) (meaning t m 2952) (meaning t m 2992) (meaning t m 3323) (meaning t m 3452) (meaning t m 4624) source

theorem rule22592 (p2027 p2248 p2264 p2499 p2588 p2807 p3452 p3570 p4556 : Prop) (h : p2027 ∨ (¬ p4556) ∨ (¬ p2807) ∨ (¬ p2248) ∨ (¬ p3452) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3570) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p3570) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory11848 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22592 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2499) (meaning t m 2588) (meaning t m 2807) (meaning t m 3452) (meaning t m 3570) (meaning t m 4556) source

theorem rule22593 (p2499 p2509 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p2499) ∨ p2509) : (¬ p2499) ∨ (p2509) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial22593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (meaning t m 2509) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory11849 (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule22593 (meaning t m 2499) (meaning t m 2509) (meaning t m 3573) source

theorem rule22596 (p2027 p2881 p2960 p3051 p3553 p4386 : Prop) (h : (¬ p2960) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p4386) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2881) ∨ (¬ p2960) ∨ (¬ p3051) ∨ (¬ p3553) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial22596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory11852 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule22596 (meaning t m 2027) (meaning t m 2881) (meaning t m 2960) (meaning t m 3051) (meaning t m 3553) (meaning t m 4386) source

theorem rule22597 (p2499 p2518 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p2499) ∨ (¬ p2518)) : (¬ p2499) ∨ (¬ p2518) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial22597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory11853 (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule22597 (meaning t m 2499) (meaning t m 2518) (meaning t m 3573) source

theorem rule22598 (p2027 p3323 p3325 p3979 p4196 p4312 p4624 p5568 : Prop) (h : (¬ p3323) ∨ (¬ p3325) ∨ (¬ p4624) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p4196) ∨ (¬ p5568) ∨ (¬ p4312)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3325) ∨ (¬ p3979) ∨ (¬ p4196) ∨ (¬ p4312) ∨ (¬ p4624) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial22598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory11854 t (m.theta 3 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule22598 (meaning t m 2027) (meaning t m 3323) (meaning t m 3325) (meaning t m 3979) (meaning t m 4196) (meaning t m 4312) (meaning t m 4624) (meaning t m 5568) source

theorem rule22600 (p2027 p2295 p2331 p3172 p4432 p4437 p4501 : Prop) (h : (¬ p4437) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p4432) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3172) ∨ (¬ p4432) ∨ (¬ p4437) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11856 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule22600 (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 3172) (meaning t m 4432) (meaning t m 4437) (meaning t m 4501) source

theorem rule22605 (p2027 p2901 p2911 p3497 p4132 p4647 : Prop) (h : p2027 ∨ (¬ p2901) ∨ (¬ p4132) ∨ (¬ p2911) ∨ (¬ p4647) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2901) ∨ (¬ p2911) ∨ (¬ p3497) ∨ (¬ p4132) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial22605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory11861 t (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule22605 (meaning t m 2027) (meaning t m 2901) (meaning t m 2911) (meaning t m 3497) (meaning t m 4132) (meaning t m 4647) source

theorem rule22608 (p2284 p3156 p3988 : Prop) (h : (¬ p3156) ∨ (¬ p3988) ∨ p2284) : (p2284) ∨ (¬ p3156) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial22608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2284) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory11864 (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule22608 (meaning t m 2284) (meaning t m 3156) (meaning t m 3988) source

theorem rule22609 (p2248 p3987 p5017 : Prop) (h : (¬ p3987) ∨ (¬ p2248) ∨ p5017) : (¬ p2248) ∨ (¬ p3987) ∨ (p5017) := by
  classical
  tauto

theorem initial22609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3987)) ∨ (meaning t m 5017) := by
  have source := ElevenTheory.theory11865 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6)
  exact rule22609 (meaning t m 2248) (meaning t m 3987) (meaning t m 5017) source

theorem rule22610 (p2667 p3323 p3654 : Prop) (h : (¬ p3323) ∨ (¬ p2667) ∨ p3654) : (¬ p2667) ∨ (¬ p3323) ∨ (p3654) := by
  classical
  tauto

theorem initial22610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3323)) ∨ (meaning t m 3654) := by
  have source := ElevenTheory.theory11866 (m.theta 0 6) (m.theta 3 6) (m.theta 6 9)
  exact rule22610 (meaning t m 2667) (meaning t m 3323) (meaning t m 3654) source

theorem rule22616 (p1994 p2027 p2202 p2563 p2630 p2957 p3370 p4173 p4315 : Prop) (h : (¬ p4173) ∨ (¬ p1994) ∨ (¬ p4315) ∨ (¬ p3370) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p2630) ∨ p2202 ∨ (¬ p2957)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2630) ∨ (¬ p2957) ∨ (¬ p3370) ∨ (¬ p4173) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial22616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory11872 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule22616 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2630) (meaning t m 2957) (meaning t m 3370) (meaning t m 4173) (meaning t m 4315) source

theorem rule22618 (p2027 p2707 p3688 p3956 p4342 p4475 p4501 : Prop) (h : (¬ p4501) ∨ (¬ p2707) ∨ (¬ p4475) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p3688) ∨ (¬ p4342)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3688) ∨ (¬ p3956) ∨ (¬ p4342) ∨ (¬ p4475) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11874 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22618 (meaning t m 2027) (meaning t m 2707) (meaning t m 3688) (meaning t m 3956) (meaning t m 4342) (meaning t m 4475) (meaning t m 4501) source

theorem rule22620 (p2027 p2088 p2295 p3555 p3989 p4118 p4173 p4196 p4501 p5239 : Prop) (h : (¬ p4173) ∨ (¬ p5239) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p4196) ∨ (¬ p3555) ∨ (¬ p2295) ∨ (¬ p3989) ∨ (¬ p4118) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2295) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4118) ∨ (¬ p4173) ∨ (¬ p4196) ∨ (¬ p4501) ∨ (¬ p5239) := by
  classical
  tauto

theorem initial22620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5239)) := by
  have source := ElevenTheory.theory11876 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule22620 (meaning t m 2027) (meaning t m 2088) (meaning t m 2295) (meaning t m 3555) (meaning t m 3989) (meaning t m 4118) (meaning t m 4173) (meaning t m 4196) (meaning t m 4501) (meaning t m 5239) source

theorem rule22622 (p2027 p2230 p3193 p3343 p3519 p3574 p4715 : Prop) (h : (¬ p3574) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p3193) ∨ (¬ p4715) ∨ (¬ p3343) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3519) ∨ (¬ p3574) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11878 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule22622 (meaning t m 2027) (meaning t m 2230) (meaning t m 3193) (meaning t m 3343) (meaning t m 3519) (meaning t m 3574) (meaning t m 4715) source

theorem rule22623 (p2027 p2542 p2651 p3414 p3740 p4644 : Prop) (h : (¬ p2651) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4644) ∨ (¬ p3740) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial22623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory11879 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule22623 (meaning t m 2027) (meaning t m 2542) (meaning t m 2651) (meaning t m 3414) (meaning t m 3740) (meaning t m 4644) source

theorem rule22624 (p2027 p2313 p2577 p2662 p3309 p3662 p4701 p4759 : Prop) (h : (¬ p2577) ∨ (¬ p4759) ∨ (¬ p3662) ∨ (¬ p2662) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p4701) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3662) ∨ (¬ p4701) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial22624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4701)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory11880 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 7)
  exact rule22624 (meaning t m 2027) (meaning t m 2313) (meaning t m 2577) (meaning t m 2662) (meaning t m 3309) (meaning t m 3662) (meaning t m 4701) (meaning t m 4759) source

theorem rule22627 (p2992 p3189 p4237 : Prop) (h : (¬ p4237) ∨ (¬ p2992) ∨ p3189) : (¬ p2992) ∨ (p3189) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial22627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2992)) ∨ (meaning t m 3189) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory11883 (m.theta 1 3) (m.theta 3 5) (m.theta 3 8)
  exact rule22627 (meaning t m 2992) (meaning t m 3189) (meaning t m 4237) source

theorem rule22631 (p2027 p3051 p3989 p4109 p4110 p4140 p4501 : Prop) (h : (¬ p4109) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3051) ∨ (¬ p4140) ∨ (¬ p3989)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3989) ∨ (¬ p4109) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11887 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule22631 (meaning t m 2027) (meaning t m 3051) (meaning t m 3989) (meaning t m 4109) (meaning t m 4110) (meaning t m 4140) (meaning t m 4501) source

theorem rule22634 (p2027 p2749 p3189 p3365 p3877 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p2749) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2749) ∨ (¬ p3189) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11890 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 8)
  exact rule22634 (meaning t m 2027) (meaning t m 2749) (meaning t m 3189) (meaning t m 3365) (meaning t m 3877) (meaning t m 4734) source

theorem rule22636 (p2027 p2928 p3222 p3947 p4327 p5182 p5299 : Prop) (h : (¬ p2928) ∨ (¬ p3947) ∨ (¬ p3222) ∨ (¬ p5182) ∨ p2027 ∨ (¬ p4327) ∨ (¬ p5299)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p5182) ∨ (¬ p5299) := by
  classical
  tauto

theorem initial22636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 5182)) ∨ (¬ (meaning t m 5299)) := by
  have source := ElevenTheory.theory11892 t (m.theta 0 9) (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule22636 (meaning t m 2027) (meaning t m 2928) (meaning t m 3222) (meaning t m 3947) (meaning t m 4327) (meaning t m 5182) (meaning t m 5299) source

theorem rule22637 (p2027 p2696 p3005 p3256 p3555 p3744 p4173 p4604 p4733 : Prop) (h : (¬ p3555) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p4733) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p2696) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11893 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22637 (meaning t m 2027) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4604) (meaning t m 4733) source

theorem rule22641 (p2027 p2563 p2922 p4173 p4202 p4646 : Prop) (h : (¬ p4202) ∨ (¬ p4173) ∨ (¬ p2922) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p2563)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2922) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial22641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory11897 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule22641 (meaning t m 2027) (meaning t m 2563) (meaning t m 2922) (meaning t m 4173) (meaning t m 4202) (meaning t m 4646) source

theorem rule22647 (p2027 p2459 p2717 p3471 p3555 p3744 p4173 p4604 p4733 : Prop) (h : (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3744) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3555) ∨ (¬ p4733) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11903 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22647 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 3471) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4604) (meaning t m 4733) source

theorem rule22649 (p2027 p2630 p2922 p3572 p3575 p4155 p4814 : Prop) (h : (¬ p4814) ∨ (¬ p3572) ∨ (¬ p3575) ∨ (¬ p2630) ∨ (¬ p4155) ∨ p2027 ∨ (¬ p2922)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2922) ∨ (¬ p3572) ∨ (¬ p3575) ∨ (¬ p4155) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial22649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory11905 t (m.theta 0 7) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule22649 (meaning t m 2027) (meaning t m 2630) (meaning t m 2922) (meaning t m 3572) (meaning t m 3575) (meaning t m 4155) (meaning t m 4814) source

theorem rule22650 (p2475 p3960 p4383 : Prop) (h : (¬ p4383) ∨ (¬ p2475) ∨ p3960) : (¬ p2475) ∨ (p3960) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial22650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2475)) ∨ (meaning t m 3960) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory11906 (m.theta 0 8) (m.theta 4 8) (m.theta 7 8)
  exact rule22650 (meaning t m 2475) (meaning t m 3960) (meaning t m 4383) source

theorem rule22658 (p2027 p2363 p3309 p4261 p4371 p4501 : Prop) (h : (¬ p2363) ∨ (¬ p4371) ∨ (¬ p4501) ∨ (¬ p4261) ∨ (¬ p3309) ∨ p2027) : (p2027) ∨ (¬ p2363) ∨ (¬ p3309) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11914 t (m.theta 1 6) (m.theta 1 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule22658 (meaning t m 2027) (meaning t m 2363) (meaning t m 3309) (meaning t m 4261) (meaning t m 4371) (meaning t m 4501) source

theorem rule22664 (p2427 p3556 p3645 p4210 : Prop) (h : (¬ p2427) ∨ (¬ p3645) ∨ (¬ p4210) ∨ (¬ p3556)) : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial22664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory11920 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule22664 (meaning t m 2427) (meaning t m 3556) (meaning t m 3645) (meaning t m 4210) source

theorem rule22667 (p2027 p2122 p2589 p2608 p2829 p3989 p4110 p4501 p5193 : Prop) (h : (¬ p3989) ∨ (¬ p2589) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4110) ∨ (¬ p2829) ∨ (¬ p4501) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4501) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory11923 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22667 (meaning t m 2027) (meaning t m 2122) (meaning t m 2589) (meaning t m 2608) (meaning t m 2829) (meaning t m 3989) (meaning t m 4110) (meaning t m 4501) (meaning t m 5193) source

theorem rule22669 (p2027 p2449 p3549 p4024 p4107 p4156 p4843 : Prop) (h : (¬ p4156) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p4024) ∨ (¬ p4107) ∨ (¬ p3549) ∨ (¬ p4843)) : (p2027) ∨ (¬ p2449) ∨ (¬ p3549) ∨ (¬ p4024) ∨ (¬ p4107) ∨ (¬ p4156) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial22669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory11925 t (m.theta 1 6) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22669 (meaning t m 2027) (meaning t m 2449) (meaning t m 3549) (meaning t m 4024) (meaning t m 4107) (meaning t m 4156) (meaning t m 4843) source

theorem rule22672 (p2027 p2743 p2839 p3572 p4650 p4700 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p4650) ∨ (¬ p2839) ∨ (¬ p4700) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3572)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3572) ∨ (¬ p4650) ∨ (¬ p4700) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial22672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory11928 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule22672 (meaning t m 2027) (meaning t m 2743) (meaning t m 2839) (meaning t m 3572) (meaning t m 4650) (meaning t m 4700) (meaning t m 5051) source

theorem rule22676 (p2027 p3083 p3367 p3588 p4106 p4186 p4750 : Prop) (h : (¬ p3588) ∨ (¬ p3367) ∨ (¬ p4186) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p4106)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4186) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11932 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule22676 (meaning t m 2027) (meaning t m 3083) (meaning t m 3367) (meaning t m 3588) (meaning t m 4106) (meaning t m 4186) (meaning t m 4750) source

theorem rule22679 (p2579 p2589 p2590 : Prop) (h : (¬ p2589) ∨ (¬ p2590) ∨ p2579) : (p2579) ∨ (¬ p2589) ∨ (¬ p2590) := by
  classical
  tauto

theorem initial22679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2579) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2590)) := by
  have source := ElevenTheory.theory11935 (m.theta 0 4) (m.theta 4 5) (m.theta 4 6)
  exact rule22679 (meaning t m 2579) (meaning t m 2589) (meaning t m 2590) source

theorem rule22686 (p2000 p2027 p2177 p2589 p2997 p3570 p4110 p4204 : Prop) (h : p2997 ∨ (¬ p2000) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2177) ∨ (¬ p4204) ∨ (¬ p3570)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2589) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p4110) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial22686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory11942 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22686 (meaning t m 2000) (meaning t m 2027) (meaning t m 2177) (meaning t m 2589) (meaning t m 2997) (meaning t m 3570) (meaning t m 4110) (meaning t m 4204) source

theorem rule22687 (p1980 p2027 p2177 p2331 p2997 p3414 p3553 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3414) ∨ (¬ p1980) ∨ (¬ p2177) ∨ (¬ p2331)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2331) ∨ (p2997) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial22687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory11943 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule22687 (meaning t m 1980) (meaning t m 2027) (meaning t m 2177) (meaning t m 2331) (meaning t m 2997) (meaning t m 3414) (meaning t m 3553) source

theorem rule22704 (p2027 p2132 p2579 p3422 p3475 p3905 p5052 : Prop) (h : (¬ p3905) ∨ (¬ p2579) ∨ (¬ p3475) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p5052) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3905) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial22704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory11960 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6)
  exact rule22704 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 3422) (meaning t m 3475) (meaning t m 3905) (meaning t m 5052) source

theorem rule22705 (p2027 p2737 p2811 p3055 p3166 p3256 p3584 p4137 p4604 p4734 : Prop) (h : (¬ p3256) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p3584) ∨ (¬ p4734) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p3055) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11961 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22705 (meaning t m 2027) (meaning t m 2737) (meaning t m 2811) (meaning t m 3055) (meaning t m 3166) (meaning t m 3256) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) (meaning t m 4734) source

theorem rule22708 (p2027 p2307 p2952 p3568 p3987 p4194 p4701 : Prop) (h : (¬ p4194) ∨ (¬ p3568) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3987) ∨ (¬ p4701) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2952) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4194) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11964 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule22708 (meaning t m 2027) (meaning t m 2307) (meaning t m 2952) (meaning t m 3568) (meaning t m 3987) (meaning t m 4194) (meaning t m 4701) source

theorem rule22709 (p4433 p4498 p4993 : Prop) (h : (¬ p4433) ∨ (¬ p4993) ∨ p4498) : (¬ p4433) ∨ (p4498) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial22709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4433)) ∨ (meaning t m 4498) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory11965 t (m.theta 1 8) (m.theta 5 8) (m.theta 6 8)
  exact rule22709 (meaning t m 4433) (meaning t m 4498) (meaning t m 4993) source

theorem rule22712 (p2027 p2307 p3172 p3568 p3987 p4194 p5008 : Prop) (h : (¬ p3987) ∨ (¬ p3172) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4194) ∨ (¬ p3568) ∨ (¬ p5008)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3172) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4194) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial22712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11968 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule22712 (meaning t m 2027) (meaning t m 2307) (meaning t m 3172) (meaning t m 3568) (meaning t m 3987) (meaning t m 4194) (meaning t m 5008) source

theorem rule22713 (p2027 p3425 p3527 p3659 p3687 p4734 : Prop) (h : (¬ p3687) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p3527) ∨ (¬ p3425)) : (p2027) ∨ (¬ p3425) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3687) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11969 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule22713 (meaning t m 2027) (meaning t m 3425) (meaning t m 3527) (meaning t m 3659) (meaning t m 3687) (meaning t m 4734) source

theorem rule22721 (p2027 p2247 p3434 p3471 p3568 p3690 p4154 p4556 p4733 : Prop) (h : (¬ p3434) ∨ (¬ p4733) ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p4556) ∨ (¬ p2247) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p4154)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4154) ∨ (¬ p4556) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11977 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22721 (meaning t m 2027) (meaning t m 2247) (meaning t m 3434) (meaning t m 3471) (meaning t m 3568) (meaning t m 3690) (meaning t m 4154) (meaning t m 4556) (meaning t m 4733) source

theorem rule22723 (p2027 p2707 p2748 p3365 p3434 p3568 p3690 p4154 p4556 p4734 : Prop) (h : (¬ p3365) ∨ (¬ p3690) ∨ (¬ p2748) ∨ (¬ p4556) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4154) ∨ (¬ p4556) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11979 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22723 (meaning t m 2027) (meaning t m 2707) (meaning t m 2748) (meaning t m 3365) (meaning t m 3434) (meaning t m 3568) (meaning t m 3690) (meaning t m 4154) (meaning t m 4556) (meaning t m 4734) source

theorem rule22724 (p2027 p2499 p2588 p2668 p2696 p2797 p3452 p4405 p4733 : Prop) (h : (¬ p4405) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p2499) ∨ (¬ p2668) ∨ (¬ p3452) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3452) ∨ (¬ p4405) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11980 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22724 (meaning t m 2027) (meaning t m 2499) (meaning t m 2588) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3452) (meaning t m 4405) (meaning t m 4733) source

theorem rule22729 (p2027 p2230 p2656 p2727 p2996 p3740 p4644 : Prop) (h : p2027 ∨ (¬ p2230) ∨ (¬ p4644) ∨ (¬ p2996) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3740)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3740) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial22729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory11985 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule22729 (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 2727) (meaning t m 2996) (meaning t m 3740) (meaning t m 4644) source

theorem rule22730 (p2027 p2542 p3564 p4037 p4194 p4715 : Prop) (h : p2027 ∨ (¬ p4037) ∨ (¬ p2542) ∨ (¬ p4715) ∨ (¬ p3564) ∨ (¬ p4194)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11986 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule22730 (meaning t m 2027) (meaning t m 2542) (meaning t m 3564) (meaning t m 4037) (meaning t m 4194) (meaning t m 4715) source

theorem rule22731 (p2027 p3399 p3542 p3631 p3860 p4668 : Prop) (h : (¬ p3542) ∨ (¬ p3860) ∨ (¬ p3631) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3399)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3631) ∨ (¬ p3860) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11987 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8) (m.theta 7 9)
  exact rule22731 (meaning t m 2027) (meaning t m 3399) (meaning t m 3542) (meaning t m 3631) (meaning t m 3860) (meaning t m 4668) source

theorem rule22732 (p2027 p3516 p3551 p4443 p5118 p5558 : Prop) (h : p2027 ∨ (¬ p3551) ∨ (¬ p3516) ∨ (¬ p5558) ∨ (¬ p5118) ∨ (¬ p4443)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial22732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory11988 t (m.theta 0 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule22732 (meaning t m 2027) (meaning t m 3516) (meaning t m 3551) (meaning t m 4443) (meaning t m 5118) (meaning t m 5558) source

theorem rule22735 (p2027 p2166 p3486 p4042 p5559 p5660 : Prop) (h : (¬ p4042) ∨ (¬ p3486) ∨ (¬ p5660) ∨ (¬ p5559) ∨ (¬ p2166) ∨ p2027) : (p2027) ∨ (¬ p2166) ∨ (¬ p3486) ∨ (¬ p4042) ∨ (¬ p5559) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial22735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 5559)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory11991 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8)
  exact rule22735 (meaning t m 2027) (meaning t m 2166) (meaning t m 3486) (meaning t m 4042) (meaning t m 5559) (meaning t m 5660) source

theorem rule22736 (p2027 p2579 p3347 p3449 p3954 p4137 p4181 p4191 p5119 p5216 : Prop) (h : (¬ p4137) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p3954) ∨ (¬ p5216) ∨ (¬ p4191) ∨ (¬ p4181) ∨ (¬ p3347) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4181) ∨ (¬ p4191) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory11992 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule22736 (meaning t m 2027) (meaning t m 2579) (meaning t m 3347) (meaning t m 3449) (meaning t m 3954) (meaning t m 4137) (meaning t m 4181) (meaning t m 4191) (meaning t m 5119) (meaning t m 5216) source

theorem rule22738 (p2027 p2589 p3347 p3399 p3570 p3631 p3954 p4235 p4668 p5216 : Prop) (h : p2027 ∨ (¬ p4668) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3347) ∨ (¬ p4235) ∨ (¬ p2589) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4235) ∨ (¬ p4668) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory11994 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22738 (meaning t m 2027) (meaning t m 2589) (meaning t m 3347) (meaning t m 3399) (meaning t m 3570) (meaning t m 3631) (meaning t m 3954) (meaning t m 4235) (meaning t m 4668) (meaning t m 5216) source

theorem rule22739 (p2027 p3051 p3486 p3954 p4172 p4877 : Prop) (h : (¬ p4172) ∨ (¬ p3486) ∨ (¬ p3051) ∨ (¬ p4877) ∨ (¬ p3954) ∨ p2027) : (p2027) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial22739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory11995 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 7)
  exact rule22739 (meaning t m 2027) (meaning t m 3051) (meaning t m 3486) (meaning t m 3954) (meaning t m 4172) (meaning t m 4877) source

theorem rule22740 (p2027 p2252 p2299 p2750 p2963 p3399 p3568 p3631 p3954 p4668 : Prop) (h : (¬ p2963) ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3568) ∨ (¬ p4668) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2299) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3399) ∨ (¬ p3568) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11996 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22740 (meaning t m 2027) (meaning t m 2252) (meaning t m 2299) (meaning t m 2750) (meaning t m 2963) (meaning t m 3399) (meaning t m 3568) (meaning t m 3631) (meaning t m 3954) (meaning t m 4668) source

theorem rule22743 (p2497 p4870 p5216 : Prop) (h : (¬ p2497) ∨ (¬ p5216) ∨ p4870) : (¬ p2497) ∨ (p4870) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2497)) ∨ (meaning t m 4870) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory11999 t (m.theta 1 2) (m.theta 1 4) (m.theta 1 6)
  exact rule22743 (meaning t m 2497) (meaning t m 4870) (meaning t m 5216) source

theorem rule22747 (p2027 p2427 p3125 p4037 p4153 p4204 p4702 : Prop) (h : (¬ p4204) ∨ (¬ p4037) ∨ (¬ p4702) ∨ (¬ p4153) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p3125)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4153) ∨ (¬ p4204) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial22747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory12003 t (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule22747 (meaning t m 2027) (meaning t m 2427) (meaning t m 3125) (meaning t m 4037) (meaning t m 4153) (meaning t m 4204) (meaning t m 4702) source

theorem rule22750 (p2027 p3266 p3346 p3347 p3399 p3631 p3950 p3954 p4425 p5216 : Prop) (h : (¬ p3954) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p3399) ∨ (¬ p3950) ∨ (¬ p5216) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p3347)) : (p2027) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12006 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule22750 (meaning t m 2027) (meaning t m 3266) (meaning t m 3346) (meaning t m 3347) (meaning t m 3399) (meaning t m 3631) (meaning t m 3950) (meaning t m 3954) (meaning t m 4425) (meaning t m 5216) source

theorem rule22753 (p2027 p2406 p3051 p4109 p4320 p4700 p4814 : Prop) (h : (¬ p4109) ∨ (¬ p4700) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p4814) ∨ (¬ p2406)) : (p2027) ∨ (¬ p2406) ∨ (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial22753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12009 t (m.theta 0 5) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule22753 (meaning t m 2027) (meaning t m 2406) (meaning t m 3051) (meaning t m 4109) (meaning t m 4320) (meaning t m 4700) (meaning t m 4814) source

theorem rule22754 (p2027 p2922 p3238 p3569 p4110 p4558 : Prop) (h : p2027 ∨ (¬ p4558) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p2922) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12010 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22754 (meaning t m 2027) (meaning t m 2922) (meaning t m 3238) (meaning t m 3569) (meaning t m 4110) (meaning t m 4558) source

theorem rule22758 (p3193 p3346 p3519 : Prop) (h : (¬ p3193) ∨ (¬ p3519) ∨ p3346) : (¬ p3193) ∨ (p3346) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial22758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3193)) ∨ (meaning t m 3346) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory12014 (m.theta 0 4) (m.theta 1 4) (m.theta 4 9)
  exact rule22758 (meaning t m 3193) (meaning t m 3346) (meaning t m 3519) source

theorem rule22760 (p2027 p2499 p2922 p4137 p4620 p4710 : Prop) (h : p2027 ∨ (¬ p4710) ∨ (¬ p4620) ∨ (¬ p2922) ∨ (¬ p2499) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial22760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory12016 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22760 (meaning t m 2027) (meaning t m 2499) (meaning t m 2922) (meaning t m 4137) (meaning t m 4620) (meaning t m 4710) source

theorem rule22761 (p2027 p2696 p3005 p3256 p3486 p3555 p3690 p4669 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p4669) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p3005) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12017 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22761 (meaning t m 2027) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4669) (meaning t m 4733) source

theorem rule22762 (p2027 p2230 p2373 p2579 p3096 p4509 : Prop) (h : (¬ p3096) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4509) ∨ (¬ p2373) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12018 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule22762 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2579) (meaning t m 3096) (meaning t m 4509) source

theorem rule22765 (p2027 p2248 p2901 p2928 p2946 p3246 p3452 p3644 p4668 : Prop) (h : (¬ p3644) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p2901) ∨ (¬ p2248) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12021 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22765 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2928) (meaning t m 2946) (meaning t m 3246) (meaning t m 3452) (meaning t m 3644) (meaning t m 4668) source

theorem rule22766 (p2027 p2230 p2577 p3564 p3946 p4715 : Prop) (h : (¬ p3564) ∨ (¬ p3946) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p2577) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2577) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial22766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12022 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule22766 (meaning t m 2027) (meaning t m 2230) (meaning t m 2577) (meaning t m 3564) (meaning t m 3946) (meaning t m 4715) source

theorem rule22771 (p2027 p2156 p3146 p3697 p3857 p4507 : Prop) (h : (¬ p2156) ∨ (¬ p4507) ∨ p2027 ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial22771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory12027 t (m.theta 0 5) (m.theta 0 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule22771 (meaning t m 2027) (meaning t m 2156) (meaning t m 3146) (meaning t m 3697) (meaning t m 3857) (meaning t m 4507) source

theorem rule22773 (p2027 p2299 p2750 p3399 p3631 p3954 p4037 p4154 p4187 p4668 : Prop) (h : (¬ p4668) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4187) ∨ (¬ p2299) ∨ (¬ p4154) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4187) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12029 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule22773 (meaning t m 2027) (meaning t m 2299) (meaning t m 2750) (meaning t m 3399) (meaning t m 3631) (meaning t m 3954) (meaning t m 4037) (meaning t m 4154) (meaning t m 4187) (meaning t m 4668) source

theorem rule22776 (p2027 p2440 p2578 p3016 p3758 p4356 p4882 : Prop) (h : (¬ p3758) ∨ (¬ p4356) ∨ (¬ p4882) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2578) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3758) ∨ (¬ p4356) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial22776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory12032 t (m.theta 0 6) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule22776 (meaning t m 2027) (meaning t m 2440) (meaning t m 2578) (meaning t m 3016) (meaning t m 3758) (meaning t m 4356) (meaning t m 4882) source

theorem rule22777 (p2027 p3073 p3692 p4042 p4189 p4442 p5559 : Prop) (h : (¬ p3073) ∨ (¬ p5559) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4042) ∨ (¬ p4442) ∨ (¬ p4189)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4042) ∨ (¬ p4189) ∨ (¬ p4442) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial22777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory12033 t (m.theta 1 7) (m.theta 1 8) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule22777 (meaning t m 2027) (meaning t m 3073) (meaning t m 3692) (meaning t m 4042) (meaning t m 4189) (meaning t m 4442) (meaning t m 5559) source

theorem rule22778 (p2027 p2437 p3516 p3575 p4256 p4383 p4668 : Prop) (h : p2027 ∨ (¬ p3575) ∨ (¬ p4256) ∨ (¬ p3516) ∨ (¬ p2437) ∨ (¬ p4383) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2437) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12034 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9)
  exact rule22778 (meaning t m 2027) (meaning t m 2437) (meaning t m 3516) (meaning t m 3575) (meaning t m 4256) (meaning t m 4383) (meaning t m 4668) source

theorem rule22781 (p2963 p3292 p5274 : Prop) (h : (¬ p5274) ∨ (¬ p2963) ∨ p3292) : (¬ p2963) ∨ (p3292) ∨ (¬ p5274) := by
  classical
  tauto

theorem initial22781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2963)) ∨ (meaning t m 3292) ∨ (¬ (meaning t m 5274)) := by
  have source := ElevenTheory.theory12037 (m.theta 0 3) (m.theta 3 6) (m.theta 3 9)
  exact rule22781 (meaning t m 2963) (meaning t m 3292) (meaning t m 5274) source

theorem rule22786 (p2027 p3399 p3555 p3571 p4244 p4878 : Prop) (h : p2027 ∨ (¬ p4878) ∨ (¬ p4244) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4244) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial22786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory12042 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7)
  exact rule22786 (meaning t m 2027) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) (meaning t m 4244) (meaning t m 4878) source

theorem rule22788 (p3399 p3471 p3576 p3873 : Prop) (h : (¬ p3873) ∨ (¬ p3576) ∨ (¬ p3399) ∨ p3471) : (¬ p3399) ∨ (p3471) ∨ (¬ p3576) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial22788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (meaning t m 3471) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory12044 (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 7)
  exact rule22788 (meaning t m 3399) (meaning t m 3471) (meaning t m 3576) (meaning t m 3873) source

theorem rule22789 (p2027 p2579 p3347 p3399 p3461 p3631 p3746 p3954 p4425 p4625 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3461) ∨ (¬ p4425) ∨ (¬ p3746)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3461) ∨ (¬ p3631) ∨ (¬ p3746) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12045 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule22789 (meaning t m 2027) (meaning t m 2579) (meaning t m 3347) (meaning t m 3399) (meaning t m 3461) (meaning t m 3631) (meaning t m 3746) (meaning t m 3954) (meaning t m 4425) (meaning t m 4625) (meaning t m 5216) source

theorem rule22790 (p2027 p2299 p3461 p4187 p4321 p4668 p5362 : Prop) (h : (¬ p4187) ∨ (¬ p5362) ∨ (¬ p4321) ∨ (¬ p3461) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p4668)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4321) ∨ (¬ p4668) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial22790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory12046 t (m.theta 1 9) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule22790 (meaning t m 2027) (meaning t m 2299) (meaning t m 3461) (meaning t m 4187) (meaning t m 4321) (meaning t m 4668) (meaning t m 5362) source

theorem rule22801 (p2247 p3399 p3846 p5363 : Prop) (h : (¬ p2247) ∨ (¬ p5363) ∨ (¬ p3399) ∨ (¬ p3846)) : (¬ p2247) ∨ (¬ p3399) ∨ (¬ p3846) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial22801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3846)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory12057 (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 1 9)
  exact rule22801 (meaning t m 2247) (meaning t m 3399) (meaning t m 3846) (meaning t m 5363) source

theorem rule22802 (p2027 p2579 p3347 p3399 p3954 p4075 p4137 p4191 p4826 p5216 : Prop) (h : (¬ p4137) ∨ (¬ p2579) ∨ (¬ p4191) ∨ (¬ p3954) ∨ (¬ p4075) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p4826) ∨ (¬ p3347) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12058 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule22802 (meaning t m 2027) (meaning t m 2579) (meaning t m 3347) (meaning t m 3399) (meaning t m 3954) (meaning t m 4075) (meaning t m 4137) (meaning t m 4191) (meaning t m 4826) (meaning t m 5216) source

theorem rule22804 (p2307 p3051 p4140 p4198 : Prop) (h : (¬ p4140) ∨ (¬ p3051) ∨ (¬ p4198) ∨ p2307) : (p2307) ∨ (¬ p3051) ∨ (¬ p4140) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial22804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2307) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory12060 (m.theta 0 5) (m.theta 0 6) (m.theta 5 7) (m.theta 6 7)
  exact rule22804 (meaning t m 2307) (meaning t m 3051) (meaning t m 4140) (meaning t m 4198) source

theorem rule22807 (p2027 p2470 p3540 p4404 p5503 p5559 : Prop) (h : (¬ p5559) ∨ (¬ p2470) ∨ (¬ p5503) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p4404)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4404) ∨ (¬ p5503) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial22807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory12063 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 10) (m.theta 7 8)
  exact rule22807 (meaning t m 2027) (meaning t m 2470) (meaning t m 3540) (meaning t m 4404) (meaning t m 5503) (meaning t m 5559) source

theorem rule22808 (p2027 p2406 p2926 p3868 p4442 p4644 : Prop) (h : (¬ p3868) ∨ (¬ p4442) ∨ (¬ p2926) ∨ p2027 ∨ (¬ p4644) ∨ (¬ p2406)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2926) ∨ (¬ p3868) ∨ (¬ p4442) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial22808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12064 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 10)
  exact rule22808 (meaning t m 2027) (meaning t m 2406) (meaning t m 2926) (meaning t m 3868) (meaning t m 4442) (meaning t m 4644) source

theorem rule22809 (p2027 p3399 p3645 p3692 p3954 p4075 p4120 p4444 p4826 p4877 : Prop) (h : (¬ p4075) ∨ (¬ p3399) ∨ (¬ p4444) ∨ (¬ p3692) ∨ (¬ p4826) ∨ (¬ p4120) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4877) ∨ (¬ p3645)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial22809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12065 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule22809 (meaning t m 2027) (meaning t m 3399) (meaning t m 3645) (meaning t m 3692) (meaning t m 3954) (meaning t m 4075) (meaning t m 4120) (meaning t m 4444) (meaning t m 4826) (meaning t m 4877) source

theorem rule22810 (p2027 p2499 p2573 p3954 p4079 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p4079) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2499) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12066 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 6)
  exact rule22810 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 3954) (meaning t m 4079) (meaning t m 5216) source

theorem rule22812 (p1979 p2027 p2114 p2253 p2807 p2992 p2996 p3954 : Prop) (h : p2114 ∨ (¬ p1979) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p2996)) : (¬ p1979) ∨ (p2027) ∨ (p2114) ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial22812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory12068 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7)
  exact rule22812 (meaning t m 1979) (meaning t m 2027) (meaning t m 2114) (meaning t m 2253) (meaning t m 2807) (meaning t m 2992) (meaning t m 2996) (meaning t m 3954) source

theorem rule22814 (p2027 p2933 p3399 p3452 p3876 p5217 : Prop) (h : (¬ p2933) ∨ (¬ p3876) ∨ (¬ p3452) ∨ (¬ p3399) ∨ (¬ p5217) ∨ p2027) : (p2027) ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3876) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial22814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory12070 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7)
  exact rule22814 (meaning t m 2027) (meaning t m 2933) (meaning t m 3399) (meaning t m 3452) (meaning t m 3876) (meaning t m 5217) source

theorem rule22815 (p2027 p2589 p2608 p2707 p3434 p3692 p3880 p3950 p5193 : Prop) (h : (¬ p3434) ∨ (¬ p3692) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p5193) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12071 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22815 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2707) (meaning t m 3434) (meaning t m 3692) (meaning t m 3880) (meaning t m 3950) (meaning t m 5193) source

theorem rule22817 (p2027 p2241 p2589 p3027 p3931 p4322 p4826 p4948 p5193 : Prop) (h : (¬ p2589) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p5193) ∨ (¬ p4948) ∨ (¬ p3931) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4322) ∨ (¬ p4826) ∨ (¬ p4948) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12073 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule22817 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3027) (meaning t m 3931) (meaning t m 4322) (meaning t m 4826) (meaning t m 4948) (meaning t m 5193) source

theorem rule22818 (p2027 p2241 p2641 p3266 p3323 p3346 p4330 p4425 p5193 : Prop) (h : (¬ p3323) ∨ (¬ p3346) ∨ (¬ p5193) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4425) ∨ (¬ p3266) ∨ (¬ p4330)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3266) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p4330) ∨ (¬ p4425) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12074 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule22818 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3266) (meaning t m 3323) (meaning t m 3346) (meaning t m 4330) (meaning t m 4425) (meaning t m 5193) source

theorem rule22820 (p2027 p2313 p3309 p3379 p4869 p5015 p5216 : Prop) (h : p2027 ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p3309) ∨ (¬ p5015) ∨ (¬ p4869) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p3379) ∨ (¬ p4869) ∨ (¬ p5015) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5015)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12076 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7)
  exact rule22820 (meaning t m 2027) (meaning t m 2313) (meaning t m 3309) (meaning t m 3379) (meaning t m 4869) (meaning t m 5015) (meaning t m 5216) source

theorem rule22821 (p2027 p2187 p2313 p2667 p3550 p3986 p4260 p5559 : Prop) (h : p2027 ∨ (¬ p2667) ∨ (¬ p3986) ∨ (¬ p4260) ∨ (¬ p5559) ∨ (¬ p2313) ∨ (¬ p3550) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3550) ∨ (¬ p3986) ∨ (¬ p4260) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial22821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory12077 t (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule22821 (meaning t m 2027) (meaning t m 2187) (meaning t m 2313) (meaning t m 2667) (meaning t m 3550) (meaning t m 3986) (meaning t m 4260) (meaning t m 5559) source

theorem rule22822 (p2027 p2248 p2274 p2284 p2499 p2946 p3452 p3956 p4501 : Prop) (h : (¬ p2946) ∨ (¬ p2284) ∨ (¬ p2499) ∨ (¬ p2248) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4501) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory12078 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22822 (meaning t m 2027) (meaning t m 2248) (meaning t m 2274) (meaning t m 2284) (meaning t m 2499) (meaning t m 2946) (meaning t m 3452) (meaning t m 3956) (meaning t m 4501) source

theorem rule22823 (p2027 p2132 p2870 p2928 p3246 p3452 p3644 p4668 p4733 : Prop) (h : (¬ p3452) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3246) ∨ (¬ p2870) ∨ (¬ p4733) ∨ (¬ p3644) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2928) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4668) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12079 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22823 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 2928) (meaning t m 3246) (meaning t m 3452) (meaning t m 3644) (meaning t m 4668) (meaning t m 4733) source

theorem rule22825 (p2027 p3189 p3874 p4111 p4346 p4750 : Prop) (h : (¬ p4346) ∨ p2027 ∨ (¬ p3189) ∨ (¬ p3874) ∨ (¬ p4750) ∨ (¬ p4111)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3874) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12081 t (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule22825 (meaning t m 2027) (meaning t m 3189) (meaning t m 3874) (meaning t m 4111) (meaning t m 4346) (meaning t m 4750) source

theorem rule22826 (p2027 p2132 p2870 p2881 p3549 p3591 p4278 p4666 p4710 p4733 : Prop) (h : (¬ p2132) ∨ (¬ p4733) ∨ (¬ p4666) ∨ (¬ p4710) ∨ (¬ p3591) ∨ (¬ p3549) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4710) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12082 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22826 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 2881) (meaning t m 3549) (meaning t m 3591) (meaning t m 4278) (meaning t m 4666) (meaning t m 4710) (meaning t m 4733) source

theorem rule22827 (p2027 p2264 p2685 p2696 p2928 p3452 p4278 p4666 p4733 : Prop) (h : (¬ p2685) ∨ (¬ p2264) ∨ (¬ p2928) ∨ (¬ p4733) ∨ (¬ p4666) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12083 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22827 (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4666) (meaning t m 4733) source

theorem rule22828 (p2027 p2476 p2518 p2662 p3662 p4281 p4701 : Prop) (h : (¬ p4281) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p3662) ∨ (¬ p2518) ∨ (¬ p2476) ∨ (¬ p4701)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2662) ∨ (¬ p3662) ∨ (¬ p4281) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12084 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8)
  exact rule22828 (meaning t m 2027) (meaning t m 2476) (meaning t m 2518) (meaning t m 2662) (meaning t m 3662) (meaning t m 4281) (meaning t m 4701) source

theorem rule22831 (p2027 p3333 p3874 p4348 p4438 p4695 : Prop) (h : p2027 ∨ (¬ p4695) ∨ (¬ p4438) ∨ (¬ p3874) ∨ (¬ p4348) ∨ (¬ p3333)) : (p2027) ∨ (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial22831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory12087 t (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22831 (meaning t m 2027) (meaning t m 3333) (meaning t m 3874) (meaning t m 4348) (meaning t m 4438) (meaning t m 4695) source

theorem rule22834 (p2027 p2248 p2901 p2946 p3246 p3585 p3954 p4641 p5160 : Prop) (h : (¬ p2901) ∨ (¬ p3954) ∨ (¬ p3246) ∨ (¬ p4641) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2946) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial22834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory12090 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule22834 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3585) (meaning t m 3954) (meaning t m 4641) (meaning t m 5160) source

theorem rule22835 (p2027 p2727 p2749 p2810 p3365 p4734 : Prop) (h : (¬ p2810) ∨ (¬ p2727) ∨ (¬ p3365) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2749)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12091 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule22835 (meaning t m 2027) (meaning t m 2727) (meaning t m 2749) (meaning t m 2810) (meaning t m 3365) (meaning t m 4734) source

theorem rule22841 (p2027 p2132 p2245 p2657 p2727 p2870 p2881 p4041 p4360 p4733 : Prop) (h : (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2881) ∨ (¬ p4041) ∨ (¬ p4733) ∨ (¬ p2657) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12097 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule22841 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2870) (meaning t m 2881) (meaning t m 4041) (meaning t m 4360) (meaning t m 4733) source

theorem rule22844 (p2027 p2630 p2655 p3222 p3346 p4116 p4787 : Prop) (h : (¬ p2630) ∨ (¬ p4787) ∨ (¬ p3222) ∨ (¬ p2655) ∨ (¬ p3346) ∨ (¬ p4116) ∨ p2027) : (p2027) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p4116) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial22844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12100 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9)
  exact rule22844 (meaning t m 2027) (meaning t m 2630) (meaning t m 2655) (meaning t m 3222) (meaning t m 3346) (meaning t m 4116) (meaning t m 4787) source

theorem rule22845 (p2027 p2928 p3222 p3690 p4451 p4647 : Prop) (h : (¬ p4451) ∨ (¬ p3222) ∨ (¬ p4647) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3690) ∨ (¬ p4451) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial22845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory12101 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule22845 (meaning t m 2027) (meaning t m 2928) (meaning t m 3222) (meaning t m 3690) (meaning t m 4451) (meaning t m 4647) source

theorem rule22847 (p2274 p3125 p4187 : Prop) (h : (¬ p4187) ∨ (¬ p2274) ∨ p3125) : (¬ p2274) ∨ (p3125) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial22847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (meaning t m 3125) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory12103 (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule22847 (meaning t m 2274) (meaning t m 3125) (meaning t m 4187) source

theorem rule22848 (p1982 p2027 p2363 p2761 p3360 p3516 p5117 p5580 : Prop) (h : (¬ p1982) ∨ p2027 ∨ p3360 ∨ (¬ p2363) ∨ (¬ p3516) ∨ (¬ p5117) ∨ (¬ p5580) ∨ (¬ p2761)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2761) ∨ (p3360) ∨ (¬ p3516) ∨ (¬ p5117) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial22848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 5117)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory12104 t (m.theta 0 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule22848 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2761) (meaning t m 3360) (meaning t m 3516) (meaning t m 5117) (meaning t m 5580) source

theorem rule22862 (p2027 p2313 p2553 p2668 p3956 p4581 : Prop) (h : (¬ p2553) ∨ (¬ p2313) ∨ (¬ p4581) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p2668)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2668) ∨ (¬ p3956) ∨ (¬ p4581) := by
  classical
  tauto

theorem initial22862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4581)) := by
  have source := ElevenTheory.theory12118 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22862 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2668) (meaning t m 3956) (meaning t m 4581) source

theorem rule22864 (p2027 p2295 p2313 p2577 p2655 p2797 p4787 : Prop) (h : (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2295) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2655) ∨ (¬ p2797) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial22864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12120 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule22864 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2577) (meaning t m 2655) (meaning t m 2797) (meaning t m 4787) source

theorem rule22868 (p1981 p3008 p3564 p4347 p4604 : Prop) (h : (¬ p4347) ∨ p3008 ∨ (¬ p3564) ∨ p4604 ∨ (¬ p1981)) : (¬ p1981) ∨ (p3008) ∨ (¬ p3564) ∨ (¬ p4347) ∨ (p4604) := by
  classical
  tauto

theorem initial22868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4347)) ∨ (meaning t m 4604) := by
  have source := ElevenTheory.theory12124 t (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule22868 (meaning t m 1981) (meaning t m 3008) (meaning t m 3564) (meaning t m 4347) (meaning t m 4604) source

theorem rule22870 (p2027 p2132 p2534 p2870 p3246 p3585 p3874 p3950 p4737 : Prop) (h : (¬ p2870) ∨ (¬ p4737) ∨ (¬ p3585) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3950) ∨ (¬ p2534) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2534) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12126 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22870 (meaning t m 2027) (meaning t m 2132) (meaning t m 2534) (meaning t m 2870) (meaning t m 3246) (meaning t m 3585) (meaning t m 3874) (meaning t m 3950) (meaning t m 4737) source

theorem rule22876 (p2027 p2210 p2254 p2657 p2972 p3680 p3742 p4831 p5503 : Prop) (h : p2027 ∨ (¬ p2210) ∨ (¬ p3680) ∨ (¬ p5503) ∨ (¬ p3742) ∨ (¬ p2657) ∨ (¬ p4831) ∨ (¬ p2254) ∨ (¬ p2972)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial22876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory12132 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule22876 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2972) (meaning t m 3680) (meaning t m 3742) (meaning t m 4831) (meaning t m 5503) source

theorem rule22878 (p2778 p3983 p4236 : Prop) (h : (¬ p4236) ∨ (¬ p3983) ∨ p2778) : (p2778) ∨ (¬ p3983) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial22878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2778) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory12134 (m.theta 0 2) (m.theta 0 3) (m.theta 0 6)
  exact rule22878 (meaning t m 2778) (meaning t m 3983) (meaning t m 4236) source

theorem rule22880 (p2027 p2132 p2657 p3105 p3680 p3742 p4789 p4831 p5503 : Prop) (h : (¬ p3680) ∨ (¬ p4831) ∨ (¬ p3105) ∨ (¬ p3742) ∨ (¬ p5503) ∨ p2027 ∨ (¬ p4789) ∨ (¬ p2132) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial22880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory12136 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule22880 (meaning t m 2027) (meaning t m 2132) (meaning t m 2657) (meaning t m 3105) (meaning t m 3680) (meaning t m 3742) (meaning t m 4789) (meaning t m 4831) (meaning t m 5503) source

theorem rule22881 (p2027 p2396 p3644 p4443 p4710 p5118 p5558 : Prop) (h : (¬ p4443) ∨ (¬ p5558) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p2396) ∨ (¬ p4710) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3644) ∨ (¬ p4443) ∨ (¬ p4710) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial22881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory12137 t (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule22881 (meaning t m 2027) (meaning t m 2396) (meaning t m 3644) (meaning t m 4443) (meaning t m 4710) (meaning t m 5118) (meaning t m 5558) source

theorem rule22882 (p2027 p3055 p3073 p3449 p3684 p3880 p4348 p4736 p4905 : Prop) (h : (¬ p4736) ∨ (¬ p3449) ∨ (¬ p4905) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4348) ∨ (¬ p3073)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial22882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory12138 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22882 (meaning t m 2027) (meaning t m 3055) (meaning t m 3073) (meaning t m 3449) (meaning t m 3684) (meaning t m 3880) (meaning t m 4348) (meaning t m 4736) (meaning t m 4905) source

theorem rule22884 (p2470 p2531 p3904 p4120 : Prop) (h : (¬ p2470) ∨ (¬ p4120) ∨ (¬ p3904) ∨ (¬ p2531)) : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p3904) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial22884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory12140 (m.theta 0 4) (m.theta 0 5) (m.theta 4 8) (m.theta 5 8)
  exact rule22884 (meaning t m 2470) (meaning t m 2531) (meaning t m 3904) (meaning t m 4120) source

theorem rule22886 (p2027 p2122 p2247 p2396 p2774 p3950 p4118 p4360 p4733 : Prop) (h : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4118) ∨ (¬ p4733) ∨ (¬ p4360) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2247) ∨ (¬ p2396) ∨ (¬ p2774) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12142 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule22886 (meaning t m 2027) (meaning t m 2122) (meaning t m 2247) (meaning t m 2396) (meaning t m 2774) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4733) source

theorem rule22888 (p2027 p2132 p2891 p3425 p4169 p4878 : Prop) (h : p2027 ∨ (¬ p4169) ∨ (¬ p2891) ∨ (¬ p2132) ∨ (¬ p4878) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2891) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial22888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory12144 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule22888 (meaning t m 2027) (meaning t m 2132) (meaning t m 2891) (meaning t m 3425) (meaning t m 4169) (meaning t m 4878) source

theorem rule22889 (p2027 p2247 p2459 p2717 p3471 p4037 p4154 p4604 p4733 : Prop) (h : p2027 ∨ (¬ p2459) ∨ (¬ p2247) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p4733) ∨ (¬ p2717) ∨ (¬ p4154) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12145 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule22889 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2717) (meaning t m 3471) (meaning t m 4037) (meaning t m 4154) (meaning t m 4604) (meaning t m 4733) source

theorem rule22890 (p2363 p4261 p4318 : Prop) (h : (¬ p4261) ∨ (¬ p2363) ∨ (¬ p4318)) : (¬ p2363) ∨ (¬ p4261) ∨ (¬ p4318) := by
  classical
  tauto

theorem initial22890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4318)) := by
  have source := ElevenTheory.theory12146 (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule22890 (meaning t m 2363) (meaning t m 4261) (meaning t m 4318) source

theorem rule22891 (p2027 p2144 p2363 p2619 p3051 p3591 p4244 p4261 p4371 p4433 p4733 : Prop) (h : (¬ p2144) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p3591) ∨ (¬ p4433) ∨ (¬ p4244) ∨ (¬ p2619) ∨ (¬ p2363) ∨ (¬ p4261) ∨ (¬ p4733) ∨ (¬ p4371)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3591) ∨ (¬ p4244) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4433) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12147 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 6) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule22891 (meaning t m 2027) (meaning t m 2144) (meaning t m 2363) (meaning t m 2619) (meaning t m 3051) (meaning t m 3591) (meaning t m 4244) (meaning t m 4261) (meaning t m 4371) (meaning t m 4433) (meaning t m 4733) source

theorem rule22892 (p2027 p3222 p3238 p3694 p4335 p4882 p4952 : Prop) (h : (¬ p3222) ∨ (¬ p3694) ∨ (¬ p4335) ∨ p2027 ∨ (¬ p4882) ∨ (¬ p4952) ∨ (¬ p3238)) : (p2027) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3694) ∨ (¬ p4335) ∨ (¬ p4882) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial22892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory12148 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9)
  exact rule22892 (meaning t m 2027) (meaning t m 3222) (meaning t m 3238) (meaning t m 3694) (meaning t m 4335) (meaning t m 4882) (meaning t m 4952) source

theorem rule22893 (p2027 p2579 p2598 p3422 p4108 p4733 : Prop) (h : (¬ p2598) ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p3422) ∨ (¬ p2579) ∨ p2027) : (p2027) ∨ (¬ p2579) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4108) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12149 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 6)
  exact rule22893 (meaning t m 2027) (meaning t m 2579) (meaning t m 2598) (meaning t m 3422) (meaning t m 4108) (meaning t m 4733) source

theorem rule22895 (p2027 p2254 p2657 p3093 p3319 p3461 p3742 p4831 p5503 : Prop) (h : (¬ p2254) ∨ (¬ p3319) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2657) ∨ (¬ p5503) ∨ (¬ p4831) ∨ (¬ p3461) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial22895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory12151 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule22895 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 3742) (meaning t m 4831) (meaning t m 5503) source

theorem rule22896 (p2027 p2318 p2417 p3821 p3920 p3956 p4501 : Prop) (h : (¬ p2417) ∨ (¬ p2318) ∨ (¬ p4501) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p3920) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory12152 t (m.theta 0 7) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule22896 (meaning t m 2027) (meaning t m 2318) (meaning t m 2417) (meaning t m 3821) (meaning t m 3920) (meaning t m 3956) (meaning t m 4501) source

theorem rule22898 (p2027 p2657 p3073 p3266 p3449 p3742 p4236 p4736 p4831 p5503 : Prop) (h : (¬ p5503) ∨ (¬ p4831) ∨ (¬ p3742) ∨ (¬ p2657) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p4736) ∨ (¬ p3266) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3742) ∨ (¬ p4236) ∨ (¬ p4736) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial22898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory12154 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule22898 (meaning t m 2027) (meaning t m 2657) (meaning t m 3073) (meaning t m 3266) (meaning t m 3449) (meaning t m 3742) (meaning t m 4236) (meaning t m 4736) (meaning t m 4831) (meaning t m 5503) source

theorem rule22899 (p2027 p2657 p3422 p3475 p3742 p3920 p4787 : Prop) (h : (¬ p3475) ∨ p2027 ∨ (¬ p3920) ∨ (¬ p3742) ∨ (¬ p4787) ∨ (¬ p2657) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3742) ∨ (¬ p3920) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial22899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12155 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule22899 (meaning t m 2027) (meaning t m 2657) (meaning t m 3422) (meaning t m 3475) (meaning t m 3742) (meaning t m 3920) (meaning t m 4787) source

theorem rule22900 (p2657 p3055 p3683 p4236 : Prop) (h : (¬ p4236) ∨ (¬ p2657) ∨ (¬ p3683) ∨ p3055) : (¬ p2657) ∨ (p3055) ∨ (¬ p3683) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial22900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (meaning t m 3055) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory12156 (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 4)
  exact rule22900 (meaning t m 2657) (meaning t m 3055) (meaning t m 3683) (meaning t m 4236) source

theorem rule22903 (p2027 p2307 p2497 p3549 p3954 p5020 p5216 : Prop) (h : (¬ p2497) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p5020)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p5020) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial22903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5020)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12159 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7)
  exact rule22903 (meaning t m 2027) (meaning t m 2307) (meaning t m 2497) (meaning t m 3549) (meaning t m 3954) (meaning t m 5020) (meaning t m 5216) source

theorem rule22904 (p2027 p2254 p2657 p3073 p3266 p3449 p3742 p4831 p5503 : Prop) (h : (¬ p3073) ∨ (¬ p3742) ∨ (¬ p5503) ∨ (¬ p3266) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial22904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory12160 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule22904 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3073) (meaning t m 3266) (meaning t m 3449) (meaning t m 3742) (meaning t m 4831) (meaning t m 5503) source

theorem rule22907 (p2027 p2252 p2657 p2750 p3093 p3309 p3574 p3954 p3956 p4501 : Prop) (h : (¬ p2252) ∨ (¬ p3574) ∨ (¬ p2750) ∨ (¬ p3956) ∨ (¬ p3093) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3954) ∨ (¬ p4501)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory12163 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22907 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3093) (meaning t m 3309) (meaning t m 3574) (meaning t m 3954) (meaning t m 3956) (meaning t m 4501) source

theorem rule22911 (p2396 p2417 p4710 : Prop) (h : (¬ p4710) ∨ (¬ p2396) ∨ p2417) : (¬ p2396) ∨ (p2417) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial22911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (meaning t m 2417) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory12167 (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22911 (meaning t m 2396) (meaning t m 2417) (meaning t m 4710) source

theorem rule22912 (p2027 p2132 p2187 p2247 p2860 p3568 p4154 p4405 p4733 : Prop) (h : (¬ p2187) ∨ (¬ p3568) ∨ (¬ p2860) ∨ (¬ p4405) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p4154) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2860) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12168 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22912 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2247) (meaning t m 2860) (meaning t m 3568) (meaning t m 4154) (meaning t m 4405) (meaning t m 4733) source

theorem rule22916 (p2005 p2233 p2573 p5119 p5121 : Prop) (h : (¬ p2005) ∨ p2233 ∨ (¬ p2573) ∨ (¬ p5121) ∨ p5119) : (¬ p2005) ∨ (p2233) ∨ (¬ p2573) ∨ (p5119) ∨ (¬ p5121) := by
  classical
  tauto

theorem initial22916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 5119) ∨ (¬ (meaning t m 5121)) := by
  have source := ElevenTheory.theory12172 t (m.theta 0 4) (m.theta 4 6) (m.theta 8 10) (m.theta 9 10)
  exact rule22916 (meaning t m 2005) (meaning t m 2233) (meaning t m 2573) (meaning t m 5119) (meaning t m 5121) source

theorem rule22917 (p2027 p2396 p3063 p3817 p4105 p4405 : Prop) (h : p2027 ∨ (¬ p3817) ∨ (¬ p2396) ∨ (¬ p4405) ∨ (¬ p4105) ∨ (¬ p3063)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3063) ∨ (¬ p3817) ∨ (¬ p4105) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial22917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory12173 t (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule22917 (meaning t m 2027) (meaning t m 2396) (meaning t m 3063) (meaning t m 3817) (meaning t m 4105) (meaning t m 4405) source

theorem rule22921 (p1991 p2027 p2542 p2545 p2641 p2963 p3238 p3402 : Prop) (h : (¬ p1991) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p3402) ∨ (¬ p2641) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p3238) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial22921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory12177 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule22921 (meaning t m 1991) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2641) (meaning t m 2963) (meaning t m 3238) (meaning t m 3402) source

theorem rule22926 (p2027 p3355 p3540 p3690 p4451 p4647 : Prop) (h : p2027 ∨ (¬ p4647) ∨ (¬ p3540) ∨ (¬ p4451) ∨ (¬ p3690) ∨ (¬ p3355)) : (p2027) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3690) ∨ (¬ p4451) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial22926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory12182 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule22926 (meaning t m 2027) (meaning t m 3355) (meaning t m 3540) (meaning t m 3690) (meaning t m 4451) (meaning t m 4647) source

theorem rule22927 (p2027 p2608 p3527 p3551 p4793 p5206 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p3551) ∨ (¬ p4793) ∨ (¬ p5206) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4793) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial22927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4793)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory12183 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 7 8)
  exact rule22927 (meaning t m 2027) (meaning t m 2608) (meaning t m 3527) (meaning t m 3551) (meaning t m 4793) (meaning t m 5206) source

theorem rule22928 (p2027 p2156 p2274 p2396 p2608 p3370 p3548 p4366 p4377 p4668 : Prop) (h : (¬ p4668) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2274) ∨ (¬ p4377) ∨ (¬ p2156) ∨ (¬ p3370) ∨ (¬ p2608) ∨ (¬ p3548) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p3370) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4377) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12184 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22928 (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2608) (meaning t m 3370) (meaning t m 3548) (meaning t m 4366) (meaning t m 4377) (meaning t m 4668) source

theorem rule22929 (p2027 p2144 p3051 p3055 p4244 p4884 : Prop) (h : (¬ p4884) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p4244) ∨ (¬ p4884) := by
  classical
  tauto

theorem initial22929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4884)) := by
  have source := ElevenTheory.theory12185 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule22929 (meaning t m 2027) (meaning t m 2144) (meaning t m 3051) (meaning t m 3055) (meaning t m 4244) (meaning t m 4884) source

end SunPrize.SMT
