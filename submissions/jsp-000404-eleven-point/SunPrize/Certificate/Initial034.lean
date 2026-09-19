import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory018
import SunPrize.Certificate.Theory019
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule16129 (p1990 p2027 p2313 p2383 p3309 p3818 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p1990) ∨ (¬ p3309) ∨ p2027 ∨ p3818 ∨ (¬ p2383) ∨ (¬ p2313)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3309) ∨ (p3818) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial16129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3309)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory5449 t (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16129 (meaning t m 1990) (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3309) (meaning t m 3818) (meaning t m 3989) source

theorem rule16130 (p1988 p2027 p2166 p2873 p3115 p3497 p3680 : Prop) (h : (¬ p2166) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3497) ∨ p2873 ∨ (¬ p3115) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2166) ∨ (p2873) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial16130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory5450 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 9 10)
  exact rule16130 (meaning t m 1988) (meaning t m 2027) (meaning t m 2166) (meaning t m 2873) (meaning t m 3115) (meaning t m 3497) (meaning t m 3680) source

theorem rule16131 (p1998 p2027 p2114 p2264 p2685 p2749 p2952 p2992 p3361 : Prop) (h : p2027 ∨ (¬ p1998) ∨ p2114 ∨ (¬ p2952) ∨ (¬ p2264) ∨ (¬ p2992) ∨ (¬ p2685) ∨ (¬ p3361) ∨ (¬ p2749)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial16131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory5451 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule16131 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2264) (meaning t m 2685) (meaning t m 2749) (meaning t m 2952) (meaning t m 2992) (meaning t m 3361) source

theorem rule16132 (p1984 p2027 p2177 p2462 p3548 p4107 p4366 : Prop) (h : (¬ p1984) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p4107) ∨ p2462 ∨ (¬ p2177)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3548) ∨ (¬ p4107) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5452 t (m.theta 0 1) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16132 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3548) (meaning t m 4107) (meaning t m 4366) source

theorem rule16133 (p1984 p2027 p2459 p2509 p2534 p2633 p3452 : Prop) (h : (¬ p3452) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p1984) ∨ p2633) : (¬ p1984) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial16133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory5453 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16133 (meaning t m 1984) (meaning t m 2027) (meaning t m 2459) (meaning t m 2509) (meaning t m 2534) (meaning t m 2633) (meaning t m 3452) source

theorem rule16134 (p1987 p2027 p2651 p2688 p2810 p2952 p2992 : Prop) (h : p2688 ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2952) ∨ (¬ p2810) ∨ (¬ p2651)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (p2688) ∨ (¬ p2810) ∨ (¬ p2952) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial16134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory5454 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule16134 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2688) (meaning t m 2810) (meaning t m 2952) (meaning t m 2992) source

theorem rule16135 (p2001 p2027 p2114 p2132 p2619 p2737 p3365 : Prop) (h : (¬ p2132) ∨ (¬ p2001) ∨ p2027 ∨ p2114 ∨ (¬ p3365) ∨ (¬ p2737) ∨ (¬ p2619)) : (¬ p2001) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2737) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial16135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory5455 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8)
  exact rule16135 (meaning t m 2001) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2619) (meaning t m 2737) (meaning t m 3365) source

theorem rule16136 (p1993 p2027 p2553 p3008 p3073 p3549 p4118 p4317 : Prop) (h : (¬ p3549) ∨ (¬ p1993) ∨ (¬ p2553) ∨ (¬ p4317) ∨ (¬ p3073) ∨ (¬ p4118) ∨ p2027 ∨ p3008) : (¬ p1993) ∨ (p2027) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3073) ∨ (¬ p3549) ∨ (¬ p4118) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial16136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory5456 t (m.theta 1 6) (m.theta 1 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 8 9)
  exact rule16136 (meaning t m 1993) (meaning t m 2027) (meaning t m 2553) (meaning t m 3008) (meaning t m 3073) (meaning t m 3549) (meaning t m 4118) (meaning t m 4317) source

theorem rule16138 (p1991 p2027 p2352 p2657 p2727 p3008 p4360 p4769 : Prop) (h : (¬ p2352) ∨ (¬ p2657) ∨ (¬ p4360) ∨ (¬ p4769) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p1991) ∨ p3008) : (¬ p1991) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (p3008) ∨ (¬ p4360) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial16138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory5458 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule16138 (meaning t m 1991) (meaning t m 2027) (meaning t m 2352) (meaning t m 2657) (meaning t m 2727) (meaning t m 3008) (meaning t m 4360) (meaning t m 4769) source

theorem rule16140 (p1984 p2027 p2247 p2622 p2743 p2839 p3662 p5051 : Prop) (h : (¬ p2839) ∨ p2622 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p2743) ∨ (¬ p5051) ∨ (¬ p3662)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3662) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial16140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory5460 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule16140 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3662) (meaning t m 5051) source

theorem rule16143 (p1998 p2027 p2388 p3189 p3256 p3662 p4348 : Prop) (h : (¬ p1998) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p3256) ∨ (¬ p3189) ∨ p2388) : (¬ p1998) ∨ (p2027) ∨ (p2388) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3662) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5463 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16143 (meaning t m 1998) (meaning t m 2027) (meaning t m 2388) (meaning t m 3189) (meaning t m 3256) (meaning t m 3662) (meaning t m 4348) source

theorem rule16144 (p3461 p4331 p5126 p5127 : Prop) (h : (¬ p5127) ∨ (¬ p5126) ∨ (¬ p4331) ∨ (¬ p3461)) : (¬ p3461) ∨ (¬ p4331) ∨ (¬ p5126) ∨ (¬ p5127) := by
  classical
  tauto

theorem initial16144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 5126)) ∨ (¬ (meaning t m 5127)) := by
  have source := ElevenTheory.theory5464 (m.theta 4 10) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule16144 (meaning t m 3461) (meaning t m 4331) (meaning t m 5126) (meaning t m 5127) source

theorem rule16146 (p1985 p2027 p2388 p2641 p2870 p3662 p3758 p3986 : Prop) (h : p2027 ∨ (¬ p3758) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p1985) ∨ (¬ p3986) ∨ (¬ p3662) ∨ p2388) : (¬ p1985) ∨ (p2027) ∨ (p2388) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p3662) ∨ (¬ p3758) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial16146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory5466 t (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule16146 (meaning t m 1985) (meaning t m 2027) (meaning t m 2388) (meaning t m 2641) (meaning t m 2870) (meaning t m 3662) (meaning t m 3758) (meaning t m 3986) source

theorem rule16149 (p1994 p2027 p2388 p2630 p2807 p2952 p3572 : Prop) (h : (¬ p2952) ∨ (¬ p1994) ∨ p2388 ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3572) ∨ (¬ p2807)) : (¬ p1994) ∨ (p2027) ∨ (p2388) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial16149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory5469 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule16149 (meaning t m 1994) (meaning t m 2027) (meaning t m 2388) (meaning t m 2630) (meaning t m 2807) (meaning t m 2952) (meaning t m 3572) source

theorem rule16150 (p1984 p2027 p2247 p2388 p2630 p4111 p4315 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p1984) ∨ p2388 ∨ (¬ p4111) ∨ (¬ p4315) ∨ (¬ p2630)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2388) ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5470 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule16150 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2388) (meaning t m 2630) (meaning t m 4111) (meaning t m 4315) source

theorem rule16154 (p1984 p2027 p2764 p3585 p3954 p4425 p5160 : Prop) (h : (¬ p1984) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p3954) ∨ p2764 ∨ (¬ p3585) ∨ (¬ p5160)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial16154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory5474 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 9 10)
  exact rule16154 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3585) (meaning t m 3954) (meaning t m 4425) (meaning t m 5160) source

theorem rule16155 (p2427 p2553 p3660 p4275 : Prop) (h : (¬ p4275) ∨ (¬ p2553) ∨ (¬ p3660) ∨ p2427) : (p2427) ∨ (¬ p2553) ∨ (¬ p3660) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial16155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory5475 (m.theta 4 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7)
  exact rule16155 (meaning t m 2427) (meaning t m 2553) (meaning t m 3660) (meaning t m 4275) source

theorem rule16156 (p3591 p4105 p4366 : Prop) (h : (¬ p4105) ∨ (¬ p3591) ∨ p4366) : (¬ p3591) ∨ (¬ p4105) ∨ (p4366) := by
  classical
  tauto

theorem initial16156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4105)) ∨ (meaning t m 4366) := by
  have source := ElevenTheory.theory5476 (m.theta 0 1) (m.theta 1 6) (m.theta 1 7)
  exact rule16156 (meaning t m 3591) (meaning t m 4105) (meaning t m 4366) source

theorem rule16157 (p1982 p2027 p2459 p2688 p2881 p2901 p2992 : Prop) (h : (¬ p1982) ∨ p2688 ∨ (¬ p2459) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2881)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial16157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory5477 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16157 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2688) (meaning t m 2881) (meaning t m 2901) (meaning t m 2992) source

theorem rule16158 (p1988 p2027 p2688 p2761 p2901 p2992 p3246 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2901) ∨ p2688 ∨ (¬ p2992) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (p2688) ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial16158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory5478 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16158 (meaning t m 1988) (meaning t m 2027) (meaning t m 2688) (meaning t m 2761) (meaning t m 2901) (meaning t m 2992) (meaning t m 3246) source

theorem rule16160 (p1984 p2027 p2247 p2553 p3008 p3568 p4111 p4194 : Prop) (h : (¬ p4194) ∨ (¬ p1984) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3568) ∨ p3008 ∨ (¬ p2247)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p4111) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial16160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory5480 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule16160 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2553) (meaning t m 3008) (meaning t m 3568) (meaning t m 4111) (meaning t m 4194) source

theorem rule16161 (p1982 p2027 p2132 p2459 p2611 p2870 p2881 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ p2611 ∨ (¬ p2132) ∨ (¬ p2881) ∨ (¬ p2870)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2459) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial16161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory5481 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16161 (meaning t m 1982) (meaning t m 2027) (meaning t m 2132) (meaning t m 2459) (meaning t m 2611) (meaning t m 2870) (meaning t m 2881) source

theorem rule16163 (p1982 p2027 p2138 p2459 p2717 p3471 p3474 : Prop) (h : p3474 ∨ (¬ p2717) ∨ (¬ p1982) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2138)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (p3474) := by
  classical
  tauto

theorem initial16163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (meaning t m 3474) := by
  have source := ElevenTheory.theory5483 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16163 (meaning t m 1982) (meaning t m 2027) (meaning t m 2138) (meaning t m 2459) (meaning t m 2717) (meaning t m 3471) (meaning t m 3474) source

theorem rule16164 (p1998 p2027 p2114 p2138 p2717 p2839 p3471 : Prop) (h : p2027 ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p2839) ∨ (¬ p2138) ∨ p2114 ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2138) ∨ (¬ p2717) ∨ (¬ p2839) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial16164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory5484 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8)
  exact rule16164 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2138) (meaning t m 2717) (meaning t m 2839) (meaning t m 3471) source

theorem rule16169 (p1998 p2027 p2132 p2611 p2619 p3146 p4348 : Prop) (h : (¬ p4348) ∨ p2027 ∨ (¬ p1998) ∨ p2611 ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3146)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5489 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16169 (meaning t m 1998) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2619) (meaning t m 3146) (meaning t m 4348) source

theorem rule16170 (p1984 p2027 p2247 p2997 p3323 p3568 p4026 p4245 : Prop) (h : p2027 ∨ (¬ p3568) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4245) ∨ p2997 ∨ (¬ p2247) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2997) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4026) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial16170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory5490 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule16170 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2997) (meaning t m 3323) (meaning t m 3568) (meaning t m 4026) (meaning t m 4245) source

theorem rule16173 (p2295 p3309 p4319 : Prop) (h : (¬ p3309) ∨ (¬ p4319) ∨ p2295) : (p2295) ∨ (¬ p3309) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial16173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2295) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory5493 (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule16173 (meaning t m 2295) (meaning t m 3309) (meaning t m 4319) source

theorem rule16174 (p2022 p2027 p2264 p2388 p3027 p3551 p3662 : Prop) (h : (¬ p3551) ∨ (¬ p2022) ∨ p2027 ∨ (¬ p2264) ∨ p2388 ∨ (¬ p3662) ∨ (¬ p3027)) : (¬ p2022) ∨ (p2027) ∨ (¬ p2264) ∨ (p2388) ∨ (¬ p3027) ∨ (¬ p3551) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial16174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory5494 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule16174 (meaning t m 2022) (meaning t m 2027) (meaning t m 2264) (meaning t m 2388) (meaning t m 3027) (meaning t m 3551) (meaning t m 3662) source

theorem rule16177 (p1984 p2027 p2245 p2462 p2657 p2727 p2996 p3947 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p2996) ∨ (¬ p2727) ∨ (¬ p2657) ∨ (¬ p2245) ∨ p2462) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2462) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial16177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory5497 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule16177 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2462) (meaning t m 2657) (meaning t m 2727) (meaning t m 2996) (meaning t m 3947) source

theorem rule16179 (p1987 p2027 p2202 p2476 p2518 p2662 p2810 p3238 : Prop) (h : (¬ p1987) ∨ (¬ p3238) ∨ p2202 ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2518) ∨ (¬ p2476)) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial16179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory5499 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule16179 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2476) (meaning t m 2518) (meaning t m 2662) (meaning t m 2810) (meaning t m 3238) source

theorem rule16180 (p2000 p2027 p2476 p2497 p2518 p2553 p3008 p3549 : Prop) (h : (¬ p2000) ∨ (¬ p2497) ∨ p2027 ∨ p3008 ∨ (¬ p3549) ∨ (¬ p2553) ∨ (¬ p2476) ∨ (¬ p2518)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2497) ∨ (¬ p2518) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial16180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory5500 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule16180 (meaning t m 2000) (meaning t m 2027) (meaning t m 2476) (meaning t m 2497) (meaning t m 2518) (meaning t m 2553) (meaning t m 3008) (meaning t m 3549) source

theorem rule16181 (p1982 p2027 p2459 p2622 p2717 p3365 p3471 : Prop) (h : (¬ p2717) ∨ p2622 ∨ (¬ p3365) ∨ (¬ p1982) ∨ (¬ p3471) ∨ (¬ p2459) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2717) ∨ (¬ p3365) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial16181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory5501 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16181 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2622) (meaning t m 2717) (meaning t m 3365) (meaning t m 3471) source

theorem rule16182 (p1976 p2027 p2202 p2440 p2780 p2829 p3585 p4343 : Prop) (h : p2202 ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p2829)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial16182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory5502 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5)
  exact rule16182 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2780) (meaning t m 2829) (meaning t m 3585) (meaning t m 4343) source

theorem rule16184 (p2000 p2027 p2169 p2579 p3319 p3923 p4137 : Prop) (h : p2169 ∨ (¬ p2000) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2579) ∨ (¬ p3319) ∨ (¬ p3923)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2579) ∨ (¬ p3319) ∨ (¬ p3923) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial16184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory5504 t (m.theta 0 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule16184 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2579) (meaning t m 3319) (meaning t m 3923) (meaning t m 4137) source

theorem rule16185 (p1992 p2027 p2202 p2247 p2440 p2608 p4111 : Prop) (h : p2202 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4111) ∨ (¬ p2440) ∨ (¬ p1992) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2247) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial16185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory5505 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5)
  exact rule16185 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2247) (meaning t m 2440) (meaning t m 2608) (meaning t m 4111) source

theorem rule16186 (p1984 p2027 p2202 p2245 p2440 p2641 p2963 p4111 : Prop) (h : (¬ p1984) ∨ (¬ p4111) ∨ (¬ p2641) ∨ p2202 ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2245) ∨ (¬ p2963)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2245) ∨ (¬ p2440) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial16186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory5506 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule16186 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2245) (meaning t m 2440) (meaning t m 2641) (meaning t m 2963) (meaning t m 4111) source

theorem rule16188 (p1984 p2027 p2245 p2657 p2914 p2928 p3222 p3359 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3222) ∨ (¬ p3359) ∨ (¬ p2657) ∨ p2914 ∨ (¬ p2245) ∨ (¬ p2928)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (p2914) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p3359) := by
  classical
  tauto

theorem initial16188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3359)) := by
  have source := ElevenTheory.theory5508 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule16188 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2914) (meaning t m 2928) (meaning t m 3222) (meaning t m 3359) source

theorem rule16189 (p1984 p2027 p2247 p3982 p4111 p4256 p4286 : Prop) (h : p3982 ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p4286) ∨ (¬ p4256) ∨ (¬ p4111) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p3982) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial16189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory5509 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 10)
  exact rule16189 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3982) (meaning t m 4111) (meaning t m 4256) (meaning t m 4286) source

theorem rule16190 (p1988 p2027 p2761 p2765 p3051 p3246 p3646 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p3051) ∨ (¬ p1988) ∨ (¬ p3646)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2761) ∨ (p2765) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial16190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory5510 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16190 (meaning t m 1988) (meaning t m 2027) (meaning t m 2761) (meaning t m 2765) (meaning t m 3051) (meaning t m 3246) (meaning t m 3646) source

theorem rule16191 (p1999 p2027 p3125 p3498 p3989 p4149 p5580 : Prop) (h : (¬ p1999) ∨ (¬ p3125) ∨ (¬ p5580) ∨ (¬ p4149) ∨ p3498 ∨ (¬ p3989) ∨ p2027) : (¬ p1999) ∨ (p2027) ∨ (¬ p3125) ∨ (p3498) ∨ (¬ p3989) ∨ (¬ p4149) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial16191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3125)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory5511 t (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule16191 (meaning t m 1999) (meaning t m 2027) (meaning t m 3125) (meaning t m 3498) (meaning t m 3989) (meaning t m 4149) (meaning t m 5580) source

theorem rule16193 (p1982 p2027 p2187 p2307 p2344 p2459 p3097 p3550 : Prop) (h : (¬ p1982) ∨ p2344 ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p2187)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (p2344) ∨ (¬ p2459) ∨ (¬ p3097) ∨ (¬ p3550) := by
  classical
  tauto

theorem initial16193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3550)) := by
  have source := ElevenTheory.theory5513 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16193 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2344) (meaning t m 2459) (meaning t m 3097) (meaning t m 3550) source

theorem rule16194 (p1984 p2027 p3008 p3452 p3574 p3807 p3901 : Prop) (h : (¬ p1984) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p3901) ∨ (¬ p3807) ∨ p3008 ∨ (¬ p3574)) : (¬ p1984) ∨ (p2027) ∨ (p3008) ∨ (¬ p3452) ∨ (¬ p3574) ∨ (¬ p3807) ∨ (¬ p3901) := by
  classical
  tauto

theorem initial16194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3807)) ∨ (¬ (meaning t m 3901)) := by
  have source := ElevenTheory.theory5514 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 10) (m.theta 4 6)
  exact rule16194 (meaning t m 1984) (meaning t m 2027) (meaning t m 3008) (meaning t m 3452) (meaning t m 3574) (meaning t m 3807) (meaning t m 3901) source

theorem rule16195 (p1999 p2027 p2737 p2797 p3323 p3586 p3688 : Prop) (h : (¬ p1999) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p3688) ∨ p3586) : (¬ p1999) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (p3586) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial16195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory5515 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule16195 (meaning t m 1999) (meaning t m 2027) (meaning t m 2737) (meaning t m 2797) (meaning t m 3323) (meaning t m 3586) (meaning t m 3688) source

theorem rule16199 (p1982 p2027 p2341 p2363 p3360 p3941 p5580 : Prop) (h : (¬ p2341) ∨ (¬ p5580) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ p3360 ∨ (¬ p3941)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2363) ∨ (p3360) ∨ (¬ p3941) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial16199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory5519 t (m.theta 0 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule16199 (meaning t m 1982) (meaning t m 2027) (meaning t m 2341) (meaning t m 2363) (meaning t m 3360) (meaning t m 3941) (meaning t m 5580) source

theorem rule16204 (p2011 p2997 p3097 p5046 : Prop) (h : (¬ p3097) ∨ p2997 ∨ p5046 ∨ (¬ p2011)) : (¬ p2011) ∨ (p2997) ∨ (¬ p3097) ∨ (p5046) := by
  classical
  tauto

theorem initial16204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 5046) := by
  have source := ElevenTheory.theory5524 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule16204 (meaning t m 2011) (meaning t m 2997) (meaning t m 3097) (meaning t m 5046) source

theorem rule16207 (p1983 p2027 p2114 p2274 p2396 p2839 p2860 : Prop) (h : (¬ p2396) ∨ p2114 ∨ (¬ p2860) ∨ (¬ p2274) ∨ (¬ p1983) ∨ (¬ p2839) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2839) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial16207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory5527 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16207 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2274) (meaning t m 2396) (meaning t m 2839) (meaning t m 2860) source

theorem rule16208 (p2000 p2027 p2911 p2914 p2926 p3222 p3346 p3548 : Prop) (h : (¬ p2926) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p2000) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p3346) ∨ (¬ p3222)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p2926) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial16208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory5528 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8)
  exact rule16208 (meaning t m 2000) (meaning t m 2027) (meaning t m 2911) (meaning t m 2914) (meaning t m 2926) (meaning t m 3222) (meaning t m 3346) (meaning t m 3548) source

theorem rule16210 (p1984 p2027 p2169 p2363 p3688 p3954 p4078 p4340 : Prop) (h : (¬ p2363) ∨ (¬ p1984) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p4078) ∨ (¬ p3954) ∨ p2169 ∨ (¬ p3688)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4078) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial16210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory5530 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16210 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 3688) (meaning t m 3954) (meaning t m 4078) (meaning t m 4340) source

theorem rule16213 (p1992 p2027 p2247 p2608 p3128 p4037 p4154 : Prop) (h : (¬ p4037) ∨ (¬ p1992) ∨ (¬ p4154) ∨ (¬ p2247) ∨ p3128 ∨ (¬ p2608) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p3128) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5533 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9)
  exact rule16213 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 3128) (meaning t m 4037) (meaning t m 4154) source

theorem rule16218 (p2006 p3437 p4244 p4898 : Prop) (h : (¬ p4244) ∨ (¬ p2006) ∨ p3437 ∨ p4898) : (¬ p2006) ∨ (p3437) ∨ (¬ p4244) ∨ (p4898) := by
  classical
  tauto

theorem initial16218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 4244)) ∨ (meaning t m 4898) := by
  have source := ElevenTheory.theory5538 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule16218 (meaning t m 2006) (meaning t m 3437) (meaning t m 4244) (meaning t m 4898) source

theorem rule16221 (p1991 p2027 p2657 p2766 p3644 p3742 p4348 : Prop) (h : (¬ p3644) ∨ (¬ p1991) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3742) ∨ p2766 ∨ (¬ p4348)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5541 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16221 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2766) (meaning t m 3644) (meaning t m 3742) (meaning t m 4348) source

theorem rule16223 (p1991 p2027 p2169 p2553 p2963 p3568 p3956 : Prop) (h : (¬ p1991) ∨ (¬ p2553) ∨ (¬ p3568) ∨ (¬ p2963) ∨ (¬ p3956) ∨ p2169 ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2553) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial16223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory5543 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16223 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2553) (meaning t m 2963) (meaning t m 3568) (meaning t m 3956) source

theorem rule16224 (p2000 p2027 p2295 p2313 p2577 p2764 p4037 p4191 : Prop) (h : (¬ p2313) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p2577) ∨ (¬ p2295) ∨ p2764 ∨ (¬ p4037)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (p2764) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5544 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule16224 (meaning t m 2000) (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2577) (meaning t m 2764) (meaning t m 4037) (meaning t m 4191) source

theorem rule16225 (p2000 p2027 p2202 p2295 p2313 p2373 p2577 p3497 p4336 : Prop) (h : (¬ p2313) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p2577) ∨ (¬ p2373) ∨ p2202 ∨ (¬ p2295) ∨ (¬ p4336) ∨ (¬ p3497)) : (¬ p2000) ∨ (p2027) ∨ (p2202) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2577) ∨ (¬ p3497) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial16225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory5545 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7)
  exact rule16225 (meaning t m 2000) (meaning t m 2027) (meaning t m 2202) (meaning t m 2295) (meaning t m 2313) (meaning t m 2373) (meaning t m 2577) (meaning t m 3497) (meaning t m 4336) source

theorem rule16226 (p1987 p2027 p2138 p2388 p2737 p3156 p3366 p3694 : Prop) (h : (¬ p3366) ∨ p2388 ∨ (¬ p2138) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p3156) ∨ (¬ p3694)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (p2388) ∨ (¬ p2737) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial16226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory5546 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule16226 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2388) (meaning t m 2737) (meaning t m 3156) (meaning t m 3366) (meaning t m 3694) source

theorem rule16228 (p1987 p2027 p2633 p2737 p3363 p3540 p3585 p3644 : Prop) (h : p2633 ∨ (¬ p3644) ∨ (¬ p3585) ∨ (¬ p2737) ∨ (¬ p3363) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p3540)) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial16228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory5548 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule16228 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2737) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 3644) source

theorem rule16233 (p1999 p2027 p2169 p2313 p2553 p3654 p3956 : Prop) (h : (¬ p3956) ∨ p2169 ∨ p2027 ∨ (¬ p2553) ∨ (¬ p1999) ∨ (¬ p2313) ∨ (¬ p3654)) : (¬ p1999) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3654) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial16233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory5553 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule16233 (meaning t m 1999) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2553) (meaning t m 3654) (meaning t m 3956) source

theorem rule16238 (p1990 p2027 p2284 p2608 p2699 p2737 p3136 : Prop) (h : p2699 ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial16238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory5558 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule16238 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2608) (meaning t m 2699) (meaning t m 2737) (meaning t m 3136) source

theorem rule16240 (p1992 p2027 p2459 p2534 p2633 p3363 p3540 p3585 p4186 : Prop) (h : p2027 ∨ (¬ p1992) ∨ (¬ p3540) ∨ (¬ p3363) ∨ p2633 ∨ (¬ p3585) ∨ (¬ p4186) ∨ (¬ p2459) ∨ (¬ p2534)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial16240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory5560 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16240 (meaning t m 1992) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 4186) source

theorem rule16246 (p1991 p2355 p2657 p4650 : Prop) (h : (¬ p1991) ∨ (¬ p2657) ∨ p2355 ∨ p4650) : (¬ p1991) ∨ (p2355) ∨ (¬ p2657) ∨ (p4650) := by
  classical
  tauto

theorem initial16246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 4650) := by
  have source := ElevenTheory.theory5566 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7)
  exact rule16246 (meaning t m 1991) (meaning t m 2355) (meaning t m 2657) (meaning t m 4650) source

theorem rule16247 (p1990 p2563 p3498 p4608 : Prop) (h : p4608 ∨ (¬ p2563) ∨ (¬ p1990) ∨ p3498) : (¬ p1990) ∨ (¬ p2563) ∨ (p3498) ∨ (p4608) := by
  classical
  tauto

theorem initial16247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3498) ∨ (meaning t m 4608) := by
  have source := ElevenTheory.theory5567 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule16247 (meaning t m 1990) (meaning t m 2563) (meaning t m 3498) (meaning t m 4608) source

theorem rule16251 (p1992 p2027 p2476 p2655 p2743 p2914 p3083 p3361 p3742 : Prop) (h : (¬ p1992) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p2476) ∨ p2914 ∨ (¬ p3742) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3083)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p2743) ∨ (p2914) ∨ (¬ p3083) ∨ (¬ p3361) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial16251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory5571 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule16251 (meaning t m 1992) (meaning t m 2027) (meaning t m 2476) (meaning t m 2655) (meaning t m 2743) (meaning t m 2914) (meaning t m 3083) (meaning t m 3361) (meaning t m 3742) source

theorem rule16252 (p1990 p2027 p2144 p2220 p2252 p2462 p2657 p2750 p2753 p2761 p2860 p3694 p3742 p4425 p4635 : Prop) (h : (¬ p2657) ∨ p2462 ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3694) ∨ (¬ p2144) ∨ (¬ p2860) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p1990) ∨ (¬ p2220) ∨ (¬ p4635) ∨ (¬ p4425) ∨ (¬ p2761)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (p2462) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p3742) ∨ (¬ p4425) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial16252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2252)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory5572 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9) (m.theta 9 10)
  exact rule16252 (meaning t m 1990) (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2252) (meaning t m 2462) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2761) (meaning t m 2860) (meaning t m 3694) (meaning t m 3742) (meaning t m 4425) (meaning t m 4635) source

theorem rule16253 (p1990 p2027 p2144 p2220 p2252 p2657 p2750 p2753 p2764 p2860 p3694 p3742 p4278 p4381 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p2860) ∨ (¬ p2753) ∨ (¬ p4278) ∨ (¬ p3742) ∨ (¬ p1990) ∨ (¬ p2657) ∨ (¬ p2220) ∨ (¬ p3694) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p4381)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (p2764) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory5573 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9) (m.theta 9 10)
  exact rule16253 (meaning t m 1990) (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2764) (meaning t m 2860) (meaning t m 3694) (meaning t m 3742) (meaning t m 4278) (meaning t m 4381) source

theorem rule16261 (p2000 p2027 p2459 p2589 p2633 p3692 p3880 : Prop) (h : (¬ p3692) ∨ (¬ p2459) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p2589) ∨ p2633) : (¬ p2000) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial16261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory5581 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16261 (meaning t m 2000) (meaning t m 2027) (meaning t m 2459) (meaning t m 2589) (meaning t m 2633) (meaning t m 3692) (meaning t m 3880) source

theorem rule16262 (p2006 p2027 p2295 p3097 p3128 p3758 p4037 : Prop) (h : (¬ p4037) ∨ (¬ p2295) ∨ (¬ p2006) ∨ p2027 ∨ p3128 ∨ (¬ p3758) ∨ (¬ p3097)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p3097) ∨ (p3128) ∨ (¬ p3758) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial16262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3097)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5582 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule16262 (meaning t m 2006) (meaning t m 2027) (meaning t m 2295) (meaning t m 3097) (meaning t m 3128) (meaning t m 3758) (meaning t m 4037) source

theorem rule16264 (p1990 p3128 p4037 p4560 : Prop) (h : (¬ p4037) ∨ (¬ p1990) ∨ p3128 ∨ p4560) : (¬ p1990) ∨ (p3128) ∨ (¬ p4037) ∨ (p4560) := by
  classical
  tauto

theorem initial16264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4037)) ∨ (meaning t m 4560) := by
  have source := ElevenTheory.theory5584 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule16264 (meaning t m 1990) (meaning t m 3128) (meaning t m 4037) (meaning t m 4560) source

theorem rule16267 (p1990 p2027 p2220 p2860 p3043 p3694 p4032 : Prop) (h : p3043 ∨ (¬ p3694) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2220) ∨ (¬ p4032)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2860) ∨ (p3043) ∨ (¬ p3694) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial16267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory5587 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 5 9)
  exact rule16267 (meaning t m 1990) (meaning t m 2027) (meaning t m 2220) (meaning t m 2860) (meaning t m 3043) (meaning t m 3694) (meaning t m 4032) source

theorem rule16268 (p1975 p2027 p2114 p2553 p3379 p3422 p3954 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p3422) ∨ (¬ p3954) ∨ (¬ p3379) ∨ (¬ p2553) ∨ p2114 ∨ (¬ p1975) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2553) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3954) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial16268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory5588 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule16268 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2553) (meaning t m 3379) (meaning t m 3422) (meaning t m 3954) (meaning t m 4030) source

theorem rule16272 (p1979 p2027 p2355 p2630 p2657 p2946 p3572 : Prop) (h : p2355 ∨ (¬ p2630) ∨ (¬ p2946) ∨ (¬ p3572) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (p2355) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial16272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory5592 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule16272 (meaning t m 1979) (meaning t m 2027) (meaning t m 2355) (meaning t m 2630) (meaning t m 2657) (meaning t m 2946) (meaning t m 3572) source

theorem rule16273 (p1976 p2027 p3043 p3055 p3237 p3680 p3684 p4425 : Prop) (h : (¬ p3055) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3237) ∨ (¬ p3684) ∨ p3043 ∨ (¬ p4425) ∨ (¬ p3680)) : (¬ p1976) ∨ (p2027) ∨ (p3043) ∨ (¬ p3055) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p3684) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial16273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory5593 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule16273 (meaning t m 1976) (meaning t m 2027) (meaning t m 3043) (meaning t m 3055) (meaning t m 3237) (meaning t m 3680) (meaning t m 3684) (meaning t m 4425) source

theorem rule16274 (p1978 p2132 p2140 p2611 : Prop) (h : (¬ p1978) ∨ p2140 ∨ (¬ p2132) ∨ p2611) : (¬ p1978) ∨ (¬ p2132) ∨ (p2140) ∨ (p2611) := by
  classical
  tauto

theorem initial16274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2140) ∨ (meaning t m 2611) := by
  have source := ElevenTheory.theory5594 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule16274 (meaning t m 1978) (meaning t m 2132) (meaning t m 2140) (meaning t m 2611) source

theorem rule16275 (p2000 p2027 p2589 p2914 p3115 p3413 p3742 p4948 : Prop) (h : (¬ p2000) ∨ p2914 ∨ (¬ p3742) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3413) ∨ (¬ p3115) ∨ (¬ p4948)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2589) ∨ (p2914) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p3742) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5595 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 9)
  exact rule16275 (meaning t m 2000) (meaning t m 2027) (meaning t m 2589) (meaning t m 2914) (meaning t m 3115) (meaning t m 3413) (meaning t m 3742) (meaning t m 4948) source

theorem rule16277 (p2000 p2027 p2427 p2766 p3556 p3692 p3880 p3904 : Prop) (h : p2766 ∨ (¬ p2000) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2427)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2427) ∨ (p2766) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial16277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory5597 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule16277 (meaning t m 2000) (meaning t m 2027) (meaning t m 2427) (meaning t m 2766) (meaning t m 3556) (meaning t m 3692) (meaning t m 3880) (meaning t m 3904) source

theorem rule16278 (p1978 p3008 p3646 p4718 : Prop) (h : p3008 ∨ (¬ p1978) ∨ p4718 ∨ (¬ p3646)) : (¬ p1978) ∨ (p3008) ∨ (¬ p3646) ∨ (p4718) := by
  classical
  tauto

theorem initial16278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3646)) ∨ (meaning t m 4718) := by
  have source := ElevenTheory.theory5598 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6)
  exact rule16278 (meaning t m 1978) (meaning t m 3008) (meaning t m 3646) (meaning t m 4718) source

theorem rule16279 (p2007 p2027 p2114 p2138 p2598 p2839 p3641 : Prop) (h : (¬ p3641) ∨ (¬ p2007) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2839) ∨ p2114) : (¬ p2007) ∨ (p2027) ∨ (p2114) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial16279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory5599 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8)
  exact rule16279 (meaning t m 2007) (meaning t m 2027) (meaning t m 2114) (meaning t m 2138) (meaning t m 2598) (meaning t m 2839) (meaning t m 3641) source

theorem rule16281 (p4425 p4952 p5402 p5403 : Prop) (h : (¬ p4952) ∨ (¬ p5402) ∨ (¬ p5403) ∨ (¬ p4425)) : (¬ p4425) ∨ (¬ p4952) ∨ (¬ p5402) ∨ (¬ p5403) := by
  classical
  tauto

theorem initial16281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4952)) ∨ (¬ (meaning t m 5402)) ∨ (¬ (meaning t m 5403)) := by
  have source := ElevenTheory.theory5601 (m.theta 4 9) (m.theta 5 10) (m.theta 5 9) (m.theta 9 10)
  exact rule16281 (meaning t m 4425) (meaning t m 4952) (meaning t m 5402) (meaning t m 5403) source

theorem rule16283 (p1986 p2027 p3063 p3128 p3584 p3956 p4037 p4319 : Prop) (h : (¬ p4037) ∨ p3128 ∨ (¬ p3956) ∨ (¬ p3584) ∨ (¬ p1986) ∨ (¬ p4319) ∨ p2027 ∨ (¬ p3063)) : (¬ p1986) ∨ (p2027) ∨ (¬ p3063) ∨ (p3128) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4037) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial16283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory5603 t (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule16283 (meaning t m 1986) (meaning t m 2027) (meaning t m 3063) (meaning t m 3128) (meaning t m 3584) (meaning t m 3956) (meaning t m 4037) (meaning t m 4319) source

theorem rule16286 (p1984 p2027 p2247 p3498 p3506 p3846 p4256 p4321 p5176 : Prop) (h : (¬ p1984) ∨ p3498 ∨ (¬ p4256) ∨ p2027 ∨ (¬ p4321) ∨ (¬ p3846) ∨ (¬ p3506) ∨ (¬ p5176) ∨ (¬ p2247)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p3498) ∨ (¬ p3506) ∨ (¬ p3846) ∨ (¬ p4256) ∨ (¬ p4321) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial16286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3846)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory5606 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 3 9) (m.theta 4 8) (m.theta 9 10)
  exact rule16286 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3498) (meaning t m 3506) (meaning t m 3846) (meaning t m 4256) (meaning t m 4321) (meaning t m 5176) source

theorem rule16289 (p1991 p2963 p3008 p4973 : Prop) (h : (¬ p1991) ∨ p3008 ∨ p4973 ∨ (¬ p2963)) : (¬ p1991) ∨ (¬ p2963) ∨ (p3008) ∨ (p4973) := by
  classical
  tauto

theorem initial16289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3008) ∨ (meaning t m 4973) := by
  have source := ElevenTheory.theory5609 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6)
  exact rule16289 (meaning t m 1991) (meaning t m 2963) (meaning t m 3008) (meaning t m 4973) source

theorem rule16291 (p1975 p2027 p2274 p2573 p2589 p2842 p2850 p4203 : Prop) (h : (¬ p1975) ∨ p2027 ∨ (¬ p4203) ∨ p2842 ∨ (¬ p2850) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial16291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory5611 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16291 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2573) (meaning t m 2589) (meaning t m 2842) (meaning t m 2850) (meaning t m 4203) source

theorem rule16293 (p1992 p2027 p2462 p2657 p2743 p3361 p3742 p4278 : Prop) (h : (¬ p2657) ∨ (¬ p3742) ∨ p2462 ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p1992) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5613 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule16293 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2657) (meaning t m 2743) (meaning t m 3361) (meaning t m 3742) (meaning t m 4278) source

theorem rule16295 (p1977 p2027 p2241 p2462 p2761 p4321 p4366 p5357 : Prop) (h : (¬ p4366) ∨ (¬ p1977) ∨ (¬ p4321) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p5357) ∨ (¬ p2241) ∨ p2462) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p4321) ∨ (¬ p4366) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial16295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory5615 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule16295 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2462) (meaning t m 2761) (meaning t m 4321) (meaning t m 4366) (meaning t m 5357) source

theorem rule16296 (p1977 p2027 p2241 p2764 p3817 p4366 p4381 : Prop) (h : (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3817) ∨ p2764 ∨ (¬ p4366) ∨ (¬ p4381)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2764) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory5616 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16296 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2764) (meaning t m 3817) (meaning t m 4366) (meaning t m 4381) source

theorem rule16297 (p1977 p2027 p2241 p2462 p3452 p3742 p4116 p4278 : Prop) (h : (¬ p2241) ∨ (¬ p3742) ∨ p2462 ∨ (¬ p4278) ∨ p2027 ∨ (¬ p4116) ∨ (¬ p3452) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2462) ∨ (¬ p3452) ∨ (¬ p3742) ∨ (¬ p4116) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5617 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule16297 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2462) (meaning t m 3452) (meaning t m 3742) (meaning t m 4116) (meaning t m 4278) source

theorem rule16298 (p1987 p2027 p2459 p2633 p3497 p3692 p4315 : Prop) (h : (¬ p1987) ∨ p2633 ∨ (¬ p3497) ∨ (¬ p2459) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p3692)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5618 t (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16298 (meaning t m 1987) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3497) (meaning t m 3692) (meaning t m 4315) source

theorem rule16299 (p1995 p2027 p2169 p3379 p3555 p3989 p4173 : Prop) (h : p2169 ∨ (¬ p4173) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p3379) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (p2169) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial16299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory5619 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 6) (m.theta 6 8)
  exact rule16299 (meaning t m 1995) (meaning t m 2027) (meaning t m 2169) (meaning t m 3379) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) source

theorem rule16300 (p1995 p2027 p2427 p3043 p3369 p3379 p3556 p4948 : Prop) (h : (¬ p3369) ∨ (¬ p3379) ∨ (¬ p1995) ∨ (¬ p3556) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4948) ∨ p3043) : (¬ p1995) ∨ (p2027) ∨ (¬ p2427) ∨ (p3043) ∨ (¬ p3369) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5620 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule16300 (meaning t m 1995) (meaning t m 2027) (meaning t m 2427) (meaning t m 3043) (meaning t m 3369) (meaning t m 3379) (meaning t m 3556) (meaning t m 4948) source

theorem rule16307 (p1984 p2027 p2169 p3584 p3585 p3954 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p3585) ∨ (¬ p1984) ∨ p2169 ∨ p2027 ∨ (¬ p3584) ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial16307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory5627 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule16307 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 3584) (meaning t m 3585) (meaning t m 3954) (meaning t m 3956) source

theorem rule16308 (p1976 p2027 p2138 p3570 p3982 p4244 p5558 : Prop) (h : (¬ p1976) ∨ (¬ p2138) ∨ (¬ p4244) ∨ (¬ p3570) ∨ p2027 ∨ p3982 ∨ (¬ p5558)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p3570) ∨ (p3982) ∨ (¬ p4244) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial16308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3570)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory5628 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10)
  exact rule16308 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 3570) (meaning t m 3982) (meaning t m 4244) (meaning t m 5558) source

theorem rule16309 (p1976 p2027 p3055 p3128 p3461 p3584 p3746 p4425 : Prop) (h : (¬ p3584) ∨ (¬ p3055) ∨ p2027 ∨ p3128 ∨ (¬ p4425) ∨ (¬ p1976) ∨ (¬ p3746) ∨ (¬ p3461)) : (¬ p1976) ∨ (p2027) ∨ (¬ p3055) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p3584) ∨ (¬ p3746) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial16309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory5629 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule16309 (meaning t m 1976) (meaning t m 2027) (meaning t m 3055) (meaning t m 3128) (meaning t m 3461) (meaning t m 3584) (meaning t m 3746) (meaning t m 4425) source

theorem rule16310 (p2002 p2169 p3956 p5222 : Prop) (h : p2169 ∨ (¬ p3956) ∨ (¬ p2002) ∨ p5222) : (¬ p2002) ∨ (p2169) ∨ (¬ p3956) ∨ (p5222) := by
  classical
  tauto

theorem initial16310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3956)) ∨ (meaning t m 5222) := by
  have source := ElevenTheory.theory5630 t (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule16310 (meaning t m 2002) (meaning t m 2169) (meaning t m 3956) (meaning t m 5222) source

theorem rule16311 (p1991 p2027 p2187 p2657 p2765 p3574 p3956 : Prop) (h : (¬ p2657) ∨ p2765 ∨ (¬ p3956) ∨ (¬ p2187) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p3574)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2657) ∨ (p2765) ∨ (¬ p3574) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial16311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory5631 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule16311 (meaning t m 1991) (meaning t m 2027) (meaning t m 2187) (meaning t m 2657) (meaning t m 2765) (meaning t m 3574) (meaning t m 3956) source

theorem rule16318 (p1991 p2027 p2462 p2657 p2761 p3742 p4425 p4635 : Prop) (h : (¬ p3742) ∨ (¬ p1991) ∨ (¬ p4635) ∨ p2462 ∨ (¬ p2761) ∨ (¬ p2657) ∨ (¬ p4425) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (p2462) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3742) ∨ (¬ p4425) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial16318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory5638 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule16318 (meaning t m 1991) (meaning t m 2027) (meaning t m 2462) (meaning t m 2657) (meaning t m 2761) (meaning t m 3742) (meaning t m 4425) (meaning t m 4635) source

theorem rule16319 (p1991 p2027 p2657 p2764 p3742 p4278 p4381 : Prop) (h : (¬ p3742) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2657) ∨ (¬ p1991) ∨ p2764) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory5639 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16319 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2764) (meaning t m 3742) (meaning t m 4278) (meaning t m 4381) source

theorem rule16320 (p1981 p2027 p2187 p2307 p2688 p2951 p2962 p2992 p3097 : Prop) (h : p2688 ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2187) ∨ (¬ p2951) ∨ (¬ p3097) ∨ (¬ p2962) ∨ (¬ p2307)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2992) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial16320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory5640 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16320 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2688) (meaning t m 2951) (meaning t m 2962) (meaning t m 2992) (meaning t m 3097) source

theorem rule16322 (p2027 p2504 p2505 p2579 p3238 p3389 p4646 : Prop) (h : (¬ p2504) ∨ (¬ p3389) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4646)) : (p2027) ∨ (¬ p2504) ∨ (¬ p2505) ∨ (¬ p2579) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial16322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory5642 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule16322 (meaning t m 2027) (meaning t m 2504) (meaning t m 2505) (meaning t m 2579) (meaning t m 3238) (meaning t m 3389) (meaning t m 4646) source

theorem rule16325 (p1988 p2027 p2202 p2417 p2440 p2656 p2761 p3389 : Prop) (h : (¬ p2440) ∨ p2202 ∨ (¬ p2656) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p2417)) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2440) ∨ (¬ p2656) ∨ (¬ p2761) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial16325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory5645 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16325 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2440) (meaning t m 2656) (meaning t m 2761) (meaning t m 3389) source

theorem rule16326 (p2000 p2027 p2542 p2545 p2922 p3238 p3540 : Prop) (h : (¬ p2542) ∨ (¬ p2000) ∨ p2027 ∨ (¬ p3238) ∨ p2545 ∨ (¬ p3540) ∨ (¬ p2922)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial16326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory5646 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule16326 (meaning t m 2000) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2922) (meaning t m 3238) (meaning t m 3540) source

theorem rule16328 (p1984 p2027 p2202 p2440 p2743 p2810 p3954 : Prop) (h : (¬ p2810) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p1984) ∨ p2202 ∨ (¬ p2743) ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5648 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule16328 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2743) (meaning t m 2810) (meaning t m 3954) source

theorem rule16330 (p1981 p2027 p2352 p2766 p3266 p4137 p4191 : Prop) (h : (¬ p2352) ∨ (¬ p1981) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p3266) ∨ p2766 ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5650 t (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16330 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2766) (meaning t m 3266) (meaning t m 4137) (meaning t m 4191) source

theorem rule16334 (p1984 p2027 p2766 p3860 p3979 p4347 p5693 : Prop) (h : (¬ p4347) ∨ p2766 ∨ (¬ p5693) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p3860) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3860) ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial16334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory5654 t (m.theta 0 1) (m.theta 1 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule16334 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3860) (meaning t m 3979) (meaning t m 4347) (meaning t m 5693) source

theorem rule16337 (p1984 p2027 p2299 p2396 p2633 p3817 p4366 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p4366) ∨ p2633 ∨ (¬ p3817) ∨ (¬ p2396) ∨ (¬ p2299)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5657 t (m.theta 0 1) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16337 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3817) (meaning t m 4366) source

theorem rule16338 (p1984 p2027 p2764 p3548 p4348 p4366 p4444 : Prop) (h : (¬ p4348) ∨ p2764 ∨ (¬ p4366) ∨ (¬ p1984) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p4444)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5658 t (m.theta 0 1) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16338 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3548) (meaning t m 4348) (meaning t m 4366) (meaning t m 4444) source

theorem rule16339 (p1998 p2027 p2542 p2545 p2911 p2922 p3238 : Prop) (h : p2027 ∨ (¬ p1998) ∨ (¬ p3238) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2542) ∨ p2545) : (¬ p1998) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial16339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory5659 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule16339 (meaning t m 1998) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2911) (meaning t m 2922) (meaning t m 3238) source

theorem rule16340 (p2027 p2542 p3238 p3402 p3842 p5177 : Prop) (h : (¬ p2542) ∨ (¬ p3402) ∨ (¬ p3238) ∨ (¬ p5177) ∨ p2027 ∨ (¬ p3842)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3842) ∨ (¬ p5177) := by
  classical
  tauto

theorem initial16340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 5177)) := by
  have source := ElevenTheory.theory5660 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5)
  exact rule16340 (meaning t m 2027) (meaning t m 2542) (meaning t m 3238) (meaning t m 3402) (meaning t m 3842) (meaning t m 5177) source

theorem rule16341 (p2005 p2027 p2202 p2573 p2922 p3238 p3540 : Prop) (h : (¬ p2005) ∨ (¬ p3238) ∨ p2202 ∨ (¬ p2573) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3540)) : (¬ p2005) ∨ (p2027) ∨ (p2202) ∨ (¬ p2573) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial16341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory5661 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule16341 (meaning t m 2005) (meaning t m 2027) (meaning t m 2202) (meaning t m 2573) (meaning t m 2922) (meaning t m 3238) (meaning t m 3540) source

theorem rule16342 (p1990 p2027 p2202 p2553 p2573 p2589 p3097 : Prop) (h : p2202 ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial16342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory5662 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16342 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2553) (meaning t m 2573) (meaning t m 2589) (meaning t m 3097) source

theorem rule16346 (p2003 p2027 p2396 p2997 p3817 p4181 p4189 p4197 p5590 : Prop) (h : (¬ p2003) ∨ (¬ p5590) ∨ (¬ p3817) ∨ (¬ p4197) ∨ (¬ p4189) ∨ (¬ p2396) ∨ p2997 ∨ p2027 ∨ (¬ p4181)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3817) ∨ (¬ p4181) ∨ (¬ p4189) ∨ (¬ p4197) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial16346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory5666 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 7) (m.theta 1 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 10)
  exact rule16346 (meaning t m 2003) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3817) (meaning t m 4181) (meaning t m 4189) (meaning t m 4197) (meaning t m 5590) source

theorem rule16347 (p1998 p2027 p2396 p2997 p3439 p3817 p3998 p4189 p5558 : Prop) (h : p2027 ∨ (¬ p3439) ∨ p2997 ∨ (¬ p3817) ∨ (¬ p3998) ∨ (¬ p4189) ∨ (¬ p2396) ∨ (¬ p5558) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3439) ∨ (¬ p3817) ∨ (¬ p3998) ∨ (¬ p4189) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial16347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3439)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory5667 t (m.theta 0 8) (m.theta 1 7) (m.theta 1 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule16347 (meaning t m 1998) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3439) (meaning t m 3817) (meaning t m 3998) (meaning t m 4189) (meaning t m 5558) source

theorem rule16348 (p2000 p2027 p2633 p3540 p3548 p3631 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p2000) ∨ (¬ p3540) ∨ p2633 ∨ p2027 ∨ (¬ p3548) ∨ (¬ p3631)) : (¬ p2000) ∨ (p2027) ∨ (p2633) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5668 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16348 (meaning t m 2000) (meaning t m 2027) (meaning t m 2633) (meaning t m 3540) (meaning t m 3548) (meaning t m 3631) (meaning t m 4278) source

theorem rule16352 (p1983 p2027 p2156 p2274 p2396 p2622 p2951 p3136 : Prop) (h : (¬ p2396) ∨ p2622 ∨ (¬ p1983) ∨ (¬ p3136) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2951)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial16352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory5672 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16352 (meaning t m 1983) (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2622) (meaning t m 2951) (meaning t m 3136) source

theorem rule16353 (p1977 p2027 p2241 p2542 p2545 p3238 p3452 : Prop) (h : (¬ p1977) ∨ (¬ p3238) ∨ p2545 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2241) ∨ (¬ p3452)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3238) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial16353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory5673 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule16353 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2542) (meaning t m 2545) (meaning t m 3238) (meaning t m 3452) source

theorem rule16354 (p2000 p2027 p2493 p2542 p2545 p2579 p3238 : Prop) (h : (¬ p2000) ∨ (¬ p3238) ∨ (¬ p2542) ∨ p2545 ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2579)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial16354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory5674 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16354 (meaning t m 2000) (meaning t m 2027) (meaning t m 2493) (meaning t m 2542) (meaning t m 2545) (meaning t m 2579) (meaning t m 3238) source

theorem rule16356 (p2005 p2027 p2542 p2573 p2589 p2622 p2630 : Prop) (h : (¬ p2005) ∨ (¬ p2573) ∨ (¬ p2589) ∨ p2622 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2542)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (p2622) ∨ (¬ p2630) := by
  classical
  tauto

theorem initial16356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) := by
  have source := ElevenTheory.theory5676 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16356 (meaning t m 2005) (meaning t m 2027) (meaning t m 2542) (meaning t m 2573) (meaning t m 2589) (meaning t m 2622) (meaning t m 2630) source

theorem rule16357 (p1992 p2027 p2542 p2545 p2608 p3238 p3452 : Prop) (h : p2545 ∨ (¬ p1992) ∨ (¬ p2542) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3238)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial16357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory5677 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule16357 (meaning t m 1992) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2608) (meaning t m 3238) (meaning t m 3452) source

theorem rule16358 (p1987 p2027 p2542 p2545 p2696 p3055 p3238 p4030 : Prop) (h : (¬ p1987) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p2696) ∨ (¬ p4030) ∨ (¬ p3238)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial16358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory5678 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule16358 (meaning t m 1987) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2696) (meaning t m 3055) (meaning t m 3238) (meaning t m 4030) source

theorem rule16362 (p1977 p2027 p2241 p2299 p2633 p3549 p3591 : Prop) (h : (¬ p3549) ∨ (¬ p2299) ∨ (¬ p1977) ∨ (¬ p3591) ∨ p2633 ∨ (¬ p2241) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial16362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory5682 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16362 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2633) (meaning t m 3549) (meaning t m 3591) source

theorem rule16364 (p1977 p2027 p2810 p3498 p3755 p3848 p4256 : Prop) (h : (¬ p3755) ∨ p2027 ∨ p3498 ∨ (¬ p4256) ∨ (¬ p2810) ∨ (¬ p1977) ∨ (¬ p3848)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2810) ∨ (p3498) ∨ (¬ p3755) ∨ (¬ p3848) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial16364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory5684 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 8)
  exact rule16364 (meaning t m 1977) (meaning t m 2027) (meaning t m 2810) (meaning t m 3498) (meaning t m 3755) (meaning t m 3848) (meaning t m 4256) source

theorem rule16369 (p1992 p2027 p2608 p2766 p3266 p3440 p3860 p4321 : Prop) (h : p2027 ∨ (¬ p1992) ∨ (¬ p3266) ∨ p2766 ∨ (¬ p4321) ∨ (¬ p3860) ∨ (¬ p3440) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3440) ∨ (¬ p3860) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial16369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory5689 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 1 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16369 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2766) (meaning t m 3266) (meaning t m 3440) (meaning t m 3860) (meaning t m 4321) source

theorem rule16371 (p1992 p2027 p2177 p2608 p2997 p3548 p4366 : Prop) (h : (¬ p2177) ∨ (¬ p3548) ∨ p2027 ∨ p2997 ∨ (¬ p4366) ∨ (¬ p1992) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2608) ∨ (p2997) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5691 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16371 (meaning t m 1992) (meaning t m 2027) (meaning t m 2177) (meaning t m 2608) (meaning t m 2997) (meaning t m 3548) (meaning t m 4366) source

theorem rule16372 (p1977 p2027 p2241 p2911 p2914 p3032 p3553 p4366 : Prop) (h : (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p3032)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3032) ∨ (¬ p3553) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5692 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule16372 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2911) (meaning t m 2914) (meaning t m 3032) (meaning t m 3553) (meaning t m 4366) source

theorem rule16373 (p1976 p2027 p2299 p2633 p3365 p3568 p4195 : Prop) (h : p2633 ∨ (¬ p1976) ∨ (¬ p3365) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2299)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial16373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory5693 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16373 (meaning t m 1976) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3365) (meaning t m 3568) (meaning t m 4195) source

theorem rule16375 (p1985 p2027 p2148 p2156 p2274 p2396 p3690 : Prop) (h : (¬ p2156) ∨ (¬ p2396) ∨ p2148 ∨ p2027 ∨ (¬ p2274) ∨ (¬ p1985) ∨ (¬ p3690)) : (¬ p1985) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial16375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory5695 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16375 (meaning t m 1985) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 3690) source

theorem rule16378 (p1992 p2027 p2287 p2608 p3323 p3591 p4026 : Prop) (h : (¬ p3323) ∨ p2287 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p1992) ∨ (¬ p3591) ∨ (¬ p4026)) : (¬ p1992) ∨ (p2027) ∨ (p2287) ∨ (¬ p2608) ∨ (¬ p3323) ∨ (¬ p3591) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial16378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory5698 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule16378 (meaning t m 1992) (meaning t m 2027) (meaning t m 2287) (meaning t m 2608) (meaning t m 3323) (meaning t m 3591) (meaning t m 4026) source

theorem rule16379 (p1996 p2202 p2440 p4652 : Prop) (h : (¬ p1996) ∨ (¬ p2440) ∨ p2202 ∨ p4652) : (¬ p1996) ∨ (p2202) ∨ (¬ p2440) ∨ (p4652) := by
  classical
  tauto

theorem initial16379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 4652) := by
  have source := ElevenTheory.theory5699 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule16379 (meaning t m 1996) (meaning t m 2202) (meaning t m 2440) (meaning t m 4652) source

theorem rule16382 (p1982 p2027 p2406 p2409 p2470 p2531 p2589 p3146 : Prop) (h : (¬ p3146) ∨ (¬ p2470) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2531) ∨ (¬ p2589) ∨ p2409 ∨ (¬ p2406)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial16382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory5702 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule16382 (meaning t m 1982) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2470) (meaning t m 2531) (meaning t m 2589) (meaning t m 3146) source

theorem rule16383 (p1998 p2027 p2470 p2509 p2699 p2911 p2922 p4079 : Prop) (h : (¬ p1998) ∨ p2699 ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2470) ∨ (¬ p4079) ∨ (¬ p2509)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial16383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory5703 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule16383 (meaning t m 1998) (meaning t m 2027) (meaning t m 2470) (meaning t m 2509) (meaning t m 2699) (meaning t m 2911) (meaning t m 2922) (meaning t m 4079) source

theorem rule16386 (p1982 p2027 p2264 p2459 p2545 p2657 p2807 : Prop) (h : (¬ p2657) ∨ p2545 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2264) ∨ (¬ p2807)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) := by
  classical
  tauto

theorem initial16386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) := by
  have source := ElevenTheory.theory5706 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16386 (meaning t m 1982) (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) source

theorem rule16387 (p1983 p2027 p2417 p2699 p3399 p3527 p3644 : Prop) (h : (¬ p2417) ∨ (¬ p3527) ∨ (¬ p1983) ∨ p2699 ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3399)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial16387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory5707 t (m.theta 0 1) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16387 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2699) (meaning t m 3399) (meaning t m 3527) (meaning t m 3644) source

theorem rule16389 (p1998 p2027 p2177 p2295 p2331 p2545 p2657 : Prop) (h : (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2177) ∨ (¬ p1998) ∨ (¬ p2331)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) := by
  classical
  tauto

theorem initial16389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) := by
  have source := ElevenTheory.theory5709 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16389 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) source

theorem rule16390 (p1982 p2027 p2528 p2622 p2630 p2657 p3166 p4346 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2528) ∨ (¬ p1982) ∨ (¬ p4346) ∨ (¬ p2657) ∨ (¬ p3166)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial16390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory5710 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule16390 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 3166) (meaning t m 4346) source

theorem rule16391 (p1982 p2027 p2252 p2528 p2622 p2630 p2657 p3189 p4346 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2528) ∨ (¬ p4346) ∨ (¬ p1982) ∨ (¬ p2657) ∨ (¬ p2252) ∨ (¬ p3189)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3189) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial16391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory5711 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule16391 (meaning t m 1982) (meaning t m 2027) (meaning t m 2252) (meaning t m 2528) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 3189) (meaning t m 4346) source

theorem rule16393 (p1998 p2027 p2114 p2911 p2922 p3379 p3954 : Prop) (h : (¬ p3379) ∨ (¬ p1998) ∨ (¬ p3954) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2922) ∨ p2114) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5713 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8)
  exact rule16393 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3954) source

theorem rule16394 (p1997 p2027 p2699 p2850 p2922 p3379 p3876 : Prop) (h : p2699 ∨ (¬ p2922) ∨ (¬ p2850) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3876)) : (¬ p1997) ∨ (p2027) ∨ (p2699) ∨ (¬ p2850) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial16394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory5714 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule16394 (meaning t m 1997) (meaning t m 2027) (meaning t m 2699) (meaning t m 2850) (meaning t m 2922) (meaning t m 3379) (meaning t m 3876) source

theorem rule16396 (p1990 p2027 p2284 p2699 p3399 p3527 p3553 p4386 : Prop) (h : (¬ p3399) ∨ p2699 ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p1990) ∨ (¬ p3553) ∨ (¬ p4386)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial16396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory5716 t (m.theta 0 1) (m.theta 1 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 7 8)
  exact rule16396 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2699) (meaning t m 3399) (meaning t m 3527) (meaning t m 3553) (meaning t m 4386) source

theorem rule16397 (p1990 p2027 p2177 p2284 p2957 p2997 p3556 p3570 : Prop) (h : p2027 ∨ (¬ p3556) ∨ (¬ p2284) ∨ p2997 ∨ (¬ p1990) ∨ (¬ p3570) ∨ (¬ p2957) ∨ (¬ p2177)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2284) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial16397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory5717 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16397 (meaning t m 1990) (meaning t m 2027) (meaning t m 2177) (meaning t m 2284) (meaning t m 2957) (meaning t m 2997) (meaning t m 3556) (meaning t m 3570) source

theorem rule16398 (p1990 p2027 p2210 p2284 p2699 p2891 p4320 : Prop) (h : (¬ p2284) ∨ (¬ p1990) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2891) ∨ p2699) : (¬ p1990) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial16398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory5718 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16398 (meaning t m 1990) (meaning t m 2027) (meaning t m 2210) (meaning t m 2284) (meaning t m 2699) (meaning t m 2891) (meaning t m 4320) source

theorem rule16399 (p1994 p2027 p2241 p2630 p2699 p2992 p4315 : Prop) (h : p2699 ∨ (¬ p2241) ∨ (¬ p4315) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2630)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5719 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule16399 (meaning t m 1994) (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2699) (meaning t m 2992) (meaning t m 4315) source

theorem rule16400 (p1980 p2027 p2241 p2699 p2727 p2797 p2810 : Prop) (h : (¬ p2727) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p2797) ∨ (¬ p1980)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p2797) ∨ (¬ p2810) := by
  classical
  tauto

theorem initial16400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) := by
  have source := ElevenTheory.theory5720 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule16400 (meaning t m 1980) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2727) (meaning t m 2797) (meaning t m 2810) source

theorem rule16401 (p1984 p2027 p2764 p3591 p3923 p4347 p4444 : Prop) (h : (¬ p1984) ∨ (¬ p4444) ∨ (¬ p3923) ∨ (¬ p4347) ∨ p2764 ∨ (¬ p3591) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5721 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16401 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) (meaning t m 4444) source

theorem rule16403 (p1985 p2027 p2114 p2427 p2542 p2651 p2737 p2811 : Prop) (h : (¬ p2427) ∨ (¬ p2811) ∨ (¬ p2542) ∨ (¬ p1985) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2737) ∨ p2114) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial16403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory5723 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule16403 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2427) (meaning t m 2542) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) source

theorem rule16404 (p2012 p2027 p2114 p2230 p2440 p2663 p2737 p2811 p3343 : Prop) (h : (¬ p2440) ∨ (¬ p2012) ∨ (¬ p3343) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2663) ∨ (¬ p2811) ∨ p2114 ∨ (¬ p2737)) : (¬ p2012) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial16404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory5724 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule16404 (meaning t m 2012) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 2737) (meaning t m 2811) (meaning t m 3343) source

theorem rule16406 (p5738 p5739 p5740 p5741 p5742 : Prop) : (p5740) ∨ (((¬ p5739) ∨ (¬ p5740) ∨ (¬ p5738) ∨ (¬ p5741) ∨ (¬ p5742))) := by
  classical
  tauto

theorem initial16406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5740) ∨ (meaning t m 6193) := by
  exact rule16406 (meaning t m 5738) (meaning t m 5739) (meaning t m 5740) (meaning t m 5741) (meaning t m 5742)

theorem rule16413 (p4272 p5744 p5745 p5746 p5747 : Prop) : (p4272) ∨ (((¬ p5744) ∨ (¬ p5745) ∨ (¬ p4272) ∨ (¬ p5746) ∨ (¬ p5747))) := by
  classical
  tauto

theorem initial16413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4272) ∨ (meaning t m 6194) := by
  exact rule16413 (meaning t m 4272) (meaning t m 5744) (meaning t m 5745) (meaning t m 5746) (meaning t m 5747)

theorem rule16419 (p6193 p6194 : Prop) : (¬ ((¬ p6193) ∨ (¬ p6194))) ∨ (¬ p6193) ∨ (¬ p6194) := by
  classical
  tauto

theorem initial16419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6192)) ∨ (¬ (meaning t m 6193)) ∨ (¬ (meaning t m 6194)) := by
  exact rule16419 (meaning t m 6193) (meaning t m 6194)

theorem rule16420 (p5736 p6192 : Prop) (h : (p5736 ↔ p6192)) : (¬ p5736) ∨ (p6192) := by
  classical
  tauto

theorem initial16420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5736)) ∨ (meaning t m 6192) := by
  have source := ElevenTheory.theory5725 t (m.theta 3 10) (m.theta 3 5) (m.theta 5 10)
  exact rule16420 (meaning t m 5736) (meaning t m 6192) source

theorem rule16423 (p2012 p2027 p2440 p2598 p2611 p2850 p3343 : Prop) (h : (¬ p2012) ∨ (¬ p3343) ∨ p2611 ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2850)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial16423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory5727 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule16423 (meaning t m 2012) (meaning t m 2027) (meaning t m 2440) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 3343) source

theorem rule16424 (p1988 p2027 p2230 p2233 p2440 p3343 p3680 p4952 : Prop) (h : p2027 ∨ (¬ p1988) ∨ (¬ p3680) ∨ p2233 ∨ (¬ p2230) ∨ (¬ p4952) ∨ (¬ p2440) ∨ (¬ p3343)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p3680) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial16424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory5728 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule16424 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2440) (meaning t m 3343) (meaning t m 3680) (meaning t m 4952) source

theorem rule16425 (p1990 p2027 p2323 p2563 p2946 p3115 p4948 : Prop) (h : (¬ p2946) ∨ (¬ p1990) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3115) ∨ (¬ p4948) ∨ p2323) : (¬ p1990) ∨ (p2027) ∨ (p2323) ∨ (¬ p2563) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5729 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule16425 (meaning t m 1990) (meaning t m 2027) (meaning t m 2323) (meaning t m 2563) (meaning t m 2946) (meaning t m 3115) (meaning t m 4948) source

theorem rule16426 (p1982 p2027 p2611 p2696 p3136 p3146 p3156 : Prop) (h : (¬ p3146) ∨ (¬ p3156) ∨ (¬ p1982) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3136) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial16426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory5730 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16426 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3136) (meaning t m 3146) (meaning t m 3156) source

theorem rule16428 (p1982 p2027 p2230 p2323 p2440 p2531 p2663 p3083 p3146 : Prop) (h : (¬ p3146) ∨ (¬ p3083) ∨ p2323 ∨ (¬ p2230) ∨ (¬ p2663) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2230) ∨ (p2323) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p2663) ∨ (¬ p3083) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial16428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory5732 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule16428 (meaning t m 1982) (meaning t m 2027) (meaning t m 2230) (meaning t m 2323) (meaning t m 2440) (meaning t m 2531) (meaning t m 2663) (meaning t m 3083) (meaning t m 3146) source

theorem rule16429 (p1990 p2027 p2230 p2476 p2563 p2842 p3641 : Prop) (h : (¬ p2563) ∨ (¬ p1990) ∨ p2842 ∨ (¬ p3641) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2476)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2563) ∨ (p2842) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial16429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory5733 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule16429 (meaning t m 1990) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2563) (meaning t m 2842) (meaning t m 3641) source

theorem rule16430 (p1992 p2027 p2608 p2764 p3591 p4026 p4191 : Prop) (h : (¬ p4191) ∨ p2764 ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2764) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5734 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 6 9) (m.theta 9 10)
  exact rule16430 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2764) (meaning t m 3591) (meaning t m 4026) (meaning t m 4191) source

theorem rule16431 (p1990 p2027 p2230 p2233 p2284 p2373 p3497 : Prop) (h : (¬ p2373) ∨ p2233 ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p1990) ∨ (¬ p3497)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2284) ∨ (¬ p2373) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial16431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory5735 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule16431 (meaning t m 1990) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2284) (meaning t m 2373) (meaning t m 3497) source

theorem rule16432 (p1990 p2027 p2323 p2958 p3016 p3998 p4203 p4238 p4256 p4286 : Prop) (h : (¬ p2958) ∨ (¬ p4256) ∨ p2323 ∨ (¬ p3998) ∨ (¬ p4238) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p4286) ∨ (¬ p1990) ∨ (¬ p4203)) : (¬ p1990) ∨ (p2027) ∨ (p2323) ∨ (¬ p2958) ∨ (¬ p3016) ∨ (¬ p3998) ∨ (¬ p4203) ∨ (¬ p4238) ∨ (¬ p4256) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial16432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory5736 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 8) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 8 10)
  exact rule16432 (meaning t m 1990) (meaning t m 2027) (meaning t m 2323) (meaning t m 2958) (meaning t m 3016) (meaning t m 3998) (meaning t m 4203) (meaning t m 4238) (meaning t m 4256) (meaning t m 4286) source

theorem rule16433 (p1982 p2027 p2166 p2210 p2247 p2688 p3146 : Prop) (h : (¬ p2247) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2166) ∨ p2688 ∨ (¬ p2210)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial16433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory5737 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16433 (meaning t m 1982) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 3146) source

theorem rule16438 (p2008 p2027 p2104 p2622 p2743 p3471 p3537 : Prop) (h : (¬ p2104) ∨ p2622 ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3471) ∨ (¬ p2008) ∨ (¬ p3537)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2104) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3471) ∨ (¬ p3537) := by
  classical
  tauto

theorem initial16438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3537)) := by
  have source := ElevenTheory.theory5742 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8)
  exact rule16438 (meaning t m 2008) (meaning t m 2027) (meaning t m 2104) (meaning t m 2622) (meaning t m 2743) (meaning t m 3471) (meaning t m 3537) source

theorem rule16440 (p1978 p2027 p2299 p2633 p2860 p3646 p4244 p4275 : Prop) (h : (¬ p1978) ∨ (¬ p4275) ∨ (¬ p3646) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p2299) ∨ p2633 ∨ p2027) : (¬ p1978) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial16440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory5744 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16440 (meaning t m 1978) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2860) (meaning t m 3646) (meaning t m 4244) (meaning t m 4275) source

theorem rule16442 (p2005 p2027 p2166 p2241 p2699 p3016 p3497 p4365 p4700 : Prop) (h : p2699 ∨ (¬ p2241) ∨ (¬ p2005) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p4365) ∨ (¬ p2166) ∨ (¬ p3497) ∨ (¬ p4700)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4365) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial16442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory5746 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8)
  exact rule16442 (meaning t m 2005) (meaning t m 2027) (meaning t m 2166) (meaning t m 2241) (meaning t m 2699) (meaning t m 3016) (meaning t m 3497) (meaning t m 4365) (meaning t m 4700) source

theorem rule16444 (p1982 p2027 p2241 p2699 p3506 p3842 p4444 : Prop) (h : (¬ p3842) ∨ (¬ p3506) ∨ (¬ p2241) ∨ p2699 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5748 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16444 (meaning t m 1982) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3506) (meaning t m 3842) (meaning t m 4444) source

theorem rule16445 (p1992 p2027 p2396 p2579 p2997 p3363 p3581 p3585 p4278 : Prop) (h : (¬ p2579) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3581) ∨ (¬ p4278) ∨ (¬ p1992) ∨ (¬ p3363) ∨ (¬ p3585) ∨ p2997) : (¬ p1992) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2579) ∨ (p2997) ∨ (¬ p3363) ∨ (¬ p3581) ∨ (¬ p3585) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5749 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16445 (meaning t m 1992) (meaning t m 2027) (meaning t m 2396) (meaning t m 2579) (meaning t m 2997) (meaning t m 3363) (meaning t m 3581) (meaning t m 3585) (meaning t m 4278) source

theorem rule16446 (p1987 p2027 p2396 p2579 p2662 p2810 p2997 p3581 p4278 : Prop) (h : p2997 ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3581) ∨ (¬ p4278) ∨ (¬ p2396) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p2997) ∨ (¬ p3581) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5750 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16446 (meaning t m 1987) (meaning t m 2027) (meaning t m 2396) (meaning t m 2579) (meaning t m 2662) (meaning t m 2810) (meaning t m 2997) (meaning t m 3581) (meaning t m 4278) source

theorem rule16448 (p1990 p2027 p2284 p2396 p2997 p3821 p4283 p4320 : Prop) (h : (¬ p3821) ∨ (¬ p4283) ∨ p2027 ∨ (¬ p2396) ∨ p2997 ∨ (¬ p2284) ∨ (¬ p4320) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial16448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory5752 t (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16448 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2396) (meaning t m 2997) (meaning t m 3821) (meaning t m 4283) (meaning t m 4320) source

theorem rule16450 (p1988 p2027 p2657 p2688 p2727 p3286 p3506 : Prop) (h : (¬ p2727) ∨ p2027 ∨ (¬ p2657) ∨ p2688 ∨ (¬ p3506) ∨ (¬ p3286) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3286) ∨ (¬ p3506) := by
  classical
  tauto

theorem initial16450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) := by
  have source := ElevenTheory.theory5754 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule16450 (meaning t m 1988) (meaning t m 2027) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3286) (meaning t m 3506) source

theorem rule16451 (p1983 p2027 p2449 p2657 p2688 p2727 p2807 : Prop) (h : (¬ p2807) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2657) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2449)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2807) := by
  classical
  tauto

theorem initial16451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2807)) := by
  have source := ElevenTheory.theory5755 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule16451 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 2807) source

theorem rule16452 (p1984 p2027 p2396 p2928 p2997 p3452 p4278 : Prop) (h : (¬ p3452) ∨ p2027 ∨ p2997 ∨ (¬ p1984) ∨ (¬ p2396) ∨ (¬ p2928) ∨ (¬ p4278)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2928) ∨ (p2997) ∨ (¬ p3452) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5756 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16452 (meaning t m 1984) (meaning t m 2027) (meaning t m 2396) (meaning t m 2928) (meaning t m 2997) (meaning t m 3452) (meaning t m 4278) source

theorem rule16455 (p1984 p2027 p2187 p2997 p3097 p3591 p3923 : Prop) (h : (¬ p3923) ∨ (¬ p1984) ∨ (¬ p3097) ∨ p2027 ∨ p2997 ∨ (¬ p3591) ∨ (¬ p2187)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2187) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial16455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory5759 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16455 (meaning t m 1984) (meaning t m 2027) (meaning t m 2187) (meaning t m 2997) (meaning t m 3097) (meaning t m 3591) (meaning t m 3923) source

theorem rule16456 (p1990 p2027 p2545 p2563 p2743 p2810 p2839 p3695 : Prop) (h : (¬ p2839) ∨ (¬ p2563) ∨ (¬ p1990) ∨ (¬ p3695) ∨ (¬ p2743) ∨ p2027 ∨ p2545 ∨ (¬ p2810)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p2839) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial16456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory5760 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule16456 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2563) (meaning t m 2743) (meaning t m 2810) (meaning t m 2839) (meaning t m 3695) source

theorem rule16458 (p1998 p2027 p2287 p2656 p2727 p2911 p3389 p4154 : Prop) (h : (¬ p2656) ∨ (¬ p1998) ∨ (¬ p2727) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3389) ∨ p2287 ∨ (¬ p4154)) : (¬ p1998) ∨ (p2027) ∨ (p2287) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5762 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 7 8)
  exact rule16458 (meaning t m 1998) (meaning t m 2027) (meaning t m 2287) (meaning t m 2656) (meaning t m 2727) (meaning t m 2911) (meaning t m 3389) (meaning t m 4154) source

theorem rule16459 (p1998 p2027 p2657 p2688 p2727 p2807 p2911 p3579 : Prop) (h : (¬ p1998) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p3579)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial16459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory5763 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule16459 (meaning t m 1998) (meaning t m 2027) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 2807) (meaning t m 2911) (meaning t m 3579) source

theorem rule16460 (p1997 p2027 p2169 p2972 p3989 p4173 p4948 : Prop) (h : (¬ p4173) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p1997) ∨ (¬ p2972) ∨ p2169 ∨ (¬ p3989)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2972) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5764 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8)
  exact rule16460 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2972) (meaning t m 3989) (meaning t m 4173) (meaning t m 4948) source

theorem rule16462 (p1984 p2688 p2743 p2751 p3954 : Prop) (h : p2688 ∨ p2751 ∨ (¬ p3954) ∨ (¬ p1984) ∨ (¬ p2743)) : (¬ p1984) ∨ (p2688) ∨ (¬ p2743) ∨ (p2751) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2751) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5766 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3)
  exact rule16462 (meaning t m 1984) (meaning t m 2688) (meaning t m 2743) (meaning t m 2751) (meaning t m 3954) source

theorem rule16464 (p1990 p2027 p2156 p2688 p2727 p2901 p3413 p3556 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p3413) ∨ (¬ p2727) ∨ (¬ p2156) ∨ (¬ p1990) ∨ (¬ p3556) ∨ (¬ p2901)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial16464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory5768 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16464 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2688) (meaning t m 2727) (meaning t m 2901) (meaning t m 3413) (meaning t m 3556) source

theorem rule16465 (p1997 p2027 p2156 p2764 p4032 p4033 p4110 p4191 : Prop) (h : (¬ p4033) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2156) ∨ (¬ p4110) ∨ p2764 ∨ (¬ p4191) ∨ (¬ p4032)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (p2764) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p4110) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5769 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule16465 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2764) (meaning t m 4032) (meaning t m 4033) (meaning t m 4110) (meaning t m 4191) source

theorem rule16466 (p1982 p2027 p2688 p2761 p3027 p3516 p4066 p4444 : Prop) (h : (¬ p1982) ∨ (¬ p2761) ∨ (¬ p3516) ∨ p2027 ∨ p2688 ∨ (¬ p4066) ∨ (¬ p4444) ∨ (¬ p3027)) : (¬ p1982) ∨ (p2027) ∨ (p2688) ∨ (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5770 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16466 (meaning t m 1982) (meaning t m 2027) (meaning t m 2688) (meaning t m 2761) (meaning t m 3027) (meaning t m 3516) (meaning t m 4066) (meaning t m 4444) source

theorem rule16467 (p1988 p2027 p2470 p2528 p2656 p2688 p2727 p3266 : Prop) (h : p2027 ∨ (¬ p3266) ∨ p2688 ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial16467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory5771 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16467 (meaning t m 1988) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3266) source

theorem rule16470 (p1985 p2027 p2427 p2656 p2688 p2727 p3212 p4399 p4948 : Prop) (h : (¬ p3212) ∨ p2688 ∨ (¬ p1985) ∨ (¬ p4948) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p2656) ∨ (¬ p2727)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5774 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule16470 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3212) (meaning t m 4399) (meaning t m 4948) source

theorem rule16472 (p1982 p2027 p2230 p2373 p2656 p2688 p2727 p3146 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2373) ∨ p2688 ∨ (¬ p2230) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial16472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory5776 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16472 (meaning t m 1982) (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3146) source

theorem rule16473 (p1988 p2027 p2230 p2656 p2688 p2727 p2982 p3680 : Prop) (h : (¬ p2982) ∨ (¬ p3680) ∨ (¬ p1988) ∨ (¬ p2727) ∨ p2688 ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2656)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2982) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial16473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory5777 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule16473 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2982) (meaning t m 3680) source

theorem rule16476 (p1997 p2027 p2396 p2997 p3051 p4032 p4235 p4382 : Prop) (h : (¬ p4032) ∨ p2997 ∨ (¬ p3051) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4382) ∨ (¬ p1997) ∨ (¬ p4235)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4235) ∨ (¬ p4382) := by
  classical
  tauto

theorem initial16476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4382)) := by
  have source := ElevenTheory.theory5780 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule16476 (meaning t m 1997) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3051) (meaning t m 4032) (meaning t m 4235) (meaning t m 4382) source

theorem rule16478 (p1991 p2027 p2952 p2992 p2997 p3568 p4154 : Prop) (h : (¬ p3568) ∨ (¬ p2992) ∨ p2997 ∨ (¬ p2952) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p4154)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5782 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule16478 (meaning t m 1991) (meaning t m 2027) (meaning t m 2952) (meaning t m 2992) (meaning t m 2997) (meaning t m 3568) (meaning t m 4154) source

theorem rule16481 (p1984 p2027 p2177 p2997 p3486 p3555 p3570 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p1984) ∨ (¬ p2177) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3486)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial16481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory5785 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16481 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) source

theorem rule16484 (p1984 p2027 p2765 p2901 p3486 p3555 p3952 : Prop) (h : p2765 ∨ (¬ p2901) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3952) ∨ (¬ p3486) ∨ (¬ p3555)) : (¬ p1984) ∨ (p2027) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial16484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory5788 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16484 (meaning t m 1984) (meaning t m 2027) (meaning t m 2765) (meaning t m 2901) (meaning t m 3486) (meaning t m 3555) (meaning t m 3952) source

theorem rule16485 (p1997 p2027 p2274 p2588 p2765 p2850 p3584 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2274) ∨ (¬ p3584) ∨ (¬ p2850) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (p2765) ∨ (¬ p2850) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial16485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory5789 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16485 (meaning t m 1997) (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2765) (meaning t m 2850) (meaning t m 3584) source

theorem rule16487 (p1982 p2027 p2114 p2459 p2911 p3367 p3389 p3759 : Prop) (h : p2027 ∨ (¬ p2911) ∨ (¬ p1982) ∨ (¬ p3389) ∨ (¬ p2459) ∨ p2114 ∨ (¬ p3759) ∨ (¬ p3367)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial16487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory5791 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16487 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2459) (meaning t m 2911) (meaning t m 3367) (meaning t m 3389) (meaning t m 3759) source

theorem rule16488 (p1987 p2027 p2545 p2696 p3027 p3425 p4111 p4777 : Prop) (h : (¬ p1987) ∨ (¬ p3027) ∨ (¬ p4777) ∨ p2027 ∨ p2545 ∨ (¬ p2696) ∨ (¬ p4111) ∨ (¬ p3425)) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p4111) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial16488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory5792 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule16488 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 2696) (meaning t m 3027) (meaning t m 3425) (meaning t m 4111) (meaning t m 4777) source

theorem rule16489 (p1991 p2027 p2633 p2952 p2992 p2996 p3553 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p3553) ∨ (¬ p2992) ∨ (¬ p1991) ∨ (¬ p2952) ∨ (¬ p2996)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial16489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory5793 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule16489 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 2952) (meaning t m 2992) (meaning t m 2996) (meaning t m 3553) source

theorem rule16490 (p2027 p2657 p2751 p2946 p3487 p4281 p4315 : Prop) (h : (¬ p2946) ∨ (¬ p4281) ∨ (¬ p4315) ∨ (¬ p2751) ∨ (¬ p3487) ∨ p2027 ∨ (¬ p2657)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2751) ∨ (¬ p2946) ∨ (¬ p3487) ∨ (¬ p4281) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5794 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule16490 (meaning t m 2027) (meaning t m 2657) (meaning t m 2751) (meaning t m 2946) (meaning t m 3487) (meaning t m 4281) (meaning t m 4315) source

theorem rule16491 (p1997 p2027 p2396 p2850 p2997 p3876 p4278 : Prop) (h : (¬ p2396) ∨ p2027 ∨ (¬ p3876) ∨ p2997 ∨ (¬ p4278) ∨ (¬ p1997) ∨ (¬ p2850)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2850) ∨ (p2997) ∨ (¬ p3876) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5795 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16491 (meaning t m 1997) (meaning t m 2027) (meaning t m 2396) (meaning t m 2850) (meaning t m 2997) (meaning t m 3876) (meaning t m 4278) source

theorem rule16492 (p1983 p2027 p2233 p2417 p2470 p3201 p3874 : Prop) (h : p2233 ∨ (¬ p3874) ∨ (¬ p3201) ∨ (¬ p2417) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (p2233) ∨ (¬ p2417) ∨ (¬ p2470) ∨ (¬ p3201) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial16492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory5796 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 9)
  exact rule16492 (meaning t m 1983) (meaning t m 2027) (meaning t m 2233) (meaning t m 2417) (meaning t m 2470) (meaning t m 3201) (meaning t m 3874) source

theorem rule16494 (p1984 p2027 p2766 p3555 p3989 p4173 p4347 : Prop) (h : (¬ p3555) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3989) ∨ p2766 ∨ (¬ p1984) ∨ (¬ p4173)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory5798 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16494 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) (meaning t m 4347) source

theorem rule16495 (p1991 p2027 p2169 p2952 p2992 p3745 p3989 p4154 : Prop) (h : (¬ p1991) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2992) ∨ p2169 ∨ (¬ p4154) ∨ (¬ p3745) ∨ (¬ p3989)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p3989) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5799 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule16495 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2952) (meaning t m 2992) (meaning t m 3745) (meaning t m 3989) (meaning t m 4154) source

theorem rule16497 (p1998 p2027 p2528 p2598 p2611 p3201 p3875 p4348 : Prop) (h : (¬ p1998) ∨ p2611 ∨ (¬ p2598) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3875) ∨ (¬ p2528)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3201) ∨ (¬ p3875) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5801 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16497 (meaning t m 1998) (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2611) (meaning t m 3201) (meaning t m 3875) (meaning t m 4348) source

theorem rule16498 (p2008 p2027 p2449 p2545 p2657 p2807 p4324 : Prop) (h : p2545 ∨ (¬ p2449) ∨ (¬ p2657) ∨ (¬ p4324) ∨ (¬ p2008) ∨ p2027 ∨ (¬ p2807)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2449) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial16498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory5802 t (m.theta 0 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule16498 (meaning t m 2008) (meaning t m 2027) (meaning t m 2449) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 4324) source

theorem rule16500 (p1984 p2027 p2545 p2668 p3019 p3555 p3989 p4173 : Prop) (h : (¬ p3019) ∨ (¬ p1984) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ p2545) : (¬ p1984) ∨ (p2027) ∨ (p2545) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial16500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory5804 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule16500 (meaning t m 1984) (meaning t m 2027) (meaning t m 2545) (meaning t m 2668) (meaning t m 3019) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) source

theorem rule16501 (p1987 p2027 p2764 p2946 p3292 p4040 p4315 p4322 : Prop) (h : (¬ p4040) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3292) ∨ p2764 ∨ (¬ p2946) ∨ (¬ p4322) ∨ (¬ p4315)) : (¬ p1987) ∨ (p2027) ∨ (p2764) ∨ (¬ p2946) ∨ (¬ p3292) ∨ (¬ p4040) ∨ (¬ p4315) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial16501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory5805 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule16501 (meaning t m 1987) (meaning t m 2027) (meaning t m 2764) (meaning t m 2946) (meaning t m 3292) (meaning t m 4040) (meaning t m 4315) (meaning t m 4322) source

theorem rule16502 (p1988 p2027 p2274 p2765 p3461 p3483 p3822 : Prop) (h : p2765 ∨ (¬ p3483) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3461) ∨ (¬ p2274) ∨ (¬ p3822)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial16502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory5806 t (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule16502 (meaning t m 1988) (meaning t m 2027) (meaning t m 2274) (meaning t m 2765) (meaning t m 3461) (meaning t m 3483) (meaning t m 3822) source

theorem rule16504 (p1988 p2027 p2331 p2545 p2657 p3323 p3461 : Prop) (h : p2027 ∨ (¬ p2657) ∨ (¬ p2331) ∨ (¬ p1988) ∨ p2545 ∨ (¬ p3323) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p3323) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial16504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory5808 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule16504 (meaning t m 1988) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 3323) (meaning t m 3461) source

theorem rule16506 (p1983 p2027 p2295 p2396 p2545 p2641 p4111 : Prop) (h : p2545 ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2396) ∨ (¬ p4111) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial16506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory5810 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16506 (meaning t m 1983) (meaning t m 2027) (meaning t m 2295) (meaning t m 2396) (meaning t m 2545) (meaning t m 2641) (meaning t m 4111) source

end SunPrize.SMT
