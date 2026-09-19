import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory025
import SunPrize.Certificate.Theory026
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule18714 (p1991 p2027 p2630 p2657 p2688 p2992 p4315 : Prop) (h : p2027 ∨ (¬ p1991) ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p4315) ∨ (¬ p2992) ∨ p2688) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory7986 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule18714 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2688) (meaning t m 2992) (meaning t m 4315) source

theorem rule18715 (p1981 p2027 p2331 p2622 p2630 p2657 p2668 : Prop) (h : p2622 ∨ (¬ p2630) ∨ (¬ p1981) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2668)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2331) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2668) := by
  classical
  tauto

theorem initial18715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2668)) := by
  have source := ElevenTheory.theory7987 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule18715 (meaning t m 1981) (meaning t m 2027) (meaning t m 2331) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2668) source

theorem rule18716 (p1984 p2027 p2780 p3128 p3309 p3822 p3873 p4026 : Prop) (h : (¬ p3309) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p2780) ∨ (¬ p3873) ∨ p3128 ∨ (¬ p3822)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2780) ∨ (p3128) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial18716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory7988 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule18716 (meaning t m 1984) (meaning t m 2027) (meaning t m 2780) (meaning t m 3128) (meaning t m 3309) (meaning t m 3822) (meaning t m 3873) (meaning t m 4026) source

theorem rule18717 (p1984 p2027 p2780 p2829 p3578 p3583 p3694 p3873 : Prop) (h : (¬ p2829) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p2780) ∨ (¬ p3873) ∨ p3578 ∨ (¬ p3694)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (p3578) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial18717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory7989 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 8)
  exact rule18717 (meaning t m 1984) (meaning t m 2027) (meaning t m 2780) (meaning t m 2829) (meaning t m 3578) (meaning t m 3583) (meaning t m 3694) (meaning t m 3873) source

theorem rule18720 (p2000 p2027 p2766 p3201 p3540 p3874 p4348 p4383 : Prop) (h : (¬ p3874) ∨ (¬ p3540) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p4383) ∨ (¬ p4348) ∨ p2766 ∨ (¬ p2000)) : (¬ p2000) ∨ (p2027) ∨ (p2766) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p4348) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial18720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory7992 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18720 (meaning t m 2000) (meaning t m 2027) (meaning t m 2766) (meaning t m 3201) (meaning t m 3540) (meaning t m 3874) (meaning t m 4348) (meaning t m 4383) source

theorem rule18723 (p1975 p2027 p2156 p2166 p2274 p2873 p4120 : Prop) (h : (¬ p1975) ∨ (¬ p2274) ∨ (¬ p2166) ∨ (¬ p2156) ∨ p2027 ∨ p2873 ∨ (¬ p4120)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p2274) ∨ (p2873) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial18723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory7995 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule18723 (meaning t m 1975) (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 2274) (meaning t m 2873) (meaning t m 4120) source

theorem rule18724 (p2013 p2027 p2608 p2633 p3548 p3599 p4366 : Prop) (h : (¬ p2013) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4366) ∨ (¬ p3599) ∨ (¬ p3548) ∨ p2633) : (¬ p2013) ∨ (p2027) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p3548) ∨ (¬ p3599) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2013)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory7996 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 9) (m.theta 7 8)
  exact rule18724 (meaning t m 2013) (meaning t m 2027) (meaning t m 2608) (meaning t m 2633) (meaning t m 3548) (meaning t m 3599) (meaning t m 4366) source

theorem rule18725 (p1992 p2027 p2202 p2608 p3201 p3540 p3684 p4108 : Prop) (h : (¬ p2608) ∨ (¬ p3684) ∨ p2202 ∨ (¬ p3201) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3540) ∨ (¬ p4108)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial18725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory7997 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule18725 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2608) (meaning t m 3201) (meaning t m 3540) (meaning t m 3684) (meaning t m 4108) source

theorem rule18727 (p1975 p2027 p2202 p2220 p2299 p2563 p3646 p4042 : Prop) (h : (¬ p3646) ∨ (¬ p2563) ∨ p2027 ∨ p2202 ∨ (¬ p2220) ∨ (¬ p4042) ∨ (¬ p1975) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2220) ∨ (¬ p2299) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial18727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory7999 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule18727 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2220) (meaning t m 2299) (meaning t m 2563) (meaning t m 3646) (meaning t m 4042) source

theorem rule18732 (p2000 p2027 p2122 p2169 p2579 p2588 p4358 : Prop) (h : p2169 ∨ (¬ p2579) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2000) ∨ (¬ p2588)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2122) ∨ (p2169) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial18732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory8004 t (m.theta 0 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18732 (meaning t m 2000) (meaning t m 2027) (meaning t m 2122) (meaning t m 2169) (meaning t m 2579) (meaning t m 2588) (meaning t m 4358) source

theorem rule18735 (p1990 p2027 p2247 p2688 p3063 p3399 p3989 p4105 : Prop) (h : (¬ p4105) ∨ (¬ p3063) ∨ p2688 ∨ (¬ p2247) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3063) ∨ (¬ p3399) ∨ (¬ p3989) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial18735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory8007 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 8)
  exact rule18735 (meaning t m 1990) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3063) (meaning t m 3399) (meaning t m 3989) (meaning t m 4105) source

theorem rule18738 (p1982 p2027 p2166 p2210 p2409 p3146 p3452 : Prop) (h : (¬ p2210) ∨ p2409 ∨ (¬ p3146) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p1982) ∨ (¬ p2166)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p3146) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial18738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory8010 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9)
  exact rule18738 (meaning t m 1982) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2409) (meaning t m 3146) (meaning t m 3452) source

theorem rule18739 (p2012 p2462 p4278 p4640 : Prop) (h : p2462 ∨ (¬ p4278) ∨ (¬ p2012) ∨ p4640) : (¬ p2012) ∨ (p2462) ∨ (¬ p4278) ∨ (p4640) := by
  classical
  tauto

theorem initial18739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 4278)) ∨ (meaning t m 4640) := by
  have source := ElevenTheory.theory8011 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule18739 (meaning t m 2012) (meaning t m 2462) (meaning t m 4278) (meaning t m 4640) source

theorem rule18740 (p1991 p2027 p2630 p2657 p2764 p4035 p4425 p5171 : Prop) (h : p2027 ∨ (¬ p4425) ∨ (¬ p4035) ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p1991) ∨ (¬ p5171) ∨ p2764) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p4035) ∨ (¬ p4425) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial18740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory8012 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule18740 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2764) (meaning t m 4035) (meaning t m 4425) (meaning t m 5171) source

theorem rule18742 (p1976 p2027 p2202 p2440 p3016 p3055 p3584 : Prop) (h : p2202 ∨ (¬ p1976) ∨ (¬ p2440) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3584)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3055) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial18742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory8014 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule18742 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3016) (meaning t m 3055) (meaning t m 3584) source

theorem rule18743 (p1985 p2027 p2388 p2685 p3516 p3690 p4066 p4315 : Prop) (h : p2027 ∨ (¬ p2685) ∨ (¬ p1985) ∨ (¬ p3516) ∨ p2388 ∨ (¬ p4066) ∨ (¬ p3690) ∨ (¬ p4315)) : (¬ p1985) ∨ (p2027) ∨ (p2388) ∨ (¬ p2685) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4066) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8015 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule18743 (meaning t m 1985) (meaning t m 2027) (meaning t m 2388) (meaning t m 2685) (meaning t m 3516) (meaning t m 3690) (meaning t m 4066) (meaning t m 4315) source

theorem rule18744 (p1991 p2027 p2202 p2657 p3333 p3359 p3684 : Prop) (h : (¬ p3359) ∨ (¬ p1991) ∨ (¬ p2657) ∨ p2027 ∨ p2202 ∨ (¬ p3684) ∨ (¬ p3333)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2657) ∨ (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial18744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory8016 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule18744 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2657) (meaning t m 3333) (meaning t m 3359) (meaning t m 3684) source

theorem rule18745 (p1990 p2027 p2307 p2388 p2797 p3097 p3567 p4315 : Prop) (h : p2027 ∨ (¬ p1990) ∨ (¬ p3567) ∨ (¬ p4315) ∨ (¬ p2307) ∨ (¬ p3097) ∨ p2388 ∨ (¬ p2797)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (p2388) ∨ (¬ p2797) ∨ (¬ p3097) ∨ (¬ p3567) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8017 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule18745 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2388) (meaning t m 2797) (meaning t m 3097) (meaning t m 3567) (meaning t m 4315) source

theorem rule18746 (p1976 p2027 p2299 p2633 p3414 p3791 p4236 p4391 : Prop) (h : (¬ p2299) ∨ (¬ p1976) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p3791) ∨ (¬ p3414) ∨ p2633 ∨ (¬ p4391)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3414) ∨ (¬ p3791) ∨ (¬ p4236) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial18746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory8018 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule18746 (meaning t m 1976) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3414) (meaning t m 3791) (meaning t m 4236) (meaning t m 4391) source

theorem rule18747 (p1983 p2027 p2542 p2545 p2589 p3246 p3389 p3569 : Prop) (h : (¬ p2542) ∨ (¬ p2589) ∨ p2545 ∨ (¬ p3389) ∨ p2027 ∨ (¬ p3569) ∨ (¬ p3246) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p3246) ∨ (¬ p3389) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial18747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory8019 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule18747 (meaning t m 1983) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 3246) (meaning t m 3389) (meaning t m 3569) source

theorem rule18748 (p1982 p2027 p2470 p2531 p2542 p2545 p2589 p3146 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p2589) ∨ (¬ p3146) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2531) ∨ p2545) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2589) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial18748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory8020 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18748 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2531) (meaning t m 2542) (meaning t m 2545) (meaning t m 2589) (meaning t m 3146) source

theorem rule18749 (p1982 p2027 p2156 p2187 p2363 p2764 p2810 p3359 p3365 p3366 p3370 p4377 p4425 : Prop) (h : (¬ p2156) ∨ (¬ p1982) ∨ (¬ p2810) ∨ (¬ p3370) ∨ (¬ p3365) ∨ (¬ p3359) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p2363) ∨ p2764 ∨ (¬ p4425)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial18749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory8021 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18749 (meaning t m 1982) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2764) (meaning t m 2810) (meaning t m 3359) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 4377) (meaning t m 4425) source

theorem rule18750 (p2015 p2027 p2307 p2388 p2797 p3549 p3567 p4315 : Prop) (h : (¬ p2015) ∨ p2027 ∨ p2388 ∨ (¬ p4315) ∨ (¬ p3567) ∨ (¬ p2797) ∨ (¬ p2307) ∨ (¬ p3549)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2307) ∨ (p2388) ∨ (¬ p2797) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8022 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule18750 (meaning t m 2015) (meaning t m 2027) (meaning t m 2307) (meaning t m 2388) (meaning t m 2797) (meaning t m 3549) (meaning t m 3567) (meaning t m 4315) source

theorem rule18751 (p1982 p2027 p2363 p2383 p2388 p2797 p3567 p4315 : Prop) (h : (¬ p3567) ∨ (¬ p2797) ∨ p2388 ∨ (¬ p2383) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p2363) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (p2388) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial18751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8023 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18751 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2388) (meaning t m 2797) (meaning t m 3567) (meaning t m 4315) source

theorem rule18752 (p1996 p2027 p2545 p2797 p2807 p2810 p2963 : Prop) (h : p2027 ∨ (¬ p1996) ∨ (¬ p2810) ∨ p2545 ∨ (¬ p2807) ∨ (¬ p2797) ∨ (¬ p2963)) : (¬ p1996) ∨ (p2027) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p2810) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial18752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory8024 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule18752 (meaning t m 1996) (meaning t m 2027) (meaning t m 2545) (meaning t m 2797) (meaning t m 2807) (meaning t m 2810) (meaning t m 2963) source

theorem rule18755 (p1982 p2027 p2388 p3005 p3171 p3680 p4315 p4374 p4387 p4444 p4461 : Prop) (h : (¬ p4315) ∨ p2388 ∨ (¬ p3005) ∨ (¬ p4374) ∨ p2027 ∨ (¬ p3171) ∨ (¬ p4461) ∨ (¬ p1982) ∨ (¬ p4387) ∨ (¬ p4444) ∨ (¬ p3680)) : (¬ p1982) ∨ (p2027) ∨ (p2388) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3680) ∨ (¬ p4315) ∨ (¬ p4374) ∨ (¬ p4387) ∨ (¬ p4444) ∨ (¬ p4461) := by
  classical
  tauto

theorem initial18755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4374)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4461)) := by
  have source := ElevenTheory.theory8027 t (m.theta 0 8) (m.theta 0 9) (m.theta 1 9) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18755 (meaning t m 1982) (meaning t m 2027) (meaning t m 2388) (meaning t m 3005) (meaning t m 3171) (meaning t m 3680) (meaning t m 4315) (meaning t m 4374) (meaning t m 4387) (meaning t m 4444) (meaning t m 4461) source

theorem rule18759 (p1991 p2027 p2685 p2764 p3414 p4035 p5284 : Prop) (h : (¬ p3414) ∨ (¬ p1991) ∨ (¬ p4035) ∨ p2027 ∨ p2764 ∨ (¬ p5284) ∨ (¬ p2685)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2685) ∨ (p2764) ∨ (¬ p3414) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial18759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory8031 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 9 10)
  exact rule18759 (meaning t m 1991) (meaning t m 2027) (meaning t m 2685) (meaning t m 2764) (meaning t m 3414) (meaning t m 4035) (meaning t m 5284) source

theorem rule18763 (p1990 p2027 p2169 p3097 p3923 p4075 p4260 p4452 : Prop) (h : p2169 ∨ (¬ p4075) ∨ (¬ p3923) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p4260) ∨ (¬ p4452)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p3097) ∨ (¬ p3923) ∨ (¬ p4075) ∨ (¬ p4260) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial18763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory8035 t (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule18763 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 3097) (meaning t m 3923) (meaning t m 4075) (meaning t m 4260) (meaning t m 4452) source

theorem rule18764 (p3544 p3860 p4366 : Prop) (h : (¬ p3544) ∨ (¬ p4366) ∨ p3860) : (¬ p3544) ∨ (p3860) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3544)) ∨ (meaning t m 3860) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8036 (m.theta 0 1) (m.theta 1 7) (m.theta 1 8)
  exact rule18764 (meaning t m 3544) (meaning t m 3860) (meaning t m 4366) source

theorem rule18765 (p1985 p2027 p2233 p2383 p2417 p2584 p3690 p3920 p3956 : Prop) (h : (¬ p2584) ∨ (¬ p3690) ∨ p2027 ∨ p2233 ∨ (¬ p1985) ∨ (¬ p2383) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p2417)) : (¬ p1985) ∨ (p2027) ∨ (p2233) ∨ (¬ p2383) ∨ (¬ p2417) ∨ (¬ p2584) ∨ (¬ p3690) ∨ (¬ p3920) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial18765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory8037 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9)
  exact rule18765 (meaning t m 1985) (meaning t m 2027) (meaning t m 2233) (meaning t m 2383) (meaning t m 2417) (meaning t m 2584) (meaning t m 3690) (meaning t m 3920) (meaning t m 3956) source

theorem rule18766 (p1988 p2027 p2148 p2156 p2187 p2363 p3266 : Prop) (h : p2148 ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial18766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory8038 t (m.theta 0 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule18766 (meaning t m 1988) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3266) source

theorem rule18770 (p1992 p2027 p2608 p2717 p3474 p3548 p3587 p4366 : Prop) (h : p3474 ∨ (¬ p3548) ∨ (¬ p1992) ∨ (¬ p4366) ∨ (¬ p2608) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3587)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2717) ∨ (p3474) ∨ (¬ p3548) ∨ (¬ p3587) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8042 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8)
  exact rule18770 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2717) (meaning t m 3474) (meaning t m 3548) (meaning t m 3587) (meaning t m 4366) source

theorem rule18771 (p1999 p2027 p2344 p2383 p3125 p3979 p3988 p5568 : Prop) (h : (¬ p1999) ∨ (¬ p3988) ∨ (¬ p3125) ∨ p2344 ∨ p2027 ∨ (¬ p5568) ∨ (¬ p2383) ∨ (¬ p3979)) : (¬ p1999) ∨ (p2027) ∨ (p2344) ∨ (¬ p2383) ∨ (¬ p3125) ∨ (¬ p3979) ∨ (¬ p3988) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial18771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory8043 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule18771 (meaning t m 1999) (meaning t m 2027) (meaning t m 2344) (meaning t m 2383) (meaning t m 3125) (meaning t m 3979) (meaning t m 3988) (meaning t m 5568) source

theorem rule18773 (p1984 p3818 p3954 p4866 : Prop) (h : p3818 ∨ p4866 ∨ (¬ p1984) ∨ (¬ p3954)) : (¬ p1984) ∨ (p3818) ∨ (¬ p3954) ∨ (p4866) := by
  classical
  tauto

theorem initial18773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3954)) ∨ (meaning t m 4866) := by
  have source := ElevenTheory.theory8045 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6)
  exact rule18773 (meaning t m 1984) (meaning t m 3818) (meaning t m 3954) (meaning t m 4866) source

theorem rule18774 (p1982 p2027 p2352 p2363 p2573 p2622 p2630 p2656 : Prop) (h : (¬ p2352) ∨ (¬ p1982) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2656) ∨ p2622 ∨ (¬ p2630)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) := by
  classical
  tauto

theorem initial18774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) := by
  have source := ElevenTheory.theory8046 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18774 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) source

theorem rule18775 (p1975 p2027 p2383 p2553 p2622 p2797 p3956 p4319 p5016 : Prop) (h : (¬ p4319) ∨ (¬ p2383) ∨ (¬ p3956) ∨ p2622 ∨ (¬ p2797) ∨ (¬ p5016) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3956) ∨ (¬ p4319) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial18775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory8047 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18775 (meaning t m 1975) (meaning t m 2027) (meaning t m 2383) (meaning t m 2553) (meaning t m 2622) (meaning t m 2797) (meaning t m 3956) (meaning t m 4319) (meaning t m 5016) source

theorem rule18780 (p1982 p2027 p2230 p2373 p2622 p2630 p2656 p3146 : Prop) (h : p2027 ∨ (¬ p2230) ∨ p2622 ∨ (¬ p2656) ∨ (¬ p2373) ∨ (¬ p2630) ∨ (¬ p1982) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial18780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory8052 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule18780 (meaning t m 1982) (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3146) source

theorem rule18781 (p1991 p2027 p2417 p2633 p3414 p3644 p3947 : Prop) (h : p2027 ∨ (¬ p3414) ∨ p2633 ∨ (¬ p1991) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p2417)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial18781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory8053 t (m.theta 0 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18781 (meaning t m 1991) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 3414) (meaning t m 3644) (meaning t m 3947) source

theorem rule18782 (p1991 p2027 p2630 p2633 p2657 p3553 p3572 : Prop) (h : (¬ p3572) ∨ (¬ p2630) ∨ p2633 ∨ (¬ p1991) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3553)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial18782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory8054 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule18782 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2633) (meaning t m 2657) (meaning t m 3553) (meaning t m 3572) source

theorem rule18783 (p1991 p2027 p2462 p2911 p3414 p3553 p4278 : Prop) (h : (¬ p3414) ∨ (¬ p3553) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p2911) ∨ p2462 ∨ (¬ p4278)) : (¬ p1991) ∨ (p2027) ∨ (p2462) ∨ (¬ p2911) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial18783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory8055 t (m.theta 0 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18783 (meaning t m 1991) (meaning t m 2027) (meaning t m 2462) (meaning t m 2911) (meaning t m 3414) (meaning t m 3553) (meaning t m 4278) source

theorem rule18786 (p2510 p3422 p3641 : Prop) (h : (¬ p3422) ∨ (¬ p2510) ∨ p3641) : (¬ p2510) ∨ (¬ p3422) ∨ (p3641) := by
  classical
  tauto

theorem initial18786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 3422)) ∨ (meaning t m 3641) := by
  have source := ElevenTheory.theory8058 (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule18786 (meaning t m 2510) (meaning t m 3422) (meaning t m 3641) source

theorem rule18787 (p3201 p3422 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3422) ∨ p3201) : (p3201) ∨ (¬ p3422) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial18787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3201) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory8059 (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule18787 (meaning t m 3201) (meaning t m 3422) (meaning t m 3920) source

theorem rule18789 (p1998 p2027 p2873 p3073 p3449 p3555 p4348 : Prop) (h : (¬ p3555) ∨ p2027 ∨ p2873 ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p1998) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (p2873) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial18789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8061 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18789 (meaning t m 1998) (meaning t m 2027) (meaning t m 2873) (meaning t m 3073) (meaning t m 3449) (meaning t m 3555) (meaning t m 4348) source

theorem rule18790 (p1982 p2027 p2518 p2528 p2873 p3379 p3555 : Prop) (h : (¬ p1982) ∨ (¬ p2528) ∨ (¬ p3555) ∨ (¬ p3379) ∨ p2027 ∨ p2873 ∨ (¬ p2518)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2873) ∨ (¬ p3379) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial18790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory8062 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8) (m.theta 8 9)
  exact rule18790 (meaning t m 1982) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2873) (meaning t m 3379) (meaning t m 3555) source

theorem rule18792 (p1976 p2027 p2630 p2657 p2911 p2914 p3877 p4236 p4548 : Prop) (h : (¬ p4548) ∨ p2914 ∨ (¬ p2657) ∨ (¬ p2911) ∨ (¬ p4236) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3877)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial18792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory8064 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule18792 (meaning t m 1976) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2911) (meaning t m 2914) (meaning t m 3877) (meaning t m 4236) (meaning t m 4548) source

theorem rule18810 (p1982 p2027 p2156 p2187 p2363 p3008 p3055 p3343 p3366 p3370 p3574 p4377 p5160 : Prop) (h : (¬ p1982) ∨ (¬ p3055) ∨ (¬ p3574) ∨ p3008 ∨ (¬ p3366) ∨ (¬ p2156) ∨ (¬ p4377) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p3370) ∨ (¬ p3343) ∨ (¬ p5160)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (p3008) ∨ (¬ p3055) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3574) ∨ (¬ p4377) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial18810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory8066 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule18810 (meaning t m 1982) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3008) (meaning t m 3055) (meaning t m 3343) (meaning t m 3366) (meaning t m 3370) (meaning t m 3574) (meaning t m 4377) (meaning t m 5160) source

theorem rule18812 (p1975 p2027 p2417 p3008 p3201 p3574 p4107 p4343 : Prop) (h : (¬ p3574) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2417) ∨ p3008 ∨ (¬ p1975) ∨ (¬ p4343) ∨ (¬ p3201)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2417) ∨ (p3008) ∨ (¬ p3201) ∨ (¬ p3574) ∨ (¬ p4107) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial18812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory8068 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule18812 (meaning t m 1975) (meaning t m 2027) (meaning t m 2417) (meaning t m 3008) (meaning t m 3201) (meaning t m 3574) (meaning t m 4107) (meaning t m 4343) source

theorem rule18818 (p1976 p2027 p2630 p2657 p3877 p3982 p4236 p4286 p4437 : Prop) (h : (¬ p4286) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4236) ∨ (¬ p2657) ∨ p3982 ∨ (¬ p3877) ∨ (¬ p4437)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (p3982) ∨ (¬ p4236) ∨ (¬ p4286) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial18818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3877)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory8074 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 10)
  exact rule18818 (meaning t m 1976) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 3877) (meaning t m 3982) (meaning t m 4236) (meaning t m 4286) (meaning t m 4437) source

theorem rule18820 (p1976 p2027 p2534 p2766 p3172 p4149 p4236 p5600 : Prop) (h : (¬ p4236) ∨ (¬ p1976) ∨ (¬ p3172) ∨ (¬ p4149) ∨ p2766 ∨ (¬ p2534) ∨ p2027 ∨ (¬ p5600)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p4149) ∨ (¬ p4236) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial18820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory8076 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule18820 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2766) (meaning t m 3172) (meaning t m 4149) (meaning t m 4236) (meaning t m 5600) source

theorem rule18823 (p1981 p2027 p2388 p3005 p4009 p4315 p5580 : Prop) (h : (¬ p4315) ∨ (¬ p1981) ∨ p2027 ∨ p2388 ∨ (¬ p3005) ∨ (¬ p5580) ∨ (¬ p4009)) : (¬ p1981) ∨ (p2027) ∨ (p2388) ∨ (¬ p3005) ∨ (¬ p4009) ∨ (¬ p4315) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial18823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory8079 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 8) (m.theta 8 10)
  exact rule18823 (meaning t m 1981) (meaning t m 2027) (meaning t m 2388) (meaning t m 3005) (meaning t m 4009) (meaning t m 4315) (meaning t m 5580) source

theorem rule18824 (p1993 p2027 p2287 p2630 p2657 p3166 p4195 : Prop) (h : p2287 ∨ (¬ p3166) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p1993)) : (¬ p1993) ∨ (p2027) ∨ (p2287) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial18824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory8080 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule18824 (meaning t m 1993) (meaning t m 2027) (meaning t m 2287) (meaning t m 2630) (meaning t m 2657) (meaning t m 3166) (meaning t m 4195) source

theorem rule18825 (p1976 p2027 p2657 p2766 p3266 p3683 p4236 p4425 p5160 : Prop) (h : (¬ p2657) ∨ (¬ p5160) ∨ p2766 ∨ p2027 ∨ (¬ p4236) ∨ (¬ p1976) ∨ (¬ p3266) ∨ (¬ p4425) ∨ (¬ p3683)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3683) ∨ (¬ p4236) ∨ (¬ p4425) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial18825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory8081 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18825 (meaning t m 1976) (meaning t m 2027) (meaning t m 2657) (meaning t m 2766) (meaning t m 3266) (meaning t m 3683) (meaning t m 4236) (meaning t m 4425) (meaning t m 5160) source

theorem rule18826 (p2002 p2027 p2743 p2766 p2829 p3877 p4118 : Prop) (h : (¬ p2829) ∨ (¬ p2002) ∨ (¬ p4118) ∨ p2766 ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2743)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p2829) ∨ (¬ p3877) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial18826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory8082 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 8) (m.theta 8 9)
  exact rule18826 (meaning t m 2002) (meaning t m 2027) (meaning t m 2743) (meaning t m 2766) (meaning t m 2829) (meaning t m 3877) (meaning t m 4118) source

theorem rule18828 (p1983 p2027 p2202 p2264 p2417 p2440 p3551 p3580 p4279 : Prop) (h : (¬ p2440) ∨ p2027 ∨ (¬ p2417) ∨ p2202 ∨ (¬ p3580) ∨ (¬ p3551) ∨ (¬ p1983) ∨ (¬ p4279) ∨ (¬ p2264)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2264) ∨ (¬ p2417) ∨ (¬ p2440) ∨ (¬ p3551) ∨ (¬ p3580) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial18828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory8084 t (m.theta 0 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18828 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2264) (meaning t m 2417) (meaning t m 2440) (meaning t m 3551) (meaning t m 3580) (meaning t m 4279) source

theorem rule18830 (p1976 p2027 p2911 p2914 p3365 p3553 p3572 : Prop) (h : p2914 ∨ (¬ p3572) ∨ (¬ p1976) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2911)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial18830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory8086 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule18830 (meaning t m 1976) (meaning t m 2027) (meaning t m 2911) (meaning t m 2914) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) source

theorem rule18832 (p1988 p2027 p2156 p2622 p2951 p3125 p3136 p3461 : Prop) (h : (¬ p2951) ∨ (¬ p1988) ∨ (¬ p3136) ∨ (¬ p2156) ∨ p2622 ∨ p2027 ∨ (¬ p3125) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2156) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3125) ∨ (¬ p3136) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial18832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory8088 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule18832 (meaning t m 1988) (meaning t m 2027) (meaning t m 2156) (meaning t m 2622) (meaning t m 2951) (meaning t m 3125) (meaning t m 3136) (meaning t m 3461) source

theorem rule18835 (p1975 p2027 p2274 p2383 p2622 p2951 p2962 p3136 p3989 : Prop) (h : (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2383) ∨ (¬ p3989) ∨ p2622 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2383) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p3136) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial18835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8091 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18835 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2383) (meaning t m 2622) (meaning t m 2951) (meaning t m 2962) (meaning t m 3136) (meaning t m 3989) source

theorem rule18843 (p2002 p2545 p2810 p4845 : Prop) (h : (¬ p2002) ∨ (¬ p2810) ∨ p4845 ∨ p2545) : (¬ p2002) ∨ (p2545) ∨ (¬ p2810) ∨ (p4845) := by
  classical
  tauto

theorem initial18843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 4845) := by
  have source := ElevenTheory.theory8099 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule18843 (meaning t m 2002) (meaning t m 2545) (meaning t m 2810) (meaning t m 4845) source

theorem rule18845 (p1976 p2027 p2997 p3323 p3365 p3568 p3917 p4841 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p3917) ∨ p2997 ∨ (¬ p3568) ∨ (¬ p4841) ∨ (¬ p3323) ∨ (¬ p3365)) : (¬ p1976) ∨ (p2027) ∨ (p2997) ∨ (¬ p3323) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p3917) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial18845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory8101 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule18845 (meaning t m 1976) (meaning t m 2027) (meaning t m 2997) (meaning t m 3323) (meaning t m 3365) (meaning t m 3568) (meaning t m 3917) (meaning t m 4841) source

theorem rule18847 (p1985 p2027 p2220 p2427 p2608 p3042 p3519 p3755 p3834 p3847 p3877 p3880 p4376 p4399 : Prop) (h : p3042 ∨ (¬ p3877) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2608) ∨ (¬ p3834) ∨ (¬ p2427) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p3880) ∨ (¬ p2220) ∨ (¬ p4399) ∨ (¬ p3847)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (p3042) ∨ (¬ p3519) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p3877) ∨ (¬ p3880) ∨ (¬ p4376) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial18847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory8103 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule18847 (meaning t m 1985) (meaning t m 2027) (meaning t m 2220) (meaning t m 2427) (meaning t m 2608) (meaning t m 3042) (meaning t m 3519) (meaning t m 3755) (meaning t m 3834) (meaning t m 3847) (meaning t m 3877) (meaning t m 3880) (meaning t m 4376) (meaning t m 4399) source

theorem rule18850 (p1990 p2027 p2220 p2462 p2563 p2963 p3366 p3519 p3791 p3880 p4067 p4107 p4236 p4376 p4391 p4399 : Prop) (h : (¬ p3519) ∨ p2462 ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2220) ∨ (¬ p4399) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4391) ∨ (¬ p3791) ∨ (¬ p4067)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2220) ∨ (p2462) ∨ (¬ p2563) ∨ (¬ p2963) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p3880) ∨ (¬ p4067) ∨ (¬ p4107) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4391) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial18850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory8106 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule18850 (meaning t m 1990) (meaning t m 2027) (meaning t m 2220) (meaning t m 2462) (meaning t m 2563) (meaning t m 2963) (meaning t m 3366) (meaning t m 3519) (meaning t m 3791) (meaning t m 3880) (meaning t m 4067) (meaning t m 4107) (meaning t m 4236) (meaning t m 4376) (meaning t m 4391) (meaning t m 4399) source

theorem rule18851 (p1982 p2027 p2459 p2873 p2881 p3399 p3555 p3571 : Prop) (h : p2873 ∨ (¬ p3571) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2459) ∨ (¬ p1982) ∨ (¬ p2881) ∨ (¬ p3399)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2873) ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) := by
  classical
  tauto

theorem initial18851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) := by
  have source := ElevenTheory.theory8107 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18851 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2873) (meaning t m 2881) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) source

theorem rule18853 (p1976 p2027 p2579 p2655 p2914 p3019 p3742 p4228 p4236 p5514 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p3742) ∨ (¬ p4228) ∨ (¬ p2579) ∨ p2914 ∨ (¬ p2655) ∨ (¬ p3019) ∨ (¬ p5514)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (p2914) ∨ (¬ p3019) ∨ (¬ p3742) ∨ (¬ p4228) ∨ (¬ p4236) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial18853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory8109 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule18853 (meaning t m 1976) (meaning t m 2027) (meaning t m 2579) (meaning t m 2655) (meaning t m 2914) (meaning t m 3019) (meaning t m 3742) (meaning t m 4228) (meaning t m 4236) (meaning t m 5514) source

theorem rule18854 (p1992 p2027 p2247 p2608 p2997 p3568 p4154 : Prop) (h : p2027 ∨ (¬ p1992) ∨ p2997 ∨ (¬ p4154) ∨ (¬ p2608) ∨ (¬ p3568) ∨ (¬ p2247)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial18854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory8110 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7)
  exact rule18854 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2997) (meaning t m 3568) (meaning t m 4154) source

theorem rule18858 (p2459 p3550 p4347 : Prop) (h : (¬ p2459) ∨ (¬ p4347) ∨ (¬ p3550)) : (¬ p2459) ∨ (¬ p3550) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory8114 (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18858 (meaning t m 2459) (meaning t m 3550) (meaning t m 4347) source

theorem rule18859 (p1989 p2027 p2388 p3051 p3156 p3486 p4120 : Prop) (h : (¬ p1989) ∨ p2027 ∨ (¬ p4120) ∨ p2388 ∨ (¬ p3486) ∨ (¬ p3051) ∨ (¬ p3156)) : (¬ p1989) ∨ (p2027) ∨ (p2388) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3486) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial18859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory8115 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule18859 (meaning t m 1989) (meaning t m 2027) (meaning t m 2388) (meaning t m 3051) (meaning t m 3156) (meaning t m 3486) (meaning t m 4120) source

theorem rule18868 (p2005 p2542 p2545 p4717 : Prop) (h : p2545 ∨ (¬ p2005) ∨ (¬ p2542) ∨ p4717) : (¬ p2005) ∨ (¬ p2542) ∨ (p2545) ∨ (p4717) := by
  classical
  tauto

theorem initial18868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (meaning t m 4717) := by
  have source := ElevenTheory.theory8124 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule18868 (meaning t m 2005) (meaning t m 2542) (meaning t m 2545) (meaning t m 4717) source

theorem rule18870 (p2210 p3449 p4496 : Prop) (h : (¬ p4496) ∨ (¬ p2210) ∨ p3449) : (¬ p2210) ∨ (p3449) ∨ (¬ p4496) := by
  classical
  tauto

theorem initial18870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (meaning t m 3449) ∨ (¬ (meaning t m 4496)) := by
  have source := ElevenTheory.theory8126 (m.theta 0 1) (m.theta 1 5) (m.theta 1 8)
  exact rule18870 (meaning t m 2210) (meaning t m 3449) (meaning t m 4496) source

theorem rule18872 (p1990 p2027 p2545 p2668 p2797 p2810 p3989 : Prop) (h : (¬ p2668) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3989) ∨ p2545 ∨ (¬ p2810) ∨ (¬ p2797)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial18872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8128 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule18872 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2668) (meaning t m 2797) (meaning t m 2810) (meaning t m 3989) source

theorem rule18873 (p1990 p2027 p2545 p2668 p2810 p3136 p3989 p4336 : Prop) (h : p2545 ∨ (¬ p4336) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2810) ∨ (¬ p3989) ∨ (¬ p3136)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2668) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3989) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial18873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory8129 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule18873 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2668) (meaning t m 2810) (meaning t m 3136) (meaning t m 3989) (meaning t m 4336) source

theorem rule18876 (p1985 p2027 p2191 p2220 p2765 p2891 p3646 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p2891) ∨ (¬ p3646) ∨ (¬ p1985) ∨ (¬ p2220) ∨ (¬ p2191)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (p2765) ∨ (¬ p2891) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial18876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory8132 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule18876 (meaning t m 1985) (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 2765) (meaning t m 2891) (meaning t m 3646) source

theorem rule18878 (p1977 p2210 p2699 p4448 : Prop) (h : (¬ p1977) ∨ (¬ p2210) ∨ p2699 ∨ p4448) : (¬ p1977) ∨ (¬ p2210) ∨ (p2699) ∨ (p4448) := by
  classical
  tauto

theorem initial18878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (meaning t m 4448) := by
  have source := ElevenTheory.theory8134 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5)
  exact rule18878 (meaning t m 1977) (meaning t m 2210) (meaning t m 2699) (meaning t m 4448) source

theorem rule18882 (p1981 p2027 p2247 p2688 p3073 p3449 p4347 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2247) ∨ (¬ p1981) ∨ (¬ p3073) ∨ (¬ p3449)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial18882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory8138 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule18882 (meaning t m 1981) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3073) (meaning t m 3449) (meaning t m 4347) source

theorem rule18883 (p1977 p3474 p3662 p5053 : Prop) (h : (¬ p3662) ∨ p3474 ∨ p5053 ∨ (¬ p1977)) : (¬ p1977) ∨ (p3474) ∨ (¬ p3662) ∨ (p5053) := by
  classical
  tauto

theorem initial18883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3662)) ∨ (meaning t m 5053) := by
  have source := ElevenTheory.theory8139 t (m.theta 1 3) (m.theta 2 5) (m.theta 3 5)
  exact rule18883 (meaning t m 1977) (meaning t m 3474) (meaning t m 3662) (meaning t m 5053) source

theorem rule18884 (p1996 p2914 p3742 p4652 : Prop) (h : p2914 ∨ (¬ p3742) ∨ (¬ p1996) ∨ p4652) : (¬ p1996) ∨ (p2914) ∨ (¬ p3742) ∨ (p4652) := by
  classical
  tauto

theorem initial18884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3742)) ∨ (meaning t m 4652) := by
  have source := ElevenTheory.theory8140 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule18884 (meaning t m 1996) (meaning t m 2914) (meaning t m 3742) (meaning t m 4652) source

theorem rule18885 (p1990 p2027 p2253 p2699 p2946 p3097 p3309 p3662 p4759 : Prop) (h : (¬ p1990) ∨ (¬ p3097) ∨ (¬ p3309) ∨ p2699 ∨ p2027 ∨ (¬ p4759) ∨ (¬ p3662) ∨ (¬ p2946) ∨ (¬ p2253)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2253) ∨ (p2699) ∨ (¬ p2946) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3662) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial18885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory8141 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule18885 (meaning t m 1990) (meaning t m 2027) (meaning t m 2253) (meaning t m 2699) (meaning t m 2946) (meaning t m 3097) (meaning t m 3309) (meaning t m 3662) (meaning t m 4759) source

theorem rule18886 (p1994 p2027 p2619 p2727 p3474 p3497 p3662 : Prop) (h : (¬ p3497) ∨ (¬ p1994) ∨ p3474 ∨ p2027 ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p2619)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2619) ∨ (¬ p2727) ∨ (p3474) ∨ (¬ p3497) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial18886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory8142 t (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule18886 (meaning t m 1994) (meaning t m 2027) (meaning t m 2619) (meaning t m 2727) (meaning t m 3474) (meaning t m 3497) (meaning t m 3662) source

theorem rule18888 (p1989 p2027 p2764 p3051 p3486 p4032 p4322 : Prop) (h : (¬ p3051) ∨ (¬ p1989) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p4322) ∨ p2764 ∨ (¬ p4032)) : (¬ p1989) ∨ (p2027) ∨ (p2764) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4032) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial18888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory8144 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule18888 (meaning t m 1989) (meaning t m 2027) (meaning t m 2764) (meaning t m 3051) (meaning t m 3486) (meaning t m 4032) (meaning t m 4322) source

theorem rule18889 (p1997 p2027 p2241 p2542 p2699 p2922 p3742 p4281 : Prop) (h : (¬ p2241) ∨ p2699 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4281)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2542) ∨ (p2699) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial18889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory8145 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule18889 (meaning t m 1997) (meaning t m 2027) (meaning t m 2241) (meaning t m 2542) (meaning t m 2699) (meaning t m 2922) (meaning t m 3742) (meaning t m 4281) source

theorem rule18891 (p2210 p3399 p4431 : Prop) (h : (¬ p2210) ∨ (¬ p4431) ∨ p3399) : (¬ p2210) ∨ (p3399) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial18891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (meaning t m 3399) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory8147 (m.theta 0 1) (m.theta 1 5) (m.theta 1 7)
  exact rule18891 (meaning t m 2210) (meaning t m 3399) (meaning t m 4431) source

theorem rule18892 (p1994 p2027 p2202 p2563 p2727 p3662 p3952 : Prop) (h : (¬ p1994) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p2727) ∨ p2202 ∨ (¬ p3662) ∨ (¬ p3952)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial18892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory8148 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule18892 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2727) (meaning t m 3662) (meaning t m 3952) source

theorem rule18893 (p1985 p2027 p2323 p2901 p2992 p3166 p4360 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2901) ∨ (¬ p1985) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p2992)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial18893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory8149 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7)
  exact rule18893 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2901) (meaning t m 2992) (meaning t m 3166) (meaning t m 4360) source

theorem rule18896 (p2027 p2295 p2850 p3097 p3426 p3879 p4336 p4401 p5085 : Prop) (h : (¬ p3879) ∨ (¬ p4336) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p4401) ∨ (¬ p3097) ∨ (¬ p3426) ∨ (¬ p2295) ∨ p5085) : (p2027) ∨ (¬ p2295) ∨ (¬ p2850) ∨ (¬ p3097) ∨ (¬ p3426) ∨ (¬ p3879) ∨ (¬ p4336) ∨ (¬ p4401) ∨ (p5085) := by
  classical
  tauto

theorem initial18896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4401)) ∨ (meaning t m 5085) := by
  have source := ElevenTheory.theory8152 t (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule18896 (meaning t m 2027) (meaning t m 2295) (meaning t m 2850) (meaning t m 3097) (meaning t m 3426) (meaning t m 3879) (meaning t m 4336) (meaning t m 4401) (meaning t m 5085) source

theorem rule18897 (p1982 p2528 p2633 p4420 : Prop) (h : (¬ p1982) ∨ p2633 ∨ (¬ p2528) ∨ p4420) : (¬ p1982) ∨ (¬ p2528) ∨ (p2633) ∨ (p4420) := by
  classical
  tauto

theorem initial18897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2633) ∨ (meaning t m 4420) := by
  have source := ElevenTheory.theory8153 t (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule18897 (meaning t m 1982) (meaning t m 2528) (meaning t m 2633) (meaning t m 4420) source

theorem rule18898 (p1982 p2027 p2409 p2528 p2922 p3083 p3742 : Prop) (h : p2409 ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3083) ∨ (¬ p3742) ∨ (¬ p1982) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (p2409) ∨ (¬ p2528) ∨ (¬ p2922) ∨ (¬ p3083) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial18898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory8154 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule18898 (meaning t m 1982) (meaning t m 2027) (meaning t m 2409) (meaning t m 2528) (meaning t m 2922) (meaning t m 3083) (meaning t m 3742) source

theorem rule18900 (p1982 p2027 p2202 p2563 p3146 p3156 p3952 : Prop) (h : (¬ p1982) ∨ (¬ p3146) ∨ (¬ p3156) ∨ p2202 ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2563)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial18900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory8156 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule18900 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3146) (meaning t m 3156) (meaning t m 3952) source

theorem rule18901 (p1982 p2027 p2355 p2992 p2996 p3146 p3156 : Prop) (h : (¬ p3156) ∨ (¬ p2992) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3146) ∨ p2355 ∨ (¬ p2996)) : (¬ p1982) ∨ (p2027) ∨ (p2355) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial18901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory8157 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 8) (m.theta 8 9)
  exact rule18901 (meaning t m 1982) (meaning t m 2027) (meaning t m 2355) (meaning t m 2992) (meaning t m 2996) (meaning t m 3146) (meaning t m 3156) source

theorem rule18903 (p1985 p2027 p2373 p2842 p2850 p2901 p3497 : Prop) (h : p2027 ∨ (¬ p1985) ∨ (¬ p3497) ∨ (¬ p2901) ∨ p2842 ∨ (¬ p2373) ∨ (¬ p2850)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2373) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p2901) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial18903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory8159 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule18903 (meaning t m 1985) (meaning t m 2027) (meaning t m 2373) (meaning t m 2842) (meaning t m 2850) (meaning t m 2901) (meaning t m 3497) source

theorem rule18906 (p1992 p2027 p2191 p2388 p2608 p3156 p3555 : Prop) (h : (¬ p2608) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p1992) ∨ p2388 ∨ (¬ p2191)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2191) ∨ (p2388) ∨ (¬ p2608) ∨ (¬ p3156) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial18906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory8162 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 3 5) (m.theta 5 8)
  exact rule18906 (meaning t m 1992) (meaning t m 2027) (meaning t m 2191) (meaning t m 2388) (meaning t m 2608) (meaning t m 3156) (meaning t m 3555) source

theorem rule18907 (p2011 p2233 p3516 p4395 p5201 : Prop) (h : p2233 ∨ (¬ p3516) ∨ p4395 ∨ (¬ p2011) ∨ (¬ p5201)) : (¬ p2011) ∨ (p2233) ∨ (¬ p3516) ∨ (p4395) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial18907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3516)) ∨ (meaning t m 4395) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory8163 t (m.theta 0 4) (m.theta 0 7) (m.theta 5 9) (m.theta 7 9)
  exact rule18907 (meaning t m 2011) (meaning t m 2233) (meaning t m 3516) (meaning t m 4395) (meaning t m 5201) source

theorem rule18909 (p1982 p2027 p2440 p2531 p2842 p2850 p3083 p3146 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p2850) ∨ (¬ p1982) ∨ p2842 ∨ (¬ p2531) ∨ (¬ p2440) ∨ (¬ p3083)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p3083) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial18909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory8165 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18909 (meaning t m 1982) (meaning t m 2027) (meaning t m 2440) (meaning t m 2531) (meaning t m 2842) (meaning t m 2850) (meaning t m 3083) (meaning t m 3146) source

theorem rule18910 (p2307 p2387 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p2387) ∨ (¬ p2307)) : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial18910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory8166 (m.theta 0 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18910 (meaning t m 2307) (meaning t m 2387) (meaning t m 3325) source

theorem rule18918 (p2946 p3172 p4237 : Prop) (h : (¬ p4237) ∨ (¬ p2946) ∨ (¬ p3172)) : (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial18918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory8174 (m.theta 0 3) (m.theta 3 5) (m.theta 3 8)
  exact rule18918 (meaning t m 2946) (meaning t m 3172) (meaning t m 4237) source

theorem rule18921 (p2482 p2584 p4114 : Prop) (h : (¬ p4114) ∨ (¬ p2584) ∨ p2482) : (p2482) ∨ (¬ p2584) ∨ (¬ p4114) := by
  classical
  tauto

theorem initial18921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2482) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 4114)) := by
  have source := ElevenTheory.theory8177 (m.theta 0 4) (m.theta 0 6) (m.theta 0 8)
  exact rule18921 (meaning t m 2482) (meaning t m 2584) (meaning t m 4114) source

theorem rule18926 (p2001 p2027 p2241 p2699 p3189 p3256 p3692 : Prop) (h : (¬ p3256) ∨ (¬ p2001) ∨ p2699 ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3189)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial18926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory8182 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule18926 (meaning t m 2001) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3189) (meaning t m 3256) (meaning t m 3692) source

theorem rule18928 (p1987 p2027 p2299 p2633 p2737 p2780 p3366 p3822 : Prop) (h : p2633 ∨ (¬ p1987) ∨ (¬ p3822) ∨ (¬ p2299) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2780)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial18928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory8184 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule18928 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2737) (meaning t m 2780) (meaning t m 3366) (meaning t m 3822) source

theorem rule18929 (p1982 p2027 p2427 p2459 p2542 p2545 p2881 : Prop) (h : p2027 ∨ (¬ p2459) ∨ (¬ p1982) ∨ p2545 ∨ (¬ p2542) ∨ (¬ p2427) ∨ (¬ p2881)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial18929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory8185 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18929 (meaning t m 1982) (meaning t m 2027) (meaning t m 2427) (meaning t m 2459) (meaning t m 2542) (meaning t m 2545) (meaning t m 2881) source

theorem rule18931 (p1990 p2027 p2166 p2563 p2842 p3055 p3366 p3371 p3880 : Prop) (h : (¬ p1990) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3880) ∨ p2842 ∨ (¬ p3371) ∨ (¬ p3366) ∨ (¬ p2166) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2563) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial18931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory8187 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule18931 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2563) (meaning t m 2842) (meaning t m 3055) (meaning t m 3366) (meaning t m 3371) (meaning t m 3880) source

theorem rule18933 (p1990 p2027 p2166 p2553 p2873 p3097 p3660 p3880 : Prop) (h : (¬ p1990) ∨ (¬ p2166) ∨ p2027 ∨ p2873 ∨ (¬ p3880) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p2553)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2553) ∨ (p2873) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial18933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory8189 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule18933 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2553) (meaning t m 2873) (meaning t m 3097) (meaning t m 3660) (meaning t m 3880) source

theorem rule18934 (p1985 p2027 p2144 p2156 p2427 p2842 p3055 p4110 : Prop) (h : (¬ p3055) ∨ p2842 ∨ (¬ p1985) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2144) ∨ (¬ p4110) ∨ (¬ p2427)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial18934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8190 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule18934 (meaning t m 1985) (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2427) (meaning t m 2842) (meaning t m 3055) (meaning t m 4110) source

theorem rule18935 (p1984 p2027 p2633 p3553 p3931 p4366 p4442 : Prop) (h : (¬ p4442) ∨ p2633 ∨ p2027 ∨ (¬ p3553) ∨ (¬ p1984) ∨ (¬ p4366) ∨ (¬ p3931)) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3553) ∨ (¬ p3931) ∨ (¬ p4366) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial18935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory8191 t (m.theta 0 1) (m.theta 1 7) (m.theta 3 7) (m.theta 7 10) (m.theta 7 8)
  exact rule18935 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3553) (meaning t m 3931) (meaning t m 4366) (meaning t m 4442) source

theorem rule18938 (p1987 p2027 p2696 p2765 p3055 p3684 p4110 : Prop) (h : p2765 ∨ (¬ p3684) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2696) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (p2765) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial18938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8194 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule18938 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 2765) (meaning t m 3055) (meaning t m 3684) (meaning t m 4110) source

theorem rule18940 (p1992 p2027 p2608 p2881 p2938 p3548 p4366 : Prop) (h : p2938 ∨ (¬ p1992) ∨ (¬ p2608) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p4366)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8196 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule18940 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2881) (meaning t m 2938) (meaning t m 3548) (meaning t m 4366) source

theorem rule18941 (p1992 p2027 p2608 p2633 p3486 p3555 p3570 : Prop) (h : (¬ p3555) ∨ (¬ p1992) ∨ (¬ p2608) ∨ p2027 ∨ p2633 ∨ (¬ p3486) ∨ (¬ p3570)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial18941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory8197 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8)
  exact rule18941 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2633) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) source

theorem rule18942 (p3369 p4984 p5206 : Prop) (h : (¬ p3369) ∨ (¬ p4984) ∨ p5206) : (¬ p3369) ∨ (¬ p4984) ∨ (p5206) := by
  classical
  tauto

theorem initial18942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4984)) ∨ (meaning t m 5206) := by
  have source := ElevenTheory.theory8198 (m.theta 0 1) (m.theta 0 5) (m.theta 0 7)
  exact rule18942 (meaning t m 3369) (meaning t m 4984) (meaning t m 5206) source

theorem rule18944 (p1997 p2027 p2344 p2542 p3574 p3654 p4137 : Prop) (h : p2344 ∨ (¬ p3574) ∨ (¬ p1997) ∨ (¬ p2542) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p3654)) : (¬ p1997) ∨ (p2027) ∨ (p2344) ∨ (¬ p2542) ∨ (¬ p3574) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial18944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory8200 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule18944 (meaning t m 1997) (meaning t m 2027) (meaning t m 2344) (meaning t m 2542) (meaning t m 3574) (meaning t m 3654) (meaning t m 4137) source

theorem rule18945 (p1984 p2027 p2997 p3097 p3125 p3591 p4026 : Prop) (h : p2997 ∨ (¬ p1984) ∨ (¬ p3591) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p3125)) : (¬ p1984) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3591) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial18945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory8201 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule18945 (meaning t m 1984) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3591) (meaning t m 4026) source

theorem rule18947 (p1997 p2027 p2284 p2341 p3360 p3553 p4110 p4386 : Prop) (h : (¬ p3553) ∨ p3360 ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2284) ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p4386)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2341) ∨ (p3360) ∨ (¬ p3553) ∨ (¬ p4110) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial18947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory8203 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 7 8)
  exact rule18947 (meaning t m 1997) (meaning t m 2027) (meaning t m 2284) (meaning t m 2341) (meaning t m 3360) (meaning t m 3553) (meaning t m 4110) (meaning t m 4386) source

theorem rule18951 (p1982 p2027 p2177 p2307 p2459 p2622 p2797 p3567 : Prop) (h : (¬ p2177) ∨ (¬ p1982) ∨ (¬ p3567) ∨ (¬ p2307) ∨ p2622 ∨ p2027 ∨ (¬ p2797) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial18951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory8207 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18951 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2459) (meaning t m 2622) (meaning t m 2797) (meaning t m 3567) source

theorem rule18953 (p1983 p2027 p2299 p2341 p2396 p2622 p2797 p4066 p4156 : Prop) (h : (¬ p1983) ∨ p2027 ∨ (¬ p4066) ∨ (¬ p2797) ∨ p2622 ∨ (¬ p2396) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p4156)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (p2622) ∨ (¬ p2797) ∨ (¬ p4066) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial18953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory8209 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule18953 (meaning t m 1983) (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2396) (meaning t m 2622) (meaning t m 2797) (meaning t m 4066) (meaning t m 4156) source

theorem rule18954 (p1997 p2027 p2230 p2579 p2622 p2630 p3016 : Prop) (h : (¬ p3016) ∨ (¬ p1997) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2630) ∨ p2622) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial18954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory8210 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule18954 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2579) (meaning t m 2622) (meaning t m 2630) (meaning t m 3016) source

theorem rule18957 (p1997 p2027 p2462 p2542 p3742 p4253 p4324 p5501 p5502 : Prop) (h : p2462 ∨ (¬ p3742) ∨ (¬ p5501) ∨ (¬ p4324) ∨ (¬ p2542) ∨ (¬ p5502) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p4253)) : (¬ p1997) ∨ (p2027) ∨ (p2462) ∨ (¬ p2542) ∨ (¬ p3742) ∨ (¬ p4253) ∨ (¬ p4324) ∨ (¬ p5501) ∨ (¬ p5502) := by
  classical
  tauto

theorem initial18957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 5501)) ∨ (¬ (meaning t m 5502)) := by
  have source := ElevenTheory.theory8213 t (m.theta 2 7) (m.theta 3 4) (m.theta 4 10) (m.theta 4 5) (m.theta 4 7) (m.theta 7 10) (m.theta 7 9)
  exact rule18957 (meaning t m 1997) (meaning t m 2027) (meaning t m 2462) (meaning t m 2542) (meaning t m 3742) (meaning t m 4253) (meaning t m 4324) (meaning t m 5501) (meaning t m 5502) source

theorem rule18961 (p1980 p2027 p2462 p3568 p4253 p4260 p4324 : Prop) (h : (¬ p4260) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p1980) ∨ (¬ p4253) ∨ (¬ p4324) ∨ p2462) : (¬ p1980) ∨ (p2027) ∨ (p2462) ∨ (¬ p3568) ∨ (¬ p4253) ∨ (¬ p4260) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial18961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory8217 t (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule18961 (meaning t m 1980) (meaning t m 2027) (meaning t m 2462) (meaning t m 3568) (meaning t m 4253) (meaning t m 4260) (meaning t m 4324) source

theorem rule18962 (p1982 p2027 p2409 p2459 p2911 p2933 p3399 p3452 : Prop) (h : p2409 ∨ (¬ p2459) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p1982) ∨ (¬ p3399) ∨ (¬ p2933)) : (¬ p1982) ∨ (p2027) ∨ (p2409) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial18962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory8218 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule18962 (meaning t m 1982) (meaning t m 2027) (meaning t m 2409) (meaning t m 2459) (meaning t m 2911) (meaning t m 2933) (meaning t m 3399) (meaning t m 3452) source

theorem rule18963 (p1997 p2027 p2542 p3232 p3359 p3623 p3830 p4366 : Prop) (h : p3623 ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p4366) ∨ (¬ p2542) ∨ (¬ p3830)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (p3623) ∨ (¬ p3830) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial18963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 3359)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8219 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule18963 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 3232) (meaning t m 3359) (meaning t m 3623) (meaning t m 3830) (meaning t m 4366) source

theorem rule18967 (p1982 p2027 p2323 p2449 p2761 p2807 p4444 : Prop) (h : (¬ p1982) ∨ (¬ p4444) ∨ p2323 ∨ (¬ p2807) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p2761)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial18967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory8223 t (m.theta 0 3) (m.theta 3 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule18967 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 4444) source

theorem rule18974 (p1982 p2027 p2241 p2528 p2699 p2727 p3083 : Prop) (h : p2699 ∨ (¬ p1982) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p2241)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2528) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3083) := by
  classical
  tauto

theorem initial18974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) := by
  have source := ElevenTheory.theory8230 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule18974 (meaning t m 1982) (meaning t m 2027) (meaning t m 2241) (meaning t m 2528) (meaning t m 2699) (meaning t m 2727) (meaning t m 3083) source

theorem rule18975 (p1980 p2027 p2307 p2764 p3568 p3946 p4191 : Prop) (h : (¬ p4191) ∨ p2027 ∨ (¬ p1980) ∨ p2764 ∨ (¬ p3568) ∨ (¬ p2307) ∨ (¬ p3946)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2307) ∨ (p2764) ∨ (¬ p3568) ∨ (¬ p3946) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial18975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory8231 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule18975 (meaning t m 1980) (meaning t m 2027) (meaning t m 2307) (meaning t m 2764) (meaning t m 3568) (meaning t m 3946) (meaning t m 4191) source

theorem rule18976 (p1976 p2027 p2169 p2274 p2780 p3822 p3989 : Prop) (h : (¬ p1976) ∨ p2169 ∨ (¬ p3822) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2780) ∨ (¬ p2274)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial18976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8232 t (m.theta 0 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule18976 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2780) (meaning t m 3822) (meaning t m 3989) source

theorem rule18977 (p1992 p2027 p2169 p3105 p3758 p3989 p4363 p4874 : Prop) (h : (¬ p4874) ∨ (¬ p1992) ∨ (¬ p4363) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3105)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4363) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial18977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory8233 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8)
  exact rule18977 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 3105) (meaning t m 3758) (meaning t m 3989) (meaning t m 4363) (meaning t m 4874) source

theorem rule18984 (p1975 p2027 p2295 p2619 p2765 p3324 p3758 p4441 : Prop) (h : (¬ p4441) ∨ (¬ p3758) ∨ (¬ p3324) ∨ (¬ p2619) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p1975) ∨ p2765) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2619) ∨ (p2765) ∨ (¬ p3324) ∨ (¬ p3758) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial18984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory8240 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule18984 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2619) (meaning t m 2765) (meaning t m 3324) (meaning t m 3758) (meaning t m 4441) source

theorem rule18992 (p1992 p2027 p2608 p2765 p3105 p3758 p3834 p4388 : Prop) (h : (¬ p2608) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p3105) ∨ p2765 ∨ (¬ p3758) ∨ (¬ p4388) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2765) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p3834) ∨ (¬ p4388) := by
  classical
  tauto

theorem initial18992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4388)) := by
  have source := ElevenTheory.theory8248 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9)
  exact rule18992 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2765) (meaning t m 3105) (meaning t m 3758) (meaning t m 3834) (meaning t m 4388) source

theorem rule18993 (p2014 p2027 p2323 p2331 p3323 p3888 p4137 : Prop) (h : (¬ p2014) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3888) ∨ (¬ p2331) ∨ p2323) : (¬ p2014) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3888) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial18993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2014)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory8249 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 10) (m.theta 6 9)
  exact rule18993 (meaning t m 2014) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 3323) (meaning t m 3888) (meaning t m 4137) source

theorem rule18995 (p2007 p2027 p2619 p2765 p3758 p3969 p4286 : Prop) (h : p2765 ∨ (¬ p4286) ∨ (¬ p3758) ∨ (¬ p2007) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p3969)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2619) ∨ (p2765) ∨ (¬ p3758) ∨ (¬ p3969) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial18995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory8251 t (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule18995 (meaning t m 2007) (meaning t m 2027) (meaning t m 2619) (meaning t m 2765) (meaning t m 3758) (meaning t m 3969) (meaning t m 4286) source

theorem rule18996 (p2573 p2656 p3574 : Prop) (h : (¬ p2573) ∨ (¬ p3574) ∨ (¬ p2656)) : (¬ p2573) ∨ (¬ p2656) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial18996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory8252 (m.theta 0 4) (m.theta 3 4) (m.theta 4 6)
  exact rule18996 (meaning t m 2573) (meaning t m 2656) (meaning t m 3574) source

theorem rule19003 (p2138 p3425 p4136 : Prop) (h : (¬ p4136) ∨ (¬ p2138) ∨ p3425) : (¬ p2138) ∨ (p3425) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial19003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (meaning t m 3425) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory8259 (m.theta 0 2) (m.theta 2 5) (m.theta 2 7)
  exact rule19003 (meaning t m 2138) (meaning t m 3425) (meaning t m 4136) source

theorem rule19004 (p2020 p2764 p4444 p5122 : Prop) (h : (¬ p2020) ∨ (¬ p4444) ∨ p5122 ∨ p2764) : (¬ p2020) ∨ (p2764) ∨ (¬ p4444) ∨ (p5122) := by
  classical
  tauto

theorem initial19004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4444)) ∨ (meaning t m 5122) := by
  have source := ElevenTheory.theory8260 t (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule19004 (meaning t m 2020) (meaning t m 2764) (meaning t m 4444) (meaning t m 5122) source

theorem rule19008 (p1983 p2027 p2264 p2323 p2417 p2807 p3644 : Prop) (h : p2323 ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p2807) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2417) ∨ (¬ p2807) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial19008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory8264 t (m.theta 0 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19008 (meaning t m 1983) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2417) (meaning t m 2807) (meaning t m 3644) source

theorem rule19009 (p1982 p2027 p2233 p2341 p2528 p3941 p4286 p5201 : Prop) (h : (¬ p4286) ∨ p2233 ∨ (¬ p5201) ∨ (¬ p2341) ∨ (¬ p3941) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (p2233) ∨ (¬ p2341) ∨ (¬ p2528) ∨ (¬ p3941) ∨ (¬ p4286) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial19009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory8265 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19009 (meaning t m 1982) (meaning t m 2027) (meaning t m 2233) (meaning t m 2341) (meaning t m 2528) (meaning t m 3941) (meaning t m 4286) (meaning t m 5201) source

theorem rule19010 (p1994 p2027 p2406 p2440 p2633 p2928 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p2440) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2406) ∨ p2633 ∨ (¬ p2928)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial19010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory8266 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule19010 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2633) (meaning t m 2928) (meaning t m 3644) source

theorem rule19011 (p1982 p2027 p2247 p2518 p2528 p2688 p3379 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p2247)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2688) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial19011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory8267 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9)
  exact rule19011 (meaning t m 1982) (meaning t m 2027) (meaning t m 2247) (meaning t m 2518) (meaning t m 2528) (meaning t m 2688) (meaning t m 3379) source

theorem rule19013 (p1997 p2177 p2997 p4383 p4608 : Prop) (h : (¬ p2177) ∨ p2997 ∨ (¬ p4383) ∨ (¬ p1997) ∨ p4608) : (¬ p1997) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p4383) ∨ (p4608) := by
  classical
  tauto

theorem initial19013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4383)) ∨ (meaning t m 4608) := by
  have source := ElevenTheory.theory8269 t (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule19013 (meaning t m 1997) (meaning t m 2177) (meaning t m 2997) (meaning t m 4383) (meaning t m 4608) source

theorem rule19017 (p2241 p3038 p3543 p5206 : Prop) (h : (¬ p5206) ∨ (¬ p3543) ∨ (¬ p3038) ∨ (¬ p2241)) : (¬ p2241) ∨ (¬ p3038) ∨ (¬ p3543) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial19017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory8273 (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7)
  exact rule19017 (meaning t m 2241) (meaning t m 3038) (meaning t m 3543) (meaning t m 5206) source

theorem rule19018 (p1976 p2027 p2274 p2588 p2765 p3055 p3584 : Prop) (h : (¬ p1976) ∨ (¬ p3055) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p2588) ∨ p2765 ∨ (¬ p2274)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (p2765) ∨ (¬ p3055) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial19018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory8274 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19018 (meaning t m 1976) (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2765) (meaning t m 3055) (meaning t m 3584) source

theorem rule19019 (p2000 p2476 p2633 p4420 : Prop) (h : (¬ p2000) ∨ p2633 ∨ p4420 ∨ (¬ p2476)) : (¬ p2000) ∨ (¬ p2476) ∨ (p2633) ∨ (p4420) := by
  classical
  tauto

theorem initial19019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2633) ∨ (meaning t m 4420) := by
  have source := ElevenTheory.theory8275 t (m.theta 0 4) (m.theta 4 8) (m.theta 7 8)
  exact rule19019 (meaning t m 2000) (meaning t m 2476) (meaning t m 2633) (meaning t m 4420) source

theorem rule19022 (p1992 p2027 p2230 p2633 p3238 p3540 p3570 p4001 p4257 : Prop) (h : (¬ p1992) ∨ p2027 ∨ p2633 ∨ (¬ p3238) ∨ (¬ p3570) ∨ (¬ p4001) ∨ (¬ p2230) ∨ (¬ p4257) ∨ (¬ p3540)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2230) ∨ (p2633) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4001) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial19022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory8278 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19022 (meaning t m 1992) (meaning t m 2027) (meaning t m 2230) (meaning t m 2633) (meaning t m 3238) (meaning t m 3540) (meaning t m 3570) (meaning t m 4001) (meaning t m 4257) source

theorem rule19024 (p1976 p2027 p2542 p3008 p3055 p3574 p3684 : Prop) (h : (¬ p3055) ∨ (¬ p1976) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p2542) ∨ p3008 ∨ (¬ p3574)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2542) ∨ (p3008) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial19024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory8280 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19024 (meaning t m 1976) (meaning t m 2027) (meaning t m 2542) (meaning t m 3008) (meaning t m 3055) (meaning t m 3574) (meaning t m 3684) source

theorem rule19027 (p1988 p2027 p2459 p2819 p2997 p3266 p3550 p3822 : Prop) (h : (¬ p2459) ∨ p2997 ∨ (¬ p3266) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3822) ∨ (¬ p3550)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2819) ∨ (p2997) ∨ (¬ p3266) ∨ (¬ p3550) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial19027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory8283 t (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19027 (meaning t m 1988) (meaning t m 2027) (meaning t m 2459) (meaning t m 2819) (meaning t m 2997) (meaning t m 3266) (meaning t m 3550) (meaning t m 3822) source

theorem rule19030 (p1976 p2027 p3043 p3365 p3680 p4035 p5284 : Prop) (h : p2027 ∨ p3043 ∨ (¬ p3365) ∨ (¬ p3680) ∨ (¬ p4035) ∨ (¬ p1976) ∨ (¬ p5284)) : (¬ p1976) ∨ (p2027) ∨ (p3043) ∨ (¬ p3365) ∨ (¬ p3680) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial19030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory8286 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule19030 (meaning t m 1976) (meaning t m 2027) (meaning t m 3043) (meaning t m 3365) (meaning t m 3680) (meaning t m 4035) (meaning t m 5284) source

theorem rule19034 (p1988 p2027 p2098 p2842 p3055 p3266 p3609 : Prop) (h : (¬ p2098) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3266) ∨ (¬ p3609) ∨ (¬ p3055) ∨ p2842) : (¬ p1988) ∨ (p2027) ∨ (¬ p2098) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3609) := by
  classical
  tauto

theorem initial19034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3609)) := by
  have source := ElevenTheory.theory8290 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19034 (meaning t m 1988) (meaning t m 2027) (meaning t m 2098) (meaning t m 2842) (meaning t m 3055) (meaning t m 3266) (meaning t m 3609) source

theorem rule19035 (p1997 p2027 p2132 p2842 p2860 p3055 p4110 : Prop) (h : p2027 ∨ p2842 ∨ (¬ p2132) ∨ (¬ p4110) ∨ (¬ p3055) ∨ (¬ p1997) ∨ (¬ p2860)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2132) ∨ (p2842) ∨ (¬ p2860) ∨ (¬ p3055) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8291 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule19035 (meaning t m 1997) (meaning t m 2027) (meaning t m 2132) (meaning t m 2842) (meaning t m 2860) (meaning t m 3055) (meaning t m 4110) source

theorem rule19037 (p1986 p2027 p2598 p2881 p2938 p3425 p3659 : Prop) (h : (¬ p1986) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2598) ∨ p2938 ∨ (¬ p2881) ∨ (¬ p3659)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial19037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory8293 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19037 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2881) (meaning t m 2938) (meaning t m 3425) (meaning t m 3659) source

theorem rule19039 (p1984 p2027 p2247 p2545 p2810 p3136 p3662 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p1984) ∨ (¬ p3136) ∨ (¬ p2810) ∨ (¬ p3662)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial19039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory8295 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule19039 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2545) (meaning t m 2810) (meaning t m 3136) (meaning t m 3662) source

theorem rule19040 (p1984 p2027 p2688 p2727 p2743 p2810 p3954 : Prop) (h : p2027 ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p1984) ∨ p2688 ∨ (¬ p2810) ∨ (¬ p2727)) : (¬ p1984) ∨ (p2027) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8296 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule19040 (meaning t m 1984) (meaning t m 2027) (meaning t m 2688) (meaning t m 2727) (meaning t m 2743) (meaning t m 2810) (meaning t m 3954) source

theorem rule19041 (p1984 p2027 p2633 p3570 p3583 p3954 p4244 : Prop) (h : p2633 ∨ (¬ p4244) ∨ (¬ p3570) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial19041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory8297 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule19041 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3570) (meaning t m 3583) (meaning t m 3954) (meaning t m 4244) source

theorem rule19042 (p1982 p2027 p2341 p2459 p2545 p2685 p2810 p4066 : Prop) (h : (¬ p2685) ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p2341) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p2810) ∨ p2545) : (¬ p1982) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (p2545) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial19042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory8298 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19042 (meaning t m 1982) (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2545) (meaning t m 2685) (meaning t m 2810) (meaning t m 4066) source

theorem rule19044 (p1988 p2027 p2388 p3189 p3256 p3266 p3662 : Prop) (h : (¬ p3662) ∨ p2388 ∨ (¬ p3189) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3256)) : (¬ p1988) ∨ (p2027) ∨ (p2388) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial19044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory8300 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19044 (meaning t m 1988) (meaning t m 2027) (meaning t m 2388) (meaning t m 3189) (meaning t m 3256) (meaning t m 3266) (meaning t m 3662) source

theorem rule19045 (p1982 p2027 p2406 p2409 p2761 p3516 p4109 p4444 p4988 : Prop) (h : (¬ p2406) ∨ p2409 ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4109) ∨ (¬ p4988) ∨ (¬ p1982) ∨ (¬ p2761) ∨ (¬ p3516)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4109) ∨ (¬ p4444) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial19045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory8301 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 4) (m.theta 4 5) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19045 (meaning t m 1982) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2761) (meaning t m 3516) (meaning t m 4109) (meaning t m 4444) (meaning t m 4988) source

theorem rule19048 (p1990 p2027 p2132 p2622 p2819 p3365 p3985 p3989 : Prop) (h : p2622 ∨ (¬ p2132) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3985) ∨ (¬ p1990) ∨ (¬ p3365) ∨ (¬ p2819)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p2819) ∨ (¬ p3365) ∨ (¬ p3985) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial19048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8304 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19048 (meaning t m 1990) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 2819) (meaning t m 3365) (meaning t m 3985) (meaning t m 3989) source

theorem rule19049 (p2008 p2027 p2098 p2622 p2707 p3365 p4242 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p2707) ∨ (¬ p2098) ∨ (¬ p4242) ∨ (¬ p2008) ∨ (¬ p3365)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2098) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p3365) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial19049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory8305 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8)
  exact rule19049 (meaning t m 2008) (meaning t m 2027) (meaning t m 2098) (meaning t m 2622) (meaning t m 2707) (meaning t m 3365) (meaning t m 4242) source

theorem rule19051 (p1984 p2027 p2247 p2287 p2685 p2996 p4195 : Prop) (h : p2027 ∨ (¬ p4195) ∨ p2287 ∨ (¬ p2685) ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p2996)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2287) ∨ (¬ p2685) ∨ (¬ p2996) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial19051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory8307 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule19051 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2287) (meaning t m 2685) (meaning t m 2996) (meaning t m 4195) source

theorem rule19055 (p1993 p3871 p4118 p5113 : Prop) (h : (¬ p4118) ∨ (¬ p1993) ∨ p3871 ∨ p5113) : (¬ p1993) ∨ (p3871) ∨ (¬ p4118) ∨ (p5113) := by
  classical
  tauto

theorem initial19055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 3871) ∨ (¬ (meaning t m 4118)) ∨ (meaning t m 5113) := by
  have source := ElevenTheory.theory8311 t (m.theta 3 8) (m.theta 3 9) (m.theta 8 9)
  exact rule19055 (meaning t m 1993) (meaning t m 3871) (meaning t m 4118) (meaning t m 5113) source

theorem rule19056 (p1988 p2027 p2363 p2383 p2409 p2493 p2578 p3266 : Prop) (h : (¬ p2578) ∨ (¬ p2493) ∨ p2027 ∨ p2409 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p1988) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial19056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory8312 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19056 (meaning t m 1988) (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2409) (meaning t m 2493) (meaning t m 2578) (meaning t m 3266) source

theorem rule19058 (p3758 p4338 p4418 p4516 : Prop) (h : (¬ p3758) ∨ (¬ p4418) ∨ (¬ p4516) ∨ (¬ p4338)) : (¬ p3758) ∨ (¬ p4338) ∨ (¬ p4418) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial19058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory8314 (m.theta 1 5) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6)
  exact rule19058 (meaning t m 3758) (meaning t m 4338) (meaning t m 4418) (meaning t m 4516) source

theorem rule19059 (p1984 p2027 p2911 p2914 p3588 p3659 p3954 : Prop) (h : p2027 ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p1984) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8315 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule19059 (meaning t m 1984) (meaning t m 2027) (meaning t m 2911) (meaning t m 2914) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) source

theorem rule19061 (p1990 p2027 p2553 p2573 p2622 p2630 p2656 p3097 : Prop) (h : p2622 ∨ (¬ p2553) ∨ (¬ p2630) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p1990) ∨ (¬ p2573)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial19061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory8317 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19061 (meaning t m 1990) (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 3097) source

theorem rule19062 (p1997 p2027 p2114 p2598 p2737 p2850 p3365 : Prop) (h : p2027 ∨ (¬ p2850) ∨ (¬ p3365) ∨ p2114 ∨ (¬ p2737) ∨ (¬ p1997) ∨ (¬ p2598)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p2850) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial19062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory8318 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule19062 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2598) (meaning t m 2737) (meaning t m 2850) (meaning t m 3365) source

theorem rule19063 (p1985 p2027 p2144 p2156 p2622 p2901 p3365 p3952 : Prop) (h : (¬ p2901) ∨ (¬ p1985) ∨ (¬ p3952) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2144) ∨ p2622 ∨ (¬ p2156)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (p2622) ∨ (¬ p2901) ∨ (¬ p3365) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial19063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory8319 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule19063 (meaning t m 1985) (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2622) (meaning t m 2901) (meaning t m 3365) (meaning t m 3952) source

theorem rule19064 (p1985 p2027 p2114 p2839 p2860 p2901 p3952 : Prop) (h : (¬ p2901) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2839) ∨ (¬ p1985) ∨ p2114 ∨ (¬ p2860)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p2901) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial19064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory8320 t (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule19064 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2839) (meaning t m 2860) (meaning t m 2901) (meaning t m 3952) source

theorem rule19065 (p2000 p2202 p2476 p4610 : Prop) (h : (¬ p2000) ∨ (¬ p2476) ∨ p2202 ∨ p4610) : (¬ p2000) ∨ (p2202) ∨ (¬ p2476) ∨ (p4610) := by
  classical
  tauto

theorem initial19065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 4610) := by
  have source := ElevenTheory.theory8321 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8)
  exact rule19065 (meaning t m 2000) (meaning t m 2202) (meaning t m 2476) (meaning t m 4610) source

theorem rule19066 (p1980 p2027 p2122 p2622 p2743 p2829 p3568 : Prop) (h : (¬ p2122) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2743) ∨ p2622 ∨ (¬ p1980) ∨ (¬ p3568)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2122) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial19066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory8322 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule19066 (meaning t m 1980) (meaning t m 2027) (meaning t m 2122) (meaning t m 2622) (meaning t m 2743) (meaning t m 2829) (meaning t m 3568) source

theorem rule19067 (p1975 p2027 p2114 p2122 p2737 p2774 p3365 : Prop) (h : (¬ p2737) ∨ p2027 ∨ (¬ p3365) ∨ p2114 ∨ (¬ p2774) ∨ (¬ p1975) ∨ (¬ p2122)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2737) ∨ (¬ p2774) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial19067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory8323 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule19067 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2122) (meaning t m 2737) (meaning t m 2774) (meaning t m 3365) source

theorem rule19070 (p1996 p2027 p2493 p2657 p2688 p2807 p3574 p4281 : Prop) (h : p2688 ∨ (¬ p2493) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4281) ∨ (¬ p2807) ∨ (¬ p1996) ∨ (¬ p3574)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2807) ∨ (¬ p3574) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial19070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory8326 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6)
  exact rule19070 (meaning t m 1996) (meaning t m 2027) (meaning t m 2493) (meaning t m 2657) (meaning t m 2688) (meaning t m 2807) (meaning t m 3574) (meaning t m 4281) source

theorem rule19072 (p1990 p2027 p2202 p2295 p2493 p2578 p2667 p3097 p3238 : Prop) (h : p2202 ∨ (¬ p3238) ∨ (¬ p2295) ∨ (¬ p1990) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2667) ∨ (¬ p2578) ∨ (¬ p2493)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2295) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p3097) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial19072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory8328 t (m.theta 0 6) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19072 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2295) (meaning t m 2493) (meaning t m 2578) (meaning t m 2667) (meaning t m 3097) (meaning t m 3238) source

theorem rule19077 (p1990 p2027 p2132 p2622 p2668 p3365 p3985 p3989 p4328 : Prop) (h : (¬ p3365) ∨ p2027 ∨ p2622 ∨ (¬ p4328) ∨ (¬ p3985) ∨ (¬ p3989) ∨ (¬ p2668) ∨ (¬ p2132) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p2668) ∨ (¬ p3365) ∨ (¬ p3985) ∨ (¬ p3989) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial19077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory8333 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19077 (meaning t m 1990) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 2668) (meaning t m 3365) (meaning t m 3985) (meaning t m 3989) (meaning t m 4328) source

theorem rule19079 (p1984 p2873 p3954 p4377 : Prop) (h : (¬ p3954) ∨ p2873 ∨ p4377 ∨ (¬ p1984)) : (¬ p1984) ∨ (p2873) ∨ (¬ p3954) ∨ (p4377) := by
  classical
  tauto

theorem initial19079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3954)) ∨ (meaning t m 4377) := by
  have source := ElevenTheory.theory8335 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5)
  exact rule19079 (meaning t m 1984) (meaning t m 2873) (meaning t m 3954) (meaning t m 4377) source

theorem rule19080 (p1978 p3586 p3646 p4401 : Prop) (h : p3586 ∨ (¬ p1978) ∨ (¬ p3646) ∨ p4401) : (¬ p1978) ∨ (p3586) ∨ (¬ p3646) ∨ (p4401) := by
  classical
  tauto

theorem initial19080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 3646)) ∨ (meaning t m 4401) := by
  have source := ElevenTheory.theory8336 t (m.theta 0 5) (m.theta 2 6) (m.theta 5 6)
  exact rule19080 (meaning t m 1978) (meaning t m 3586) (meaning t m 3646) (meaning t m 4401) source

theorem rule19082 (p1997 p2027 p2406 p2462 p2761 p3346 p3347 p4425 : Prop) (h : (¬ p2406) ∨ (¬ p3347) ∨ (¬ p1997) ∨ (¬ p3346) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p2761) ∨ p2462) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial19082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory8338 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19082 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2462) (meaning t m 2761) (meaning t m 3346) (meaning t m 3347) (meaning t m 4425) source

theorem rule19083 (p1975 p2027 p2295 p2323 p2641 p3166 p4360 : Prop) (h : p2027 ∨ (¬ p4360) ∨ (¬ p1975) ∨ (¬ p3166) ∨ (¬ p2641) ∨ (¬ p2295) ∨ p2323) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p3166) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial19083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory8339 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule19083 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2641) (meaning t m 3166) (meaning t m 4360) source

theorem rule19084 (p1997 p2027 p2764 p2850 p3363 p3540 p4278 p4381 : Prop) (h : (¬ p1997) ∨ (¬ p3363) ∨ (¬ p2850) ∨ (¬ p4278) ∨ (¬ p4381) ∨ p2764 ∨ p2027 ∨ (¬ p3540)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p2850) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial19084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory8340 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19084 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 2850) (meaning t m 3363) (meaning t m 3540) (meaning t m 4278) (meaning t m 4381) source

theorem rule19085 (p2011 p2027 p2169 p2274 p2313 p3212 p3989 p4198 : Prop) (h : (¬ p3989) ∨ (¬ p2011) ∨ p2027 ∨ p2169 ∨ (¬ p2274) ∨ (¬ p4198) ∨ (¬ p3212) ∨ (¬ p2313)) : (¬ p2011) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3212) ∨ (¬ p3989) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial19085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory8341 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 8)
  exact rule19085 (meaning t m 2011) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2313) (meaning t m 3212) (meaning t m 3989) (meaning t m 4198) source

theorem rule19086 (p2311 p4198 p4984 : Prop) (h : (¬ p2311) ∨ (¬ p4198) ∨ p4984) : (¬ p2311) ∨ (¬ p4198) ∨ (p4984) := by
  classical
  tauto

theorem initial19086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 4198)) ∨ (meaning t m 4984) := by
  have source := ElevenTheory.theory8342 (m.theta 0 5) (m.theta 0 6) (m.theta 0 7)
  exact rule19086 (meaning t m 2311) (meaning t m 4198) (meaning t m 4984) source

theorem rule19090 (p2005 p2027 p2233 p2295 p2470 p2588 p3019 p4256 : Prop) (h : p2233 ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p3019) ∨ (¬ p4256) ∨ (¬ p2005) ∨ p2027 ∨ (¬ p2470)) : (¬ p2005) ∨ (p2027) ∨ (p2233) ∨ (¬ p2295) ∨ (¬ p2470) ∨ (¬ p2588) ∨ (¬ p3019) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial19090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory8346 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule19090 (meaning t m 2005) (meaning t m 2027) (meaning t m 2233) (meaning t m 2295) (meaning t m 2470) (meaning t m 2588) (meaning t m 3019) (meaning t m 4256) source

theorem rule19091 (p2006 p2027 p2132 p2780 p2829 p2842 p3585 : Prop) (h : p2027 ∨ (¬ p2006) ∨ p2842 ∨ (¬ p3585) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2829)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial19091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory8347 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 2 6)
  exact rule19091 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 2829) (meaning t m 2842) (meaning t m 3585) source

theorem rule19094 (p3016 p3422 p3683 : Prop) (h : (¬ p3016) ∨ (¬ p3683) ∨ p3422) : (¬ p3016) ∨ (p3422) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial19094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (meaning t m 3422) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory8350 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule19094 (meaning t m 3016) (meaning t m 3422) (meaning t m 3683) source

theorem rule19095 (p2001 p2027 p2088 p2406 p2409 p2482 p2589 p3692 : Prop) (h : (¬ p2589) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2001) ∨ p2409 ∨ (¬ p3692) ∨ (¬ p2482) ∨ (¬ p2088)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2482) ∨ (¬ p2589) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial19095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory8351 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule19095 (meaning t m 2001) (meaning t m 2027) (meaning t m 2088) (meaning t m 2406) (meaning t m 2409) (meaning t m 2482) (meaning t m 2589) (meaning t m 3692) source

theorem rule19097 (p1979 p2027 p2997 p3063 p3549 p3952 p3989 : Prop) (h : p2997 ∨ (¬ p1979) ∨ (¬ p3989) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p3549)) : (¬ p1979) ∨ (p2027) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3952) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial19097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8353 t (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19097 (meaning t m 1979) (meaning t m 2027) (meaning t m 2997) (meaning t m 3063) (meaning t m 3549) (meaning t m 3952) (meaning t m 3989) source

theorem rule19098 (p1978 p2027 p2192 p2462 p3486 p3646 p3690 : Prop) (h : (¬ p1978) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3690) ∨ p2462 ∨ (¬ p3646) ∨ (¬ p2192)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2192) ∨ (p2462) ∨ (¬ p3486) ∨ (¬ p3646) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial19098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory8354 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule19098 (meaning t m 1978) (meaning t m 2027) (meaning t m 2192) (meaning t m 2462) (meaning t m 3486) (meaning t m 3646) (meaning t m 3690) source

theorem rule19099 (p1990 p2027 p2220 p2284 p2406 p2688 p3497 p4109 p4281 : Prop) (h : (¬ p3497) ∨ p2688 ∨ (¬ p2220) ∨ (¬ p4281) ∨ (¬ p1990) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p2284)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p2406) ∨ (p2688) ∨ (¬ p3497) ∨ (¬ p4109) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial19099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory8355 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule19099 (meaning t m 1990) (meaning t m 2027) (meaning t m 2220) (meaning t m 2284) (meaning t m 2406) (meaning t m 2688) (meaning t m 3497) (meaning t m 4109) (meaning t m 4281) source

theorem rule19100 (p2313 p3549 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p3549) ∨ p2313) : (p2313) ∨ (¬ p3549) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial19100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2313) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory8356 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule19100 (meaning t m 2313) (meaning t m 3549) (meaning t m 5016) source

theorem rule19102 (p1994 p2027 p2440 p2598 p2622 p2850 p3365 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2440) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p2850) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial19102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory8358 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule19102 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2598) (meaning t m 2622) (meaning t m 2850) (meaning t m 3365) source

theorem rule19104 (p2010 p2027 p2230 p2323 p2437 p2663 p2982 p4208 p4700 : Prop) (h : p2323 ∨ (¬ p2230) ∨ (¬ p4700) ∨ (¬ p4208) ∨ (¬ p2982) ∨ (¬ p2010) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2663)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2230) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2663) ∨ (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial19104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory8360 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 9)
  exact rule19104 (meaning t m 2010) (meaning t m 2027) (meaning t m 2230) (meaning t m 2323) (meaning t m 2437) (meaning t m 2663) (meaning t m 2982) (meaning t m 4208) (meaning t m 4700) source

theorem rule19105 (p1980 p2027 p2797 p3572 p3623 p4075 p4391 : Prop) (h : (¬ p2797) ∨ p3623 ∨ (¬ p1980) ∨ p2027 ∨ (¬ p4391) ∨ (¬ p3572) ∨ (¬ p4075)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2797) ∨ (¬ p3572) ∨ (p3623) ∨ (¬ p4075) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial19105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3572)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory8361 t (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 10)
  exact rule19105 (meaning t m 1980) (meaning t m 2027) (meaning t m 2797) (meaning t m 3572) (meaning t m 3623) (meaning t m 4075) (meaning t m 4391) source

theorem rule19107 (p2005 p2027 p2122 p2409 p2588 p3093 p3452 p4024 : Prop) (h : (¬ p2005) ∨ (¬ p2588) ∨ (¬ p3093) ∨ p2409 ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4024) ∨ (¬ p2122)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2122) ∨ (p2409) ∨ (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p4024) := by
  classical
  tauto

theorem initial19107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4024)) := by
  have source := ElevenTheory.theory8363 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19107 (meaning t m 2005) (meaning t m 2027) (meaning t m 2122) (meaning t m 2409) (meaning t m 2588) (meaning t m 3093) (meaning t m 3452) (meaning t m 4024) source

theorem rule19108 (p1979 p2027 p2323 p2437 p2651 p3136 p3364 p3876 : Prop) (h : (¬ p3364) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3136) ∨ (¬ p2651) ∨ p2323 ∨ (¬ p3876)) : (¬ p1979) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial19108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory8364 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule19108 (meaning t m 1979) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2651) (meaning t m 3136) (meaning t m 3364) (meaning t m 3876) source

theorem rule19110 (p2015 p2699 p3093 p3580 p4650 : Prop) (h : p2699 ∨ (¬ p2015) ∨ (¬ p3093) ∨ (¬ p3580) ∨ p4650) : (¬ p2015) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3580) ∨ (p4650) := by
  classical
  tauto

theorem initial19110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3580)) ∨ (meaning t m 4650) := by
  have source := ElevenTheory.theory8366 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 4) (m.theta 3 7)
  exact rule19110 (meaning t m 2015) (meaning t m 2699) (meaning t m 3093) (meaning t m 3580) (meaning t m 4650) source

theorem rule19111 (p1997 p2027 p2542 p2611 p2630 p2807 p3572 p4117 : Prop) (h : (¬ p1997) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p4117) ∨ p2611 ∨ (¬ p3572) ∨ p2027 ∨ (¬ p2542)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial19111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory8367 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule19111 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2611) (meaning t m 2630) (meaning t m 2807) (meaning t m 3572) (meaning t m 4117) source

theorem rule19112 (p1981 p2027 p2323 p2668 p2797 p2807 p3572 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2797) ∨ (¬ p2668) ∨ (¬ p1981) ∨ (¬ p2807) ∨ (¬ p3572)) : (¬ p1981) ∨ (p2027) ∨ (p2323) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2807) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial19112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory8368 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 8)
  exact rule19112 (meaning t m 1981) (meaning t m 2027) (meaning t m 2323) (meaning t m 2668) (meaning t m 2797) (meaning t m 2807) (meaning t m 3572) source

theorem rule19113 (p2005 p2027 p2611 p2651 p2810 p3005 p3956 p4117 p4417 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p4417) ∨ (¬ p4117) ∨ (¬ p2005) ∨ (¬ p3005) ∨ (¬ p3956)) : (¬ p2005) ∨ (p2027) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial19113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory8369 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule19113 (meaning t m 2005) (meaning t m 2027) (meaning t m 2611) (meaning t m 2651) (meaning t m 2810) (meaning t m 3005) (meaning t m 3956) (meaning t m 4117) (meaning t m 4417) source

theorem rule19114 (p1999 p2027 p2122 p2588 p2611 p2774 p3564 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p3564) ∨ (¬ p2588) ∨ (¬ p1999)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial19114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory8370 t (m.theta 0 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule19114 (meaning t m 1999) (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 2611) (meaning t m 2774) (meaning t m 3564) source

theorem rule19115 (p1989 p2027 p2210 p2462 p3549 p3591 p4107 : Prop) (h : (¬ p1989) ∨ (¬ p3591) ∨ (¬ p3549) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p4107) ∨ p2462) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2462) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial19115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory8371 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 6 7) (m.theta 7 9)
  exact rule19115 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2462) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) source

theorem rule19116 (p2005 p2027 p2114 p2230 p2440 p2663 p2737 p2811 p3016 : Prop) (h : (¬ p2230) ∨ (¬ p2811) ∨ p2027 ∨ p2114 ∨ (¬ p2737) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2005) ∨ (¬ p3016)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial19116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory8372 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19116 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 2737) (meaning t m 2811) (meaning t m 3016) source

theorem rule19119 (p1998 p2027 p2598 p2622 p2911 p3201 p3365 : Prop) (h : (¬ p3201) ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p1998) ∨ p2622 ∨ p2027 ∨ (¬ p2911)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial19119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory8375 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule19119 (meaning t m 1998) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 2911) (meaning t m 3201) (meaning t m 3365) source

theorem rule19121 (p1998 p2027 p2323 p2449 p2807 p2881 p3690 : Prop) (h : p2027 ∨ (¬ p1998) ∨ p2323 ∨ (¬ p2807) ∨ (¬ p2881) ∨ (¬ p2449) ∨ (¬ p3690)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p2881) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial19121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory8377 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19121 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2807) (meaning t m 2881) (meaning t m 3690) source

theorem rule19122 (p1990 p2027 p2202 p2352 p2573 p3238 p3519 p3989 : Prop) (h : p2202 ∨ (¬ p2352) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p3519) ∨ (¬ p3238) ∨ (¬ p1990) ∨ (¬ p2573)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3238) ∨ (¬ p3519) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial19122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory8378 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19122 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2352) (meaning t m 2573) (meaning t m 3238) (meaning t m 3519) (meaning t m 3989) source

theorem rule19123 (p1998 p2027 p2132 p2622 p2870 p2881 p3365 : Prop) (h : p2027 ∨ p2622 ∨ (¬ p3365) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial19123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory8379 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule19123 (meaning t m 1998) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 2870) (meaning t m 2881) (meaning t m 3365) source

theorem rule19124 (p2922 p3590 p3686 p4106 : Prop) (h : (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3686) ∨ (¬ p4106)) : (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3686) ∨ (¬ p4106) := by
  classical
  tauto

theorem initial19124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4106)) := by
  have source := ElevenTheory.theory8380 (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule19124 (meaning t m 2922) (meaning t m 3590) (meaning t m 3686) (meaning t m 4106) source

theorem rule19126 (p1984 p2027 p2765 p3609 p3758 p3860 p4261 p4744 : Prop) (h : (¬ p4744) ∨ (¬ p1984) ∨ (¬ p3758) ∨ p2027 ∨ p2765 ∨ (¬ p3609) ∨ (¬ p3860) ∨ (¬ p4261)) : (¬ p1984) ∨ (p2027) ∨ (p2765) ∨ (¬ p3609) ∨ (¬ p3758) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4744) := by
  classical
  tauto

theorem initial19126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4744)) := by
  have source := ElevenTheory.theory8382 t (m.theta 0 1) (m.theta 1 8) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 8 9)
  exact rule19126 (meaning t m 1984) (meaning t m 2027) (meaning t m 2765) (meaning t m 3609) (meaning t m 3758) (meaning t m 3860) (meaning t m 4261) (meaning t m 4744) source

theorem rule19127 (p3371 p4512 p4869 : Prop) (h : (¬ p4869) ∨ p3371 ∨ (¬ p4512)) : (p3371) ∨ (¬ p4512) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial19127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3371) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory8383 (m.theta 1 2) (m.theta 1 5) (m.theta 1 6)
  exact rule19127 (meaning t m 3371) (meaning t m 4512) (meaning t m 4869) source

theorem rule19128 (p1984 p2027 p2819 p2997 p3591 p3822 p3923 : Prop) (h : (¬ p3822) ∨ (¬ p1984) ∨ (¬ p3923) ∨ p2027 ∨ p2997 ∨ (¬ p2819) ∨ (¬ p3591)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2819) ∨ (p2997) ∨ (¬ p3591) ∨ (¬ p3822) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial19128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory8384 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19128 (meaning t m 1984) (meaning t m 2027) (meaning t m 2819) (meaning t m 2997) (meaning t m 3591) (meaning t m 3822) (meaning t m 3923) source

end SunPrize.SMT
