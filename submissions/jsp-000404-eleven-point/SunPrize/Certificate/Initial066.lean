import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory050
import SunPrize.Certificate.Theory051
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule28812 (p2027 p2104 p3366 p3399 p3452 p4075 p4340 p4376 p4444 p4826 : Prop) (h : p2027 ∨ (¬ p4826) ∨ (¬ p4444) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p4075) ∨ (¬ p3399) ∨ (¬ p4340) ∨ (¬ p2104) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2104) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4075) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial28812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory18068 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule28812 (meaning t m 2027) (meaning t m 2104) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 4075) (meaning t m 4340) (meaning t m 4376) (meaning t m 4444) (meaning t m 4826) source

theorem rule28813 (p2027 p3172 p3366 p3399 p3452 p4075 p4236 p4340 p4376 p4444 p4826 p4967 : Prop) (h : (¬ p4236) ∨ (¬ p4967) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4376) ∨ (¬ p4340) ∨ (¬ p4826) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p4075) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4075) ∨ (¬ p4236) ∨ (¬ p4340) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial28813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory18069 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 8) (m.theta 3 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule28813 (meaning t m 2027) (meaning t m 3172) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 4075) (meaning t m 4236) (meaning t m 4340) (meaning t m 4376) (meaning t m 4444) (meaning t m 4826) (meaning t m 4967) source

theorem rule28820 (p1990 p2027 p2307 p2545 p2810 p3097 p3136 p3567 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p3567) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p2307) ∨ p2545) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial28820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory18076 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule28820 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2545) (meaning t m 2810) (meaning t m 3097) (meaning t m 3136) (meaning t m 3567) (meaning t m 4336) source

theorem rule28821 (p3246 p3434 p4344 : Prop) (h : (¬ p3246) ∨ (¬ p4344) ∨ p3434) : (¬ p3246) ∨ (p3434) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial28821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (meaning t m 3434) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory18077 (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule28821 (meaning t m 3246) (meaning t m 3434) (meaning t m 4344) source

theorem rule28822 (p2027 p2264 p2274 p3956 p4138 p4203 p4361 : Prop) (h : (¬ p4203) ∨ (¬ p2274) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4361) ∨ (¬ p4138) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4203) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial28822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory18078 t (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule28822 (meaning t m 2027) (meaning t m 2264) (meaning t m 2274) (meaning t m 3956) (meaning t m 4138) (meaning t m 4203) (meaning t m 4361) source

theorem rule28823 (p1975 p2027 p2202 p2417 p2589 p3389 p4107 : Prop) (h : (¬ p2589) ∨ p2202 ∨ (¬ p3389) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2417)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial28823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory18079 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule28823 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2589) (meaning t m 3389) (meaning t m 4107) source

theorem rule28825 (p2027 p2341 p2641 p2656 p3031 p3548 p4975 p5201 : Prop) (h : (¬ p3548) ∨ (¬ p2656) ∨ (¬ p5201) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p3031) ∨ (¬ p2641) ∨ (¬ p4975)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4975) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial28825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4975)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory18081 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 6) (m.theta 7 8)
  exact rule28825 (meaning t m 2027) (meaning t m 2341) (meaning t m 2641) (meaning t m 2656) (meaning t m 3031) (meaning t m 3548) (meaning t m 4975) (meaning t m 5201) source

theorem rule28828 (p2027 p2254 p2417 p2598 p2963 p3201 p3324 p3589 p3950 p4347 : Prop) (h : (¬ p2598) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p3589) ∨ (¬ p3950) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2254) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p3324) ∨ (¬ p3589) ∨ (¬ p3950) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial28828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory18084 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28828 (meaning t m 2027) (meaning t m 2254) (meaning t m 2417) (meaning t m 2598) (meaning t m 2963) (meaning t m 3201) (meaning t m 3324) (meaning t m 3589) (meaning t m 3950) (meaning t m 4347) source

theorem rule28829 (p2252 p2952 p2992 : Prop) (h : (¬ p2952) ∨ (¬ p2252) ∨ (¬ p2992)) : (¬ p2252) ∨ (¬ p2952) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial28829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory18085 (m.theta 0 3) (m.theta 1 3) (m.theta 3 5)
  exact rule28829 (meaning t m 2252) (meaning t m 2952) (meaning t m 2992) source

theorem rule28830 (p2252 p2952 p3662 : Prop) (h : (¬ p2952) ∨ (¬ p2252) ∨ p3662) : (¬ p2252) ∨ (¬ p2952) ∨ (p3662) := by
  classical
  tauto

theorem initial28830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 3662) := by
  have source := ElevenTheory.theory18086 (m.theta 0 3) (m.theta 1 3) (m.theta 3 5)
  exact rule28830 (meaning t m 2252) (meaning t m 2952) (meaning t m 3662) source

theorem rule28832 (p1982 p2027 p2608 p2699 p3537 p3670 p4444 p5344 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p4444) ∨ (¬ p5344) ∨ (¬ p3537) ∨ (¬ p3670)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3537) ∨ (¬ p3670) ∨ (¬ p4444) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial28832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory18088 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 8) (m.theta 2 9) (m.theta 8 9) (m.theta 9 10)
  exact rule28832 (meaning t m 1982) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 3537) (meaning t m 3670) (meaning t m 4444) (meaning t m 5344) source

theorem rule28834 (p1991 p2027 p2534 p2630 p2657 p2766 p3877 p4437 : Prop) (h : p2766 ∨ (¬ p1991) ∨ (¬ p2534) ∨ (¬ p4437) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2630) ∨ (¬ p2657)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3877) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial28834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory18090 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule28834 (meaning t m 1991) (meaning t m 2027) (meaning t m 2534) (meaning t m 2630) (meaning t m 2657) (meaning t m 2766) (meaning t m 3877) (meaning t m 4437) source

theorem rule28837 (p2027 p2137 p2156 p2748 p2839 p3125 p3365 p4118 p4330 p4360 p4734 : Prop) (h : (¬ p4734) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4360) ∨ (¬ p2839) ∨ (¬ p4118) ∨ (¬ p2137) ∨ (¬ p4330) ∨ (¬ p3125) ∨ (¬ p2748) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial28837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory18093 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule28837 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2748) (meaning t m 2839) (meaning t m 3125) (meaning t m 3365) (meaning t m 4118) (meaning t m 4330) (meaning t m 4360) (meaning t m 4734) source

theorem rule28839 (p2482 p4079 p5242 : Prop) (h : (¬ p4079) ∨ (¬ p2482) ∨ p5242) : (¬ p2482) ∨ (¬ p4079) ∨ (p5242) := by
  classical
  tauto

theorem initial28839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 4079)) ∨ (meaning t m 5242) := by
  have source := ElevenTheory.theory18095 (m.theta 0 1) (m.theta 0 4) (m.theta 0 8)
  exact rule28839 (meaning t m 2482) (meaning t m 4079) (meaning t m 5242) source

theorem rule28841 (p2926 p3453 p4189 : Prop) (h : (¬ p4189) ∨ p2926 ∨ (¬ p3453)) : (p2926) ∨ (¬ p3453) ∨ (¬ p4189) := by
  classical
  tauto

theorem initial28841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2926) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4189)) := by
  have source := ElevenTheory.theory18097 (m.theta 1 4) (m.theta 1 7) (m.theta 1 8)
  exact rule28841 (meaning t m 2926) (meaning t m 3453) (meaning t m 4189) source

theorem rule28846 (p3434 p3947 p4777 : Prop) (h : (¬ p3947) ∨ (¬ p3434) ∨ (¬ p4777)) : (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial28846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory18102 (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule28846 (meaning t m 3434) (meaning t m 3947) (meaning t m 4777) source

theorem rule28850 (p2027 p3051 p3367 p3486 p3759 p4399 p4877 : Prop) (h : (¬ p4877) ∨ p2027 ∨ (¬ p3759) ∨ (¬ p4399) ∨ (¬ p3367) ∨ (¬ p3051) ∨ (¬ p3486)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3759) ∨ (¬ p4399) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial28850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory18106 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 5 7)
  exact rule28850 (meaning t m 2027) (meaning t m 3051) (meaning t m 3367) (meaning t m 3486) (meaning t m 3759) (meaning t m 4399) (meaning t m 4877) source

theorem rule28855 (p2027 p2619 p3696 p3758 p3956 p3958 p4113 : Prop) (h : (¬ p2619) ∨ (¬ p3696) ∨ (¬ p4113) ∨ (¬ p3958) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3696) ∨ (¬ p3758) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4113) := by
  classical
  tauto

theorem initial28855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4113)) := by
  have source := ElevenTheory.theory18111 t (m.theta 0 8) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule28855 (meaning t m 2027) (meaning t m 2619) (meaning t m 3696) (meaning t m 3758) (meaning t m 3956) (meaning t m 3958) (meaning t m 4113) source

theorem rule28860 (p3572 p3699 p4244 p4313 : Prop) (h : (¬ p4313) ∨ (¬ p3572) ∨ (¬ p3699) ∨ p4244) : (¬ p3572) ∨ (¬ p3699) ∨ (p4244) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial28860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3699)) ∨ (meaning t m 4244) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory18116 (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7)
  exact rule28860 (meaning t m 3572) (meaning t m 3699) (meaning t m 4244) (meaning t m 4313) source

theorem rule28863 (p2027 p2590 p2797 p2810 p3238 p3984 p4811 : Prop) (h : (¬ p3984) ∨ (¬ p2797) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p4811) ∨ (¬ p2590)) : (p2027) ∨ (¬ p2590) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3984) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial28863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory18119 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule28863 (meaning t m 2027) (meaning t m 2590) (meaning t m 2797) (meaning t m 2810) (meaning t m 3238) (meaning t m 3984) (meaning t m 4811) source

theorem rule28865 (p2027 p2088 p3819 p4242 p4340 p4590 p4737 : Prop) (h : (¬ p3819) ∨ (¬ p4242) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p4590) ∨ (¬ p4340) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3819) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4590) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial28865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory18121 t (m.theta 0 2) (m.theta 0 7) (m.theta 0 8) (m.theta 1 2) (m.theta 2 8) (m.theta 8 9)
  exact rule28865 (meaning t m 2027) (meaning t m 2088) (meaning t m 3819) (meaning t m 4242) (meaning t m 4340) (meaning t m 4590) (meaning t m 4737) source

theorem rule28866 (p2027 p2210 p2780 p2891 p3246 p3950 p4347 p4358 p4736 : Prop) (h : (¬ p3246) ∨ (¬ p2210) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p2780) ∨ (¬ p4358) ∨ (¬ p2891) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial28866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory18122 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28866 (meaning t m 2027) (meaning t m 2210) (meaning t m 2780) (meaning t m 2891) (meaning t m 3246) (meaning t m 3950) (meaning t m 4347) (meaning t m 4358) (meaning t m 4736) source

theorem rule28867 (p1980 p2027 p2241 p2699 p2797 p3027 p3572 : Prop) (h : p2699 ∨ (¬ p1980) ∨ (¬ p2797) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p2241)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2797) ∨ (¬ p3027) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial28867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory18123 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule28867 (meaning t m 1980) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2797) (meaning t m 3027) (meaning t m 3572) source

theorem rule28868 (p2027 p2307 p2788 p3319 p3549 p3917 : Prop) (h : (¬ p2307) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p2788) ∨ p2027 ∨ (¬ p3917)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2788) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial28868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2788)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory18124 t (m.theta 0 6) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule28868 (meaning t m 2027) (meaning t m 2307) (meaning t m 2788) (meaning t m 3319) (meaning t m 3549) (meaning t m 3917) source

theorem rule28869 (p1977 p2027 p2534 p2651 p2766 p3172 p4111 p4437 : Prop) (h : (¬ p4437) ∨ (¬ p2651) ∨ (¬ p3172) ∨ p2766 ∨ (¬ p1977) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2534)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p4111) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial28869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory18125 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule28869 (meaning t m 1977) (meaning t m 2027) (meaning t m 2534) (meaning t m 2651) (meaning t m 2766) (meaning t m 3172) (meaning t m 4111) (meaning t m 4437) source

theorem rule28873 (p1981 p2027 p2187 p2210 p2699 p3097 p3309 p4338 : Prop) (h : (¬ p3309) ∨ (¬ p4338) ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p2210) ∨ (¬ p1981) ∨ p2027 ∨ p2699) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial28873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory18129 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28873 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2210) (meaning t m 2699) (meaning t m 3097) (meaning t m 3309) (meaning t m 4338) source

theorem rule28874 (p1987 p2027 p2388 p2737 p2952 p3286 p4379 p5454 : Prop) (h : (¬ p2952) ∨ p2388 ∨ (¬ p1987) ∨ (¬ p3286) ∨ (¬ p5454) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p4379)) : (¬ p1987) ∨ (p2027) ∨ (p2388) ∨ (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4379) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial28874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory18130 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 9) (m.theta 3 5) (m.theta 3 9)
  exact rule28874 (meaning t m 1987) (meaning t m 2027) (meaning t m 2388) (meaning t m 2737) (meaning t m 2952) (meaning t m 3286) (meaning t m 4379) (meaning t m 5454) source

theorem rule28879 (p2685 p2748 p2996 : Prop) (h : (¬ p2748) ∨ (¬ p2996) ∨ (¬ p2685)) : (¬ p2685) ∨ (¬ p2748) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial28879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory18135 (m.theta 1 3) (m.theta 2 3) (m.theta 3 7)
  exact rule28879 (meaning t m 2685) (meaning t m 2748) (meaning t m 2996) source

theorem rule28882 (p2027 p2493 p2509 p2553 p4432 p4501 : Prop) (h : p2027 ∨ (¬ p4501) ∨ (¬ p2553) ∨ (¬ p2493) ∨ (¬ p4432) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2553) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial28882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory18138 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule28882 (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2553) (meaning t m 4432) (meaning t m 4501) source

theorem rule28883 (p1979 p2027 p2177 p2992 p2996 p2997 p3551 p4155 : Prop) (h : p2027 ∨ (¬ p3551) ∨ (¬ p1979) ∨ (¬ p2992) ∨ (¬ p2996) ∨ p2997 ∨ (¬ p4155) ∨ (¬ p2177)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial28883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory18139 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule28883 (meaning t m 1979) (meaning t m 2027) (meaning t m 2177) (meaning t m 2992) (meaning t m 2996) (meaning t m 2997) (meaning t m 3551) (meaning t m 4155) source

theorem rule28888 (p2027 p2138 p2972 p3371 p4385 p4734 : Prop) (h : (¬ p4385) ∨ (¬ p2972) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3371) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p4385) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial28888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory18144 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 9)
  exact rule28888 (meaning t m 2027) (meaning t m 2138) (meaning t m 2972) (meaning t m 3371) (meaning t m 4385) (meaning t m 4734) source

theorem rule28891 (p2027 p2387 p2500 p3063 p3379 p5015 : Prop) (h : (¬ p5015) ∨ (¬ p3063) ∨ (¬ p2500) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2500) ∨ (¬ p3063) ∨ (¬ p3379) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial28891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2500)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory18147 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 6 8)
  exact rule28891 (meaning t m 2027) (meaning t m 2387) (meaning t m 2500) (meaning t m 3063) (meaning t m 3379) (meaning t m 5015) source

theorem rule28899 (p1991 p2027 p2202 p2440 p3189 p3414 p3919 p4111 : Prop) (h : p2027 ∨ (¬ p1991) ∨ p2202 ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p2440) ∨ (¬ p3919) ∨ (¬ p3189)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3189) ∨ (¬ p3414) ∨ (¬ p3919) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial28899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory18155 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5)
  exact rule28899 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3189) (meaning t m 3414) (meaning t m 3919) (meaning t m 4111) source

theorem rule28901 (p2027 p2248 p2499 p2946 p3256 p3452 p3692 p3956 p4237 p4433 : Prop) (h : (¬ p2946) ∨ (¬ p3956) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p4433) ∨ (¬ p2499) ∨ (¬ p3692) ∨ (¬ p3452) ∨ (¬ p4237) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4237) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial28901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory18157 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule28901 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2946) (meaning t m 3256) (meaning t m 3452) (meaning t m 3692) (meaning t m 3956) (meaning t m 4237) (meaning t m 4433) source

theorem rule28902 (p2027 p2528 p3497 p3692 p4355 p4702 : Prop) (h : (¬ p3692) ∨ p2027 ∨ (¬ p4355) ∨ (¬ p4702) ∨ (¬ p2528) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial28902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory18158 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule28902 (meaning t m 2027) (meaning t m 2528) (meaning t m 3497) (meaning t m 3692) (meaning t m 4355) (meaning t m 4702) source

theorem rule28905 (p2027 p2220 p2528 p3857 p4197 p4198 p4434 : Prop) (h : (¬ p4198) ∨ (¬ p4197) ∨ (¬ p2528) ∨ (¬ p4434) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial28905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory18161 t (m.theta 0 5) (m.theta 0 6) (m.theta 0 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule28905 (meaning t m 2027) (meaning t m 2220) (meaning t m 2528) (meaning t m 3857) (meaning t m 4197) (meaning t m 4198) (meaning t m 4434) source

theorem rule28910 (p1988 p2027 p2114 p2449 p2737 p2761 p2807 p2811 : Prop) (h : (¬ p1988) ∨ (¬ p2449) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p2737) ∨ p2114 ∨ (¬ p2811) ∨ (¬ p2807)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial28910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory18166 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule28910 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2449) (meaning t m 2737) (meaning t m 2761) (meaning t m 2807) (meaning t m 2811) source

theorem rule28913 (p2911 p3553 p3579 : Prop) (h : (¬ p3553) ∨ (¬ p3579) ∨ (¬ p2911)) : (¬ p2911) ∨ (¬ p3553) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial28913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory18169 (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule28913 (meaning t m 2911) (meaning t m 3553) (meaning t m 3579) source

theorem rule28916 (p2027 p2499 p3156 p3212 p3452 p3956 p4208 p4433 p4521 : Prop) (h : (¬ p3156) ∨ (¬ p2499) ∨ (¬ p3212) ∨ (¬ p4433) ∨ (¬ p3956) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4521) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2499) ∨ (¬ p3156) ∨ (¬ p3212) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4208) ∨ (¬ p4433) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial28916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory18172 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8)
  exact rule28916 (meaning t m 2027) (meaning t m 2499) (meaning t m 3156) (meaning t m 3212) (meaning t m 3452) (meaning t m 3956) (meaning t m 4208) (meaning t m 4433) (meaning t m 4521) source

theorem rule28921 (p1981 p2027 p2114 p2122 p2313 p2383 p2829 : Prop) (h : (¬ p2829) ∨ p2114 ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p1981) ∨ (¬ p2122)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial28921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory18177 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28921 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2122) (meaning t m 2313) (meaning t m 2383) (meaning t m 2829) source

theorem rule28923 (p2003 p2027 p2387 p2510 p2528 p2588 p2997 p4347 : Prop) (h : p2997 ∨ (¬ p2003) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4347) ∨ (¬ p2528) ∨ (¬ p2510)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial28923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory18179 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule28923 (meaning t m 2003) (meaning t m 2027) (meaning t m 2387) (meaning t m 2510) (meaning t m 2528) (meaning t m 2588) (meaning t m 2997) (meaning t m 4347) source

theorem rule28925 (p3319 p3654 p5016 : Prop) (h : (¬ p3654) ∨ (¬ p5016) ∨ p3319) : (p3319) ∨ (¬ p3654) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial28925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3319) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory18181 (m.theta 0 6) (m.theta 1 6) (m.theta 6 9)
  exact rule28925 (meaning t m 3319) (meaning t m 3654) (meaning t m 5016) source

theorem rule28930 (p1991 p2027 p2765 p2952 p2982 p4110 p4208 : Prop) (h : (¬ p1991) ∨ (¬ p4110) ∨ p2765 ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2982) ∨ (¬ p4208)) : (¬ p1991) ∨ (p2027) ∨ (p2765) ∨ (¬ p2952) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial28930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory18186 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule28930 (meaning t m 1991) (meaning t m 2027) (meaning t m 2765) (meaning t m 2952) (meaning t m 2982) (meaning t m 4110) (meaning t m 4208) source

theorem rule28932 (p2027 p2254 p2534 p2608 p2657 p2707 p3434 p3950 p4256 : Prop) (h : (¬ p3950) ∨ (¬ p2534) ∨ (¬ p4256) ∨ (¬ p3434) ∨ (¬ p2657) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial28932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory18188 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28932 (meaning t m 2027) (meaning t m 2254) (meaning t m 2534) (meaning t m 2608) (meaning t m 2657) (meaning t m 2707) (meaning t m 3434) (meaning t m 3950) (meaning t m 4256) source

theorem rule28934 (p1990 p2027 p2169 p2284 p2498 p3319 p3956 p4033 p4208 : Prop) (h : (¬ p3319) ∨ (¬ p4033) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2498) ∨ p2169 ∨ (¬ p2284) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2284) ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3956) ∨ (¬ p4033) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial28934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory18190 t (m.theta 1 6) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9)
  exact rule28934 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2284) (meaning t m 2498) (meaning t m 3319) (meaning t m 3956) (meaning t m 4033) (meaning t m 4208) source

theorem rule28935 (p2027 p2313 p2542 p2553 p2577 p2659 p3660 : Prop) (h : (¬ p2553) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2577) ∨ (¬ p3660) ∨ (¬ p2659) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2659) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial28935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory18191 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule28935 (meaning t m 2027) (meaning t m 2313) (meaning t m 2542) (meaning t m 2553) (meaning t m 2577) (meaning t m 2659) (meaning t m 3660) source

theorem rule28937 (p2027 p2132 p2528 p2870 p2881 p3452 p3453 p4261 p4438 p4733 : Prop) (h : (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p2870) ∨ (¬ p4733) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2528) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial28937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory18193 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule28937 (meaning t m 2027) (meaning t m 2132) (meaning t m 2528) (meaning t m 2870) (meaning t m 2881) (meaning t m 3452) (meaning t m 3453) (meaning t m 4261) (meaning t m 4438) (meaning t m 4733) source

theorem rule28938 (p1984 p2027 p2247 p2287 p2630 p4111 p4195 : Prop) (h : (¬ p1984) ∨ p2287 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4111) ∨ (¬ p2630) ∨ (¬ p4195)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2287) ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial28938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory18194 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule28938 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2287) (meaning t m 2630) (meaning t m 4111) (meaning t m 4195) source

theorem rule28942 (p1990 p2027 p2699 p2860 p3073 p3449 p4340 p4359 : Prop) (h : (¬ p4359) ∨ p2699 ∨ p2027 ∨ (¬ p3073) ∨ (¬ p2860) ∨ (¬ p1990) ∨ (¬ p3449) ∨ (¬ p4340)) : (¬ p1990) ∨ (p2027) ∨ (p2699) ∨ (¬ p2860) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p4340) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial28942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory18198 t (m.theta 0 1) (m.theta 1 8) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 8 9)
  exact rule28942 (meaning t m 1990) (meaning t m 2027) (meaning t m 2699) (meaning t m 2860) (meaning t m 3073) (meaning t m 3449) (meaning t m 4340) (meaning t m 4359) source

theorem rule28943 (p4472 p4778 p4841 : Prop) (h : (¬ p4778) ∨ (¬ p4841) ∨ p4472) : (p4472) ∨ (¬ p4778) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial28943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4472) ∨ (¬ (meaning t m 4778)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory18199 t (m.theta 2 3) (m.theta 2 6) (m.theta 2 7)
  exact rule28943 (meaning t m 4472) (meaning t m 4778) (meaning t m 4841) source

theorem rule28946 (p2313 p2785 p3097 p4185 : Prop) (h : (¬ p4185) ∨ (¬ p2785) ∨ (¬ p2313) ∨ p3097) : (¬ p2313) ∨ (¬ p2785) ∨ (p3097) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial28946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 3097) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory18202 (m.theta 0 6) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule28946 (meaning t m 2313) (meaning t m 2785) (meaning t m 3097) (meaning t m 4185) source

theorem rule28950 (p2027 p2241 p3189 p3646 p3744 p4009 p4191 p4524 p5119 : Prop) (h : (¬ p2241) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p4191) ∨ (¬ p4009) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p4524) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial28950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory18206 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule28950 (meaning t m 2027) (meaning t m 2241) (meaning t m 3189) (meaning t m 3646) (meaning t m 3744) (meaning t m 4009) (meaning t m 4191) (meaning t m 4524) (meaning t m 5119) source

theorem rule28954 (p1979 p2027 p2946 p2997 p3097 p3125 p3292 p4190 : Prop) (h : (¬ p1979) ∨ (¬ p3097) ∨ (¬ p4190) ∨ p2997 ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3292) ∨ (¬ p3125)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2946) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3292) ∨ (¬ p4190) := by
  classical
  tauto

theorem initial28954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4190)) := by
  have source := ElevenTheory.theory18210 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule28954 (meaning t m 1979) (meaning t m 2027) (meaning t m 2946) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3292) (meaning t m 4190) source

theorem rule28956 (p1981 p2027 p2114 p2307 p2352 p2584 p2588 p3367 p3759 : Prop) (h : (¬ p3759) ∨ p2114 ∨ (¬ p2588) ∨ (¬ p1981) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p2584) ∨ (¬ p2307) ∨ (¬ p2352)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial28956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory18212 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule28956 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2307) (meaning t m 2352) (meaning t m 2584) (meaning t m 2588) (meaning t m 3367) (meaning t m 3759) source

theorem rule28969 (p2191 p3115 p4282 p4335 : Prop) (h : (¬ p4282) ∨ (¬ p3115) ∨ (¬ p2191) ∨ (¬ p4335)) : (¬ p2191) ∨ (¬ p3115) ∨ (¬ p4282) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial28969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory18225 (m.theta 1 5) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9)
  exact rule28969 (meaning t m 2191) (meaning t m 3115) (meaning t m 4282) (meaning t m 4335) source

theorem rule28972 (p2027 p2459 p2641 p2668 p2696 p2742 p4133 p4242 p4340 p4737 : Prop) (h : (¬ p2742) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2459) ∨ (¬ p4737) ∨ (¬ p4242) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p4133) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial28972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory18228 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule28972 (meaning t m 2027) (meaning t m 2459) (meaning t m 2641) (meaning t m 2668) (meaning t m 2696) (meaning t m 2742) (meaning t m 4133) (meaning t m 4242) (meaning t m 4340) (meaning t m 4737) source

theorem rule28974 (p2839 p3054 p3585 : Prop) (h : (¬ p3054) ∨ (¬ p2839) ∨ (¬ p3585)) : (¬ p2839) ∨ (¬ p3054) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial28974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory18230 (m.theta 1 2) (m.theta 2 4) (m.theta 2 5)
  exact rule28974 (meaning t m 2839) (meaning t m 3054) (meaning t m 3585) source

theorem rule28975 (p2839 p3054 p3367 : Prop) (h : (¬ p3054) ∨ (¬ p2839) ∨ p3367) : (¬ p2839) ∨ (¬ p3054) ∨ (p3367) := by
  classical
  tauto

theorem initial28975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3054)) ∨ (meaning t m 3367) := by
  have source := ElevenTheory.theory18231 (m.theta 1 2) (m.theta 2 4) (m.theta 2 5)
  exact rule28975 (meaning t m 2839) (meaning t m 3054) (meaning t m 3367) source

theorem rule28976 (p2027 p2254 p2417 p2922 p2963 p3324 p3379 p3950 p4347 : Prop) (h : (¬ p3324) ∨ (¬ p3950) ∨ (¬ p3379) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2417) ∨ (¬ p2963) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3950) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial28976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory18232 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule28976 (meaning t m 2027) (meaning t m 2254) (meaning t m 2417) (meaning t m 2922) (meaning t m 2963) (meaning t m 3324) (meaning t m 3379) (meaning t m 3950) (meaning t m 4347) source

theorem rule28977 (p1987 p2027 p2299 p2633 p2737 p3688 p3822 : Prop) (h : (¬ p3822) ∨ (¬ p3688) ∨ p2633 ∨ p2027 ∨ (¬ p2299) ∨ (¬ p1987) ∨ (¬ p2737)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial28977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory18233 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule28977 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2737) (meaning t m 3688) (meaning t m 3822) source

theorem rule28978 (p1987 p2027 p2299 p2313 p2633 p2737 p2785 p3688 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p2785) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial28978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory18234 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule28978 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2633) (meaning t m 2737) (meaning t m 2785) (meaning t m 3688) source

theorem rule28979 (p2012 p2027 p2881 p2938 p3548 p3707 p4425 p5363 : Prop) (h : (¬ p3707) ∨ p2938 ∨ (¬ p5363) ∨ (¬ p4425) ∨ (¬ p3548) ∨ (¬ p2012) ∨ p2027 ∨ (¬ p2881)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3548) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial28979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory18235 t (m.theta 1 7) (m.theta 1 9) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 9 10)
  exact rule28979 (meaning t m 2012) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3548) (meaning t m 3707) (meaning t m 4425) (meaning t m 5363) source

theorem rule28980 (p1987 p2027 p2287 p2696 p2780 p3323 p3917 : Prop) (h : (¬ p2696) ∨ p2287 ∨ p2027 ∨ (¬ p3323) ∨ (¬ p1987) ∨ (¬ p2780) ∨ (¬ p3917)) : (¬ p1987) ∨ (p2027) ∨ (p2287) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3323) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial28980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory18236 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule28980 (meaning t m 1987) (meaning t m 2027) (meaning t m 2287) (meaning t m 2696) (meaning t m 2780) (meaning t m 3323) (meaning t m 3917) source

theorem rule28981 (p2027 p2254 p2518 p2528 p2952 p3379 p3744 p3952 p4604 : Prop) (h : (¬ p2528) ∨ (¬ p2254) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4604) ∨ (¬ p2952) ∨ (¬ p2518) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial28981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory18237 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule28981 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2528) (meaning t m 2952) (meaning t m 3379) (meaning t m 3744) (meaning t m 3952) (meaning t m 4604) source

theorem rule28982 (p1980 p2027 p2563 p2938 p3125 p4037 p4235 : Prop) (h : (¬ p1980) ∨ p2027 ∨ p2938 ∨ (¬ p4037) ∨ (¬ p4235) ∨ (¬ p3125) ∨ (¬ p2563)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial28982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory18238 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule28982 (meaning t m 1980) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 3125) (meaning t m 4037) (meaning t m 4235) source

theorem rule28984 (p2027 p2363 p3365 p3366 p3449 p3591 p4208 p4315 p4318 p4866 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p4318) ∨ (¬ p2363) ∨ (¬ p4208) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p3366) ∨ (¬ p4866)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p4318) ∨ (¬ p4866) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial28984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory18240 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule28984 (meaning t m 2027) (meaning t m 2363) (meaning t m 3365) (meaning t m 3366) (meaning t m 3449) (meaning t m 3591) (meaning t m 4208) (meaning t m 4315) (meaning t m 4318) (meaning t m 4866) (meaning t m 5059) source

theorem rule28990 (p2027 p2619 p3146 p3661 p4118 p4241 p4885 : Prop) (h : (¬ p4241) ∨ (¬ p4118) ∨ (¬ p3661) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4885) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4241) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial28990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory18246 t (m.theta 2 5) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule28990 (meaning t m 2027) (meaning t m 2619) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 4241) (meaning t m 4885) source

theorem rule28992 (p2027 p2192 p2230 p2579 p3096 p4632 : Prop) (h : p2027 ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4632) ∨ (¬ p2230) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial28992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory18248 t (m.theta 0 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule28992 (meaning t m 2027) (meaning t m 2192) (meaning t m 2230) (meaning t m 2579) (meaning t m 3096) (meaning t m 4632) source

theorem rule28993 (p1979 p2027 p2409 p2493 p2657 p2946 p3574 : Prop) (h : (¬ p1979) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2493) ∨ (¬ p2946) ∨ p2409 ∨ (¬ p3574)) : (¬ p1979) ∨ (p2027) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial28993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory18249 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule28993 (meaning t m 1979) (meaning t m 2027) (meaning t m 2409) (meaning t m 2493) (meaning t m 2657) (meaning t m 2946) (meaning t m 3574) source

theorem rule28999 (p1994 p2027 p2440 p2441 p2633 p3246 p3570 p4278 : Prop) (h : (¬ p3570) ∨ p2633 ∨ (¬ p4278) ∨ (¬ p3246) ∨ (¬ p1994) ∨ (¬ p2441) ∨ p2027 ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2441) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial28999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2441)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory18255 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule28999 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2441) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 4278) source

theorem rule29000 (p1994 p2027 p2633 p3246 p3570 p3742 p4278 : Prop) (h : (¬ p3570) ∨ p2633 ∨ (¬ p4278) ∨ (¬ p3246) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3742)) : (¬ p1994) ∨ (p2027) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial29000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory18256 t (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29000 (meaning t m 1994) (meaning t m 2027) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 3742) (meaning t m 4278) source

theorem rule29001 (p1995 p2027 p2441 p2633 p3238 p3246 p3570 p4278 : Prop) (h : p2633 ∨ (¬ p4278) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2441) ∨ (¬ p3570) ∨ (¬ p1995) ∨ (¬ p3238)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2441) ∨ (p2633) ∨ (¬ p3238) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial29001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory18257 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29001 (meaning t m 1995) (meaning t m 2027) (meaning t m 2441) (meaning t m 2633) (meaning t m 3238) (meaning t m 3246) (meaning t m 3570) (meaning t m 4278) source

theorem rule29010 (p2027 p2177 p2307 p2440 p2459 p2657 p2781 p4236 p4948 p5059 : Prop) (h : (¬ p4948) ∨ (¬ p4236) ∨ (¬ p2177) ∨ (¬ p2657) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p5059) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial29010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory18266 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule29010 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2440) (meaning t m 2459) (meaning t m 2657) (meaning t m 2781) (meaning t m 4236) (meaning t m 4948) (meaning t m 5059) source

theorem rule29013 (p3583 p3588 p4136 : Prop) (h : (¬ p4136) ∨ (¬ p3583) ∨ p3588) : (¬ p3583) ∨ (p3588) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial29013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3583)) ∨ (meaning t m 3588) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory18269 (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule29013 (meaning t m 3583) (meaning t m 3588) (meaning t m 4136) source

theorem rule29014 (p1986 p2027 p2241 p2437 p2699 p2727 p3876 : Prop) (h : (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3876) ∨ p2699 ∨ p2027 ∨ (¬ p1986) ∨ (¬ p2241)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2437) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial29014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory18270 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule29014 (meaning t m 1986) (meaning t m 2027) (meaning t m 2241) (meaning t m 2437) (meaning t m 2699) (meaning t m 2727) (meaning t m 3876) source

theorem rule29019 (p2743 p3583 p4313 : Prop) (h : (¬ p4313) ∨ (¬ p3583) ∨ p2743) : (p2743) ∨ (¬ p3583) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial29019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2743) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory18275 (m.theta 1 2) (m.theta 2 3) (m.theta 2 5)
  exact rule29019 (meaning t m 2743) (meaning t m 3583) (meaning t m 4313) source

theorem rule29023 (p1984 p2027 p2230 p2409 p2493 p2579 p2860 p2891 p3369 p3556 p4173 p4885 : Prop) (h : (¬ p3556) ∨ (¬ p1984) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3369) ∨ (¬ p2860) ∨ (¬ p2493) ∨ (¬ p2579) ∨ p2409 ∨ (¬ p4885) ∨ (¬ p2230)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2230) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2860) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4173) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial29023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory18279 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule29023 (meaning t m 1984) (meaning t m 2027) (meaning t m 2230) (meaning t m 2409) (meaning t m 2493) (meaning t m 2579) (meaning t m 2860) (meaning t m 2891) (meaning t m 3369) (meaning t m 3556) (meaning t m 4173) (meaning t m 4885) source

theorem rule29024 (p1981 p2027 p2542 p2545 p2819 p2829 p3583 p3698 : Prop) (h : p2027 ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p1981) ∨ (¬ p3583) ∨ p2545 ∨ (¬ p3698) ∨ (¬ p2542)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3698) := by
  classical
  tauto

theorem initial29024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) := by
  have source := ElevenTheory.theory18280 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 6 8)
  exact rule29024 (meaning t m 1981) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 2819) (meaning t m 2829) (meaning t m 3583) (meaning t m 3698) source

theorem rule29029 (p2027 p3073 p3662 p3859 p3878 p4118 p4701 : Prop) (h : (¬ p3878) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4701) ∨ (¬ p3662) ∨ (¬ p3859)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3662) ∨ (¬ p3859) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial29029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory18285 t (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule29029 (meaning t m 2027) (meaning t m 3073) (meaning t m 3662) (meaning t m 3859) (meaning t m 3878) (meaning t m 4118) (meaning t m 4701) source

theorem rule29031 (p2027 p2651 p2901 p2950 p3556 p4701 : Prop) (h : (¬ p2901) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p4701) ∨ (¬ p2950) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial29031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory18287 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule29031 (meaning t m 2027) (meaning t m 2651) (meaning t m 2901) (meaning t m 2950) (meaning t m 3556) (meaning t m 4701) source

theorem rule29032 (p2027 p2589 p3093 p3319 p3347 p3692 p3880 p3954 p4330 p5216 : Prop) (h : (¬ p3093) ∨ (¬ p5216) ∨ (¬ p3692) ∨ (¬ p3347) ∨ (¬ p4330) ∨ (¬ p2589) ∨ (¬ p3319) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3880)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18288 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule29032 (meaning t m 2027) (meaning t m 2589) (meaning t m 3093) (meaning t m 3319) (meaning t m 3347) (meaning t m 3692) (meaning t m 3880) (meaning t m 3954) (meaning t m 4330) (meaning t m 5216) source

theorem rule29034 (p4365 p4512 p4759 : Prop) (h : (¬ p4759) ∨ (¬ p4512) ∨ p4365) : (p4365) ∨ (¬ p4512) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial29034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4365) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory18290 (m.theta 1 3) (m.theta 1 5) (m.theta 1 6)
  exact rule29034 (meaning t m 4365) (meaning t m 4512) (meaning t m 4759) source

theorem rule29036 (p2027 p2190 p3146 p3324 p4347 p4564 : Prop) (h : (¬ p2190) ∨ (¬ p3324) ∨ (¬ p3146) ∨ (¬ p4564) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial29036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory18292 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule29036 (meaning t m 2027) (meaning t m 2190) (meaning t m 3146) (meaning t m 3324) (meaning t m 4347) (meaning t m 4564) source

theorem rule29042 (p2027 p2230 p2427 p2748 p3365 p3367 p3662 p3759 p3952 p4558 p4734 : Prop) (h : (¬ p3952) ∨ (¬ p3365) ∨ (¬ p4558) ∨ (¬ p2748) ∨ (¬ p2427) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p3759) ∨ (¬ p3952) ∨ (¬ p4558) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial29042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory18298 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule29042 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2748) (meaning t m 3365) (meaning t m 3367) (meaning t m 3662) (meaning t m 3759) (meaning t m 3952) (meaning t m 4558) (meaning t m 4734) source

theorem rule29044 (p2027 p2137 p2156 p2187 p2839 p4436 p4998 : Prop) (h : (¬ p2137) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p4998) ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p4436)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2839) ∨ (¬ p4436) ∨ (¬ p4998) := by
  classical
  tauto

theorem initial29044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 4998)) := by
  have source := ElevenTheory.theory18300 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8)
  exact rule29044 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2187) (meaning t m 2839) (meaning t m 4436) (meaning t m 4998) source

theorem rule29048 (p1990 p2027 p2545 p2668 p2992 p3989 p4111 p4336 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2992) ∨ (¬ p4336) ∨ (¬ p1990) ∨ (¬ p4111) ∨ (¬ p2668)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2668) ∨ (¬ p2992) ∨ (¬ p3989) ∨ (¬ p4111) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial29048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory18304 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule29048 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2668) (meaning t m 2992) (meaning t m 3989) (meaning t m 4111) (meaning t m 4336) source

theorem rule29050 (p2027 p2363 p3325 p3644 p3857 p4276 p4403 : Prop) (h : p2027 ∨ (¬ p4276) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p3325) ∨ (¬ p4403) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p3857) ∨ (¬ p4276) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial29050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory18306 t (m.theta 0 8) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29050 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3644) (meaning t m 3857) (meaning t m 4276) (meaning t m 4403) source

theorem rule29054 (p1984 p2027 p3146 p3578 p3583 p3954 p4340 p4359 : Prop) (h : (¬ p3146) ∨ (¬ p1984) ∨ (¬ p3954) ∨ p2027 ∨ p3578 ∨ (¬ p4359) ∨ (¬ p3583) ∨ (¬ p4340)) : (¬ p1984) ∨ (p2027) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4340) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial29054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory18310 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29054 (meaning t m 1984) (meaning t m 2027) (meaning t m 3146) (meaning t m 3578) (meaning t m 3583) (meaning t m 3954) (meaning t m 4340) (meaning t m 4359) source

theorem rule29056 (p1992 p2027 p2245 p2545 p2608 p2641 p2963 p4111 : Prop) (h : (¬ p1992) ∨ (¬ p2608) ∨ (¬ p2245) ∨ (¬ p2963) ∨ p2545 ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2641)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2245) ∨ (p2545) ∨ (¬ p2608) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial29056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory18312 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule29056 (meaning t m 1992) (meaning t m 2027) (meaning t m 2245) (meaning t m 2545) (meaning t m 2608) (meaning t m 2641) (meaning t m 2963) (meaning t m 4111) source

theorem rule29057 (p2027 p2470 p2528 p2608 p3519 p3591 p3923 p4348 p4376 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p2470) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p3923) ∨ (¬ p3519) ∨ (¬ p2608) ∨ (¬ p2528) ∨ (¬ p3591) ∨ p2027) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial29057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory18313 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29057 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2608) (meaning t m 3519) (meaning t m 3591) (meaning t m 3923) (meaning t m 4348) (meaning t m 4376) (meaning t m 4503) source

theorem rule29059 (p1976 p2027 p2138 p2545 p2743 p2810 p2839 : Prop) (h : p2545 ∨ (¬ p2810) ∨ (¬ p2743) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2839)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2545) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p2839) := by
  classical
  tauto

theorem initial29059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2839)) := by
  have source := ElevenTheory.theory18315 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4)
  exact rule29059 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2545) (meaning t m 2743) (meaning t m 2810) (meaning t m 2839) source

theorem rule29064 (p2027 p3146 p3641 p4158 p5107 p5160 p5175 : Prop) (h : (¬ p3641) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4158) ∨ (¬ p5107) ∨ (¬ p5175) ∨ (¬ p5160)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3641) ∨ (¬ p4158) ∨ (¬ p5107) ∨ (¬ p5160) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial29064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 5107)) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory18320 t (m.theta 2 4) (m.theta 3 9) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule29064 (meaning t m 2027) (meaning t m 3146) (meaning t m 3641) (meaning t m 4158) (meaning t m 5107) (meaning t m 5160) (meaning t m 5175) source

theorem rule29066 (p1988 p2027 p2388 p2761 p2901 p3212 p3556 p4135 : Prop) (h : (¬ p3212) ∨ (¬ p2901) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p4135) ∨ (¬ p1988) ∨ p2388 ∨ (¬ p3556)) : (¬ p1988) ∨ (p2027) ∨ (p2388) ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4135) := by
  classical
  tauto

theorem initial29066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4135)) := by
  have source := ElevenTheory.theory18322 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29066 (meaning t m 1988) (meaning t m 2027) (meaning t m 2388) (meaning t m 2761) (meaning t m 2901) (meaning t m 3212) (meaning t m 3556) (meaning t m 4135) source

theorem rule29067 (p4118 p4340 p4963 : Prop) (h : (¬ p4118) ∨ (¬ p4963) ∨ p4340) : (¬ p4118) ∨ (p4340) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial29067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4118)) ∨ (meaning t m 4340) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory18323 (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule29067 (meaning t m 4118) (meaning t m 4340) (meaning t m 4963) source

theorem rule29068 (p2027 p2668 p3550 p3568 p4260 p5559 : Prop) (h : (¬ p2668) ∨ (¬ p3550) ∨ (¬ p5559) ∨ (¬ p3568) ∨ (¬ p4260) ∨ p2027) : (p2027) ∨ (¬ p2668) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial29068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory18324 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule29068 (meaning t m 2027) (meaning t m 2668) (meaning t m 3550) (meaning t m 3568) (meaning t m 4260) (meaning t m 5559) source

theorem rule29070 (p2027 p2331 p2753 p3347 p3540 p3644 p3755 p4117 p4195 p4330 p4348 p4367 p5216 : Prop) (h : (¬ p3347) ∨ (¬ p4367) ∨ (¬ p4330) ∨ (¬ p5216) ∨ (¬ p4195) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p3644) ∨ (¬ p3540) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4367) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18326 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule29070 (meaning t m 2027) (meaning t m 2331) (meaning t m 2753) (meaning t m 3347) (meaning t m 3540) (meaning t m 3644) (meaning t m 3755) (meaning t m 4117) (meaning t m 4195) (meaning t m 4330) (meaning t m 4348) (meaning t m 4367) (meaning t m 5216) source

theorem rule29071 (p1986 p2027 p2373 p2997 p3054 p3097 p3694 p4110 : Prop) (h : (¬ p3054) ∨ (¬ p1986) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p3694) ∨ p2997 ∨ (¬ p3097)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2373) ∨ (p2997) ∨ (¬ p3054) ∨ (¬ p3097) ∨ (¬ p3694) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial29071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory18327 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule29071 (meaning t m 1986) (meaning t m 2027) (meaning t m 2373) (meaning t m 2997) (meaning t m 3054) (meaning t m 3097) (meaning t m 3694) (meaning t m 4110) source

theorem rule29072 (p2027 p2417 p2598 p2743 p2922 p3172 p3361 p3590 p3950 p4118 p4737 : Prop) (h : (¬ p2922) ∨ (¬ p3361) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p3950) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3590) ∨ (¬ p4737) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p3590) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial29072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory18328 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule29072 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 2743) (meaning t m 2922) (meaning t m 3172) (meaning t m 3361) (meaning t m 3590) (meaning t m 3950) (meaning t m 4118) (meaning t m 4737) source

theorem rule29073 (p2027 p2406 p2499 p3016 p3742 p4644 : Prop) (h : (¬ p4644) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial29073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory18329 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule29073 (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 3016) (meaning t m 3742) (meaning t m 4644) source

theorem rule29075 (p2027 p2532 p2534 p3115 p3497 p4158 : Prop) (h : (¬ p3497) ∨ (¬ p2532) ∨ p2027 ∨ (¬ p4158) ∨ (¬ p2534) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4158) := by
  classical
  tauto

theorem initial29075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4158)) := by
  have source := ElevenTheory.theory18331 t (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule29075 (meaning t m 2027) (meaning t m 2532) (meaning t m 2534) (meaning t m 3115) (meaning t m 3497) (meaning t m 4158) source

theorem rule29079 (p2027 p2254 p2363 p2518 p2928 p2963 p3389 p4079 p4118 p4196 p4596 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p4596) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p2254) ∨ (¬ p4079) ∨ (¬ p3389) ∨ (¬ p2928) ∨ (¬ p4196)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p2963) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial29079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory18335 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule29079 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2518) (meaning t m 2928) (meaning t m 2963) (meaning t m 3389) (meaning t m 4079) (meaning t m 4118) (meaning t m 4196) (meaning t m 4596) source

theorem rule29080 (p2027 p2657 p2946 p3412 p3684 p4210 p4750 : Prop) (h : (¬ p3684) ∨ (¬ p4210) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p2946) ∨ (¬ p3412)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial29080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory18336 t (m.theta 0 3) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule29080 (meaning t m 2027) (meaning t m 2657) (meaning t m 2946) (meaning t m 3412) (meaning t m 3684) (meaning t m 4210) (meaning t m 4750) source

theorem rule29082 (p2027 p2252 p2750 p2819 p2952 p3093 p3570 p3954 p4024 p4133 p4320 : Prop) (h : (¬ p3093) ∨ (¬ p4024) ∨ (¬ p4133) ∨ (¬ p2819) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3570) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4133) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial29082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory18338 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule29082 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2819) (meaning t m 2952) (meaning t m 3093) (meaning t m 3570) (meaning t m 3954) (meaning t m 4024) (meaning t m 4133) (meaning t m 4320) source

theorem rule29085 (p3591 p3834 p4430 : Prop) (h : (¬ p4430) ∨ (¬ p3591) ∨ p3834) : (¬ p3591) ∨ (p3834) ∨ (¬ p4430) := by
  classical
  tauto

theorem initial29085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3591)) ∨ (meaning t m 3834) ∨ (¬ (meaning t m 4430)) := by
  have source := ElevenTheory.theory18341 (m.theta 0 1) (m.theta 1 6) (m.theta 1 9)
  exact rule29085 (meaning t m 3591) (meaning t m 3834) (meaning t m 4430) source

theorem rule29086 (p1997 p2027 p2114 p2737 p2811 p2901 p2946 p4235 : Prop) (h : (¬ p2901) ∨ p2027 ∨ (¬ p1997) ∨ p2114 ∨ (¬ p4235) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p2737)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial29086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory18342 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule29086 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2811) (meaning t m 2901) (meaning t m 2946) (meaning t m 4235) source

theorem rule29088 (p1997 p2027 p2406 p2545 p2657 p2807 p2928 p3579 : Prop) (h : (¬ p2807) ∨ (¬ p3579) ∨ (¬ p2406) ∨ (¬ p1997) ∨ (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p2928)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial29088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory18344 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule29088 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 2928) (meaning t m 3579) source

theorem rule29090 (p2027 p2313 p2553 p2787 p2946 p3005 p3956 p4117 p4315 p4771 : Prop) (h : (¬ p2787) ∨ (¬ p4315) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p4771)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2787) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4771) := by
  classical
  tauto

theorem initial29090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4771)) := by
  have source := ElevenTheory.theory18346 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule29090 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2787) (meaning t m 2946) (meaning t m 3005) (meaning t m 3956) (meaning t m 4117) (meaning t m 4315) (meaning t m 4771) source

theorem rule29097 (p3880 p4335 p4948 : Prop) (h : (¬ p3880) ∨ (¬ p4335) ∨ p4948) : (¬ p3880) ∨ (¬ p4335) ∨ (p4948) := by
  classical
  tauto

theorem initial29097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4335)) ∨ (meaning t m 4948) := by
  have source := ElevenTheory.theory18353 (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule29097 (meaning t m 3880) (meaning t m 4335) (meaning t m 4948) source

theorem rule29098 (p2027 p2534 p3323 p3324 p4345 p4596 : Prop) (h : (¬ p4596) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p4345) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial29098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory18354 t (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule29098 (meaning t m 2027) (meaning t m 2534) (meaning t m 3323) (meaning t m 3324) (meaning t m 4345) (meaning t m 4596) source

theorem rule29099 (p2027 p2248 p2807 p3452 p3475 p3572 p3590 : Prop) (h : p2027 ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3590) ∨ (¬ p3452) ∨ (¬ p3572) ∨ (¬ p3475)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p3452) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial29099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory18355 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule29099 (meaning t m 2027) (meaning t m 2248) (meaning t m 2807) (meaning t m 3452) (meaning t m 3475) (meaning t m 3572) (meaning t m 3590) source

theorem rule29102 (p2023 p2027 p2388 p3005 p3171 p3998 p4315 p5693 : Prop) (h : (¬ p2023) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4315) ∨ p2027 ∨ p2388 ∨ (¬ p5693) ∨ (¬ p3998)) : (¬ p2023) ∨ (p2027) ∨ (p2388) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4315) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial29102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory18358 t (m.theta 0 8) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 10)
  exact rule29102 (meaning t m 2023) (meaning t m 2027) (meaning t m 2388) (meaning t m 3005) (meaning t m 3171) (meaning t m 3998) (meaning t m 4315) (meaning t m 5693) source

theorem rule29103 (p1990 p2027 p2545 p2563 p2685 p2810 p4066 p4235 p4283 : Prop) (h : (¬ p2810) ∨ (¬ p4066) ∨ (¬ p4283) ∨ (¬ p2563) ∨ (¬ p1990) ∨ (¬ p4235) ∨ p2545 ∨ p2027 ∨ (¬ p2685)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial29103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory18359 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule29103 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2563) (meaning t m 2685) (meaning t m 2810) (meaning t m 4066) (meaning t m 4235) (meaning t m 4283) source

theorem rule29104 (p2027 p2532 p2534 p3212 p4120 p4158 : Prop) (h : (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4158) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2534)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4158) := by
  classical
  tauto

theorem initial29104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4158)) := by
  have source := ElevenTheory.theory18360 t (m.theta 0 5) (m.theta 4 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule29104 (meaning t m 2027) (meaning t m 2532) (meaning t m 2534) (meaning t m 3212) (meaning t m 4120) (meaning t m 4158) source

theorem rule29105 (p3032 p3548 p3553 : Prop) (h : (¬ p3032) ∨ (¬ p3553) ∨ p3548) : (¬ p3032) ∨ (p3548) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial29105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3032)) ∨ (meaning t m 3548) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory18361 (m.theta 1 7) (m.theta 3 7) (m.theta 7 8)
  exact rule29105 (meaning t m 3032) (meaning t m 3548) (meaning t m 3553) source

theorem rule29107 (p2027 p2241 p2352 p2598 p2750 p2753 p3032 p3422 p3553 p4133 p4366 : Prop) (h : (¬ p2352) ∨ (¬ p4133) ∨ (¬ p3422) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3032) ∨ (¬ p2750) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial29107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory18363 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8)
  exact rule29107 (meaning t m 2027) (meaning t m 2241) (meaning t m 2352) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3032) (meaning t m 3422) (meaning t m 3553) (meaning t m 4133) (meaning t m 4366) source

theorem rule29109 (p1977 p2027 p2437 p2764 p2928 p3359 p3402 p4425 : Prop) (h : (¬ p1977) ∨ (¬ p3402) ∨ (¬ p2928) ∨ p2027 ∨ p2764 ∨ (¬ p2437) ∨ (¬ p3359) ∨ (¬ p4425)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2437) ∨ (p2764) ∨ (¬ p2928) ∨ (¬ p3359) ∨ (¬ p3402) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial29109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory18365 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 9 10)
  exact rule29109 (meaning t m 1977) (meaning t m 2027) (meaning t m 2437) (meaning t m 2764) (meaning t m 2928) (meaning t m 3359) (meaning t m 3402) (meaning t m 4425) source

theorem rule29110 (p2027 p2252 p2750 p2952 p3440 p3497 p3692 p3830 p3954 p4181 p5122 : Prop) (h : (¬ p3954) ∨ (¬ p3692) ∨ (¬ p2252) ∨ (¬ p3497) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3440) ∨ (¬ p3830) ∨ (¬ p5122) ∨ (¬ p2750) ∨ (¬ p4181)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3440) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial29110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory18366 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 1 9) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29110 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3440) (meaning t m 3497) (meaning t m 3692) (meaning t m 3830) (meaning t m 3954) (meaning t m 4181) (meaning t m 5122) source

theorem rule29113 (p1992 p2027 p2633 p2657 p2743 p3361 p3644 p3742 : Prop) (h : (¬ p3361) ∨ (¬ p1992) ∨ (¬ p2657) ∨ (¬ p3742) ∨ p2027 ∨ p2633 ∨ (¬ p2743) ∨ (¬ p3644)) : (¬ p1992) ∨ (p2027) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial29113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory18369 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule29113 (meaning t m 1992) (meaning t m 2027) (meaning t m 2633) (meaning t m 2657) (meaning t m 2743) (meaning t m 3361) (meaning t m 3644) (meaning t m 3742) source

theorem rule29119 (p2352 p2383 p2578 : Prop) (h : (¬ p2578) ∨ (¬ p2383) ∨ p2352) : (p2352) ∨ (¬ p2383) ∨ (¬ p2578) := by
  classical
  tauto

theorem initial29119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2578)) := by
  have source := ElevenTheory.theory18375 (m.theta 0 6) (m.theta 4 6) (m.theta 6 8)
  exact rule29119 (meaning t m 2352) (meaning t m 2383) (meaning t m 2578) source

theorem rule29124 (p1981 p2027 p2352 p2765 p3115 p3952 p4137 p5045 : Prop) (h : (¬ p2352) ∨ (¬ p1981) ∨ (¬ p3952) ∨ (¬ p3115) ∨ (¬ p5045) ∨ p2765 ∨ p2027 ∨ (¬ p4137)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (p2765) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4137) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial29124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory18380 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9)
  exact rule29124 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2765) (meaning t m 3115) (meaning t m 3952) (meaning t m 4137) (meaning t m 5045) source

theorem rule29127 (p2027 p2156 p2951 p3027 p3368 p3413 p4173 p4652 : Prop) (h : p2027 ∨ (¬ p2951) ∨ (¬ p4173) ∨ (¬ p3413) ∨ (¬ p2156) ∨ (¬ p4652) ∨ (¬ p3368) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2951) ∨ (¬ p3027) ∨ (¬ p3368) ∨ (¬ p3413) ∨ (¬ p4173) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial29127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory18383 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule29127 (meaning t m 2027) (meaning t m 2156) (meaning t m 2951) (meaning t m 3027) (meaning t m 3368) (meaning t m 3413) (meaning t m 4173) (meaning t m 4652) source

theorem rule29130 (p1999 p2027 p2545 p2810 p3506 p3755 p4191 : Prop) (h : (¬ p1999) ∨ (¬ p3755) ∨ p2545 ∨ (¬ p2810) ∨ (¬ p4191) ∨ (¬ p3506) ∨ p2027) : (¬ p1999) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial29130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory18386 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule29130 (meaning t m 1999) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 3506) (meaning t m 3755) (meaning t m 4191) source

theorem rule29134 (p2027 p2166 p2210 p3055 p3146 p3874 p4286 p4736 p5118 : Prop) (h : (¬ p3874) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p2166) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p5118) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3874) ∨ (¬ p4286) ∨ (¬ p4736) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial29134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory18390 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29134 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 3055) (meaning t m 3146) (meaning t m 3874) (meaning t m 4286) (meaning t m 4736) (meaning t m 5118) source

theorem rule29139 (p2027 p2098 p2743 p2952 p3361 p3497 p3609 p4348 p4737 p4905 : Prop) (h : p2027 ∨ (¬ p4905) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p2743) ∨ (¬ p2098) ∨ (¬ p2952) ∨ (¬ p4737) ∨ (¬ p3361) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4737) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial29139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory18395 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29139 (meaning t m 2027) (meaning t m 2098) (meaning t m 2743) (meaning t m 2952) (meaning t m 3361) (meaning t m 3497) (meaning t m 3609) (meaning t m 4348) (meaning t m 4737) (meaning t m 4905) source

theorem rule29140 (p2252 p2742 p2811 : Prop) (h : (¬ p2811) ∨ p2742 ∨ (¬ p2252)) : (¬ p2252) ∨ (p2742) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial29140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (meaning t m 2742) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory18396 (m.theta 0 3) (m.theta 1 3) (m.theta 2 3)
  exact rule29140 (meaning t m 2252) (meaning t m 2742) (meaning t m 2811) source

theorem rule29142 (p2027 p2166 p2210 p3055 p3969 p4425 p4736 p5119 p5160 : Prop) (h : p2027 ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p2166) ∨ (¬ p5160) ∨ (¬ p4425) ∨ (¬ p3969) ∨ (¬ p5119) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial29142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory18398 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule29142 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 3055) (meaning t m 3969) (meaning t m 4425) (meaning t m 4736) (meaning t m 5119) (meaning t m 5160) source

theorem rule29143 (p2027 p2331 p3055 p3323 p3461 p3876 p4786 p4831 p5503 : Prop) (h : (¬ p4831) ∨ p2027 ∨ (¬ p5503) ∨ (¬ p3876) ∨ (¬ p3055) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4786) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial29143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory18399 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule29143 (meaning t m 2027) (meaning t m 2331) (meaning t m 3055) (meaning t m 3323) (meaning t m 3461) (meaning t m 3876) (meaning t m 4786) (meaning t m 4831) (meaning t m 5503) source

theorem rule29145 (p2027 p2533 p3680 p4134 p4347 p4444 : Prop) (h : (¬ p2533) ∨ (¬ p4347) ∨ (¬ p4134) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p4444)) : (p2027) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial29145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory18401 t (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule29145 (meaning t m 2027) (meaning t m 2533) (meaning t m 3680) (meaning t m 4134) (meaning t m 4347) (meaning t m 4444) source

theorem rule29147 (p2027 p2246 p2589 p2744 p2850 p3286 p3366 p3506 p3905 p4444 p4697 p5160 : Prop) (h : (¬ p4444) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3286) ∨ (¬ p5160) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3905) ∨ (¬ p2246) ∨ (¬ p3506) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p2850) ∨ (¬ p3286) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3905) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial29147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory18403 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29147 (meaning t m 2027) (meaning t m 2246) (meaning t m 2589) (meaning t m 2744) (meaning t m 2850) (meaning t m 3286) (meaning t m 3366) (meaning t m 3506) (meaning t m 3905) (meaning t m 4444) (meaning t m 4697) (meaning t m 5160) source

theorem rule29148 (p2027 p3016 p3359 p3483 p4022 p5225 : Prop) (h : (¬ p3483) ∨ (¬ p4022) ∨ (¬ p5225) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p3359)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3483) ∨ (¬ p4022) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial29148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory18404 t (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule29148 (meaning t m 2027) (meaning t m 3016) (meaning t m 3359) (meaning t m 3483) (meaning t m 4022) (meaning t m 5225) source

theorem rule29159 (p1982 p2027 p2911 p2914 p3073 p3941 p5693 : Prop) (h : p2914 ∨ (¬ p3941) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p1982) ∨ (¬ p5693)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3073) ∨ (¬ p3941) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial29159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory18415 t (m.theta 1 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule29159 (meaning t m 1982) (meaning t m 2027) (meaning t m 2911) (meaning t m 2914) (meaning t m 3073) (meaning t m 3941) (meaning t m 5693) source

theorem rule29161 (p2104 p3172 p4236 p4967 : Prop) (h : (¬ p4236) ∨ (¬ p3172) ∨ (¬ p4967) ∨ p2104) : (p2104) ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial29161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2104) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory18417 (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 8)
  exact rule29161 (meaning t m 2104) (meaning t m 3172) (meaning t m 4236) (meaning t m 4967) source

theorem rule29162 (p2027 p2139 p2220 p2982 p3365 p3572 p3880 p3947 p4395 : Prop) (h : (¬ p4395) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3947) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p2982)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3880) ∨ (¬ p3947) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial29162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory18418 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule29162 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 2982) (meaning t m 3365) (meaning t m 3572) (meaning t m 3880) (meaning t m 3947) (meaning t m 4395) source

theorem rule29163 (p2741 p3953 p4245 : Prop) (h : (¬ p4245) ∨ (¬ p2741) ∨ p3953) : (¬ p2741) ∨ (p3953) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial29163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2741)) ∨ (meaning t m 3953) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory18419 (m.theta 1 2) (m.theta 1 3) (m.theta 1 6)
  exact rule29163 (meaning t m 2741) (meaning t m 3953) (meaning t m 4245) source

theorem rule29164 (p2027 p2427 p2717 p3880 p3960 p4115 p4898 : Prop) (h : (¬ p4898) ∨ (¬ p4115) ∨ (¬ p2717) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3960)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2717) ∨ (¬ p3880) ∨ (¬ p3960) ∨ (¬ p4115) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial29164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory18420 t (m.theta 0 8) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule29164 (meaning t m 2027) (meaning t m 2427) (meaning t m 2717) (meaning t m 3880) (meaning t m 3960) (meaning t m 4115) (meaning t m 4898) source

theorem rule29167 (p1991 p2027 p2633 p3414 p3644 p3868 p4391 : Prop) (h : (¬ p1991) ∨ (¬ p3644) ∨ p2633 ∨ (¬ p3414) ∨ (¬ p4391) ∨ p2027 ∨ (¬ p3868)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial29167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory18423 t (m.theta 0 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 10) (m.theta 7 8)
  exact rule29167 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 3414) (meaning t m 3644) (meaning t m 3868) (meaning t m 4391) source

theorem rule29171 (p3582 p3985 p4375 : Prop) (h : (¬ p3582) ∨ (¬ p3985) ∨ p4375) : (¬ p3582) ∨ (¬ p3985) ∨ (p4375) := by
  classical
  tauto

theorem initial29171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3985)) ∨ (meaning t m 4375) := by
  have source := ElevenTheory.theory18427 (m.theta 2 4) (m.theta 2 5) (m.theta 2 6)
  exact rule29171 (meaning t m 3582) (meaning t m 3985) (meaning t m 4375) source

theorem rule29173 (p2027 p2946 p3055 p3156 p3969 p4425 p4786 p5119 p5160 : Prop) (h : (¬ p4786) ∨ (¬ p3969) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p5160) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial29173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory18429 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule29173 (meaning t m 2027) (meaning t m 2946) (meaning t m 3055) (meaning t m 3156) (meaning t m 3969) (meaning t m 4425) (meaning t m 4786) (meaning t m 5119) (meaning t m 5160) source

theorem rule29176 (p2027 p2122 p2588 p3574 p4375 p4753 : Prop) (h : (¬ p4375) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4753) ∨ (¬ p3574) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial29176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory18432 t (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule29176 (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 3574) (meaning t m 4375) (meaning t m 4753) source

theorem rule29177 (p2027 p2253 p2299 p2780 p2946 p3189 p3662 p3822 p4311 p4736 p4902 : Prop) (h : (¬ p4311) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p4736) ∨ (¬ p2946) ∨ (¬ p2299) ∨ (¬ p3822) ∨ (¬ p2253) ∨ (¬ p4902) ∨ (¬ p3662) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3822) ∨ (¬ p4311) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial29177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory18433 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule29177 (meaning t m 2027) (meaning t m 2253) (meaning t m 2299) (meaning t m 2780) (meaning t m 2946) (meaning t m 3189) (meaning t m 3662) (meaning t m 3822) (meaning t m 4311) (meaning t m 4736) (meaning t m 4902) source

theorem rule29178 (p2027 p2230 p2247 p2982 p2996 p3680 p4391 p4831 p5190 : Prop) (h : (¬ p2230) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p2996) ∨ (¬ p2247) ∨ (¬ p4831) ∨ (¬ p3680) ∨ (¬ p4391)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p2996) ∨ (¬ p3680) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial29178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory18434 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule29178 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2982) (meaning t m 2996) (meaning t m 3680) (meaning t m 4391) (meaning t m 4831) (meaning t m 5190) source

theorem rule29179 (p2027 p2230 p2247 p2373 p3146 p4037 p4154 p4604 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p4154) ∨ (¬ p2230) ∨ (¬ p4604) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial29179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory18435 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule29179 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2373) (meaning t m 3146) (meaning t m 4037) (meaning t m 4154) (meaning t m 4604) (meaning t m 5190) source

theorem rule29186 (p1997 p2027 p2542 p3105 p3232 p3359 p3578 p3694 p4388 : Prop) (h : (¬ p3359) ∨ (¬ p3694) ∨ (¬ p3232) ∨ p3578 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p3105) ∨ (¬ p4388)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p3105) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (p3578) ∨ (¬ p3694) ∨ (¬ p4388) := by
  classical
  tauto

theorem initial29186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 3359)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4388)) := by
  have source := ElevenTheory.theory18442 t (m.theta 1 9) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 8) (m.theta 5 9)
  exact rule29186 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 3105) (meaning t m 3232) (meaning t m 3359) (meaning t m 3578) (meaning t m 3694) (meaning t m 4388) source

theorem rule29189 (p2027 p2387 p3552 p3767 p4036 p4429 p4501 p5284 : Prop) (h : (¬ p4429) ∨ (¬ p3552) ∨ (¬ p3767) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p4036) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2387) ∨ (¬ p3552) ∨ (¬ p3767) ∨ (¬ p4036) ∨ (¬ p4429) ∨ (¬ p4501) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial29189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4036)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory18445 t (m.theta 0 6) (m.theta 0 9) (m.theta 3 7) (m.theta 3 9) (m.theta 6 7) (m.theta 6 8) (m.theta 9 10)
  exact rule29189 (meaning t m 2027) (meaning t m 2387) (meaning t m 3552) (meaning t m 3767) (meaning t m 4036) (meaning t m 4429) (meaning t m 4501) (meaning t m 5284) source

theorem rule29190 (p1997 p2027 p2169 p2497 p2542 p2573 p3519 p3574 p3923 : Prop) (h : (¬ p3574) ∨ (¬ p1997) ∨ p2169 ∨ (¬ p3923) ∨ (¬ p3519) ∨ (¬ p2542) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p2497)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2497) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3519) ∨ (¬ p3574) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial29190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory18446 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule29190 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2497) (meaning t m 2542) (meaning t m 2573) (meaning t m 3519) (meaning t m 3574) (meaning t m 3923) source

theorem rule29192 (p1975 p2027 p2373 p2765 p3309 p3923 p4110 p4441 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p4110) ∨ (¬ p1975) ∨ (¬ p3923) ∨ (¬ p4441) ∨ (¬ p3309) ∨ (¬ p2373)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4110) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial29192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory18448 t (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule29192 (meaning t m 1975) (meaning t m 2027) (meaning t m 2373) (meaning t m 2765) (meaning t m 3309) (meaning t m 3923) (meaning t m 4110) (meaning t m 4441) source

theorem rule29193 (p2027 p2319 p2781 p2952 p3136 p3461 p3516 p4035 p4236 p4396 p4444 p5113 : Prop) (h : (¬ p3516) ∨ (¬ p4236) ∨ (¬ p3461) ∨ (¬ p4396) ∨ (¬ p2781) ∨ p2027 ∨ (¬ p5113) ∨ (¬ p2319) ∨ (¬ p4444) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2781) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3461) ∨ (¬ p3516) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial29193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory18449 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule29193 (meaning t m 2027) (meaning t m 2319) (meaning t m 2781) (meaning t m 2952) (meaning t m 3136) (meaning t m 3461) (meaning t m 3516) (meaning t m 4035) (meaning t m 4236) (meaning t m 4396) (meaning t m 4444) (meaning t m 5113) source

theorem rule29197 (p1990 p2027 p2166 p2241 p2284 p2699 p3497 p4365 : Prop) (h : p2699 ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p3497) ∨ (¬ p4365) ∨ (¬ p2284) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p3497) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial29197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory18453 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule29197 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2241) (meaning t m 2284) (meaning t m 2699) (meaning t m 3497) (meaning t m 4365) source

theorem rule29198 (p2027 p2098 p2313 p2553 p2577 p3347 p3365 p3609 p4030 p4137 p4604 p4752 : Prop) (h : (¬ p2577) ∨ (¬ p3347) ∨ (¬ p2313) ∨ (¬ p4137) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4752) ∨ (¬ p4030) ∨ (¬ p2098) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p2553)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4030) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial29198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory18454 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule29198 (meaning t m 2027) (meaning t m 2098) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 3347) (meaning t m 3365) (meaning t m 3609) (meaning t m 4030) (meaning t m 4137) (meaning t m 4604) (meaning t m 4752) source

theorem rule29201 (p2470 p3355 p3358 : Prop) (h : (¬ p3358) ∨ (¬ p2470) ∨ p3355) : (¬ p2470) ∨ (p3355) ∨ (¬ p3358) := by
  classical
  tauto

theorem initial29201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (meaning t m 3355) ∨ (¬ (meaning t m 3358)) := by
  have source := ElevenTheory.theory18457 (m.theta 0 4) (m.theta 4 8) (m.theta 4 9)
  exact rule29201 (meaning t m 2470) (meaning t m 3355) (meaning t m 3358) source

theorem rule29202 (p2470 p2656 p3358 p3359 : Prop) (h : (¬ p3358) ∨ (¬ p2656) ∨ (¬ p2470) ∨ (¬ p3359)) : (¬ p2470) ∨ (¬ p2656) ∨ (¬ p3358) ∨ (¬ p3359) := by
  classical
  tauto

theorem initial29202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3359)) := by
  have source := ElevenTheory.theory18458 (m.theta 0 4) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9)
  exact rule29202 (meaning t m 2470) (meaning t m 2656) (meaning t m 3358) (meaning t m 3359) source

theorem rule29204 (p2027 p2598 p2748 p3365 p3683 p4154 p4972 : Prop) (h : (¬ p3683) ∨ (¬ p2748) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p4154) ∨ (¬ p2598) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4154) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial29204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory18460 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6)
  exact rule29204 (meaning t m 2027) (meaning t m 2598) (meaning t m 2748) (meaning t m 3365) (meaning t m 3683) (meaning t m 4154) (meaning t m 4972) source

theorem rule29207 (p2406 p3054 p3590 p3698 : Prop) (h : (¬ p2406) ∨ (¬ p3590) ∨ (¬ p3698) ∨ (¬ p3054)) : (¬ p2406) ∨ (¬ p3054) ∨ (¬ p3590) ∨ (¬ p3698) := by
  classical
  tauto

theorem initial29207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3698)) := by
  have source := ElevenTheory.theory18463 (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule29207 (meaning t m 2406) (meaning t m 3054) (meaning t m 3590) (meaning t m 3698) source

theorem rule29208 (p2027 p2406 p2499 p2589 p3389 p4711 : Prop) (h : (¬ p2406) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4711) ∨ (¬ p3389) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial29208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory18464 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule29208 (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 2589) (meaning t m 3389) (meaning t m 4711) source

theorem rule29209 (p2190 p2619 p2860 : Prop) (h : (¬ p2860) ∨ (¬ p2190) ∨ p2619) : (¬ p2190) ∨ (p2619) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial29209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (meaning t m 2619) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory18465 (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule29209 (meaning t m 2190) (meaning t m 2619) (meaning t m 2860) source

theorem rule29210 (p2027 p2589 p2608 p3537 p4019 p4322 p4948 p5119 p5193 : Prop) (h : (¬ p2608) ∨ (¬ p4019) ∨ (¬ p5193) ∨ (¬ p4948) ∨ (¬ p2589) ∨ (¬ p5119) ∨ (¬ p3537) ∨ (¬ p4322) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p4019) ∨ (¬ p4322) ∨ (¬ p4948) ∨ (¬ p5119) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial29210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory18466 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule29210 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 3537) (meaning t m 4019) (meaning t m 4322) (meaning t m 4948) (meaning t m 5119) (meaning t m 5193) source

theorem rule29211 (p1979 p2027 p2274 p2313 p2765 p3136 p3177 p3877 p4114 : Prop) (h : (¬ p1979) ∨ p2765 ∨ (¬ p2313) ∨ (¬ p3136) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p4114) ∨ (¬ p3177) ∨ (¬ p3877)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p3136) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4114) := by
  classical
  tauto

theorem initial29211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4114)) := by
  have source := ElevenTheory.theory18467 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7)
  exact rule29211 (meaning t m 1979) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 3136) (meaning t m 3177) (meaning t m 3877) (meaning t m 4114) source

theorem rule29214 (p3582 p3587 p5085 : Prop) (h : (¬ p3587) ∨ (¬ p3582) ∨ p5085) : (¬ p3582) ∨ (¬ p3587) ∨ (p5085) := by
  classical
  tauto

theorem initial29214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3587)) ∨ (meaning t m 5085) := by
  have source := ElevenTheory.theory18470 (m.theta 2 4) (m.theta 2 5) (m.theta 2 7)
  exact rule29214 (meaning t m 3582) (meaning t m 3587) (meaning t m 5085) source

theorem rule29215 (p1988 p2027 p2409 p2761 p2922 p3355 p3540 p4451 : Prop) (h : (¬ p3355) ∨ (¬ p2761) ∨ p2409 ∨ (¬ p3540) ∨ (¬ p1988) ∨ (¬ p4451) ∨ p2027 ∨ (¬ p2922)) : (¬ p1988) ∨ (p2027) ∨ (p2409) ∨ (¬ p2761) ∨ (¬ p2922) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial29215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory18471 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29215 (meaning t m 1988) (meaning t m 2027) (meaning t m 2409) (meaning t m 2761) (meaning t m 2922) (meaning t m 3355) (meaning t m 3540) (meaning t m 4451) source

theorem rule29217 (p2027 p2498 p2753 p3166 p3256 p3379 p3591 p3956 p4117 p4348 p4503 p5216 : Prop) (h : (¬ p4117) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p4348) ∨ (¬ p2498) ∨ (¬ p3956) ∨ (¬ p5216) ∨ (¬ p4503) ∨ (¬ p2753) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2498) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18473 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29217 (meaning t m 2027) (meaning t m 2498) (meaning t m 2753) (meaning t m 3166) (meaning t m 3256) (meaning t m 3379) (meaning t m 3591) (meaning t m 3956) (meaning t m 4117) (meaning t m 4348) (meaning t m 4503) (meaning t m 5216) source

theorem rule29218 (p2027 p2145 p2563 p2807 p3005 p3572 p3646 p3880 p4117 p5063 : Prop) (h : (¬ p3880) ∨ (¬ p5063) ∨ (¬ p2145) ∨ (¬ p2807) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial29218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory18474 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule29218 (meaning t m 2027) (meaning t m 2145) (meaning t m 2563) (meaning t m 2807) (meaning t m 3005) (meaning t m 3572) (meaning t m 3646) (meaning t m 3880) (meaning t m 4117) (meaning t m 5063) source

theorem rule29219 (p2027 p2098 p2579 p2588 p2753 p3347 p3609 p3692 p3945 p4107 p4902 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p2098) ∨ (¬ p4902) ∨ (¬ p2753) ∨ (¬ p2588) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3945) ∨ (¬ p3347) ∨ (¬ p4107) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4902) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18475 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule29219 (meaning t m 2027) (meaning t m 2098) (meaning t m 2579) (meaning t m 2588) (meaning t m 2753) (meaning t m 3347) (meaning t m 3609) (meaning t m 3692) (meaning t m 3945) (meaning t m 4107) (meaning t m 4902) (meaning t m 5216) source

theorem rule29220 (p2027 p2579 p2588 p2753 p2946 p3005 p3347 p3945 p4107 p4117 p4311 p4315 p4902 p5216 : Prop) (h : (¬ p2753) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4311) ∨ (¬ p4902) ∨ (¬ p4315) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p4902) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18476 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29220 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2753) (meaning t m 2946) (meaning t m 3005) (meaning t m 3347) (meaning t m 3945) (meaning t m 4107) (meaning t m 4117) (meaning t m 4311) (meaning t m 4315) (meaning t m 4902) (meaning t m 5216) source

theorem rule29221 (p2927 p3921 p4427 : Prop) (h : (¬ p3921) ∨ (¬ p2927) ∨ p4427) : (¬ p2927) ∨ (¬ p3921) ∨ (p4427) := by
  classical
  tauto

theorem initial29221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3921)) ∨ (meaning t m 4427) := by
  have source := ElevenTheory.theory18477 (m.theta 1 7) (m.theta 4 7) (m.theta 6 7)
  exact rule29221 (meaning t m 2927) (meaning t m 3921) (meaning t m 4427) source

theorem rule29224 (p3555 p4366 p4431 : Prop) (h : (¬ p4431) ∨ (¬ p4366) ∨ p3555) : (p3555) ∨ (¬ p4366) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial29224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3555) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory18480 (m.theta 0 1) (m.theta 1 5) (m.theta 1 7)
  exact rule29224 (meaning t m 3555) (meaning t m 4366) (meaning t m 4431) source

theorem rule29225 (p2027 p2373 p2406 p2928 p4001 p4904 : Prop) (h : (¬ p2406) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4001) ∨ (¬ p4904) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial29225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory18481 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8)
  exact rule29225 (meaning t m 2027) (meaning t m 2373) (meaning t m 2406) (meaning t m 2928) (meaning t m 4001) (meaning t m 4904) source

theorem rule29229 (p2027 p2449 p2685 p2696 p3486 p3555 p3570 p4668 p4733 : Prop) (h : (¬ p3570) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4733) ∨ (¬ p4668) ∨ (¬ p2685) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4668) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial29229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory18485 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule29229 (meaning t m 2027) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4668) (meaning t m 4733) source

theorem rule29238 (p3591 p3860 p4317 : Prop) (h : (¬ p4317) ∨ (¬ p3860) ∨ p3591) : (p3591) ∨ (¬ p3860) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial29238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3591) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory18494 (m.theta 0 1) (m.theta 1 6) (m.theta 1 8)
  exact rule29238 (meaning t m 3591) (meaning t m 3860) (meaning t m 4317) source

theorem rule29244 (p2156 p3212 p4334 : Prop) (h : (¬ p4334) ∨ (¬ p2156) ∨ p3212) : (¬ p2156) ∨ (p3212) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial29244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 3212) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory18500 (m.theta 0 5) (m.theta 5 6) (m.theta 5 9)
  exact rule29244 (meaning t m 2156) (meaning t m 3212) (meaning t m 4334) source

theorem rule29251 (p2027 p2363 p2753 p2774 p2819 p3379 p3555 p4363 p5059 p5216 : Prop) (h : (¬ p2819) ∨ (¬ p5059) ∨ (¬ p2774) ∨ (¬ p2363) ∨ (¬ p5216) ∨ (¬ p4363) ∨ (¬ p3379) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p2753)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial29251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory18507 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule29251 (meaning t m 2027) (meaning t m 2363) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3379) (meaning t m 3555) (meaning t m 4363) (meaning t m 5059) (meaning t m 5216) source

theorem rule29252 (p1994 p2027 p2630 p3623 p3830 p3853 p4035 p4366 : Prop) (h : (¬ p3830) ∨ p2027 ∨ p3623 ∨ (¬ p3853) ∨ (¬ p4035) ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p4366)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p3623) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial29252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory18508 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9)
  exact rule29252 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 3623) (meaning t m 3830) (meaning t m 3853) (meaning t m 4035) (meaning t m 4366) source

theorem rule29253 (p2027 p2352 p3660 p3758 p3989 p4882 : Prop) (h : (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4882) ∨ p2027 ∨ (¬ p3660) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3660) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial29253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory18509 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule29253 (meaning t m 2027) (meaning t m 2352) (meaning t m 3660) (meaning t m 3758) (meaning t m 3989) (meaning t m 4882) source

theorem rule29256 (p1976 p2027 p2138 p2545 p2839 p3016 p3688 p4342 : Prop) (h : (¬ p2138) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p1976) ∨ (¬ p4342) ∨ p2545 ∨ (¬ p3688)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2545) ∨ (¬ p2839) ∨ (¬ p3016) ∨ (¬ p3688) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial29256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory18512 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule29256 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2545) (meaning t m 2839) (meaning t m 3016) (meaning t m 3688) (meaning t m 4342) source

theorem rule29259 (p2010 p2027 p2707 p2842 p3434 p3585 p4278 : Prop) (h : (¬ p3434) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2707) ∨ (¬ p2010) ∨ p2842 ∨ (¬ p3585)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2707) ∨ (p2842) ∨ (¬ p3434) ∨ (¬ p3585) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial29259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory18515 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule29259 (meaning t m 2010) (meaning t m 2027) (meaning t m 2707) (meaning t m 2842) (meaning t m 3434) (meaning t m 3585) (meaning t m 4278) source

theorem rule29260 (p2027 p2132 p2657 p3105 p3680 p4256 p4286 p4789 p5123 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p3105) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p4256) ∨ (¬ p2132) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4789) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial29260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory18516 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule29260 (meaning t m 2027) (meaning t m 2132) (meaning t m 2657) (meaning t m 3105) (meaning t m 3680) (meaning t m 4256) (meaning t m 4286) (meaning t m 4789) (meaning t m 5123) source

theorem rule29261 (p1975 p2027 p2299 p2765 p2870 p2881 p3758 : Prop) (h : (¬ p2881) ∨ (¬ p1975) ∨ (¬ p2299) ∨ p2765 ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2870)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial29261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory18517 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule29261 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2765) (meaning t m 2870) (meaning t m 2881) (meaning t m 3758) source

theorem rule29263 (p2027 p2954 p3005 p4120 p4311 p4315 : Prop) (h : (¬ p2954) ∨ p2027 ∨ (¬ p4311) ∨ (¬ p3005) ∨ (¬ p4120) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2954) ∨ (¬ p3005) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial29263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory18519 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule29263 (meaning t m 2027) (meaning t m 2954) (meaning t m 3005) (meaning t m 4120) (meaning t m 4311) (meaning t m 4315) source

theorem rule29265 (p2027 p2252 p2657 p2750 p3212 p3370 p3371 p3680 p3742 p4191 p4278 p4621 : Prop) (h : (¬ p3212) ∨ (¬ p4191) ∨ (¬ p3680) ∨ (¬ p4621) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p3371) ∨ (¬ p3742) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p4278)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3212) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial29265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory18521 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule29265 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3212) (meaning t m 3370) (meaning t m 3371) (meaning t m 3680) (meaning t m 3742) (meaning t m 4191) (meaning t m 4278) (meaning t m 4621) source

theorem rule29266 (p2027 p2156 p2252 p2750 p3105 p3370 p3371 p3414 p3553 p3758 p4348 p4450 : Prop) (h : (¬ p4450) ∨ (¬ p2156) ∨ (¬ p3371) ∨ (¬ p3370) ∨ (¬ p2750) ∨ (¬ p3414) ∨ (¬ p3105) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p4348) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3105) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3758) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial29266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory18522 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule29266 (meaning t m 2027) (meaning t m 2156) (meaning t m 2252) (meaning t m 2750) (meaning t m 3105) (meaning t m 3370) (meaning t m 3371) (meaning t m 3414) (meaning t m 3553) (meaning t m 3758) (meaning t m 4348) (meaning t m 4450) source

theorem rule29267 (p1977 p2027 p2810 p2811 p3008 p3166 p3574 p4360 : Prop) (h : p3008 ∨ (¬ p3574) ∨ (¬ p1977) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p4360)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2810) ∨ (¬ p2811) ∨ (p3008) ∨ (¬ p3166) ∨ (¬ p3574) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial29267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2811)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory18523 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6)
  exact rule29267 (meaning t m 1977) (meaning t m 2027) (meaning t m 2810) (meaning t m 2811) (meaning t m 3008) (meaning t m 3166) (meaning t m 3574) (meaning t m 4360) source

theorem rule29269 (p2027 p2144 p2252 p2363 p2619 p2750 p2753 p3051 p3172 p4118 p4244 p4433 : Prop) (h : (¬ p3172) ∨ (¬ p3051) ∨ (¬ p2252) ∨ (¬ p2144) ∨ (¬ p2750) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p4118) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p4244)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4244) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial29269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory18525 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule29269 (meaning t m 2027) (meaning t m 2144) (meaning t m 2252) (meaning t m 2363) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3051) (meaning t m 3172) (meaning t m 4118) (meaning t m 4244) (meaning t m 4433) source

theorem rule29270 (p2027 p2132 p2534 p2657 p2870 p3246 p3950 p4256 p4789 : Prop) (h : (¬ p3246) ∨ (¬ p2870) ∨ (¬ p2657) ∨ (¬ p4789) ∨ (¬ p3950) ∨ (¬ p2534) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial29270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory18526 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule29270 (meaning t m 2027) (meaning t m 2132) (meaning t m 2534) (meaning t m 2657) (meaning t m 2870) (meaning t m 3246) (meaning t m 3950) (meaning t m 4256) (meaning t m 4789) source

theorem rule29273 (p2027 p2230 p2252 p2741 p2753 p2963 p2982 p3324 p3680 p4419 p5123 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p2963) ∨ (¬ p2741) ∨ (¬ p3324) ∨ (¬ p2252) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4419) ∨ (¬ p2753) ∨ (¬ p5123) ∨ (¬ p2982) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p3680) ∨ (¬ p4419) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial29273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory18529 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule29273 (meaning t m 2027) (meaning t m 2230) (meaning t m 2252) (meaning t m 2741) (meaning t m 2753) (meaning t m 2963) (meaning t m 2982) (meaning t m 3324) (meaning t m 3680) (meaning t m 4419) (meaning t m 5123) (meaning t m 5580) source

theorem rule29275 (p1982 p2027 p2528 p2611 p3362 p3389 p3641 p3876 : Prop) (h : (¬ p3389) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p3876) ∨ p2611 ∨ (¬ p1982) ∨ (¬ p2528) ∨ (¬ p3362)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (p2611) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial29275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory18531 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule29275 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2611) (meaning t m 3362) (meaning t m 3389) (meaning t m 3641) (meaning t m 3876) source

theorem rule29277 (p2027 p2249 p2341 p2459 p2952 p3027 p3744 p4066 p4173 p4282 p4604 : Prop) (h : (¬ p2459) ∨ (¬ p4604) ∨ (¬ p4066) ∨ (¬ p4282) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4173) ∨ (¬ p2952) ∨ (¬ p2249) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p4066) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial29277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory18533 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule29277 (meaning t m 2027) (meaning t m 2249) (meaning t m 2341) (meaning t m 2459) (meaning t m 2952) (meaning t m 3027) (meaning t m 3744) (meaning t m 4066) (meaning t m 4173) (meaning t m 4282) (meaning t m 4604) source

theorem rule29279 (p2027 p2088 p2166 p2534 p3696 p4607 p4632 : Prop) (h : p2027 ∨ (¬ p4632) ∨ (¬ p2534) ∨ (¬ p4607) ∨ (¬ p2088) ∨ (¬ p2166) ∨ (¬ p3696)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2166) ∨ (¬ p2534) ∨ (¬ p3696) ∨ (¬ p4607) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial29279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory18535 t (m.theta 0 8) (m.theta 1 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule29279 (meaning t m 2027) (meaning t m 2088) (meaning t m 2166) (meaning t m 2534) (meaning t m 3696) (meaning t m 4607) (meaning t m 4632) source

theorem rule29280 (p2481 p3960 p4383 : Prop) (h : (¬ p3960) ∨ (¬ p2481) ∨ p4383) : (¬ p2481) ∨ (¬ p3960) ∨ (p4383) := by
  classical
  tauto

theorem initial29280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 3960)) ∨ (meaning t m 4383) := by
  have source := ElevenTheory.theory18536 (m.theta 0 8) (m.theta 4 8) (m.theta 7 8)
  exact rule29280 (meaning t m 2481) (meaning t m 3960) (meaning t m 4383) source

theorem rule29281 (p2027 p2245 p2641 p2717 p2963 p2996 p3471 p3570 p4362 p4733 : Prop) (h : (¬ p3570) ∨ (¬ p2717) ∨ (¬ p4362) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2245) ∨ (¬ p2963) ∨ (¬ p2641) ∨ (¬ p4733) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2717) ∨ (¬ p2963) ∨ (¬ p2996) ∨ (¬ p3471) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial29281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory18537 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule29281 (meaning t m 2027) (meaning t m 2245) (meaning t m 2641) (meaning t m 2717) (meaning t m 2963) (meaning t m 2996) (meaning t m 3471) (meaning t m 3570) (meaning t m 4362) (meaning t m 4733) source

theorem rule29282 (p2027 p2264 p3146 p3955 p3960 p4115 p4347 p4361 : Prop) (h : (¬ p3955) ∨ (¬ p4361) ∨ (¬ p4115) ∨ (¬ p2264) ∨ (¬ p3960) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3146) ∨ (¬ p3955) ∨ (¬ p3960) ∨ (¬ p4115) ∨ (¬ p4347) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial29282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory18538 t (m.theta 0 8) (m.theta 3 7) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule29282 (meaning t m 2027) (meaning t m 2264) (meaning t m 3146) (meaning t m 3955) (meaning t m 3960) (meaning t m 4115) (meaning t m 4347) (meaning t m 4361) source

theorem rule29283 (p1981 p2027 p2307 p2352 p2584 p2588 p2656 p2688 p2727 : Prop) (h : (¬ p2588) ∨ (¬ p2307) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p2727) ∨ (¬ p2584) ∨ p2688 ∨ (¬ p2352)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial29283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory18539 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule29283 (meaning t m 1981) (meaning t m 2027) (meaning t m 2307) (meaning t m 2352) (meaning t m 2584) (meaning t m 2588) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) source

theorem rule29285 (p1985 p2027 p2132 p2427 p2611 p2860 p4110 : Prop) (h : (¬ p2132) ∨ p2611 ∨ p2027 ∨ (¬ p2427) ∨ (¬ p1985) ∨ (¬ p2860) ∨ (¬ p4110)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2427) ∨ (p2611) ∨ (¬ p2860) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial29285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory18541 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule29285 (meaning t m 1985) (meaning t m 2027) (meaning t m 2132) (meaning t m 2427) (meaning t m 2611) (meaning t m 2860) (meaning t m 4110) source

theorem rule29287 (p2027 p2387 p2668 p2787 p3333 p3362 p3389 p3876 p4037 p5322 : Prop) (h : (¬ p3389) ∨ (¬ p3876) ∨ (¬ p3362) ∨ p2027 ∨ (¬ p2787) ∨ (¬ p2668) ∨ (¬ p5322) ∨ (¬ p4037) ∨ (¬ p3333) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4037) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial29287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory18543 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9)
  exact rule29287 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2787) (meaning t m 3333) (meaning t m 3362) (meaning t m 3389) (meaning t m 3876) (meaning t m 4037) (meaning t m 5322) source

theorem rule29288 (p2027 p2138 p2630 p2696 p4316 p4701 : Prop) (h : (¬ p2138) ∨ (¬ p4316) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4701) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p4316) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial29288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory18544 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule29288 (meaning t m 2027) (meaning t m 2138) (meaning t m 2630) (meaning t m 2696) (meaning t m 4316) (meaning t m 4701) source

theorem rule29300 (p2027 p2470 p2501 p2579 p3923 p4157 : Prop) (h : (¬ p3923) ∨ (¬ p2579) ∨ (¬ p4157) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p2501)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2501) ∨ (¬ p2579) ∨ (¬ p3923) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial29300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory18556 t (m.theta 0 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule29300 (meaning t m 2027) (meaning t m 2470) (meaning t m 2501) (meaning t m 2579) (meaning t m 3923) (meaning t m 4157) source

theorem rule29309 (p2027 p2662 p2810 p2946 p3156 p3346 p3969 p4425 p4790 p5119 : Prop) (h : (¬ p3969) ∨ (¬ p3346) ∨ (¬ p5119) ∨ (¬ p2946) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p4790)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3346) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p4790) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial29309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory18565 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule29309 (meaning t m 2027) (meaning t m 2662) (meaning t m 2810) (meaning t m 2946) (meaning t m 3156) (meaning t m 3346) (meaning t m 3969) (meaning t m 4425) (meaning t m 4790) (meaning t m 5119) source

theorem rule29312 (p1979 p2027 p2114 p2210 p2891 p3954 p4320 : Prop) (h : (¬ p2891) ∨ (¬ p2210) ∨ (¬ p1979) ∨ (¬ p3954) ∨ p2114 ∨ p2027 ∨ (¬ p4320)) : (¬ p1979) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3954) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial29312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory18568 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule29312 (meaning t m 1979) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2891) (meaning t m 3954) (meaning t m 4320) source

theorem rule29313 (p1983 p2027 p2114 p2210 p2417 p2891 p3954 p4001 : Prop) (h : (¬ p2417) ∨ (¬ p1983) ∨ p2027 ∨ p2114 ∨ (¬ p2891) ∨ (¬ p3954) ∨ (¬ p2210) ∨ (¬ p4001)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2417) ∨ (¬ p2891) ∨ (¬ p3954) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial29313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory18569 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule29313 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2417) (meaning t m 2891) (meaning t m 3954) (meaning t m 4001) source

theorem rule29316 (p2657 p2963 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2963) ∨ p2657) : (p2657) ∨ (¬ p2963) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial29316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2657) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory18572 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule29316 (meaning t m 2657) (meaning t m 2963) (meaning t m 3019) source

theorem rule29317 (p2023 p2027 p2355 p3005 p3256 p3572 p4261 : Prop) (h : (¬ p3256) ∨ p2355 ∨ (¬ p3572) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p2023) ∨ (¬ p3005)) : (¬ p2023) ∨ (p2027) ∨ (p2355) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3572) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial29317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory18573 t (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule29317 (meaning t m 2023) (meaning t m 2027) (meaning t m 2355) (meaning t m 3005) (meaning t m 3256) (meaning t m 3572) (meaning t m 4261) source

theorem rule29318 (p2504 p4757 p4976 : Prop) (h : (¬ p4976) ∨ (¬ p2504) ∨ p4757) : (¬ p2504) ∨ (p4757) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial29318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (meaning t m 4757) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory18574 t (m.theta 1 6) (m.theta 3 6) (m.theta 4 6)
  exact rule29318 (meaning t m 2504) (meaning t m 4757) (meaning t m 4976) source

end SunPrize.SMT
