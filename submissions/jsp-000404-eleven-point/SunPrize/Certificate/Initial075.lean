import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory059
import SunPrize.Certificate.Theory060
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule34051 (p2027 p2246 p2352 p2651 p2744 p2870 p3016 p3556 p3645 p3694 p4134 p4874 : Prop) (h : (¬ p2352) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p3556) ∨ (¬ p2870) ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p3694) ∨ (¬ p4874) ∨ (¬ p2744) ∨ (¬ p3645)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p3016) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3694) ∨ (¬ p4134) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial34051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory23307 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule34051 (meaning t m 2027) (meaning t m 2246) (meaning t m 2352) (meaning t m 2651) (meaning t m 2744) (meaning t m 2870) (meaning t m 3016) (meaning t m 3556) (meaning t m 3645) (meaning t m 3694) (meaning t m 4134) (meaning t m 4874) source

theorem rule34058 (p2027 p2246 p2553 p2651 p2744 p2870 p3016 p3556 p3645 p3694 p4501 p4506 p4874 : Prop) (h : (¬ p2744) ∨ (¬ p3645) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4874) ∨ (¬ p4506) ∨ (¬ p2553) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p3016) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p3016) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3694) ∨ (¬ p4501) ∨ (¬ p4506) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial34058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory23314 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule34058 (meaning t m 2027) (meaning t m 2246) (meaning t m 2553) (meaning t m 2651) (meaning t m 2744) (meaning t m 2870) (meaning t m 3016) (meaning t m 3556) (meaning t m 3645) (meaning t m 3694) (meaning t m 4501) (meaning t m 4506) (meaning t m 4874) source

theorem rule34060 (p1983 p2027 p2911 p2914 p3434 p3685 p3941 p5612 : Prop) (h : (¬ p3685) ∨ p2914 ∨ (¬ p1983) ∨ (¬ p3941) ∨ (¬ p5612) ∨ (¬ p3434) ∨ p2027 ∨ (¬ p2911)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3434) ∨ (¬ p3685) ∨ (¬ p3941) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial34060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory23316 t (m.theta 2 7) (m.theta 2 8) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule34060 (meaning t m 1983) (meaning t m 2027) (meaning t m 2911) (meaning t m 2914) (meaning t m 3434) (meaning t m 3685) (meaning t m 3941) (meaning t m 5612) source

theorem rule34062 (p2027 p2136 p2247 p2744 p3073 p3366 p3449 p3646 p3989 p5118 p5580 : Prop) (h : (¬ p5118) ∨ (¬ p3989) ∨ (¬ p2247) ∨ (¬ p3646) ∨ (¬ p5580) ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2136)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial34062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory23318 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule34062 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2744) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3646) (meaning t m 3989) (meaning t m 5118) (meaning t m 5580) source

theorem rule34064 (p2027 p2246 p2528 p2651 p2744 p2870 p3083 p3556 p3645 p4385 p4874 p5059 : Prop) (h : p2027 ∨ (¬ p3556) ∨ (¬ p2246) ∨ (¬ p3645) ∨ (¬ p5059) ∨ (¬ p2744) ∨ (¬ p4874) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p2870) ∨ (¬ p2528) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4385) ∨ (¬ p4874) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial34064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory23320 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule34064 (meaning t m 2027) (meaning t m 2246) (meaning t m 2528) (meaning t m 2651) (meaning t m 2744) (meaning t m 2870) (meaning t m 3083) (meaning t m 3556) (meaning t m 3645) (meaning t m 4385) (meaning t m 4874) (meaning t m 5059) source

theorem rule34068 (p2027 p2136 p2247 p2744 p2761 p3093 p3319 p3366 p4032 p4322 p4621 : Prop) (h : (¬ p3093) ∨ (¬ p2247) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p4032) ∨ (¬ p2761) ∨ (¬ p3319) ∨ (¬ p4621) ∨ (¬ p3366) ∨ (¬ p2136) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial34068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory23324 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule34068 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2744) (meaning t m 2761) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 4032) (meaning t m 4322) (meaning t m 4621) source

theorem rule34070 (p1979 p2027 p2247 p2688 p3707 p3830 p4314 p5284 : Prop) (h : p2027 ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4314) ∨ (¬ p2247) ∨ (¬ p5284) ∨ p2688 ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4314) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial34070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4314)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory23326 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 3 9) (m.theta 9 10)
  exact rule34070 (meaning t m 1979) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3707) (meaning t m 3830) (meaning t m 4314) (meaning t m 5284) source

theorem rule34077 (p1994 p2027 p2187 p2630 p2765 p2963 p3324 p3361 : Prop) (h : (¬ p3324) ∨ (¬ p3361) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p1994) ∨ (¬ p2187) ∨ p2765) : (¬ p1994) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2630) ∨ (p2765) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial34077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory23333 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule34077 (meaning t m 1994) (meaning t m 2027) (meaning t m 2187) (meaning t m 2630) (meaning t m 2765) (meaning t m 2963) (meaning t m 3324) (meaning t m 3361) source

theorem rule34084 (p2005 p2027 p2409 p3399 p3452 p3527 p3581 p3644 : Prop) (h : (¬ p3581) ∨ (¬ p2005) ∨ (¬ p3399) ∨ (¬ p3527) ∨ p2409 ∨ (¬ p3452) ∨ (¬ p3644) ∨ p2027) : (¬ p2005) ∨ (p2027) ∨ (p2409) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p3581) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial34084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory23340 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule34084 (meaning t m 2005) (meaning t m 2027) (meaning t m 2409) (meaning t m 3399) (meaning t m 3452) (meaning t m 3527) (meaning t m 3581) (meaning t m 3644) source

theorem rule34085 (p1976 p2027 p2177 p2997 p3365 p3553 p4067 p4195 : Prop) (h : (¬ p1976) ∨ (¬ p4195) ∨ p2997 ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p2177) ∨ (¬ p4067)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial34085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory23341 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34085 (meaning t m 1976) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3365) (meaning t m 3553) (meaning t m 4067) (meaning t m 4195) source

theorem rule34086 (p2027 p2136 p2761 p2860 p3366 p3516 p3543 p3646 p4385 p4444 p4793 p5059 : Prop) (h : (¬ p2761) ∨ (¬ p3366) ∨ (¬ p2136) ∨ (¬ p4385) ∨ p2027 ∨ (¬ p3543) ∨ (¬ p3646) ∨ (¬ p4793) ∨ (¬ p3516) ∨ (¬ p2860) ∨ (¬ p4444) ∨ (¬ p5059)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2761) ∨ (¬ p2860) ∨ (¬ p3366) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3646) ∨ (¬ p4385) ∨ (¬ p4444) ∨ (¬ p4793) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial34086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4793)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory23342 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34086 (meaning t m 2027) (meaning t m 2136) (meaning t m 2761) (meaning t m 2860) (meaning t m 3366) (meaning t m 3516) (meaning t m 3543) (meaning t m 3646) (meaning t m 4385) (meaning t m 4444) (meaning t m 4793) (meaning t m 5059) source

theorem rule34088 (p2027 p2743 p3309 p3822 p4752 p4869 p5220 : Prop) (h : (¬ p5220) ∨ (¬ p4752) ∨ (¬ p4869) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3309) ∨ (¬ p2743)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4752) ∨ (¬ p4869) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial34088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory23344 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule34088 (meaning t m 2027) (meaning t m 2743) (meaning t m 3309) (meaning t m 3822) (meaning t m 4752) (meaning t m 4869) (meaning t m 5220) source

theorem rule34089 (p2027 p2138 p2352 p2573 p3979 p4322 p4385 p4419 p5119 : Prop) (h : (¬ p4419) ∨ (¬ p3979) ∨ (¬ p2573) ∨ (¬ p5119) ∨ (¬ p4385) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4419) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial34089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory23345 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule34089 (meaning t m 2027) (meaning t m 2138) (meaning t m 2352) (meaning t m 2573) (meaning t m 3979) (meaning t m 4322) (meaning t m 4385) (meaning t m 4419) (meaning t m 5119) source

theorem rule34092 (p2656 p3540 p3742 : Prop) (h : (¬ p3742) ∨ (¬ p2656) ∨ p3540) : (¬ p2656) ∨ (p3540) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial34092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2656)) ∨ (meaning t m 3540) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory23348 (m.theta 0 4) (m.theta 3 4) (m.theta 4 7)
  exact rule34092 (meaning t m 2656) (meaning t m 3540) (meaning t m 3742) source

theorem rule34093 (p1995 p2027 p2230 p2462 p2656 p3238 p3742 p4278 : Prop) (h : (¬ p2656) ∨ (¬ p1995) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3742) ∨ p2462 ∨ p2027 ∨ (¬ p4278)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (p2462) ∨ (¬ p2656) ∨ (¬ p3238) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial34093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory23349 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule34093 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2462) (meaning t m 2656) (meaning t m 3238) (meaning t m 3742) (meaning t m 4278) source

theorem rule34098 (p1995 p2027 p2230 p2534 p2656 p2766 p3238 p4256 : Prop) (h : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p4256) ∨ p2766 ∨ p2027 ∨ (¬ p1995) ∨ (¬ p2656) ∨ (¬ p2534)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2534) ∨ (¬ p2656) ∨ (p2766) ∨ (¬ p3238) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial34098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory23354 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule34098 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2534) (meaning t m 2656) (meaning t m 2766) (meaning t m 3238) (meaning t m 4256) source

theorem rule34101 (p3413 p3497 p3693 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p3693) ∨ (¬ p3413) ∨ p3497) : (¬ p3413) ∨ (p3497) ∨ (¬ p3693) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial34101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3413)) ∨ (meaning t m 3497) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory23357 (m.theta 3 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8)
  exact rule34101 (meaning t m 3413) (meaning t m 3497) (meaning t m 3693) (meaning t m 4256) source

theorem rule34103 (p2383 p3322 p3654 : Prop) (h : (¬ p3322) ∨ (¬ p3654) ∨ p2383) : (p2383) ∨ (¬ p3322) ∨ (¬ p3654) := by
  classical
  tauto

theorem initial34103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2383) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3654)) := by
  have source := ElevenTheory.theory23359 (m.theta 0 6) (m.theta 6 8) (m.theta 6 9)
  exact rule34103 (meaning t m 2383) (meaning t m 3322) (meaning t m 3654) source

theorem rule34107 (p2027 p2098 p2952 p3055 p3361 p4019 p4208 p4322 p4749 p5119 : Prop) (h : (¬ p4749) ∨ (¬ p3361) ∨ (¬ p4322) ∨ (¬ p3055) ∨ (¬ p4019) ∨ (¬ p2098) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2952) ∨ (¬ p3055) ∨ (¬ p3361) ∨ (¬ p4019) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4749) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial34107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory23363 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule34107 (meaning t m 2027) (meaning t m 2098) (meaning t m 2952) (meaning t m 3055) (meaning t m 3361) (meaning t m 4019) (meaning t m 4208) (meaning t m 4322) (meaning t m 4749) (meaning t m 5119) source

theorem rule34108 (p2027 p2254 p2493 p2950 p3266 p3379 p3564 p4120 p4311 p4330 p4349 p5284 : Prop) (h : (¬ p2493) ∨ (¬ p2950) ∨ (¬ p4311) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3379) ∨ (¬ p4120) ∨ (¬ p2254) ∨ (¬ p4349) ∨ (¬ p3266) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2493) ∨ (¬ p2950) ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p4330) ∨ (¬ p4349) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial34108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory23364 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34108 (meaning t m 2027) (meaning t m 2254) (meaning t m 2493) (meaning t m 2950) (meaning t m 3266) (meaning t m 3379) (meaning t m 3564) (meaning t m 4120) (meaning t m 4311) (meaning t m 4330) (meaning t m 4349) (meaning t m 5284) source

theorem rule34109 (p2027 p2138 p3073 p3366 p3449 p3452 p3744 p3758 p4376 p4604 : Prop) (h : (¬ p3452) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p3758) ∨ (¬ p3744) ∨ (¬ p3449)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4376) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial34109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory23365 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule34109 (meaning t m 2027) (meaning t m 2138) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 3744) (meaning t m 3758) (meaning t m 4376) (meaning t m 4604) source

theorem rule34110 (p2027 p2383 p2810 p3309 p3365 p3742 p3923 p4712 p4736 p5020 : Prop) (h : (¬ p2383) ∨ (¬ p3365) ∨ (¬ p5020) ∨ (¬ p4736) ∨ (¬ p2810) ∨ (¬ p3742) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p4712) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2810) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p3923) ∨ (¬ p4712) ∨ (¬ p4736) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial34110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory23366 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule34110 (meaning t m 2027) (meaning t m 2383) (meaning t m 2810) (meaning t m 3309) (meaning t m 3365) (meaning t m 3742) (meaning t m 3923) (meaning t m 4712) (meaning t m 4736) (meaning t m 5020) source

theorem rule34112 (p2027 p2254 p2417 p2922 p2952 p3379 p3497 p3692 p3950 : Prop) (h : (¬ p2952) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3497) ∨ (¬ p2922) ∨ (¬ p2417) ∨ (¬ p3379) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial34112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory23368 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule34112 (meaning t m 2027) (meaning t m 2254) (meaning t m 2417) (meaning t m 2922) (meaning t m 2952) (meaning t m 3379) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule34113 (p2027 p2254 p2417 p2922 p2952 p3379 p3744 p3952 p4625 : Prop) (h : (¬ p2952) ∨ (¬ p3744) ∨ (¬ p4625) ∨ (¬ p3379) ∨ (¬ p2922) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial34113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory23369 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule34113 (meaning t m 2027) (meaning t m 2254) (meaning t m 2417) (meaning t m 2922) (meaning t m 2952) (meaning t m 3379) (meaning t m 3744) (meaning t m 3952) (meaning t m 4625) source

theorem rule34118 (p1976 p2027 p3128 p3365 p3461 p4195 p5274 p5284 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p3365) ∨ (¬ p5284) ∨ (¬ p3461) ∨ (¬ p5274) ∨ p3128 ∨ (¬ p4195)) : (¬ p1976) ∨ (p2027) ∨ (p3128) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p4195) ∨ (¬ p5274) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial34118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory23374 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule34118 (meaning t m 1976) (meaning t m 2027) (meaning t m 3128) (meaning t m 3365) (meaning t m 3461) (meaning t m 4195) (meaning t m 5274) (meaning t m 5284) source

theorem rule34120 (p2027 p2254 p2922 p2952 p3379 p3497 p3868 p5560 p5568 : Prop) (h : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p5568) ∨ (¬ p5560) ∨ (¬ p2922) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3868) ∨ (¬ p5560) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial34120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 5560)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory23376 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 10)
  exact rule34120 (meaning t m 2027) (meaning t m 2254) (meaning t m 2922) (meaning t m 2952) (meaning t m 3379) (meaning t m 3497) (meaning t m 3868) (meaning t m 5560) (meaning t m 5568) source

theorem rule34122 (p2027 p2138 p2241 p3189 p3256 p3744 p3758 p4604 p4736 : Prop) (h : p2027 ∨ (¬ p3744) ∨ (¬ p3256) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p4604) ∨ (¬ p2138) ∨ (¬ p4736) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23378 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule34122 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 3189) (meaning t m 3256) (meaning t m 3744) (meaning t m 3758) (meaning t m 4604) (meaning t m 4736) source

theorem rule34124 (p2027 p2254 p2952 p3222 p3276 p3379 p3952 p4393 p5254 : Prop) (h : (¬ p3379) ∨ (¬ p3222) ∨ (¬ p2254) ∨ (¬ p3952) ∨ (¬ p5254) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p4393)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial34124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory23380 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 6) (m.theta 6 10) (m.theta 9 10)
  exact rule34124 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 3952) (meaning t m 4393) (meaning t m 5254) source

theorem rule34125 (p2027 p2138 p2761 p3366 p3516 p3519 p3744 p3758 p4376 p4444 p4604 p5201 : Prop) (h : (¬ p4376) ∨ p2027 ∨ (¬ p5201) ∨ (¬ p3519) ∨ (¬ p4444) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p3758) ∨ (¬ p3516) ∨ (¬ p4604) ∨ (¬ p2761) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p3516) ∨ (¬ p3519) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial34125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory23381 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34125 (meaning t m 2027) (meaning t m 2138) (meaning t m 2761) (meaning t m 3366) (meaning t m 3516) (meaning t m 3519) (meaning t m 3744) (meaning t m 3758) (meaning t m 4376) (meaning t m 4444) (meaning t m 4604) (meaning t m 5201) source

theorem rule34129 (p2027 p2797 p2954 p3646 p3986 p4315 : Prop) (h : (¬ p3646) ∨ (¬ p3986) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p2797) ∨ (¬ p2954)) : (p2027) ∨ (¬ p2797) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3986) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory23385 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule34129 (meaning t m 2027) (meaning t m 2797) (meaning t m 2954) (meaning t m 3646) (meaning t m 3986) (meaning t m 4315) source

theorem rule34133 (p2027 p2476 p2534 p2668 p2696 p2797 p3146 p4108 p4134 p4733 : Prop) (h : (¬ p2797) ∨ (¬ p2696) ∨ (¬ p2668) ∨ (¬ p4108) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2534) ∨ (¬ p2476) ∨ (¬ p3146) ∨ (¬ p4134)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3146) ∨ (¬ p4108) ∨ (¬ p4134) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial34133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory23389 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule34133 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3146) (meaning t m 4108) (meaning t m 4134) (meaning t m 4733) source

theorem rule34148 (p2307 p2499 p2584 p2588 p3519 : Prop) (h : (¬ p2307) ∨ (¬ p3519) ∨ (¬ p2588) ∨ (¬ p2584) ∨ (¬ p2499)) : (¬ p2307) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial34148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory23404 (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7)
  exact rule34148 (meaning t m 2307) (meaning t m 2499) (meaning t m 2584) (meaning t m 2588) (meaning t m 3519) source

theorem rule34149 (p2027 p2493 p2911 p2926 p3548 p4708 : Prop) (h : (¬ p2926) ∨ (¬ p3548) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p4708)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4708) := by
  classical
  tauto

theorem initial34149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4708)) := by
  have source := ElevenTheory.theory23405 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule34149 (meaning t m 2027) (meaning t m 2493) (meaning t m 2911) (meaning t m 2926) (meaning t m 3548) (meaning t m 4708) source

theorem rule34152 (p2027 p2318 p2507 p2588 p3073 p3857 p3961 p4317 : Prop) (h : (¬ p2588) ∨ (¬ p2507) ∨ (¬ p3961) ∨ p2027 ∨ (¬ p2318) ∨ (¬ p3073) ∨ (¬ p4317) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial34152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory23408 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 4 6) (m.theta 6 7) (m.theta 8 9)
  exact rule34152 (meaning t m 2027) (meaning t m 2318) (meaning t m 2507) (meaning t m 2588) (meaning t m 3073) (meaning t m 3857) (meaning t m 3961) (meaning t m 4317) source

theorem rule34163 (p2534 p4347 p4432 : Prop) (h : (¬ p4347) ∨ (¬ p4432) ∨ p2534) : (p2534) ∨ (¬ p4347) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial34163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2534) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory23419 (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule34163 (meaning t m 2534) (meaning t m 4347) (meaning t m 4432) source

theorem rule34165 (p2027 p2230 p2497 p2911 p3548 p3741 p4105 p5194 : Prop) (h : (¬ p4105) ∨ (¬ p2497) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p5194) ∨ (¬ p2230) ∨ (¬ p3741) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2497) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p3741) ∨ (¬ p4105) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial34165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory23421 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule34165 (meaning t m 2027) (meaning t m 2230) (meaning t m 2497) (meaning t m 2911) (meaning t m 3548) (meaning t m 3741) (meaning t m 4105) (meaning t m 5194) source

theorem rule34173 (p2027 p2088 p2507 p3956 p4114 p4347 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p2507) ∨ (¬ p4114) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2088) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2507) ∨ (¬ p3956) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial34173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory23429 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule34173 (meaning t m 2027) (meaning t m 2088) (meaning t m 2507) (meaning t m 3956) (meaning t m 4114) (meaning t m 4347) (meaning t m 5016) source

theorem rule34179 (p2027 p2187 p3256 p3744 p4171 p4774 : Prop) (h : (¬ p3256) ∨ (¬ p4171) ∨ (¬ p2187) ∨ (¬ p4774) ∨ p2027 ∨ (¬ p3744)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p4171) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial34179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory23435 t (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule34179 (meaning t m 2027) (meaning t m 2187) (meaning t m 3256) (meaning t m 3744) (meaning t m 4171) (meaning t m 4774) source

theorem rule34188 (p2027 p2156 p2619 p3758 p3880 p4539 : Prop) (h : p2027 ∨ (¬ p3880) ∨ (¬ p3758) ∨ (¬ p2619) ∨ (¬ p4539) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p3880) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial34188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory23444 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule34188 (meaning t m 2027) (meaning t m 2156) (meaning t m 2619) (meaning t m 3758) (meaning t m 3880) (meaning t m 4539) source

theorem rule34194 (p2577 p4079 p5015 : Prop) (h : (¬ p5015) ∨ (¬ p4079) ∨ p2577) : (p2577) ∨ (¬ p4079) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial34194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2577) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory23450 (m.theta 0 1) (m.theta 0 4) (m.theta 0 6)
  exact rule34194 (meaning t m 2577) (meaning t m 4079) (meaning t m 5015) source

theorem rule34195 (p1984 p2027 p2245 p2287 p2295 p3172 p3189 p3549 p4245 : Prop) (h : (¬ p3189) ∨ (¬ p1984) ∨ (¬ p3172) ∨ (¬ p2295) ∨ (¬ p2245) ∨ p2027 ∨ p2287 ∨ (¬ p3549) ∨ (¬ p4245)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial34195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory23451 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule34195 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2287) (meaning t m 2295) (meaning t m 3172) (meaning t m 3189) (meaning t m 3549) (meaning t m 4245) source

theorem rule34197 (p2027 p2807 p3019 p3323 p3946 p3983 p4652 : Prop) (h : (¬ p2807) ∨ (¬ p3019) ∨ (¬ p3983) ∨ p2027 ∨ (¬ p4652) ∨ (¬ p3323) ∨ (¬ p3946)) : (p2027) ∨ (¬ p2807) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p3983) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial34197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory23453 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 6 9)
  exact rule34197 (meaning t m 2027) (meaning t m 2807) (meaning t m 3019) (meaning t m 3323) (meaning t m 3946) (meaning t m 3983) (meaning t m 4652) source

theorem rule34217 (p1981 p2027 p2247 p2307 p2688 p3063 p3549 p5020 : Prop) (h : (¬ p2307) ∨ p2688 ∨ (¬ p3549) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p1981) ∨ (¬ p5020)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (p2688) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial34217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory23473 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule34217 (meaning t m 1981) (meaning t m 2027) (meaning t m 2247) (meaning t m 2307) (meaning t m 2688) (meaning t m 3063) (meaning t m 3549) (meaning t m 5020) source

theorem rule34221 (p2352 p2504 p3549 p3955 : Prop) (h : (¬ p3549) ∨ (¬ p2504) ∨ (¬ p2352) ∨ (¬ p3955)) : (¬ p2352) ∨ (¬ p2504) ∨ (¬ p3549) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial34221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory23477 (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule34221 (meaning t m 2352) (meaning t m 2504) (meaning t m 3549) (meaning t m 3955) source

theorem rule34230 (p1988 p2027 p2409 p2493 p2579 p3276 p3355 : Prop) (h : (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3355) ∨ p2027 ∨ p2409 ∨ (¬ p3276) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3276) ∨ (¬ p3355) := by
  classical
  tauto

theorem initial34230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) := by
  have source := ElevenTheory.theory23486 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule34230 (meaning t m 1988) (meaning t m 2027) (meaning t m 2409) (meaning t m 2493) (meaning t m 2579) (meaning t m 3276) (meaning t m 3355) source

theorem rule34233 (p2891 p2922 p3569 p4202 : Prop) (h : (¬ p2922) ∨ (¬ p4202) ∨ (¬ p3569) ∨ p2891) : (p2891) ∨ (¬ p2922) ∨ (¬ p3569) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial34233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2891) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory23489 (m.theta 1 4) (m.theta 1 5) (m.theta 4 7) (m.theta 5 7)
  exact rule34233 (meaning t m 2891) (meaning t m 2922) (meaning t m 3569) (meaning t m 4202) source

theorem rule34235 (p2027 p2590 p3019 p3323 p3684 p4137 p4750 : Prop) (h : (¬ p3684) ∨ (¬ p2590) ∨ (¬ p4137) ∨ (¬ p3019) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p4750)) : (p2027) ∨ (¬ p2590) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3684) ∨ (¬ p4137) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial34235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory23491 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule34235 (meaning t m 2027) (meaning t m 2590) (meaning t m 3019) (meaning t m 3323) (meaning t m 3684) (meaning t m 4137) (meaning t m 4750) source

theorem rule34257 (p3379 p3519 p4108 : Prop) (h : (¬ p3379) ∨ (¬ p4108) ∨ (¬ p3519)) : (¬ p3379) ∨ (¬ p3519) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial34257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory23513 (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule34257 (meaning t m 3379) (meaning t m 3519) (meaning t m 4108) source

theorem rule34264 (p2132 p2774 p4193 : Prop) (h : (¬ p2774) ∨ (¬ p4193) ∨ p2132) : (p2132) ∨ (¬ p2774) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial34264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2132) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory23520 (m.theta 0 2) (m.theta 2 5) (m.theta 2 6)
  exact rule34264 (meaning t m 2132) (meaning t m 2774) (meaning t m 4193) source

theorem rule34265 (p4275 p4473 p4895 : Prop) (h : (¬ p4473) ∨ (¬ p4275) ∨ p4895) : (¬ p4275) ∨ (¬ p4473) ∨ (p4895) := by
  classical
  tauto

theorem initial34265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4473)) ∨ (meaning t m 4895) := by
  have source := ElevenTheory.theory23521 t (m.theta 2 7) (m.theta 5 7) (m.theta 6 7)
  exact rule34265 (meaning t m 4275) (meaning t m 4473) (meaning t m 4895) source

theorem rule34267 (p1982 p2027 p2098 p2114 p3055 p3367 p3609 : Prop) (h : (¬ p2098) ∨ p2114 ∨ (¬ p3367) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3055) ∨ (¬ p3609)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (p2114) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3609) := by
  classical
  tauto

theorem initial34267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3609)) := by
  have source := ElevenTheory.theory23523 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 8 9)
  exact rule34267 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2114) (meaning t m 3055) (meaning t m 3367) (meaning t m 3609) source

theorem rule34270 (p1982 p2027 p2323 p2331 p3189 p3256 p4154 : Prop) (h : p2323 ∨ (¬ p1982) ∨ (¬ p3256) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3189) ∨ (¬ p4154)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial34270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory23526 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule34270 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 3189) (meaning t m 3256) (meaning t m 4154) source

theorem rule34271 (p2027 p2220 p2255 p2958 p3497 p3662 : Prop) (h : (¬ p2255) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2958) ∨ (¬ p2220) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p3497) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial34271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory23527 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8)
  exact rule34271 (meaning t m 2027) (meaning t m 2220) (meaning t m 2255) (meaning t m 2958) (meaning t m 3497) (meaning t m 3662) source

theorem rule34272 (p2027 p2321 p2341 p3548 p3631 p4025 p4396 : Prop) (h : (¬ p4025) ∨ (¬ p4396) ∨ (¬ p2321) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p2341) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4025) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial34272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2321)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory23528 t (m.theta 0 7) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule34272 (meaning t m 2027) (meaning t m 2321) (meaning t m 2341) (meaning t m 3548) (meaning t m 3631) (meaning t m 4025) (meaning t m 4396) source

theorem rule34274 (p2144 p3362 p3904 : Prop) (h : p3362 ∨ (¬ p3904) ∨ (¬ p2144)) : (¬ p2144) ∨ (p3362) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial34274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2144)) ∨ (meaning t m 3362) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory23530 (m.theta 0 2) (m.theta 0 4) (m.theta 0 5)
  exact rule34274 (meaning t m 2144) (meaning t m 3362) (meaning t m 3904) source

theorem rule34277 (p2027 p2140 p2274 p2313 p2860 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p2313) ∨ (¬ p2140)) : (p2027) ∨ (¬ p2140) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2860) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial34277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory23533 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule34277 (meaning t m 2027) (meaning t m 2140) (meaning t m 2274) (meaning t m 2313) (meaning t m 2860) (meaning t m 4198) source

theorem rule34279 (p3575 p4327 p4854 : Prop) (h : (¬ p3575) ∨ (¬ p4327) ∨ p4854) : (¬ p3575) ∨ (¬ p4327) ∨ (p4854) := by
  classical
  tauto

theorem initial34279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4327)) ∨ (meaning t m 4854) := by
  have source := ElevenTheory.theory23535 t (m.theta 0 7) (m.theta 3 7) (m.theta 4 7)
  exact rule34279 (meaning t m 3575) (meaning t m 4327) (meaning t m 4854) source

theorem rule34280 (p3699 p3740 p4001 : Prop) (h : (¬ p4001) ∨ (¬ p3740) ∨ p3699) : (p3699) ∨ (¬ p3740) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial34280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3699) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory23536 (m.theta 3 7) (m.theta 4 7) (m.theta 5 7)
  exact rule34280 (meaning t m 3699) (meaning t m 3740) (meaning t m 4001) source

theorem rule34285 (p2027 p2476 p2573 p2668 p4432 p4976 : Prop) (h : (¬ p2573) ∨ (¬ p4432) ∨ (¬ p2668) ∨ (¬ p4976) ∨ p2027 ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p2668) ∨ (¬ p4432) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial34285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory23541 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule34285 (meaning t m 2027) (meaning t m 2476) (meaning t m 2573) (meaning t m 2668) (meaning t m 4432) (meaning t m 4976) source

theorem rule34288 (p2027 p2177 p2807 p3172 p4548 p4570 : Prop) (h : (¬ p2807) ∨ (¬ p4570) ∨ p2027 ∨ (¬ p4548) ∨ (¬ p2177) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p4548) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial34288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory23544 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule34288 (meaning t m 2027) (meaning t m 2177) (meaning t m 2807) (meaning t m 3172) (meaning t m 4548) (meaning t m 4570) source

theorem rule34296 (p3475 p3582 p4313 : Prop) (h : (¬ p3582) ∨ (¬ p3475) ∨ p4313) : (¬ p3475) ∨ (¬ p3582) ∨ (p4313) := by
  classical
  tauto

theorem initial34296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3582)) ∨ (meaning t m 4313) := by
  have source := ElevenTheory.theory23552 (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule34296 (meaning t m 3475) (meaning t m 3582) (meaning t m 4313) source

theorem rule34299 (p2027 p3115 p3136 p3572 p3699 p5104 : Prop) (h : (¬ p3572) ∨ p2027 ∨ (¬ p3699) ∨ (¬ p5104) ∨ (¬ p3115) ∨ (¬ p3136)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p3699) ∨ (¬ p5104) := by
  classical
  tauto

theorem initial34299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 5104)) := by
  have source := ElevenTheory.theory23555 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 9)
  exact rule34299 (meaning t m 2027) (meaning t m 3115) (meaning t m 3136) (meaning t m 3572) (meaning t m 3699) (meaning t m 5104) source

theorem rule34306 (p3037 p4570 p5142 : Prop) (h : (¬ p4570) ∨ (¬ p3037) ∨ p5142) : (¬ p3037) ∨ (¬ p4570) ∨ (p5142) := by
  classical
  tauto

theorem initial34306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 4570)) ∨ (meaning t m 5142) := by
  have source := ElevenTheory.theory23562 t (m.theta 1 7) (m.theta 3 7) (m.theta 6 7)
  exact rule34306 (meaning t m 3037) (meaning t m 4570) (meaning t m 5142) source

theorem rule34308 (p1976 p2027 p2542 p2914 p3055 p3684 p3742 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p2542) ∨ (¬ p3055) ∨ p2914 ∨ (¬ p3742)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2542) ∨ (p2914) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial34308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory23564 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule34308 (meaning t m 1976) (meaning t m 2027) (meaning t m 2542) (meaning t m 2914) (meaning t m 3055) (meaning t m 3684) (meaning t m 3742) source

theorem rule34313 (p3051 p3370 p4173 p4204 : Prop) (h : (¬ p3370) ∨ (¬ p4204) ∨ (¬ p4173) ∨ (¬ p3051)) : (¬ p3051) ∨ (¬ p3370) ∨ (¬ p4173) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial34313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory23569 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7)
  exact rule34313 (meaning t m 3051) (meaning t m 3370) (meaning t m 4173) (meaning t m 4204) source

theorem rule34314 (p3370 p3556 p4173 p4204 : Prop) (h : (¬ p3370) ∨ (¬ p4204) ∨ (¬ p4173) ∨ p3556) : (¬ p3370) ∨ (p3556) ∨ (¬ p4173) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial34314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3370)) ∨ (meaning t m 3556) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory23570 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7)
  exact rule34314 (meaning t m 3370) (meaning t m 3556) (meaning t m 4173) (meaning t m 4204) source

theorem rule34317 (p2027 p2396 p2437 p3359 p4276 p4636 : Prop) (h : p2027 ∨ (¬ p4636) ∨ (¬ p4276) ∨ (¬ p3359) ∨ (¬ p2396) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2437) ∨ (¬ p3359) ∨ (¬ p4276) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial34317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory23573 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule34317 (meaning t m 2027) (meaning t m 2396) (meaning t m 2437) (meaning t m 3359) (meaning t m 4276) (meaning t m 4636) source

theorem rule34331 (p2027 p2504 p2774 p3055 p3574 p3918 p4753 : Prop) (h : (¬ p2504) ∨ (¬ p3055) ∨ (¬ p3918) ∨ p2027 ∨ (¬ p4753) ∨ (¬ p3574) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2504) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3918) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial34331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory23587 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule34331 (meaning t m 2027) (meaning t m 2504) (meaning t m 2774) (meaning t m 3055) (meaning t m 3574) (meaning t m 3918) (meaning t m 4753) source

theorem rule34334 (p2027 p2177 p2241 p2437 p2727 p3425 p3659 p4276 p4736 : Prop) (h : (¬ p3425) ∨ (¬ p2727) ∨ (¬ p4736) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4276) ∨ (¬ p3659) ∨ (¬ p2437) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4276) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23590 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34334 (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2437) (meaning t m 2727) (meaning t m 3425) (meaning t m 3659) (meaning t m 4276) (meaning t m 4736) source

theorem rule34338 (p1982 p2027 p2331 p2622 p2811 p3189 p3256 p4154 : Prop) (h : (¬ p1982) ∨ p2622 ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4154) ∨ (¬ p2811) ∨ (¬ p2331) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (¬ p2331) ∨ (p2622) ∨ (¬ p2811) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial34338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory23594 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule34338 (meaning t m 1982) (meaning t m 2027) (meaning t m 2331) (meaning t m 2622) (meaning t m 2811) (meaning t m 3189) (meaning t m 3256) (meaning t m 4154) source

theorem rule34343 (p1979 p2027 p2946 p3146 p3172 p3578 p4118 : Prop) (h : (¬ p3172) ∨ (¬ p1979) ∨ (¬ p2946) ∨ (¬ p3146) ∨ p2027 ∨ p3578 ∨ (¬ p4118)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3172) ∨ (p3578) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial34343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3172)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory23599 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule34343 (meaning t m 1979) (meaning t m 2027) (meaning t m 2946) (meaning t m 3146) (meaning t m 3172) (meaning t m 3578) (meaning t m 4118) source

theorem rule34344 (p3319 p3549 p4025 : Prop) (h : (¬ p3319) ∨ (¬ p3549) ∨ (¬ p4025)) : (¬ p3319) ∨ (¬ p3549) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial34344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory23600 (m.theta 1 6) (m.theta 6 7) (m.theta 6 9)
  exact rule34344 (meaning t m 3319) (meaning t m 3549) (meaning t m 4025) source

theorem rule34349 (p1991 p2027 p2630 p2657 p2938 p3879 p4235 p4315 : Prop) (h : (¬ p2657) ∨ (¬ p3879) ∨ (¬ p2630) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p1991) ∨ p2938) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2938) ∨ (¬ p3879) ∨ (¬ p4235) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory23605 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule34349 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2938) (meaning t m 3879) (meaning t m 4235) (meaning t m 4315) source

theorem rule34356 (p1994 p2027 p2299 p2313 p2386 p2766 p3574 p4348 : Prop) (h : (¬ p3574) ∨ p2027 ∨ (¬ p2313) ∨ p2766 ∨ (¬ p2299) ∨ (¬ p1994) ∨ (¬ p4348) ∨ (¬ p2386)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (p2766) ∨ (¬ p3574) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial34356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory23612 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule34356 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2386) (meaning t m 2766) (meaning t m 3574) (meaning t m 4348) source

theorem rule34361 (p2027 p2252 p2449 p2685 p2745 p3821 p4849 : Prop) (h : (¬ p2252) ∨ (¬ p2745) ∨ p2027 ∨ (¬ p4849) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3821) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial34361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory23617 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9)
  exact rule34361 (meaning t m 2027) (meaning t m 2252) (meaning t m 2449) (meaning t m 2685) (meaning t m 2745) (meaning t m 3821) (meaning t m 4849) source

theorem rule34364 (p2018 p2027 p2098 p2707 p2842 p3425 p3585 : Prop) (h : (¬ p3425) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p3585) ∨ p2842 ∨ (¬ p2098) ∨ (¬ p2018)) : (¬ p2018) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2707) ∨ (p2842) ∨ (¬ p3425) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial34364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory23620 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 2 8)
  exact rule34364 (meaning t m 2018) (meaning t m 2027) (meaning t m 2098) (meaning t m 2707) (meaning t m 2842) (meaning t m 3425) (meaning t m 3585) source

theorem rule34368 (p2027 p2230 p2373 p2780 p3146 p3822 p4107 p4419 p4669 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p4669) ∨ (¬ p2373) ∨ (¬ p4419) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2780) ∨ (¬ p3146) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4419) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial34368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory23624 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule34368 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2780) (meaning t m 3146) (meaning t m 3822) (meaning t m 4107) (meaning t m 4419) (meaning t m 4669) source

theorem rule34371 (p1990 p2027 p2545 p2797 p2810 p3323 p3744 : Prop) (h : p2545 ∨ (¬ p2810) ∨ (¬ p2797) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3323)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3323) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial34371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory23627 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule34371 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 3323) (meaning t m 3744) source

theorem rule34375 (p2027 p2807 p2963 p3552 p4037 p4620 : Prop) (h : (¬ p3552) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4620) ∨ (¬ p4037) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial34375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory23631 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9)
  exact rule34375 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3552) (meaning t m 4037) (meaning t m 4620) source

theorem rule34378 (p2027 p2122 p2313 p2778 p2946 p3146 p3156 p3917 p4604 p4786 : Prop) (h : (¬ p2122) ∨ (¬ p4786) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3917) ∨ (¬ p4604) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial34378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory23634 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule34378 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2778) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3917) (meaning t m 4604) (meaning t m 4786) source

theorem rule34379 (p2027 p2499 p2573 p2839 p3475 p3759 p4257 p5052 : Prop) (h : (¬ p3475) ∨ (¬ p4257) ∨ (¬ p5052) ∨ (¬ p3759) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2839) ∨ (¬ p3475) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial34379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory23635 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6)
  exact rule34379 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2839) (meaning t m 3475) (meaning t m 3759) (meaning t m 4257) (meaning t m 5052) source

theorem rule34382 (p2027 p2088 p3452 p4261 p4376 p4436 p5242 : Prop) (h : (¬ p4436) ∨ (¬ p4376) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p4261) ∨ (¬ p5242)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3452) ∨ (¬ p4261) ∨ (¬ p4376) ∨ (¬ p4436) ∨ (¬ p5242) := by
  classical
  tauto

theorem initial34382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 5242)) := by
  have source := ElevenTheory.theory23638 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 8 9)
  exact rule34382 (meaning t m 2027) (meaning t m 2088) (meaning t m 3452) (meaning t m 4261) (meaning t m 4376) (meaning t m 4436) (meaning t m 5242) source

theorem rule34387 (p2027 p2230 p2780 p2982 p3680 p3822 p4260 p4419 p4831 : Prop) (h : (¬ p2230) ∨ (¬ p4419) ∨ (¬ p3680) ∨ (¬ p4831) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4260)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4419) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial34387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory23643 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule34387 (meaning t m 2027) (meaning t m 2230) (meaning t m 2780) (meaning t m 2982) (meaning t m 3680) (meaning t m 3822) (meaning t m 4260) (meaning t m 4419) (meaning t m 4831) source

theorem rule34392 (p2027 p2138 p2383 p2528 p2781 p3266 p4244 p4432 p4831 p5660 : Prop) (h : p2027 ∨ (¬ p2781) ∨ (¬ p2383) ∨ (¬ p2528) ∨ (¬ p4432) ∨ (¬ p3266) ∨ (¬ p5660) ∨ (¬ p4244) ∨ (¬ p2138) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2528) ∨ (¬ p2781) ∨ (¬ p3266) ∨ (¬ p4244) ∨ (¬ p4432) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial34392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory23648 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule34392 (meaning t m 2027) (meaning t m 2138) (meaning t m 2383) (meaning t m 2528) (meaning t m 2781) (meaning t m 3266) (meaning t m 4244) (meaning t m 4432) (meaning t m 4831) (meaning t m 5660) source

theorem rule34393 (p2027 p2901 p3246 p3554 p3817 p4957 : Prop) (h : p2027 ∨ (¬ p3817) ∨ (¬ p3246) ∨ (¬ p4957) ∨ (¬ p3554) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial34393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory23649 t (m.theta 1 5) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule34393 (meaning t m 2027) (meaning t m 2901) (meaning t m 3246) (meaning t m 3554) (meaning t m 3817) (meaning t m 4957) source

theorem rule34396 (p2027 p2252 p2748 p3055 p3276 p3414 p3553 p3619 p4749 p5123 p5164 p5558 : Prop) (h : (¬ p4749) ∨ (¬ p2748) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p3055) ∨ (¬ p5558) ∨ (¬ p3619) ∨ (¬ p3553) ∨ (¬ p5164) ∨ (¬ p3414) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial34396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5164)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory23652 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule34396 (meaning t m 2027) (meaning t m 2252) (meaning t m 2748) (meaning t m 3055) (meaning t m 3276) (meaning t m 3414) (meaning t m 3553) (meaning t m 3619) (meaning t m 4749) (meaning t m 5123) (meaning t m 5164) (meaning t m 5558) source

theorem rule34398 (p1989 p2027 p2122 p2608 p2699 p2829 p3549 p4512 : Prop) (h : p2027 ∨ (¬ p4512) ∨ p2699 ∨ (¬ p3549) ∨ (¬ p1989) ∨ (¬ p2829) ∨ (¬ p2608) ∨ (¬ p2122)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2829) ∨ (¬ p3549) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial34398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory23654 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule34398 (meaning t m 1989) (meaning t m 2027) (meaning t m 2122) (meaning t m 2608) (meaning t m 2699) (meaning t m 2829) (meaning t m 3549) (meaning t m 4512) source

theorem rule34400 (p2027 p2138 p2177 p3093 p3309 p3690 p4244 p4666 p4736 : Prop) (h : (¬ p4244) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3309) ∨ (¬ p2138) ∨ (¬ p3093) ∨ (¬ p4666) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23656 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule34400 (meaning t m 2027) (meaning t m 2138) (meaning t m 2177) (meaning t m 3093) (meaning t m 3309) (meaning t m 3690) (meaning t m 4244) (meaning t m 4666) (meaning t m 4736) source

theorem rule34404 (p2005 p2027 p2307 p2387 p2588 p3982 p5580 : Prop) (h : p2027 ∨ (¬ p2005) ∨ (¬ p2307) ∨ p3982 ∨ (¬ p2588) ∨ (¬ p2387) ∨ (¬ p5580)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (p3982) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial34404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory23660 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule34404 (meaning t m 2005) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2588) (meaning t m 3982) (meaning t m 5580) source

theorem rule34406 (p2001 p2027 p2668 p2766 p3979 p4037 p4171 p5568 : Prop) (h : p2027 ∨ (¬ p3979) ∨ p2766 ∨ (¬ p4037) ∨ (¬ p2668) ∨ (¬ p4171) ∨ (¬ p2001) ∨ (¬ p5568)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2668) ∨ (p2766) ∨ (¬ p3979) ∨ (¬ p4037) ∨ (¬ p4171) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial34406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory23662 t (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule34406 (meaning t m 2001) (meaning t m 2027) (meaning t m 2668) (meaning t m 2766) (meaning t m 3979) (meaning t m 4037) (meaning t m 4171) (meaning t m 5568) source

theorem rule34410 (p2663 p3362 p4236 : Prop) (h : (¬ p3362) ∨ (¬ p4236) ∨ p2663) : (p2663) ∨ (¬ p3362) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial34410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2663) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory23666 (m.theta 0 2) (m.theta 0 3) (m.theta 0 4)
  exact rule34410 (meaning t m 2663) (meaning t m 3362) (meaning t m 4236) source

theorem rule34412 (p2027 p2254 p2922 p2952 p3379 p3868 p4208 p4322 p4826 : Prop) (h : p2027 ∨ (¬ p4826) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p4322) ∨ (¬ p2254) ∨ (¬ p4208) ∨ (¬ p3379) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3868) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial34412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory23668 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule34412 (meaning t m 2027) (meaning t m 2254) (meaning t m 2922) (meaning t m 2952) (meaning t m 3379) (meaning t m 3868) (meaning t m 4208) (meaning t m 4322) (meaning t m 4826) source

theorem rule34413 (p2027 p2850 p2982 p3876 p4001 p5104 : Prop) (h : (¬ p3876) ∨ (¬ p4001) ∨ (¬ p5104) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p2982)) : (p2027) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p5104) := by
  classical
  tauto

theorem initial34413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 5104)) := by
  have source := ElevenTheory.theory23669 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9)
  exact rule34413 (meaning t m 2027) (meaning t m 2850) (meaning t m 2982) (meaning t m 3876) (meaning t m 4001) (meaning t m 5104) source

theorem rule34414 (p2138 p2589 p3695 p3905 : Prop) (h : (¬ p2589) ∨ (¬ p3905) ∨ (¬ p3695) ∨ p2138) : (p2138) ∨ (¬ p2589) ∨ (¬ p3695) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial34414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2138) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory23670 (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 5)
  exact rule34414 (meaning t m 2138) (meaning t m 2589) (meaning t m 3695) (meaning t m 3905) source

theorem rule34418 (p2027 p2387 p3005 p4195 p4417 p4581 : Prop) (h : (¬ p4417) ∨ (¬ p4195) ∨ (¬ p3005) ∨ (¬ p2387) ∨ (¬ p4581) ∨ p2027) : (p2027) ∨ (¬ p2387) ∨ (¬ p3005) ∨ (¬ p4195) ∨ (¬ p4417) ∨ (¬ p4581) := by
  classical
  tauto

theorem initial34418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4581)) := by
  have source := ElevenTheory.theory23674 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule34418 (meaning t m 2027) (meaning t m 2387) (meaning t m 3005) (meaning t m 4195) (meaning t m 4417) (meaning t m 4581) source

theorem rule34422 (p1997 p2027 p2545 p2810 p3115 p3136 p4948 : Prop) (h : p2545 ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p1997) ∨ (¬ p4948) ∨ p2027 ∨ (¬ p3115)) : (¬ p1997) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial34422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory23678 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 9)
  exact rule34422 (meaning t m 1997) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 3115) (meaning t m 3136) (meaning t m 4948) source

theorem rule34426 (p2027 p2573 p2952 p3366 p3461 p3519 p3564 p4236 p4244 p4376 p4831 p5051 p5660 : Prop) (h : (¬ p3519) ∨ (¬ p3366) ∨ (¬ p5051) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p2952) ∨ (¬ p4831) ∨ (¬ p3461) ∨ (¬ p2573) ∨ (¬ p3564) ∨ (¬ p4376) ∨ (¬ p4236) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p4236) ∨ (¬ p4244) ∨ (¬ p4376) ∨ (¬ p4831) ∨ (¬ p5051) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial34426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5051)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory23682 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule34426 (meaning t m 2027) (meaning t m 2573) (meaning t m 2952) (meaning t m 3366) (meaning t m 3461) (meaning t m 3519) (meaning t m 3564) (meaning t m 4236) (meaning t m 4244) (meaning t m 4376) (meaning t m 4831) (meaning t m 5051) (meaning t m 5660) source

theorem rule34429 (p2027 p2138 p2383 p2781 p3564 p3690 p3956 p4244 p4621 : Prop) (h : (¬ p3690) ∨ (¬ p4621) ∨ (¬ p3564) ∨ (¬ p2781) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p2138) ∨ (¬ p4244) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3564) ∨ (¬ p3690) ∨ (¬ p3956) ∨ (¬ p4244) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial34429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory23685 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule34429 (meaning t m 2027) (meaning t m 2138) (meaning t m 2383) (meaning t m 2781) (meaning t m 3564) (meaning t m 3690) (meaning t m 3956) (meaning t m 4244) (meaning t m 4621) source

theorem rule34430 (p2027 p2553 p3956 p4138 p4345 p4348 p4620 : Prop) (h : p2027 ∨ (¬ p2553) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4138) ∨ (¬ p4620) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial34430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory23686 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule34430 (meaning t m 2027) (meaning t m 2553) (meaning t m 3956) (meaning t m 4138) (meaning t m 4345) (meaning t m 4348) (meaning t m 4620) source

theorem rule34432 (p2027 p2352 p2363 p2573 p2685 p3366 p3414 p3519 p4035 p4236 p4376 p5113 : Prop) (h : (¬ p4236) ∨ (¬ p3414) ∨ (¬ p2685) ∨ (¬ p2573) ∨ (¬ p3519) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p5113) ∨ (¬ p4035) ∨ (¬ p2352) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2685) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial34432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory23688 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule34432 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2685) (meaning t m 3366) (meaning t m 3414) (meaning t m 3519) (meaning t m 4035) (meaning t m 4236) (meaning t m 4376) (meaning t m 5113) source

theorem rule34437 (p2027 p2341 p2589 p2850 p2930 p3366 p3545 p3548 p3591 p3742 p3905 p4343 p4866 : Prop) (h : (¬ p3366) ∨ (¬ p4866) ∨ (¬ p3545) ∨ (¬ p3905) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2930) ∨ (¬ p2341) ∨ (¬ p4343) ∨ (¬ p3548) ∨ (¬ p2850) ∨ (¬ p2589) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p2930) ∨ (¬ p3366) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p3591) ∨ (¬ p3742) ∨ (¬ p3905) ∨ (¬ p4343) ∨ (¬ p4866) := by
  classical
  tauto

theorem initial34437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4866)) := by
  have source := ElevenTheory.theory23693 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule34437 (meaning t m 2027) (meaning t m 2341) (meaning t m 2589) (meaning t m 2850) (meaning t m 2930) (meaning t m 3366) (meaning t m 3545) (meaning t m 3548) (meaning t m 3591) (meaning t m 3742) (meaning t m 3905) (meaning t m 4343) (meaning t m 4866) source

theorem rule34439 (p2027 p2156 p2373 p2685 p2741 p2996 p3370 p3877 p4043 p4110 p4377 : Prop) (h : (¬ p4110) ∨ (¬ p2685) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4043) ∨ (¬ p3877) ∨ (¬ p2373) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2741) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p2685) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4110) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial34439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory23695 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule34439 (meaning t m 2027) (meaning t m 2156) (meaning t m 2373) (meaning t m 2685) (meaning t m 2741) (meaning t m 2996) (meaning t m 3370) (meaning t m 3877) (meaning t m 4043) (meaning t m 4110) (meaning t m 4377) source

theorem rule34440 (p2027 p2470 p2528 p3266 p3365 p3572 p4391 p4419 p4831 : Prop) (h : (¬ p3365) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p4419) ∨ (¬ p4391) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial34440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory23696 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule34440 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3266) (meaning t m 3365) (meaning t m 3572) (meaning t m 4391) (meaning t m 4419) (meaning t m 4831) source

theorem rule34441 (p2027 p2138 p2383 p2781 p3276 p3690 p3990 p4022 p4244 p4444 p4669 : Prop) (h : (¬ p2781) ∨ (¬ p3690) ∨ (¬ p4022) ∨ (¬ p4669) ∨ (¬ p3276) ∨ (¬ p4244) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3990) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3276) ∨ (¬ p3690) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p4244) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial34441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory23697 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 4 9) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34441 (meaning t m 2027) (meaning t m 2138) (meaning t m 2383) (meaning t m 2781) (meaning t m 3276) (meaning t m 3690) (meaning t m 3990) (meaning t m 4022) (meaning t m 4244) (meaning t m 4444) (meaning t m 4669) source

theorem rule34443 (p2027 p2104 p2139 p2156 p2373 p2459 p4110 p4133 p4340 p4441 : Prop) (h : (¬ p4133) ∨ (¬ p4441) ∨ (¬ p2373) ∨ (¬ p2139) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4340) ∨ (¬ p2104) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p4110) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial34443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory23699 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34443 (meaning t m 2027) (meaning t m 2104) (meaning t m 2139) (meaning t m 2156) (meaning t m 2373) (meaning t m 2459) (meaning t m 4110) (meaning t m 4133) (meaning t m 4340) (meaning t m 4441) source

theorem rule34452 (p2497 p2922 p3309 p4710 : Prop) (h : (¬ p4710) ∨ (¬ p2922) ∨ (¬ p2497) ∨ p3309) : (¬ p2497) ∨ (¬ p2922) ∨ (p3309) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial34452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2922)) ∨ (meaning t m 3309) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory23708 (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 6 7)
  exact rule34452 (meaning t m 2497) (meaning t m 2922) (meaning t m 3309) (meaning t m 4710) source

theorem rule34453 (p2027 p2254 p3005 p3093 p3172 p3527 p3572 p3644 p4452 p4653 : Prop) (h : (¬ p3527) ∨ (¬ p2254) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p4653) ∨ (¬ p3172) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p4452) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2254) ∨ (¬ p3005) ∨ (¬ p3093) ∨ (¬ p3172) ∨ (¬ p3527) ∨ (¬ p3572) ∨ (¬ p3644) ∨ (¬ p4452) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial34453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory23709 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule34453 (meaning t m 2027) (meaning t m 2254) (meaning t m 3005) (meaning t m 3093) (meaning t m 3172) (meaning t m 3527) (meaning t m 3572) (meaning t m 3644) (meaning t m 4452) (meaning t m 4653) source

theorem rule34455 (p3516 p3577 p4324 : Prop) (h : (¬ p3577) ∨ (¬ p4324) ∨ (¬ p3516)) : (¬ p3516) ∨ (¬ p3577) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial34455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory23711 (m.theta 0 7) (m.theta 2 7) (m.theta 7 9)
  exact rule34455 (meaning t m 3516) (meaning t m 3577) (meaning t m 4324) source

theorem rule34457 (p1992 p2027 p2696 p2743 p2914 p3055 p3742 p4343 : Prop) (h : p2914 ∨ (¬ p1992) ∨ (¬ p4343) ∨ (¬ p2743) ∨ (¬ p3742) ∨ (¬ p3055) ∨ (¬ p2696) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (p2914) ∨ (¬ p3055) ∨ (¬ p3742) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial34457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory23713 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule34457 (meaning t m 1992) (meaning t m 2027) (meaning t m 2696) (meaning t m 2743) (meaning t m 2914) (meaning t m 3055) (meaning t m 3742) (meaning t m 4343) source

theorem rule34462 (p2027 p2254 p2608 p2657 p3537 p3574 p3609 p4137 p4604 : Prop) (h : (¬ p2608) ∨ (¬ p3609) ∨ (¬ p4604) ∨ (¬ p3537) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2657) ∨ (¬ p2254) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p3537) ∨ (¬ p3574) ∨ (¬ p3609) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial34462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory23718 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule34462 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2657) (meaning t m 3537) (meaning t m 3574) (meaning t m 3609) (meaning t m 4137) (meaning t m 4604) source

theorem rule34464 (p2000 p2027 p2534 p2579 p2766 p3016 p4256 : Prop) (h : (¬ p2534) ∨ p2027 ∨ p2766 ∨ (¬ p4256) ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p2000)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2579) ∨ (p2766) ∨ (¬ p3016) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial34464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory23720 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule34464 (meaning t m 2000) (meaning t m 2027) (meaning t m 2534) (meaning t m 2579) (meaning t m 2766) (meaning t m 3016) (meaning t m 4256) source

theorem rule34468 (p4026 p4037 p4319 : Prop) (h : (¬ p4319) ∨ (¬ p4037) ∨ p4026) : (p4026) ∨ (¬ p4037) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial34468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4026) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory23724 (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule34468 (meaning t m 4026) (meaning t m 4037) (meaning t m 4319) source

theorem rule34469 (p2027 p2341 p2780 p2926 p3548 p3819 p4030 p5221 : Prop) (h : (¬ p2926) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p3819) ∨ (¬ p4030) ∨ (¬ p5221) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2780) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p4030) ∨ (¬ p5221) := by
  classical
  tauto

theorem initial34469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 5221)) := by
  have source := ElevenTheory.theory23725 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 2 6) (m.theta 7 8)
  exact rule34469 (meaning t m 2027) (meaning t m 2341) (meaning t m 2780) (meaning t m 2926) (meaning t m 3548) (meaning t m 3819) (meaning t m 4030) (meaning t m 5221) source

theorem rule34472 (p1982 p2027 p2459 p2873 p3399 p3527 p3555 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p2459) ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2873) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2873) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial34472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory23728 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule34472 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2873) (meaning t m 3399) (meaning t m 3527) (meaning t m 3555) source

theorem rule34473 (p2027 p2619 p3497 p4195 p4313 p4700 p4972 : Prop) (h : (¬ p4195) ∨ (¬ p4313) ∨ (¬ p2619) ∨ (¬ p4700) ∨ (¬ p4972) ∨ (¬ p3497) ∨ p2027) : (p2027) ∨ (¬ p2619) ∨ (¬ p3497) ∨ (¬ p4195) ∨ (¬ p4313) ∨ (¬ p4700) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial34473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory23729 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule34473 (meaning t m 2027) (meaning t m 2619) (meaning t m 3497) (meaning t m 4195) (meaning t m 4313) (meaning t m 4700) (meaning t m 4972) source

theorem rule34482 (p2027 p2573 p3540 p3564 p3921 p4624 : Prop) (h : (¬ p4624) ∨ (¬ p3921) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3564) ∨ p2027) : (p2027) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3564) ∨ (¬ p3921) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial34482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory23738 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9)
  exact rule34482 (meaning t m 2027) (meaning t m 2573) (meaning t m 3540) (meaning t m 3564) (meaning t m 3921) (meaning t m 4624) source

theorem rule34485 (p1998 p2027 p2287 p2295 p3527 p3791 p4442 : Prop) (h : p2287 ∨ p2027 ∨ (¬ p3527) ∨ (¬ p2295) ∨ (¬ p3791) ∨ (¬ p1998) ∨ (¬ p4442)) : (¬ p1998) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p3527) ∨ (¬ p3791) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial34485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory23741 t (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule34485 (meaning t m 1998) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 3527) (meaning t m 3791) (meaning t m 4442) source

theorem rule34487 (p1986 p2027 p2766 p3367 p3551 p3588 p3959 p4348 : Prop) (h : (¬ p3551) ∨ (¬ p3367) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3959) ∨ p2766 ∨ (¬ p3588) ∨ (¬ p4348)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p3367) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial34487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory23743 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule34487 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 3367) (meaning t m 3551) (meaning t m 3588) (meaning t m 3959) (meaning t m 4348) source

theorem rule34500 (p3246 p3516 p4283 : Prop) (h : (¬ p4283) ∨ (¬ p3246) ∨ p3516) : (¬ p3246) ∨ (p3516) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial34500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (meaning t m 3516) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory23756 (m.theta 0 7) (m.theta 5 7) (m.theta 7 9)
  exact rule34500 (meaning t m 3246) (meaning t m 3516) (meaning t m 4283) source

theorem rule34503 (p2027 p3055 p3073 p3449 p3584 p3956 p4348 p4503 p4736 : Prop) (h : (¬ p4348) ∨ (¬ p3956) ∨ (¬ p3055) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p4503) ∨ (¬ p4736) ∨ (¬ p3073)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23759 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34503 (meaning t m 2027) (meaning t m 3055) (meaning t m 3073) (meaning t m 3449) (meaning t m 3584) (meaning t m 3956) (meaning t m 4348) (meaning t m 4503) (meaning t m 4736) source

theorem rule34504 (p2027 p2166 p3051 p3055 p3486 p3584 p3956 p4172 p4433 p4736 : Prop) (h : (¬ p3584) ∨ (¬ p4172) ∨ (¬ p3486) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p4736) ∨ (¬ p3055) ∨ (¬ p4433) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3486) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4172) ∨ (¬ p4433) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23760 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule34504 (meaning t m 2027) (meaning t m 2166) (meaning t m 3051) (meaning t m 3055) (meaning t m 3486) (meaning t m 3584) (meaning t m 3956) (meaning t m 4172) (meaning t m 4433) (meaning t m 4736) source

theorem rule34505 (p2027 p3425 p3619 p4029 p4107 p4477 p5362 : Prop) (h : (¬ p5362) ∨ (¬ p4107) ∨ (¬ p3425) ∨ (¬ p4029) ∨ (¬ p4477) ∨ p2027 ∨ (¬ p3619)) : (p2027) ∨ (¬ p3425) ∨ (¬ p3619) ∨ (¬ p4029) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial34505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 4029)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory23761 t (m.theta 0 2) (m.theta 1 9) (m.theta 2 7) (m.theta 2 9) (m.theta 6 7) (m.theta 7 9)
  exact rule34505 (meaning t m 2027) (meaning t m 3425) (meaning t m 3619) (meaning t m 4029) (meaning t m 4107) (meaning t m 4477) (meaning t m 5362) source

theorem rule34510 (p2027 p2870 p3323 p3745 p3917 p4193 p4558 : Prop) (h : p2027 ∨ (¬ p3323) ∨ (¬ p3917) ∨ (¬ p3745) ∨ (¬ p4558) ∨ (¬ p4193) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3323) ∨ (¬ p3745) ∨ (¬ p3917) ∨ (¬ p4193) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial34510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory23766 t (m.theta 2 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule34510 (meaning t m 2027) (meaning t m 2870) (meaning t m 3323) (meaning t m 3745) (meaning t m 3917) (meaning t m 4193) (meaning t m 4558) source

theorem rule34511 (p1992 p2027 p2696 p2743 p2764 p4232 p4425 p5159 : Prop) (h : (¬ p5159) ∨ (¬ p4425) ∨ (¬ p4232) ∨ (¬ p1992) ∨ p2027 ∨ p2764 ∨ (¬ p2696) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p4232) ∨ (¬ p4425) ∨ (¬ p5159) := by
  classical
  tauto

theorem initial34511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5159)) := by
  have source := ElevenTheory.theory23767 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 9) (m.theta 4 9) (m.theta 9 10)
  exact rule34511 (meaning t m 1992) (meaning t m 2027) (meaning t m 2696) (meaning t m 2743) (meaning t m 2764) (meaning t m 4232) (meaning t m 4425) (meaning t m 5159) source

theorem rule34515 (p2298 p4362 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p2298) ∨ p4362) : (¬ p2298) ∨ (p4362) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial34515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2298)) ∨ (meaning t m 4362) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory23771 t (m.theta 3 7) (m.theta 5 7) (m.theta 6 7)
  exact rule34515 (meaning t m 2298) (meaning t m 4362) (meaning t m 4556) source

theorem rule34516 (p2138 p3425 p3587 : Prop) (h : (¬ p3587) ∨ (¬ p3425) ∨ p2138) : (p2138) ∨ (¬ p3425) ∨ (¬ p3587) := by
  classical
  tauto

theorem initial34516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2138) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3587)) := by
  have source := ElevenTheory.theory23772 (m.theta 0 2) (m.theta 2 5) (m.theta 2 7)
  exact rule34516 (meaning t m 2138) (meaning t m 3425) (meaning t m 3587) source

theorem rule34517 (p1992 p2027 p3043 p3346 p3363 p3585 p3680 p4425 : Prop) (h : p2027 ∨ p3043 ∨ (¬ p4425) ∨ (¬ p3363) ∨ (¬ p1992) ∨ (¬ p3585) ∨ (¬ p3346) ∨ (¬ p3680)) : (¬ p1992) ∨ (p2027) ∨ (p3043) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3680) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial34517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory23773 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule34517 (meaning t m 1992) (meaning t m 2027) (meaning t m 3043) (meaning t m 3346) (meaning t m 3363) (meaning t m 3585) (meaning t m 3680) (meaning t m 4425) source

theorem rule34520 (p1981 p2027 p2187 p2699 p3093 p3097 p3309 : Prop) (h : (¬ p1981) ∨ p2027 ∨ (¬ p3309) ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial34520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory23776 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule34520 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2699) (meaning t m 3093) (meaning t m 3097) (meaning t m 3309) source

theorem rule34521 (p1990 p2027 p2388 p2797 p3567 p3654 p3744 p4315 : Prop) (h : (¬ p1990) ∨ p2388 ∨ (¬ p2797) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p3744) ∨ (¬ p4315)) : (¬ p1990) ∨ (p2027) ∨ (p2388) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory23777 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule34521 (meaning t m 1990) (meaning t m 2027) (meaning t m 2388) (meaning t m 2797) (meaning t m 3567) (meaning t m 3654) (meaning t m 3744) (meaning t m 4315) source

theorem rule34534 (p2027 p2192 p2210 p2254 p2657 p3125 p3742 p4278 p4621 : Prop) (h : (¬ p2192) ∨ (¬ p2657) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p2254) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p3742) ∨ p2027) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3125) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial34534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory23790 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule34534 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 3125) (meaning t m 3742) (meaning t m 4278) (meaning t m 4621) source

theorem rule34537 (p1994 p2027 p2630 p2699 p2737 p3471 p3588 p3589 : Prop) (h : p2027 ∨ (¬ p3588) ∨ p2699 ∨ (¬ p3471) ∨ (¬ p3589) ∨ (¬ p2737) ∨ (¬ p1994) ∨ (¬ p2630)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial34537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory23793 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4)
  exact rule34537 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2699) (meaning t m 2737) (meaning t m 3471) (meaning t m 3588) (meaning t m 3589) source

theorem rule34538 (p2011 p2027 p2210 p2699 p2761 p3631 p4322 p4431 : Prop) (h : (¬ p4322) ∨ (¬ p4431) ∨ (¬ p2011) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3631) ∨ p2699 ∨ (¬ p2761)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p3631) ∨ (¬ p4322) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial34538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory23794 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule34538 (meaning t m 2011) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2761) (meaning t m 3631) (meaning t m 4322) (meaning t m 4431) source

theorem rule34541 (p2027 p2247 p2589 p2744 p2850 p3366 p3399 p3527 p3874 p3905 p4438 : Prop) (h : (¬ p2589) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2744) ∨ (¬ p4438) ∨ (¬ p3527) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3874) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p2850) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial34541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory23797 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8)
  exact rule34541 (meaning t m 2027) (meaning t m 2247) (meaning t m 2589) (meaning t m 2744) (meaning t m 2850) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3874) (meaning t m 3905) (meaning t m 4438) source

theorem rule34547 (p1982 p2027 p2699 p3063 p3093 p3461 p3990 p4444 : Prop) (h : (¬ p3063) ∨ (¬ p3990) ∨ (¬ p1982) ∨ (¬ p3093) ∨ p2027 ∨ p2699 ∨ (¬ p3461) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial34547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory23803 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34547 (meaning t m 1982) (meaning t m 2027) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 3461) (meaning t m 3990) (meaning t m 4444) source

theorem rule34548 (p2027 p2230 p2563 p4173 p4202 p5194 : Prop) (h : (¬ p5194) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p2563) ∨ (¬ p2230) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial34548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory23804 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule34548 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 4173) (meaning t m 4202) (meaning t m 5194) source

theorem rule34552 (p2027 p2254 p2608 p2963 p3537 p3969 p4037 p4188 p4191 p5119 : Prop) (h : (¬ p2608) ∨ (¬ p4191) ∨ (¬ p3969) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p4188) ∨ (¬ p4037) ∨ (¬ p5119) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2963) ∨ (¬ p3537) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4188) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial34552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory23808 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule34552 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2963) (meaning t m 3537) (meaning t m 3969) (meaning t m 4037) (meaning t m 4188) (meaning t m 4191) (meaning t m 5119) source

theorem rule34553 (p2027 p2166 p2210 p2254 p2657 p3146 p3574 p4137 p4604 : Prop) (h : (¬ p3574) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p4604) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial34553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory23809 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule34553 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 3146) (meaning t m 3574) (meaning t m 4137) (meaning t m 4604) source

theorem rule34554 (p1990 p2027 p2192 p2220 p2588 p2997 p3055 p3146 p3584 p4172 p4261 p4492 p4736 : Prop) (h : (¬ p3055) ∨ (¬ p2220) ∨ (¬ p1990) ∨ (¬ p4172) ∨ (¬ p2192) ∨ (¬ p2588) ∨ (¬ p4736) ∨ (¬ p3584) ∨ p2997 ∨ p2027 ∨ (¬ p4261) ∨ (¬ p3146) ∨ (¬ p4492)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2220) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3584) ∨ (¬ p4172) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23810 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 8 9)
  exact rule34554 (meaning t m 1990) (meaning t m 2027) (meaning t m 2192) (meaning t m 2220) (meaning t m 2588) (meaning t m 2997) (meaning t m 3055) (meaning t m 3146) (meaning t m 3584) (meaning t m 4172) (meaning t m 4261) (meaning t m 4492) (meaning t m 4736) source

theorem rule34555 (p1995 p2027 p2765 p3193 p3333 p3684 p4110 : Prop) (h : p2027 ∨ (¬ p1995) ∨ (¬ p3193) ∨ (¬ p3333) ∨ p2765 ∨ (¬ p3684) ∨ (¬ p4110)) : (¬ p1995) ∨ (p2027) ∨ (p2765) ∨ (¬ p3193) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial34555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory23811 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule34555 (meaning t m 1995) (meaning t m 2027) (meaning t m 2765) (meaning t m 3193) (meaning t m 3333) (meaning t m 3684) (meaning t m 4110) source

theorem rule34557 (p1994 p2027 p2727 p2766 p2996 p3551 p4155 p4348 : Prop) (h : (¬ p1994) ∨ (¬ p3551) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p4155) ∨ p2766 ∨ (¬ p4348)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2727) ∨ (p2766) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial34557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory23813 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule34557 (meaning t m 1994) (meaning t m 2027) (meaning t m 2727) (meaning t m 2766) (meaning t m 2996) (meaning t m 3551) (meaning t m 4155) (meaning t m 4348) source

theorem rule34559 (p3146 p3256 p4311 : Prop) (h : (¬ p3146) ∨ (¬ p4311) ∨ p3256) : (¬ p3146) ∨ (p3256) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial34559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (meaning t m 3256) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory23815 (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule34559 (meaning t m 3146) (meaning t m 3256) (meaning t m 4311) source

theorem rule34561 (p1987 p2027 p2534 p2696 p2766 p3055 p4256 p4343 : Prop) (h : p2766 ∨ (¬ p2534) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p4343) ∨ (¬ p2696) ∨ (¬ p3055)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2696) ∨ (p2766) ∨ (¬ p3055) ∨ (¬ p4256) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial34561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory23817 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule34561 (meaning t m 1987) (meaning t m 2027) (meaning t m 2534) (meaning t m 2696) (meaning t m 2766) (meaning t m 3055) (meaning t m 4256) (meaning t m 4343) source

theorem rule34565 (p1983 p2027 p2449 p2608 p2685 p2699 p2737 : Prop) (h : (¬ p2449) ∨ (¬ p2685) ∨ p2699 ∨ (¬ p1983) ∨ (¬ p2608) ∨ (¬ p2737) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (p2699) ∨ (¬ p2737) := by
  classical
  tauto

theorem initial34565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) := by
  have source := ElevenTheory.theory23821 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9)
  exact rule34565 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2608) (meaning t m 2685) (meaning t m 2699) (meaning t m 2737) source

theorem rule34570 (p2027 p2963 p3286 p4026 p4367 p4757 : Prop) (h : (¬ p4757) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p4367) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p4026) ∨ (¬ p4367) ∨ (¬ p4757) := by
  classical
  tauto

theorem initial34570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 4757)) := by
  have source := ElevenTheory.theory23826 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule34570 (meaning t m 2027) (meaning t m 2963) (meaning t m 3286) (meaning t m 4026) (meaning t m 4367) (meaning t m 4757) source

theorem rule34572 (p2027 p2177 p3093 p3309 p3365 p3877 p3947 p4044 p4666 p4736 : Prop) (h : (¬ p3309) ∨ (¬ p3947) ∨ (¬ p2177) ∨ (¬ p3877) ∨ (¬ p3093) ∨ (¬ p4666) ∨ (¬ p4736) ∨ (¬ p4044) ∨ (¬ p3365) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3947) ∨ (¬ p4044) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23828 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule34572 (meaning t m 2027) (meaning t m 2177) (meaning t m 3093) (meaning t m 3309) (meaning t m 3365) (meaning t m 3877) (meaning t m 3947) (meaning t m 4044) (meaning t m 4666) (meaning t m 4736) source

theorem rule34573 (p2027 p2138 p2598 p3422 p3879 p4316 p4717 : Prop) (h : (¬ p4717) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3879) ∨ (¬ p4316) ∨ (¬ p2138) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3879) ∨ (¬ p4316) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial34573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory23829 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule34573 (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 3422) (meaning t m 3879) (meaning t m 4316) (meaning t m 4717) source

theorem rule34574 (p2027 p2957 p3156 p3646 p3955 p4393 p4441 p5472 : Prop) (h : (¬ p5472) ∨ (¬ p3955) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p4393) ∨ (¬ p3646) ∨ (¬ p4441) ∨ (¬ p2957)) : (p2027) ∨ (¬ p2957) ∨ (¬ p3156) ∨ (¬ p3646) ∨ (¬ p3955) ∨ (¬ p4393) ∨ (¬ p4441) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial34574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory23830 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 7) (m.theta 6 8)
  exact rule34574 (meaning t m 2027) (meaning t m 2957) (meaning t m 3156) (meaning t m 3646) (meaning t m 3955) (meaning t m 4393) (meaning t m 4441) (meaning t m 5472) source

theorem rule34578 (p2027 p2248 p2499 p2958 p3051 p3156 p3452 p3956 p4320 p4433 : Prop) (h : (¬ p2248) ∨ (¬ p4320) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2958) ∨ (¬ p2499) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4320) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial34578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory23834 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule34578 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2958) (meaning t m 3051) (meaning t m 3156) (meaning t m 3452) (meaning t m 3956) (meaning t m 4320) (meaning t m 4433) source

theorem rule34581 (p1979 p2027 p2764 p2891 p4320 p4322 p4363 : Prop) (h : (¬ p2891) ∨ (¬ p1979) ∨ (¬ p4363) ∨ (¬ p4322) ∨ (¬ p4320) ∨ p2027 ∨ p2764) : (¬ p1979) ∨ (p2027) ∨ (p2764) ∨ (¬ p2891) ∨ (¬ p4320) ∨ (¬ p4322) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial34581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory23837 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule34581 (meaning t m 1979) (meaning t m 2027) (meaning t m 2764) (meaning t m 2891) (meaning t m 4320) (meaning t m 4322) (meaning t m 4363) source

theorem rule34582 (p1986 p2027 p2493 p2509 p2534 p2766 p3584 : Prop) (h : p2766 ∨ (¬ p2509) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2534) ∨ (¬ p1986) ∨ (¬ p3584)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial34582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory23838 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule34582 (meaning t m 1986) (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2534) (meaning t m 2766) (meaning t m 3584) source

theorem rule34585 (p2027 p2254 p2440 p2608 p2657 p3537 p3609 p4948 p5059 : Prop) (h : (¬ p3609) ∨ (¬ p2254) ∨ (¬ p4948) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p5059) ∨ (¬ p3537)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial34585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory23841 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 8 9)
  exact rule34585 (meaning t m 2027) (meaning t m 2254) (meaning t m 2440) (meaning t m 2608) (meaning t m 2657) (meaning t m 3537) (meaning t m 3609) (meaning t m 4948) (meaning t m 5059) source

theorem rule34587 (p2015 p2027 p2388 p2797 p3323 p4026 p4315 : Prop) (h : (¬ p2015) ∨ (¬ p4026) ∨ p2388 ∨ (¬ p3323) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p4315)) : (¬ p2015) ∨ (p2027) ∨ (p2388) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p4026) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory23843 t (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 9)
  exact rule34587 (meaning t m 2015) (meaning t m 2027) (meaning t m 2388) (meaning t m 2797) (meaning t m 3323) (meaning t m 4026) (meaning t m 4315) source

theorem rule34591 (p2027 p2298 p3286 p3414 p3690 p4556 p4660 : Prop) (h : (¬ p2298) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p3690) ∨ (¬ p3414) ∨ (¬ p4660) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2298) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p4556) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial34591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory23847 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 9) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule34591 (meaning t m 2027) (meaning t m 2298) (meaning t m 3286) (meaning t m 3414) (meaning t m 3690) (meaning t m 4556) (meaning t m 4660) source

theorem rule34592 (p2003 p2027 p2247 p2313 p2688 p3093 p3309 : Prop) (h : (¬ p2313) ∨ p2688 ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p2003) ∨ (¬ p3309)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2313) ∨ (p2688) ∨ (¬ p3093) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial34592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory23848 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 6 7)
  exact rule34592 (meaning t m 2003) (meaning t m 2027) (meaning t m 2247) (meaning t m 2313) (meaning t m 2688) (meaning t m 3093) (meaning t m 3309) source

theorem rule34600 (p2027 p2109 p2177 p2707 p3960 p4242 p4473 : Prop) (h : (¬ p2177) ∨ (¬ p3960) ∨ p2027 ∨ (¬ p2109) ∨ (¬ p4473) ∨ (¬ p2707) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2109) ∨ (¬ p2177) ∨ (¬ p2707) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial34600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2109)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory23856 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 6 7) (m.theta 7 8)
  exact rule34600 (meaning t m 2027) (meaning t m 2109) (meaning t m 2177) (meaning t m 2707) (meaning t m 3960) (meaning t m 4242) (meaning t m 4473) source

theorem rule34602 (p2396 p3631 p4427 : Prop) (h : (¬ p3631) ∨ (¬ p4427) ∨ p2396) : (p2396) ∨ (¬ p3631) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial34602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2396) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory23858 (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule34602 (meaning t m 2396) (meaning t m 3631) (meaning t m 4427) source

theorem rule34603 (p1983 p2027 p2202 p2440 p3276 p3343 p4381 : Prop) (h : p2202 ∨ (¬ p4381) ∨ (¬ p1983) ∨ (¬ p3276) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3343)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial34603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory23859 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule34603 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3276) (meaning t m 3343) (meaning t m 4381) source

theorem rule34610 (p2027 p2210 p2476 p2891 p3083 p3246 p3359 p4641 p5193 : Prop) (h : (¬ p2891) ∨ (¬ p4641) ∨ (¬ p3246) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3359) ∨ (¬ p2476) ∨ (¬ p5193) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2476) ∨ (¬ p2891) ∨ (¬ p3083) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p4641) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial34610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory23866 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule34610 (meaning t m 2027) (meaning t m 2210) (meaning t m 2476) (meaning t m 2891) (meaning t m 3083) (meaning t m 3246) (meaning t m 3359) (meaning t m 4641) (meaning t m 5193) source

theorem rule34611 (p1991 p2027 p2440 p2462 p2657 p3690 p4235 : Prop) (h : (¬ p1991) ∨ p2027 ∨ (¬ p2440) ∨ p2462 ∨ (¬ p2657) ∨ (¬ p4235) ∨ (¬ p3690)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2440) ∨ (p2462) ∨ (¬ p2657) ∨ (¬ p3690) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial34611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory23867 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule34611 (meaning t m 1991) (meaning t m 2027) (meaning t m 2440) (meaning t m 2462) (meaning t m 2657) (meaning t m 3690) (meaning t m 4235) source

theorem rule34614 (p3692 p4188 p4340 : Prop) (h : (¬ p4340) ∨ (¬ p4188) ∨ p3692) : (p3692) ∨ (¬ p4188) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial34614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory23870 (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule34614 (meaning t m 3692) (meaning t m 4188) (meaning t m 4340) source

theorem rule34615 (p2027 p2588 p3276 p4349 p4405 p4417 p4422 p5284 : Prop) (h : (¬ p4349) ∨ (¬ p4417) ∨ (¬ p5284) ∨ (¬ p3276) ∨ (¬ p2588) ∨ (¬ p4422) ∨ p2027 ∨ (¬ p4405)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3276) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p4422) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial34615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory23871 t (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 8) (m.theta 9 10)
  exact rule34615 (meaning t m 2027) (meaning t m 2588) (meaning t m 3276) (meaning t m 4349) (meaning t m 4405) (meaning t m 4417) (meaning t m 4422) (meaning t m 5284) source

theorem rule34616 (p2027 p2254 p2542 p2589 p2608 p2655 p3359 p3537 p3609 p4947 p5059 : Prop) (h : (¬ p2655) ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p5059) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p2254) ∨ (¬ p4947) ∨ (¬ p3609) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2655) ∨ (¬ p3359) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4947) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial34616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4947)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory23872 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 8 9)
  exact rule34616 (meaning t m 2027) (meaning t m 2254) (meaning t m 2542) (meaning t m 2589) (meaning t m 2608) (meaning t m 2655) (meaning t m 3359) (meaning t m 3537) (meaning t m 3609) (meaning t m 4947) (meaning t m 5059) source

theorem rule34617 (p1975 p2027 p2114 p2299 p2341 p2737 p3365 p3819 : Prop) (h : (¬ p2299) ∨ (¬ p1975) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p3819) ∨ (¬ p3365) ∨ p2114 ∨ (¬ p2737)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3819) := by
  classical
  tauto

theorem initial34617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3819)) := by
  have source := ElevenTheory.theory23873 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 6 7) (m.theta 7 8)
  exact rule34617 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2299) (meaning t m 2341) (meaning t m 2737) (meaning t m 3365) (meaning t m 3819) source

theorem rule34624 (p1992 p2027 p2388 p2608 p3755 p3834 p3847 p4315 : Prop) (h : (¬ p1992) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p3755) ∨ (¬ p3847) ∨ p2388 ∨ (¬ p4315) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (p2388) ∨ (¬ p2608) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory23880 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9)
  exact rule34624 (meaning t m 1992) (meaning t m 2027) (meaning t m 2388) (meaning t m 2608) (meaning t m 3755) (meaning t m 3834) (meaning t m 3847) (meaning t m 4315) source

theorem rule34625 (p2027 p2166 p2210 p3055 p3146 p3584 p4137 p4604 p4736 : Prop) (h : (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p4736) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23881 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule34625 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 3055) (meaning t m 3146) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) (meaning t m 4736) source

theorem rule34629 (p2027 p2088 p2578 p2588 p4114 p4118 p4405 p4417 : Prop) (h : (¬ p4405) ∨ (¬ p4417) ∨ (¬ p4118) ∨ (¬ p2588) ∨ (¬ p2578) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4114)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p4114) ∨ (¬ p4118) ∨ (¬ p4405) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial34629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory23885 t (m.theta 0 6) (m.theta 0 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule34629 (meaning t m 2027) (meaning t m 2088) (meaning t m 2578) (meaning t m 2588) (meaning t m 4114) (meaning t m 4118) (meaning t m 4405) (meaning t m 4417) source

theorem rule34630 (p1986 p2027 p2104 p2598 p2764 p4340 p4444 : Prop) (h : p2764 ∨ p2027 ∨ (¬ p1986) ∨ (¬ p4444) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4340)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (p2764) ∨ (¬ p4340) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial34630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory23886 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule34630 (meaning t m 1986) (meaning t m 2027) (meaning t m 2104) (meaning t m 2598) (meaning t m 2764) (meaning t m 4340) (meaning t m 4444) source

theorem rule34632 (p1982 p2027 p2699 p2761 p3399 p3527 p3945 p4444 : Prop) (h : p2699 ∨ (¬ p3945) ∨ (¬ p4444) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p1982) ∨ (¬ p2761)) : (¬ p1982) ∨ (p2027) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3945) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial34632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory23888 t (m.theta 0 1) (m.theta 1 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34632 (meaning t m 1982) (meaning t m 2027) (meaning t m 2699) (meaning t m 2761) (meaning t m 3399) (meaning t m 3527) (meaning t m 3945) (meaning t m 4444) source

theorem rule34643 (p3953 p4371 p4436 : Prop) (h : (¬ p3953) ∨ (¬ p4371) ∨ p4436) : (¬ p3953) ∨ (¬ p4371) ∨ (p4436) := by
  classical
  tauto

theorem initial34643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4371)) ∨ (meaning t m 4436) := by
  have source := ElevenTheory.theory23899 (m.theta 1 2) (m.theta 1 6) (m.theta 1 8)
  exact rule34643 (meaning t m 3953) (meaning t m 4371) (meaning t m 4436) source

theorem rule34646 (p1986 p2027 p2598 p2766 p2780 p4347 p4358 : Prop) (h : (¬ p1986) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4358) ∨ (¬ p2780) ∨ p2766 ∨ (¬ p4347)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial34646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory23902 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule34646 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2766) (meaning t m 2780) (meaning t m 4347) (meaning t m 4358) source

theorem rule34648 (p1986 p2027 p2169 p2363 p2598 p2780 p4078 p4340 : Prop) (h : p2169 ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2598) ∨ (¬ p1986) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p2363)) : (¬ p1986) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4078) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial34648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory23904 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule34648 (meaning t m 1986) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2598) (meaning t m 2780) (meaning t m 4078) (meaning t m 4340) source

theorem rule34649 (p1990 p2027 p2177 p2192 p2997 p3486 p3570 : Prop) (h : p2997 ∨ (¬ p3486) ∨ (¬ p2177) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p3570)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2192) ∨ (p2997) ∨ (¬ p3486) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial34649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory23905 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34649 (meaning t m 1990) (meaning t m 2027) (meaning t m 2177) (meaning t m 2192) (meaning t m 2997) (meaning t m 3486) (meaning t m 3570) source

theorem rule34650 (p2027 p2363 p3063 p3093 p3346 p3680 p4425 p5059 p5193 : Prop) (h : (¬ p4425) ∨ (¬ p3346) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p5193) ∨ (¬ p5059) ∨ (¬ p3063) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3346) ∨ (¬ p3680) ∨ (¬ p4425) ∨ (¬ p5059) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial34650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory23906 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule34650 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 3093) (meaning t m 3346) (meaning t m 3680) (meaning t m 4425) (meaning t m 5059) (meaning t m 5193) source

theorem rule34651 (p2007 p2027 p2202 p2440 p2470 p2579 p3016 : Prop) (h : p2202 ∨ (¬ p2007) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016)) : (¬ p2007) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial34651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory23907 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule34651 (meaning t m 2007) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2470) (meaning t m 2579) (meaning t m 3016) source

theorem rule34653 (p2002 p2027 p2774 p2997 p3365 p3568 p4195 : Prop) (h : p2997 ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p3365) ∨ (¬ p2002) ∨ (¬ p2774) ∨ p2027) : (¬ p2002) ∨ (p2027) ∨ (¬ p2774) ∨ (p2997) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial34653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory23909 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule34653 (meaning t m 2002) (meaning t m 2027) (meaning t m 2774) (meaning t m 2997) (meaning t m 3365) (meaning t m 3568) (meaning t m 4195) source

theorem rule34659 (p2027 p2870 p3238 p3582 p4235 p5214 : Prop) (h : (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p2870) ∨ (¬ p5214) ∨ p2027) : (p2027) ∨ (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4235) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial34659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory23915 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule34659 (meaning t m 2027) (meaning t m 2870) (meaning t m 3238) (meaning t m 3582) (meaning t m 4235) (meaning t m 5214) source

theorem rule34660 (p2027 p2870 p3238 p3413 p4235 p4316 p4811 : Prop) (h : (¬ p4235) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p4316) ∨ (¬ p3413) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p4235) ∨ (¬ p4316) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial34660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory23916 t (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule34660 (meaning t m 2027) (meaning t m 2870) (meaning t m 3238) (meaning t m 3413) (meaning t m 4235) (meaning t m 4316) (meaning t m 4811) source

theorem rule34662 (p2417 p2927 p3631 : Prop) (h : (¬ p3631) ∨ (¬ p2927) ∨ p2417) : (p2417) ∨ (¬ p2927) ∨ (¬ p3631) := by
  classical
  tauto

theorem initial34662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3631)) := by
  have source := ElevenTheory.theory23918 (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule34662 (meaning t m 2417) (meaning t m 2927) (meaning t m 3631) source

theorem rule34665 (p2027 p2299 p3093 p3365 p3497 p3527 p3747 p4315 p4452 p4559 p4736 : Prop) (h : p2027 ∨ (¬ p4452) ∨ (¬ p2299) ∨ (¬ p3747) ∨ (¬ p3527) ∨ (¬ p3093) ∨ (¬ p3497) ∨ (¬ p4559) ∨ (¬ p4315) ∨ (¬ p4736) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3527) ∨ (¬ p3747) ∨ (¬ p4315) ∨ (¬ p4452) ∨ (¬ p4559) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory23921 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule34665 (meaning t m 2027) (meaning t m 2299) (meaning t m 3093) (meaning t m 3365) (meaning t m 3497) (meaning t m 3527) (meaning t m 3747) (meaning t m 4315) (meaning t m 4452) (meaning t m 4559) (meaning t m 4736) source

theorem rule34666 (p2363 p3979 p4200 : Prop) (h : (¬ p4200) ∨ (¬ p2363) ∨ p3979) : (¬ p2363) ∨ (p3979) ∨ (¬ p4200) := by
  classical
  tauto

theorem initial34666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (meaning t m 3979) ∨ (¬ (meaning t m 4200)) := by
  have source := ElevenTheory.theory23922 (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule34666 (meaning t m 2363) (meaning t m 3979) (meaning t m 4200) source

theorem rule34667 (p2780 p2829 p3366 : Prop) (h : (¬ p3366) ∨ (¬ p2829) ∨ (¬ p2780)) : (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3366) := by
  classical
  tauto

theorem initial34667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3366)) := by
  have source := ElevenTheory.theory23923 (m.theta 0 2) (m.theta 1 2) (m.theta 2 6)
  exact rule34667 (meaning t m 2780) (meaning t m 2829) (meaning t m 3366) source

theorem rule34673 (p3941 p4181 p5307 : Prop) (h : (¬ p3941) ∨ (¬ p5307) ∨ p4181) : (¬ p3941) ∨ (p4181) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial34673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3941)) ∨ (meaning t m 4181) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory23929 (m.theta 1 8) (m.theta 7 8) (m.theta 8 10)
  exact rule34673 (meaning t m 3941) (meaning t m 4181) (meaning t m 5307) source

theorem rule34674 (p2781 p4736 p5020 : Prop) (h : p2781 ∨ (¬ p5020) ∨ (¬ p4736)) : (p2781) ∨ (¬ p4736) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial34674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2781) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory23930 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6)
  exact rule34674 (meaning t m 2781) (meaning t m 4736) (meaning t m 5020) source

theorem rule34679 (p2352 p2498 p3063 : Prop) (h : (¬ p2498) ∨ (¬ p3063) ∨ p2352) : (p2352) ∨ (¬ p2498) ∨ (¬ p3063) := by
  classical
  tauto

theorem initial34679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3063)) := by
  have source := ElevenTheory.theory23935 (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule34679 (meaning t m 2352) (meaning t m 2498) (meaning t m 3063) source

theorem rule34686 (p3486 p3645 p3646 p4204 : Prop) (h : (¬ p3645) ∨ (¬ p4204) ∨ (¬ p3646) ∨ p3486) : (p3486) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial34686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3486) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory23942 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7)
  exact rule34686 (meaning t m 3486) (meaning t m 3645) (meaning t m 3646) (meaning t m 4204) source

theorem rule34687 (p2027 p2352 p2573 p2665 p3324 p4194 : Prop) (h : (¬ p4194) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p3324) ∨ p2027) : (p2027) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p3324) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial34687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory23943 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule34687 (meaning t m 2027) (meaning t m 2352) (meaning t m 2573) (meaning t m 2665) (meaning t m 3324) (meaning t m 4194) source

theorem rule34695 (p2027 p2927 p3389 p3527 p3659 p3686 p4730 : Prop) (h : (¬ p3686) ∨ (¬ p4730) ∨ (¬ p3389) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p2927) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2927) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial34695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory23951 t (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule34695 (meaning t m 2027) (meaning t m 2927) (meaning t m 3389) (meaning t m 3527) (meaning t m 3659) (meaning t m 3686) (meaning t m 4730) source

theorem rule34703 (p2027 p2138 p2241 p2264 p3027 p3146 p4340 p4359 p4736 p4905 : Prop) (h : (¬ p4736) ∨ (¬ p4340) ∨ (¬ p2264) ∨ (¬ p4359) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3027) ∨ (¬ p2138) ∨ (¬ p4905) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial34703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory23959 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 2 8) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34703 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2264) (meaning t m 3027) (meaning t m 3146) (meaning t m 4340) (meaning t m 4359) (meaning t m 4736) (meaning t m 4905) source

theorem rule34707 (p2481 p3256 p3857 p4437 : Prop) (h : (¬ p3857) ∨ (¬ p3256) ∨ (¬ p4437) ∨ (¬ p2481)) : (¬ p2481) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial34707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory23963 (m.theta 0 8) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule34707 (meaning t m 2481) (meaning t m 3256) (meaning t m 3857) (meaning t m 4437) source

theorem rule34710 (p2027 p2470 p2579 p4318 p4358 p4370 p5222 : Prop) (h : (¬ p4370) ∨ p2027 ∨ (¬ p4318) ∨ (¬ p5222) ∨ (¬ p4358) ∨ (¬ p2470) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p4318) ∨ (¬ p4358) ∨ (¬ p4370) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial34710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory23966 t (m.theta 0 4) (m.theta 1 8) (m.theta 2 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule34710 (meaning t m 2027) (meaning t m 2470) (meaning t m 2579) (meaning t m 4318) (meaning t m 4358) (meaning t m 4370) (meaning t m 5222) source

theorem rule34718 (p2027 p2363 p2383 p2781 p3266 p3365 p4315 p5405 p5740 : Prop) (h : (¬ p3365) ∨ (¬ p2781) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p2363) ∨ (¬ p5740) ∨ (¬ p5405) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p5405) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial34718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory23974 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule34718 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2781) (meaning t m 3266) (meaning t m 3365) (meaning t m 4315) (meaning t m 5405) (meaning t m 5740) source

theorem rule34719 (p2027 p2132 p2753 p2870 p2881 p3379 p3591 p3923 p4503 p5216 : Prop) (h : (¬ p2132) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3923) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial34719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory23975 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule34719 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2870) (meaning t m 2881) (meaning t m 3379) (meaning t m 3591) (meaning t m 3923) (meaning t m 4503) (meaning t m 5216) source

theorem rule34722 (p2010 p2027 p2765 p2881 p3051 p3644 p3646 : Prop) (h : (¬ p3051) ∨ p2765 ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2881) ∨ (¬ p2010) ∨ (¬ p3644)) : (¬ p2010) ∨ (p2027) ∨ (p2765) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3644) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial34722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory23978 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule34722 (meaning t m 2010) (meaning t m 2027) (meaning t m 2765) (meaning t m 2881) (meaning t m 3051) (meaning t m 3644) (meaning t m 3646) source

theorem rule34723 (p3246 p3569 p4278 : Prop) (h : (¬ p3246) ∨ (¬ p3569) ∨ (¬ p4278)) : (¬ p3246) ∨ (¬ p3569) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial34723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory23979 (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule34723 (meaning t m 3246) (meaning t m 3569) (meaning t m 4278) source

theorem rule34724 (p2417 p3246 p3569 : Prop) (h : (¬ p3246) ∨ (¬ p3569) ∨ p2417) : (p2417) ∨ (¬ p3246) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial34724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory23980 (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule34724 (meaning t m 2417) (meaning t m 3246) (meaning t m 3569) source

theorem rule34725 (p2027 p2247 p2589 p2744 p3366 p3399 p3631 p3744 p3905 p4110 p4625 : Prop) (h : (¬ p3905) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p2744) ∨ (¬ p3744) ∨ (¬ p3366) ∨ (¬ p4110) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial34725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory23981 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule34725 (meaning t m 2027) (meaning t m 2247) (meaning t m 2589) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3631) (meaning t m 3744) (meaning t m 3905) (meaning t m 4110) (meaning t m 4625) source

theorem rule34729 (p1994 p2027 p2230 p2440 p2476 p2534 p2766 : Prop) (h : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p1994) ∨ p2766 ∨ p2027 ∨ (¬ p2534)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2766) := by
  classical
  tauto

theorem initial34729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) := by
  have source := ElevenTheory.theory23985 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule34729 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2476) (meaning t m 2534) (meaning t m 2766) source

theorem rule34731 (p2027 p3105 p3947 p4135 p4244 p4280 : Prop) (h : p2027 ∨ (¬ p3105) ∨ (¬ p4135) ∨ (¬ p4280) ∨ (¬ p4244) ∨ (¬ p3947)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3947) ∨ (¬ p4135) ∨ (¬ p4244) ∨ (¬ p4280) := by
  classical
  tauto

theorem initial34731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4280)) := by
  have source := ElevenTheory.theory23987 t (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule34731 (meaning t m 2027) (meaning t m 3105) (meaning t m 3947) (meaning t m 4135) (meaning t m 4244) (meaning t m 4280) source

theorem rule34732 (p2475 p2534 p3857 : Prop) (h : (¬ p2475) ∨ (¬ p2534) ∨ p3857) : (¬ p2475) ∨ (¬ p2534) ∨ (p3857) := by
  classical
  tauto

theorem initial34732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 3857) := by
  have source := ElevenTheory.theory23988 (m.theta 0 8) (m.theta 4 8) (m.theta 8 9)
  exact rule34732 (meaning t m 2475) (meaning t m 2534) (meaning t m 3857) source

theorem rule34733 (p2027 p2363 p2476 p2534 p2881 p2901 p2946 p3905 p4503 p4786 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p2534) ∨ (¬ p4786) ∨ (¬ p2476) ∨ (¬ p4503) ∨ (¬ p2363) ∨ (¬ p2881) ∨ (¬ p3905) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p4503) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial34733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory23989 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34733 (meaning t m 2027) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3905) (meaning t m 4503) (meaning t m 4786) source

end SunPrize.SMT
