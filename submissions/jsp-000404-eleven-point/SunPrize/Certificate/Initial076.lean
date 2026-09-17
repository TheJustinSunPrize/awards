import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory060
import SunPrize.Certificate.Theory061
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule34735 (p1984 p2027 p2850 p3008 p3238 p3584 p3954 p4257 : Prop) (h : (¬ p2850) ∨ (¬ p3584) ∨ (¬ p3238) ∨ p2027 ∨ p3008 ∨ (¬ p1984) ∨ (¬ p4257) ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2850) ∨ (p3008) ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p3954) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial34735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory23991 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule34735 (meaning t m 1984) (meaning t m 2027) (meaning t m 2850) (meaning t m 3008) (meaning t m 3238) (meaning t m 3584) (meaning t m 3954) (meaning t m 4257) source

theorem rule34737 (p2027 p2307 p2406 p2497 p2578 p3549 p4715 : Prop) (h : (¬ p3549) ∨ (¬ p2497) ∨ (¬ p4715) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2578)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p2578) ∨ (¬ p3549) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial34737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory23993 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule34737 (meaning t m 2027) (meaning t m 2307) (meaning t m 2406) (meaning t m 2497) (meaning t m 2578) (meaning t m 3549) (meaning t m 4715) source

theorem rule34738 (p2027 p2299 p2341 p2396 p3359 p3365 p3413 p4315 p4641 p5257 : Prop) (h : (¬ p2341) ∨ (¬ p5257) ∨ (¬ p2299) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p3413) ∨ (¬ p3359) ∨ (¬ p4641) ∨ p2027 ∨ (¬ p2396)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3413) ∨ (¬ p4315) ∨ (¬ p4641) ∨ (¬ p5257) := by
  classical
  tauto

theorem initial34738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5257)) := by
  have source := ElevenTheory.theory23994 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule34738 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2396) (meaning t m 3359) (meaning t m 3365) (meaning t m 3413) (meaning t m 4315) (meaning t m 4641) (meaning t m 5257) source

theorem rule34739 (p2531 p4043 p5012 : Prop) (h : (¬ p2531) ∨ (¬ p4043) ∨ p5012) : (¬ p2531) ∨ (¬ p4043) ∨ (p5012) := by
  classical
  tauto

theorem initial34739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 4043)) ∨ (meaning t m 5012) := by
  have source := ElevenTheory.theory23995 t (m.theta 3 8) (m.theta 4 8) (m.theta 5 8)
  exact rule34739 (meaning t m 2531) (meaning t m 4043) (meaning t m 5012) source

theorem rule34742 (p2027 p2246 p2509 p2608 p2744 p2958 p3051 p3156 p3452 p4320 p4434 : Prop) (h : (¬ p3452) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p2958) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p4434) ∨ (¬ p2509) ∨ (¬ p4320) ∨ p2027) : (p2027) ∨ (¬ p2246) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4320) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial34742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory23998 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule34742 (meaning t m 2027) (meaning t m 2246) (meaning t m 2509) (meaning t m 2608) (meaning t m 2744) (meaning t m 2958) (meaning t m 3051) (meaning t m 3156) (meaning t m 3452) (meaning t m 4320) (meaning t m 4434) source

theorem rule34743 (p2027 p2254 p2952 p3093 p3309 p3791 p4208 p4322 p4826 : Prop) (h : (¬ p3309) ∨ (¬ p2952) ∨ (¬ p4826) ∨ (¬ p4208) ∨ (¬ p3093) ∨ (¬ p4322) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3791)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial34743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory23999 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule34743 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3093) (meaning t m 3309) (meaning t m 3791) (meaning t m 4208) (meaning t m 4322) (meaning t m 4826) source

theorem rule34744 (p1982 p2027 p2459 p2842 p2850 p2881 p3051 p4109 : Prop) (h : p2842 ∨ (¬ p1982) ∨ (¬ p2881) ∨ (¬ p2850) ∨ (¬ p4109) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial34744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory24000 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule34744 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2842) (meaning t m 2850) (meaning t m 2881) (meaning t m 3051) (meaning t m 4109) source

theorem rule34746 (p2027 p2139 p2363 p2476 p2534 p3051 p3156 p3905 p4320 p4433 : Prop) (h : (¬ p4320) ∨ (¬ p3905) ∨ (¬ p2476) ∨ (¬ p2363) ∨ (¬ p2139) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4433) ∨ (¬ p3051) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3905) ∨ (¬ p4320) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial34746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory24002 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule34746 (meaning t m 2027) (meaning t m 2139) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 3051) (meaning t m 3156) (meaning t m 3905) (meaning t m 4320) (meaning t m 4433) source

theorem rule34748 (p2027 p2406 p2499 p2860 p3096 p4885 : Prop) (h : p2027 ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3096) ∨ (¬ p2406) ∨ (¬ p4885)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2860) ∨ (¬ p3096) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial34748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory24004 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule34748 (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 2860) (meaning t m 3096) (meaning t m 4885) source

theorem rule34749 (p2027 p3319 p3359 p3365 p3366 p3413 p3461 p4315 p4444 p4697 p4866 : Prop) (h : (¬ p4866) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p4697) ∨ (¬ p3365) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3413) ∨ (¬ p3319) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3319) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3413) ∨ (¬ p3461) ∨ (¬ p4315) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4866) := by
  classical
  tauto

theorem initial34749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4866)) := by
  have source := ElevenTheory.theory24005 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule34749 (meaning t m 2027) (meaning t m 3319) (meaning t m 3359) (meaning t m 3365) (meaning t m 3366) (meaning t m 3413) (meaning t m 3461) (meaning t m 4315) (meaning t m 4444) (meaning t m 4697) (meaning t m 4866) source

theorem rule34751 (p1992 p2027 p2608 p2850 p3008 p3555 p3584 p4034 : Prop) (h : (¬ p1992) ∨ (¬ p2608) ∨ p3008 ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3584) ∨ (¬ p4034) ∨ (¬ p3555)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2850) ∨ (p3008) ∨ (¬ p3555) ∨ (¬ p3584) ∨ (¬ p4034) := by
  classical
  tauto

theorem initial34751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4034)) := by
  have source := ElevenTheory.theory24007 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule34751 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2850) (meaning t m 3008) (meaning t m 3555) (meaning t m 3584) (meaning t m 4034) source

theorem rule34752 (p1975 p2027 p2114 p2299 p3093 p3527 p3954 p4452 : Prop) (h : (¬ p2299) ∨ (¬ p3093) ∨ (¬ p1975) ∨ (¬ p3527) ∨ (¬ p4452) ∨ p2114 ∨ p2027 ∨ (¬ p3954)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial34752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory24008 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34752 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2299) (meaning t m 3093) (meaning t m 3527) (meaning t m 3954) (meaning t m 4452) source

theorem rule34755 (p2027 p2122 p2563 p3556 p3645 p4210 p4275 p4401 : Prop) (h : (¬ p4401) ∨ (¬ p3645) ∨ (¬ p4210) ∨ (¬ p2563) ∨ (¬ p3556) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2563) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4210) ∨ (¬ p4275) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial34755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory24011 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule34755 (meaning t m 2027) (meaning t m 2122) (meaning t m 2563) (meaning t m 3556) (meaning t m 3645) (meaning t m 4210) (meaning t m 4275) (meaning t m 4401) source

theorem rule34756 (p2027 p2598 p3585 p3589 p4366 p4793 : Prop) (h : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ p2027 ∨ (¬ p4793) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial34756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory24012 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4)
  exact rule34756 (meaning t m 2027) (meaning t m 2598) (meaning t m 3585) (meaning t m 3589) (meaning t m 4366) (meaning t m 4793) source

theorem rule34758 (p2027 p2598 p3555 p3585 p3589 p4377 : Prop) (h : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial34758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory24014 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4)
  exact rule34758 (meaning t m 2027) (meaning t m 2598) (meaning t m 3555) (meaning t m 3585) (meaning t m 3589) (meaning t m 4377) source

theorem rule34759 (p2027 p2598 p3585 p3589 p3591 p4866 : Prop) (h : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ p2027 ∨ (¬ p4866) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p4866) := by
  classical
  tauto

theorem initial34759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4866)) := by
  have source := ElevenTheory.theory24015 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4)
  exact rule34759 (meaning t m 2027) (meaning t m 2598) (meaning t m 3585) (meaning t m 3589) (meaning t m 3591) (meaning t m 4866) source

theorem rule34761 (p2619 p4119 p4244 : Prop) (h : (¬ p2619) ∨ (¬ p4244) ∨ (¬ p4119)) : (¬ p2619) ∨ (¬ p4119) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial34761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory24017 (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule34761 (meaning t m 2619) (meaning t m 4119) (meaning t m 4244) source

theorem rule34764 (p2027 p2396 p2743 p2774 p3172 p3309 p3361 p3918 p3950 p4118 p4737 : Prop) (h : (¬ p3918) ∨ (¬ p4737) ∨ (¬ p3950) ∨ (¬ p2743) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p3309) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p3361) ∨ (¬ p3918) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial34764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory24020 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule34764 (meaning t m 2027) (meaning t m 2396) (meaning t m 2743) (meaning t m 2774) (meaning t m 3172) (meaning t m 3309) (meaning t m 3361) (meaning t m 3918) (meaning t m 3950) (meaning t m 4118) (meaning t m 4737) source

theorem rule34765 (p3358 p3874 p5160 : Prop) (h : (¬ p3358) ∨ (¬ p5160) ∨ p3874) : (¬ p3358) ∨ (p3874) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial34765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3358)) ∨ (meaning t m 3874) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory24021 (m.theta 2 4) (m.theta 4 8) (m.theta 4 9)
  exact rule34765 (meaning t m 3358) (meaning t m 3874) (meaning t m 5160) source

theorem rule34768 (p2027 p2284 p3125 p4275 p4320 p4624 : Prop) (h : (¬ p4320) ∨ (¬ p2284) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial34768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory24024 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule34768 (meaning t m 2027) (meaning t m 2284) (meaning t m 3125) (meaning t m 4275) (meaning t m 4320) (meaning t m 4624) source

theorem rule34769 (p2027 p2284 p2383 p3743 p4275 p4320 p4405 : Prop) (h : (¬ p3743) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p4405) ∨ (¬ p2284) ∨ (¬ p4275) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2383) ∨ (¬ p3743) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial34769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory24025 t (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule34769 (meaning t m 2027) (meaning t m 2284) (meaning t m 2383) (meaning t m 3743) (meaning t m 4275) (meaning t m 4320) (meaning t m 4405) source

theorem rule34770 (p2027 p2139 p3212 p3365 p3572 p3680 p3947 p4191 p4621 : Prop) (h : (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p4621) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p3212) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4191) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial34770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory24026 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule34770 (meaning t m 2027) (meaning t m 2139) (meaning t m 3212) (meaning t m 3365) (meaning t m 3572) (meaning t m 3680) (meaning t m 3947) (meaning t m 4191) (meaning t m 4621) source

theorem rule34771 (p2027 p2299 p2319 p2341 p2779 p2829 p3055 p3238 p4030 p4235 p4559 p4734 : Prop) (h : (¬ p4559) ∨ (¬ p4030) ∨ (¬ p4235) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p2319) ∨ (¬ p2829) ∨ (¬ p2779) ∨ (¬ p3238) ∨ (¬ p2341) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p4030) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial34771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory24027 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34771 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2779) (meaning t m 2829) (meaning t m 3055) (meaning t m 3238) (meaning t m 4030) (meaning t m 4235) (meaning t m 4559) (meaning t m 4734) source

theorem rule34773 (p1978 p2027 p2169 p3323 p3324 p3646 p3744 : Prop) (h : p2169 ∨ (¬ p3324) ∨ (¬ p1978) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3323)) : (¬ p1978) ∨ (p2027) ∨ (p2169) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3646) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial34773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory24029 t (m.theta 0 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule34773 (meaning t m 1978) (meaning t m 2027) (meaning t m 2169) (meaning t m 3323) (meaning t m 3324) (meaning t m 3646) (meaning t m 3744) source

theorem rule34775 (p2027 p3609 p3822 p4347 p4405 p4861 : Prop) (h : p2027 ∨ (¬ p3609) ∨ (¬ p4405) ∨ (¬ p4347) ∨ (¬ p3822) ∨ (¬ p4861)) : (p2027) ∨ (¬ p3609) ∨ (¬ p3822) ∨ (¬ p4347) ∨ (¬ p4405) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial34775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory24031 t (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule34775 (meaning t m 2027) (meaning t m 3609) (meaning t m 3822) (meaning t m 4347) (meaning t m 4405) (meaning t m 4861) source

theorem rule34779 (p1981 p2027 p2187 p2699 p3093 p3319 p3744 : Prop) (h : p2027 ∨ (¬ p3093) ∨ p2699 ∨ (¬ p2187) ∨ (¬ p1981) ∨ (¬ p3319) ∨ (¬ p3744)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial34779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory24035 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule34779 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 3744) source

theorem rule34780 (p1975 p2027 p2299 p2608 p2699 p2717 p2829 p3426 : Prop) (h : (¬ p2717) ∨ (¬ p3426) ∨ (¬ p2299) ∨ p2699 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p1975) ∨ (¬ p2829)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2717) ∨ (¬ p2829) ∨ (¬ p3426) := by
  classical
  tauto

theorem initial34780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3426)) := by
  have source := ElevenTheory.theory24036 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34780 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2608) (meaning t m 2699) (meaning t m 2717) (meaning t m 2829) (meaning t m 3426) source

theorem rule34783 (p1976 p2027 p2797 p2938 p2963 p4236 p4315 p4320 : Prop) (h : (¬ p1976) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4320) ∨ p2027 ∨ p2938 ∨ (¬ p4315)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2797) ∨ (p2938) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial34783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory24039 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule34783 (meaning t m 1976) (meaning t m 2027) (meaning t m 2797) (meaning t m 2938) (meaning t m 2963) (meaning t m 4236) (meaning t m 4315) (meaning t m 4320) source

theorem rule34787 (p2027 p2753 p3379 p3434 p3471 p3657 p3860 p3941 p4261 p5122 p5216 : Prop) (h : (¬ p4261) ∨ (¬ p3941) ∨ (¬ p3471) ∨ (¬ p5216) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p3657) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3657) ∨ (¬ p3860) ∨ (¬ p3941) ∨ (¬ p4261) ∨ (¬ p5122) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial34787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory24043 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule34787 (meaning t m 2027) (meaning t m 2753) (meaning t m 3379) (meaning t m 3434) (meaning t m 3471) (meaning t m 3657) (meaning t m 3860) (meaning t m 3941) (meaning t m 4261) (meaning t m 5122) (meaning t m 5216) source

theorem rule34789 (p1998 p2027 p2177 p2247 p2545 p2553 p2573 p2810 p3005 p4360 p5190 : Prop) (h : p2545 ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p5190) ∨ (¬ p2573) ∨ (¬ p1998) ∨ (¬ p3005) ∨ (¬ p4360)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (p2545) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4360) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial34789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory24045 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule34789 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2545) (meaning t m 2553) (meaning t m 2573) (meaning t m 2810) (meaning t m 3005) (meaning t m 4360) (meaning t m 5190) source

theorem rule34791 (p1987 p2027 p2938 p2982 p4208 p4235 p4315 : Prop) (h : (¬ p4315) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4235) ∨ p2938 ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (p2938) ∨ (¬ p2982) ∨ (¬ p4208) ∨ (¬ p4235) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory24047 t (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule34791 (meaning t m 1987) (meaning t m 2027) (meaning t m 2938) (meaning t m 2982) (meaning t m 4208) (meaning t m 4235) (meaning t m 4315) source

theorem rule34792 (p2027 p2651 p2745 p2797 p2963 p4111 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p2745) ∨ (¬ p2651) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial34792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory24048 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule34792 (meaning t m 2027) (meaning t m 2651) (meaning t m 2745) (meaning t m 2797) (meaning t m 2963) (meaning t m 4111) source

theorem rule34795 (p1998 p2027 p2177 p2553 p2622 p2630 p3016 : Prop) (h : p2622 ∨ (¬ p2630) ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3016)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial34795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory24051 t (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule34795 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2622) (meaning t m 2630) (meaning t m 3016) source

theorem rule34797 (p2027 p2299 p2589 p2850 p3399 p3527 p3876 p3905 p4001 p4559 p4736 : Prop) (h : (¬ p4736) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p2299) ∨ (¬ p4559) ∨ (¬ p3527) ∨ (¬ p3399) ∨ (¬ p4001) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4001) ∨ (¬ p4559) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24053 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34797 (meaning t m 2027) (meaning t m 2299) (meaning t m 2589) (meaning t m 2850) (meaning t m 3399) (meaning t m 3527) (meaning t m 3876) (meaning t m 3905) (meaning t m 4001) (meaning t m 4559) (meaning t m 4736) source

theorem rule34799 (p2027 p2248 p2264 p2807 p3941 p3954 p4242 p4340 p5122 : Prop) (h : (¬ p3941) ∨ (¬ p4340) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2807) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial34799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory24055 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule34799 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2807) (meaning t m 3941) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) (meaning t m 5122) source

theorem rule34803 (p1992 p2027 p2608 p2765 p3238 p3452 p4110 : Prop) (h : p2027 ∨ (¬ p1992) ∨ (¬ p3452) ∨ (¬ p4110) ∨ p2765 ∨ (¬ p3238) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2765) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial34803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory24059 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6)
  exact rule34803 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2765) (meaning t m 3238) (meaning t m 3452) (meaning t m 4110) source

theorem rule34804 (p2027 p2406 p3364 p3541 p3588 p3684 p4778 : Prop) (h : (¬ p3364) ∨ (¬ p2406) ∨ (¬ p4778) ∨ (¬ p3541) ∨ p2027 ∨ (¬ p3588) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2406) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3588) ∨ (¬ p3684) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial34804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory24060 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5)
  exact rule34804 (meaning t m 2027) (meaning t m 2406) (meaning t m 3364) (meaning t m 3541) (meaning t m 3588) (meaning t m 3684) (meaning t m 4778) source

theorem rule34809 (p2027 p2299 p2406 p2589 p2717 p2928 p3471 p4001 p4108 p4559 p4733 : Prop) (h : (¬ p4001) ∨ (¬ p2928) ∨ (¬ p2299) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p4733) ∨ (¬ p4108) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2928) ∨ (¬ p3471) ∨ (¬ p4001) ∨ (¬ p4108) ∨ (¬ p4559) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial34809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory24065 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34809 (meaning t m 2027) (meaning t m 2299) (meaning t m 2406) (meaning t m 2589) (meaning t m 2717) (meaning t m 2928) (meaning t m 3471) (meaning t m 4001) (meaning t m 4108) (meaning t m 4559) (meaning t m 4733) source

theorem rule34811 (p1983 p2027 p2299 p2341 p2396 p2688 p3027 p4066 : Prop) (h : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p4066) ∨ (¬ p1983) ∨ p2688 ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3027)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial34811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory24067 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule34811 (meaning t m 1983) (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2396) (meaning t m 2688) (meaning t m 3027) (meaning t m 4066) source

theorem rule34815 (p2027 p2299 p2406 p2589 p2717 p2928 p3471 p4108 p4712 p4733 : Prop) (h : (¬ p4733) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2928) ∨ (¬ p4712) ∨ (¬ p2589) ∨ (¬ p2299) ∨ (¬ p2406) ∨ (¬ p4108) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p2928) ∨ (¬ p3471) ∨ (¬ p4108) ∨ (¬ p4712) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial34815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory24071 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule34815 (meaning t m 2027) (meaning t m 2299) (meaning t m 2406) (meaning t m 2589) (meaning t m 2717) (meaning t m 2928) (meaning t m 3471) (meaning t m 4108) (meaning t m 4712) (meaning t m 4733) source

theorem rule34817 (p3657 p3945 : Prop) (h : p3657 ∨ p3945) : (p3657) ∨ (p3945) := by
  classical
  tauto

theorem initial34817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3657) ∨ (meaning t m 3945) := by
  have source := ElevenTheory.theory24073 (m.theta 7 8) (m.theta 7 9)
  exact rule34817 (meaning t m 3657) (meaning t m 3945) source

theorem rule34819 (p1994 p2027 p2264 p2651 p2688 p3027 p3551 p4849 : Prop) (h : (¬ p4849) ∨ (¬ p2264) ∨ (¬ p3551) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p2651) ∨ p2688 ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2651) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3551) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial34819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory24075 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule34819 (meaning t m 1994) (meaning t m 2027) (meaning t m 2264) (meaning t m 2651) (meaning t m 2688) (meaning t m 3027) (meaning t m 3551) (meaning t m 4849) source

theorem rule34820 (p3550 p4134 p4905 : Prop) (h : (¬ p3550) ∨ (¬ p4905) ∨ p4134) : (¬ p3550) ∨ (p4134) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial34820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (meaning t m 4134) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory24076 t (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule34820 (meaning t m 3550) (meaning t m 4134) (meaning t m 4905) source

theorem rule34827 (p2027 p2246 p2331 p2363 p2608 p2668 p2744 p3555 p4363 p5059 : Prop) (h : (¬ p2363) ∨ (¬ p2331) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p5059) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p4363)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial34827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory24083 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule34827 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2363) (meaning t m 2608) (meaning t m 2668) (meaning t m 2744) (meaning t m 3555) (meaning t m 4363) (meaning t m 5059) source

theorem rule34830 (p1994 p2027 p2633 p2651 p2952 p3570 p4320 : Prop) (h : (¬ p1994) ∨ p2633 ∨ (¬ p4320) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570)) : (¬ p1994) ∨ (p2027) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial34830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory24086 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule34830 (meaning t m 1994) (meaning t m 2027) (meaning t m 2633) (meaning t m 2651) (meaning t m 2952) (meaning t m 3570) (meaning t m 4320) source

theorem rule34838 (p2027 p2319 p2341 p2584 p2665 p3644 p3742 : Prop) (h : (¬ p2584) ∨ (¬ p2319) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2665) ∨ (¬ p2341) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial34838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory24094 t (m.theta 0 4) (m.theta 0 6) (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule34838 (meaning t m 2027) (meaning t m 2319) (meaning t m 2341) (meaning t m 2584) (meaning t m 2665) (meaning t m 3644) (meaning t m 3742) source

theorem rule34840 (p2137 p4525 p4875 : Prop) (h : (¬ p4875) ∨ (¬ p2137) ∨ p4525) : (¬ p2137) ∨ (p4525) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial34840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (meaning t m 4525) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory24096 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 5)
  exact rule34840 (meaning t m 2137) (meaning t m 4525) (meaning t m 4875) source

theorem rule34842 (p2027 p3005 p3572 p3947 p4378 p4666 : Prop) (h : (¬ p4378) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4666)) : (p2027) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4378) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial34842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory24098 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 7 9)
  exact rule34842 (meaning t m 2027) (meaning t m 3005) (meaning t m 3572) (meaning t m 3947) (meaning t m 4378) (meaning t m 4666) source

theorem rule34843 (p2027 p2657 p3166 p3238 p3487 p3880 p5063 : Prop) (h : (¬ p3238) ∨ p2027 ∨ (¬ p3487) ∨ (¬ p2657) ∨ (¬ p5063) ∨ (¬ p3880) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial34843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory24099 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule34843 (meaning t m 2027) (meaning t m 2657) (meaning t m 3166) (meaning t m 3238) (meaning t m 3487) (meaning t m 3880) (meaning t m 5063) source

theorem rule34845 (p2027 p2104 p2177 p2528 p3093 p3309 p4340 p4438 p4736 : Prop) (h : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2104) ∨ (¬ p2528) ∨ (¬ p3309) ∨ (¬ p4438)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4340) ∨ (¬ p4438) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24101 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 8) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule34845 (meaning t m 2027) (meaning t m 2104) (meaning t m 2177) (meaning t m 2528) (meaning t m 3093) (meaning t m 3309) (meaning t m 4340) (meaning t m 4438) (meaning t m 4736) source

theorem rule34861 (p2027 p2104 p2187 p2192 p2210 p2528 p4340 p4384 p4736 : Prop) (h : (¬ p2187) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4736) ∨ (¬ p4384) ∨ (¬ p2104) ∨ (¬ p4340) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4384) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24117 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule34861 (meaning t m 2027) (meaning t m 2104) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2528) (meaning t m 4340) (meaning t m 4384) (meaning t m 4736) source

theorem rule34871 (p1987 p2027 p2373 p2765 p3497 p4110 p4315 : Prop) (h : (¬ p2373) ∨ (¬ p4315) ∨ p2765 ∨ (¬ p1987) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3497)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3497) ∨ (¬ p4110) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory24127 t (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule34871 (meaning t m 1987) (meaning t m 2027) (meaning t m 2373) (meaning t m 2765) (meaning t m 3497) (meaning t m 4110) (meaning t m 4315) source

theorem rule34875 (p1987 p2027 p2737 p3360 p3516 p3588 p4324 : Prop) (h : p3360 ∨ (¬ p3516) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p2737) ∨ (¬ p3588) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p3360) ∨ (¬ p3516) ∨ (¬ p3588) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial34875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory24131 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule34875 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 3360) (meaning t m 3516) (meaning t m 3588) (meaning t m 4324) source

theorem rule34876 (p1986 p2027 p2287 p2963 p3166 p3367 p4242 p4963 : Prop) (h : p2287 ∨ (¬ p4963) ∨ (¬ p2963) ∨ (¬ p3367) ∨ (¬ p1986) ∨ (¬ p4242) ∨ p2027 ∨ (¬ p3166)) : (¬ p1986) ∨ (p2027) ∨ (p2287) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial34876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory24132 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 3 6) (m.theta 3 8)
  exact rule34876 (meaning t m 1986) (meaning t m 2027) (meaning t m 2287) (meaning t m 2963) (meaning t m 3166) (meaning t m 3367) (meaning t m 4242) (meaning t m 4963) source

theorem rule34877 (p1987 p2027 p2982 p3578 p3880 p4208 p4315 : Prop) (h : p3578 ∨ (¬ p3880) ∨ (¬ p4315) ∨ (¬ p1987) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p4208)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2982) ∨ (p3578) ∨ (¬ p3880) ∨ (¬ p4208) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory24133 t (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule34877 (meaning t m 1987) (meaning t m 2027) (meaning t m 2982) (meaning t m 3578) (meaning t m 3880) (meaning t m 4208) (meaning t m 4315) source

theorem rule34880 (p1987 p2027 p2765 p2982 p4110 p4208 p4315 : Prop) (h : (¬ p4110) ∨ (¬ p1987) ∨ (¬ p4315) ∨ p2027 ∨ p2765 ∨ (¬ p4208) ∨ (¬ p2982)) : (¬ p1987) ∨ (p2027) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4208) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory24136 t (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule34880 (meaning t m 1987) (meaning t m 2027) (meaning t m 2765) (meaning t m 2982) (meaning t m 4110) (meaning t m 4208) (meaning t m 4315) source

theorem rule34887 (p1977 p2027 p2459 p2534 p2633 p2662 p3540 p4111 p4186 : Prop) (h : p2027 ∨ (¬ p4111) ∨ (¬ p2662) ∨ (¬ p1977) ∨ (¬ p3540) ∨ (¬ p2459) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p4186)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial34887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory24143 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34887 (meaning t m 1977) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2633) (meaning t m 2662) (meaning t m 3540) (meaning t m 4111) (meaning t m 4186) source

theorem rule34889 (p1977 p2027 p2462 p2911 p2996 p3551 p4155 p4278 : Prop) (h : (¬ p1977) ∨ (¬ p4278) ∨ (¬ p2996) ∨ p2462 ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4155) ∨ (¬ p2911)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial34889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory24145 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule34889 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2911) (meaning t m 2996) (meaning t m 3551) (meaning t m 4155) (meaning t m 4278) source

theorem rule34891 (p2027 p2952 p3286 p4039 p4385 p4906 : Prop) (h : (¬ p2952) ∨ (¬ p4906) ∨ p2027 ∨ (¬ p4039) ∨ (¬ p3286) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4039) ∨ (¬ p4385) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial34891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory24147 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9)
  exact rule34891 (meaning t m 2027) (meaning t m 2952) (meaning t m 3286) (meaning t m 4039) (meaning t m 4385) (meaning t m 4906) source

theorem rule34902 (p1993 p2027 p2299 p2313 p2633 p2667 p3189 p4154 : Prop) (h : (¬ p2667) ∨ p2027 ∨ (¬ p1993) ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2313) ∨ (¬ p3189) ∨ (¬ p4154)) : (¬ p1993) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial34902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory24158 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule34902 (meaning t m 1993) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2633) (meaning t m 2667) (meaning t m 3189) (meaning t m 4154) source

theorem rule34903 (p1987 p2027 p2252 p2588 p2727 p2810 p2963 p2997 p4389 : Prop) (h : (¬ p2252) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2963) ∨ (¬ p2727) ∨ (¬ p4389) ∨ (¬ p1987) ∨ (¬ p2810) ∨ p2997) : (¬ p1987) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2588) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial34903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory24159 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule34903 (meaning t m 1987) (meaning t m 2027) (meaning t m 2252) (meaning t m 2588) (meaning t m 2727) (meaning t m 2810) (meaning t m 2963) (meaning t m 2997) (meaning t m 4389) source

theorem rule34904 (p1977 p2027 p2352 p2387 p2588 p2667 p2997 p4154 : Prop) (h : (¬ p2352) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2667) ∨ (¬ p4154) ∨ (¬ p2387) ∨ p2997 ∨ (¬ p2588)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (p2997) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial34904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory24160 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule34904 (meaning t m 1977) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2588) (meaning t m 2667) (meaning t m 2997) (meaning t m 4154) source

theorem rule34905 (p2027 p2255 p3031 p3166 p3256 p3544 p4261 : Prop) (h : (¬ p2255) ∨ (¬ p3166) ∨ (¬ p3544) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p3031) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2255) ∨ (¬ p3031) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3544) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial34905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory24161 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 1 8) (m.theta 3 8) (m.theta 8 9)
  exact rule34905 (meaning t m 2027) (meaning t m 2255) (meaning t m 3031) (meaning t m 3166) (meaning t m 3256) (meaning t m 3544) (meaning t m 4261) source

theorem rule34906 (p2641 p3189 p4196 : Prop) (h : (¬ p3189) ∨ (¬ p4196) ∨ p2641) : (p2641) ∨ (¬ p3189) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial34906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2641) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory24162 (m.theta 1 3) (m.theta 3 6) (m.theta 3 8)
  exact rule34906 (meaning t m 2641) (meaning t m 3189) (meaning t m 4196) source

theorem rule34910 (p1987 p2027 p2252 p2588 p2651 p2810 p2997 p4154 p4389 : Prop) (h : p2997 ∨ (¬ p4389) ∨ (¬ p2810) ∨ (¬ p2588) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4154) ∨ p2252) : (¬ p1987) ∨ (p2027) ∨ (p2252) ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (p2997) ∨ (¬ p4154) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial34910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2252) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory24166 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule34910 (meaning t m 1987) (meaning t m 2027) (meaning t m 2252) (meaning t m 2588) (meaning t m 2651) (meaning t m 2810) (meaning t m 2997) (meaning t m 4154) (meaning t m 4389) source

theorem rule34911 (p1975 p2027 p2299 p2331 p2388 p2952 p3527 p4319 p4452 : Prop) (h : p2388 ∨ (¬ p1975) ∨ p2027 ∨ (¬ p4319) ∨ (¬ p2952) ∨ (¬ p2331) ∨ (¬ p3527) ∨ (¬ p4452) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3527) ∨ (¬ p4319) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial34911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory24167 t (m.theta 0 3) (m.theta 1 6) (m.theta 1 7) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule34911 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2331) (meaning t m 2388) (meaning t m 2952) (meaning t m 3527) (meaning t m 4319) (meaning t m 4452) source

theorem rule34912 (p2027 p2255 p2352 p2493 p2651 p2957 p3556 p3570 p3662 p4116 p4133 : Prop) (h : (¬ p3662) ∨ (¬ p2352) ∨ (¬ p2957) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2493) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4116) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4116) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial34912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory24168 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule34912 (meaning t m 2027) (meaning t m 2255) (meaning t m 2352) (meaning t m 2493) (meaning t m 2651) (meaning t m 2957) (meaning t m 3556) (meaning t m 3570) (meaning t m 3662) (meaning t m 4116) (meaning t m 4133) source

theorem rule34913 (p2027 p2255 p2651 p2996 p3222 p3276 p3577 p3659 p4116 p4155 p5123 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p3577) ∨ p2027 ∨ (¬ p3222) ∨ (¬ p3659) ∨ (¬ p2255) ∨ (¬ p3276) ∨ (¬ p5123) ∨ (¬ p4116) ∨ (¬ p2651) ∨ (¬ p4155) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3577) ∨ (¬ p3659) ∨ (¬ p4116) ∨ (¬ p4155) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial34913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory24169 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule34913 (meaning t m 2027) (meaning t m 2255) (meaning t m 2651) (meaning t m 2996) (meaning t m 3222) (meaning t m 3276) (meaning t m 3577) (meaning t m 3659) (meaning t m 4116) (meaning t m 4155) (meaning t m 5123) (meaning t m 5558) source

theorem rule34918 (p2027 p2177 p3027 p3177 p3960 p4360 p4570 : Prop) (h : (¬ p3027) ∨ (¬ p3177) ∨ (¬ p3960) ∨ (¬ p2177) ∨ (¬ p4570) ∨ (¬ p4360) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p3027) ∨ (¬ p3177) ∨ (¬ p3960) ∨ (¬ p4360) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial34918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory24174 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule34918 (meaning t m 2027) (meaning t m 2177) (meaning t m 3027) (meaning t m 3177) (meaning t m 3960) (meaning t m 4360) (meaning t m 4570) source

theorem rule34919 (p2027 p2331 p2952 p3758 p4319 p4516 p4906 : Prop) (h : p2027 ∨ (¬ p4516) ∨ (¬ p4906) ∨ (¬ p3758) ∨ (¬ p4319) ∨ (¬ p2952) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3758) ∨ (¬ p4319) ∨ (¬ p4516) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial34919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory24175 t (m.theta 0 3) (m.theta 1 6) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule34919 (meaning t m 2027) (meaning t m 2331) (meaning t m 2952) (meaning t m 3758) (meaning t m 4319) (meaning t m 4516) (meaning t m 4906) source

theorem rule34922 (p2027 p3527 p3570 p4173 p4431 p4558 : Prop) (h : p2027 ∨ (¬ p4558) ∨ (¬ p4173) ∨ (¬ p3570) ∨ (¬ p4431) ∨ (¬ p3527)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4173) ∨ (¬ p4431) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial34922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory24178 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule34922 (meaning t m 2027) (meaning t m 3527) (meaning t m 3570) (meaning t m 4173) (meaning t m 4431) (meaning t m 4558) source

theorem rule34923 (p2210 p3093 p4338 : Prop) (h : (¬ p2210) ∨ (¬ p4338) ∨ p3093) : (¬ p2210) ∨ (p3093) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial34923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (meaning t m 3093) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory24179 (m.theta 0 1) (m.theta 1 5) (m.theta 1 6)
  exact rule34923 (meaning t m 2210) (meaning t m 3093) (meaning t m 4338) source

theorem rule34928 (p1998 p2027 p2210 p2352 p2588 p2780 p2881 p2891 p2997 p4358 p4736 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2780) ∨ (¬ p4736) ∨ (¬ p2891) ∨ (¬ p1998) ∨ (¬ p2352) ∨ p2997) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (p2997) ∨ (¬ p4358) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24184 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule34928 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2352) (meaning t m 2588) (meaning t m 2780) (meaning t m 2881) (meaning t m 2891) (meaning t m 2997) (meaning t m 4358) (meaning t m 4736) source

theorem rule34930 (p1994 p2027 p2633 p2651 p2952 p3570 p3879 p4235 : Prop) (h : (¬ p3570) ∨ (¬ p2651) ∨ (¬ p3879) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p1994) ∨ p2633 ∨ (¬ p2952)) : (¬ p1994) ∨ (p2027) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial34930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory24186 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule34930 (meaning t m 1994) (meaning t m 2027) (meaning t m 2633) (meaning t m 2651) (meaning t m 2952) (meaning t m 3570) (meaning t m 3879) (meaning t m 4235) source

theorem rule34931 (p1994 p2027 p2630 p2633 p3570 p3879 p4235 p4315 : Prop) (h : (¬ p3570) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3879) ∨ (¬ p4235) ∨ (¬ p2630) ∨ p2633 ∨ (¬ p4315)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p3570) ∨ (¬ p3879) ∨ (¬ p4235) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial34931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory24187 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule34931 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2633) (meaning t m 3570) (meaning t m 3879) (meaning t m 4235) (meaning t m 4315) source

theorem rule34934 (p2027 p3246 p3309 p4026 p4396 p4559 : Prop) (h : p2027 ∨ (¬ p4396) ∨ (¬ p3246) ∨ (¬ p4026) ∨ (¬ p4559) ∨ (¬ p3309)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial34934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory24190 t (m.theta 1 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule34934 (meaning t m 2027) (meaning t m 3246) (meaning t m 3309) (meaning t m 4026) (meaning t m 4396) (meaning t m 4559) source

theorem rule34935 (p2027 p2255 p2417 p2651 p2922 p2957 p3662 p3680 p3773 p3951 p4116 p4380 : Prop) (h : (¬ p2651) ∨ (¬ p2255) ∨ (¬ p2417) ∨ (¬ p3662) ∨ (¬ p3773) ∨ (¬ p4116) ∨ (¬ p4380) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p2922) ∨ (¬ p3951) ∨ (¬ p2957)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3951) ∨ (¬ p4116) ∨ (¬ p4380) := by
  classical
  tauto

theorem initial34935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4380)) := by
  have source := ElevenTheory.theory24191 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 9) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule34935 (meaning t m 2027) (meaning t m 2255) (meaning t m 2417) (meaning t m 2651) (meaning t m 2922) (meaning t m 2957) (meaning t m 3662) (meaning t m 3680) (meaning t m 3773) (meaning t m 3951) (meaning t m 4116) (meaning t m 4380) source

theorem rule34938 (p2166 p3412 p3497 : Prop) (h : (¬ p2166) ∨ (¬ p3412) ∨ (¬ p3497)) : (¬ p2166) ∨ (¬ p3412) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial34938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory24194 (m.theta 1 5) (m.theta 3 5) (m.theta 5 8)
  exact rule34938 (meaning t m 2166) (meaning t m 3412) (meaning t m 3497) source

theorem rule34944 (p3323 p3483 p4328 : Prop) (h : (¬ p3323) ∨ (¬ p4328) ∨ p3483) : (¬ p3323) ∨ (p3483) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial34944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3323)) ∨ (meaning t m 3483) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory24200 (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule34944 (meaning t m 3323) (meaning t m 3483) (meaning t m 4328) source

theorem rule34949 (p2027 p2518 p2651 p3364 p3874 p4116 p4790 : Prop) (h : (¬ p4790) ∨ (¬ p2651) ∨ (¬ p3364) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p4116) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4116) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial34949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory24205 t (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8)
  exact rule34949 (meaning t m 2027) (meaning t m 2518) (meaning t m 2651) (meaning t m 3364) (meaning t m 3874) (meaning t m 4116) (meaning t m 4790) source

theorem rule34952 (p1989 p2027 p2313 p2764 p4107 p4173 p4356 p4381 : Prop) (h : p2027 ∨ (¬ p2313) ∨ (¬ p4356) ∨ (¬ p4173) ∨ (¬ p4107) ∨ (¬ p1989) ∨ p2764 ∨ (¬ p4381)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2313) ∨ (p2764) ∨ (¬ p4107) ∨ (¬ p4173) ∨ (¬ p4356) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial34952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory24208 t (m.theta 0 6) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule34952 (meaning t m 1989) (meaning t m 2027) (meaning t m 2313) (meaning t m 2764) (meaning t m 4107) (meaning t m 4173) (meaning t m 4356) (meaning t m 4381) source

theorem rule34954 (p4322 p4425 p4952 : Prop) (h : (¬ p4425) ∨ (¬ p4952) ∨ p4322) : (p4322) ∨ (¬ p4425) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial34954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4322) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory24210 (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule34954 (meaning t m 4322) (meaning t m 4425) (meaning t m 4952) source

theorem rule34955 (p3920 p4137 p4278 p4396 : Prop) (h : (¬ p3920) ∨ (¬ p4137) ∨ (¬ p4396) ∨ p4278) : (¬ p3920) ∨ (¬ p4137) ∨ (p4278) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial34955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4137)) ∨ (meaning t m 4278) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory24211 (m.theta 4 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9)
  exact rule34955 (meaning t m 3920) (meaning t m 4137) (meaning t m 4278) (meaning t m 4396) source

theorem rule34959 (p2807 p2946 p4386 : Prop) (h : (¬ p4386) ∨ (¬ p2807) ∨ p2946) : (¬ p2807) ∨ (p2946) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial34959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (meaning t m 2946) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory24215 (m.theta 0 3) (m.theta 3 5) (m.theta 3 7)
  exact rule34959 (meaning t m 2807) (meaning t m 2946) (meaning t m 4386) source

theorem rule34963 (p2027 p2255 p2528 p2651 p2957 p3083 p3556 p3662 p3690 p4669 : Prop) (h : (¬ p2651) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p2528) ∨ (¬ p2255) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2957) ∨ (¬ p3083) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial34963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory24219 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule34963 (meaning t m 2027) (meaning t m 2255) (meaning t m 2528) (meaning t m 2651) (meaning t m 2957) (meaning t m 3083) (meaning t m 3556) (meaning t m 3662) (meaning t m 3690) (meaning t m 4669) source

theorem rule34964 (p2027 p2417 p2476 p3389 p4383 p4668 : Prop) (h : (¬ p2417) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4668) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial34964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory24220 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9)
  exact rule34964 (meaning t m 2027) (meaning t m 2417) (meaning t m 2476) (meaning t m 3389) (meaning t m 4383) (meaning t m 4668) source

theorem rule34966 (p1979 p2027 p2699 p3093 p3136 p3309 p3822 p4841 : Prop) (h : (¬ p3822) ∨ p2699 ∨ (¬ p1979) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p4841)) : (¬ p1979) ∨ (p2027) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial34966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory24222 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 6 7)
  exact rule34966 (meaning t m 1979) (meaning t m 2027) (meaning t m 2699) (meaning t m 3093) (meaning t m 3136) (meaning t m 3309) (meaning t m 3822) (meaning t m 4841) source

theorem rule34969 (p2027 p2254 p2363 p2440 p2657 p3063 p3093 p4948 p5059 : Prop) (h : (¬ p2363) ∨ (¬ p2254) ∨ (¬ p3093) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2440) ∨ (¬ p5059) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial34969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory24225 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule34969 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2440) (meaning t m 2657) (meaning t m 3063) (meaning t m 3093) (meaning t m 4948) (meaning t m 5059) source

theorem rule34976 (p1990 p2027 p2114 p2210 p3097 p3309 p3954 p4338 : Prop) (h : (¬ p3954) ∨ p2114 ∨ (¬ p4338) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p3309)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p3954) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial34976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory24232 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule34976 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 3097) (meaning t m 3309) (meaning t m 3954) (meaning t m 4338) source

theorem rule34977 (p2027 p3073 p3201 p3449 p3540 p3874 p3905 p4347 p4384 p4736 : Prop) (h : (¬ p3874) ∨ (¬ p3905) ∨ (¬ p3449) ∨ (¬ p4384) ∨ (¬ p4736) ∨ (¬ p3201) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4347)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3201) ∨ (¬ p3449) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial34977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24233 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule34977 (meaning t m 2027) (meaning t m 3073) (meaning t m 3201) (meaning t m 3449) (meaning t m 3540) (meaning t m 3874) (meaning t m 3905) (meaning t m 4347) (meaning t m 4384) (meaning t m 4736) source

theorem rule34982 (p1975 p2027 p2553 p2598 p2633 p2819 p3486 p3555 p3570 p3956 p4375 p4733 : Prop) (h : (¬ p1975) ∨ (¬ p4733) ∨ (¬ p2819) ∨ (¬ p2598) ∨ (¬ p4375) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ p2633 ∨ (¬ p3956) ∨ (¬ p2553)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p2819) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial34982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory24238 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule34982 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2598) (meaning t m 2633) (meaning t m 2819) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 3956) (meaning t m 4375) (meaning t m 4733) source

theorem rule34984 (p2027 p2187 p2641 p3958 p3984 p4360 p4769 : Prop) (h : (¬ p2187) ∨ (¬ p4769) ∨ (¬ p3958) ∨ (¬ p4360) ∨ p2027 ∨ (¬ p3984) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2641) ∨ (¬ p3958) ∨ (¬ p3984) ∨ (¬ p4360) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial34984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory24240 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule34984 (meaning t m 2027) (meaning t m 2187) (meaning t m 2641) (meaning t m 3958) (meaning t m 3984) (meaning t m 4360) (meaning t m 4769) source

theorem rule34989 (p3848 p4154 p5274 : Prop) (h : (¬ p4154) ∨ (¬ p5274) ∨ p3848) : (p3848) ∨ (¬ p4154) ∨ (¬ p5274) := by
  classical
  tauto

theorem initial34989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3848) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5274)) := by
  have source := ElevenTheory.theory24245 (m.theta 1 3) (m.theta 3 6) (m.theta 3 9)
  exact rule34989 (meaning t m 3848) (meaning t m 4154) (meaning t m 5274) source

theorem rule34990 (p2027 p2246 p2437 p2608 p2651 p2744 p2911 p3591 p3923 p4503 : Prop) (h : (¬ p2651) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p3591) ∨ (¬ p2744) ∨ (¬ p4503) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial34990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory24246 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule34990 (meaning t m 2027) (meaning t m 2246) (meaning t m 2437) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 2911) (meaning t m 3591) (meaning t m 3923) (meaning t m 4503) source

theorem rule34991 (p3319 p3323 p4319 : Prop) (h : (¬ p4319) ∨ (¬ p3319) ∨ p3323) : (¬ p3319) ∨ (p3323) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial34991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3319)) ∨ (meaning t m 3323) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory24247 (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule34991 (meaning t m 3319) (meaning t m 3323) (meaning t m 4319) source

theorem rule34992 (p2027 p2138 p3093 p3319 p3461 p3694 p4736 p5123 p5568 : Prop) (h : (¬ p3694) ∨ (¬ p2138) ∨ (¬ p3461) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p5123) ∨ (¬ p3319) ∨ (¬ p3093)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial34992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory24248 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule34992 (meaning t m 2027) (meaning t m 2138) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 3694) (meaning t m 4736) (meaning t m 5123) (meaning t m 5568) source

theorem rule34993 (p1992 p2027 p2132 p2780 p3128 p3583 p3917 : Prop) (h : p2027 ∨ p3128 ∨ (¬ p3917) ∨ (¬ p1992) ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p2780)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (p3128) ∨ (¬ p3583) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial34993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory24249 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 6 9)
  exact rule34993 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 3128) (meaning t m 3583) (meaning t m 3917) source

theorem rule34994 (p2138 p3819 p3959 p4136 : Prop) (h : (¬ p3819) ∨ (¬ p3959) ∨ (¬ p2138) ∨ (¬ p4136)) : (¬ p2138) ∨ (¬ p3819) ∨ (¬ p3959) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial34994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory24250 (m.theta 0 2) (m.theta 0 7) (m.theta 2 5) (m.theta 2 7)
  exact rule34994 (meaning t m 2138) (meaning t m 3819) (meaning t m 3959) (meaning t m 4136) source

theorem rule34995 (p2027 p2459 p2476 p2534 p3063 p3093 p3347 p3954 p4133 p5216 : Prop) (h : (¬ p2459) ∨ (¬ p4133) ∨ (¬ p3954) ∨ (¬ p3063) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3093) ∨ (¬ p3347) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3347) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial34995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory24251 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule34995 (meaning t m 2027) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 3063) (meaning t m 3093) (meaning t m 3347) (meaning t m 3954) (meaning t m 4133) (meaning t m 5216) source

theorem rule34999 (p2027 p2663 p2774 p3363 p3414 p3585 p3609 p3945 p3947 p4133 p4347 p4737 p4861 : Prop) (h : (¬ p3414) ∨ (¬ p3363) ∨ (¬ p3947) ∨ (¬ p3945) ∨ (¬ p2663) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p4737) ∨ (¬ p4133) ∨ (¬ p3585) ∨ (¬ p4347) ∨ (¬ p4861) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2663) ∨ (¬ p2774) ∨ (¬ p3363) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p3609) ∨ (¬ p3945) ∨ (¬ p3947) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4737) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial34999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory24255 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 8) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule34999 (meaning t m 2027) (meaning t m 2663) (meaning t m 2774) (meaning t m 3363) (meaning t m 3414) (meaning t m 3585) (meaning t m 3609) (meaning t m 3945) (meaning t m 3947) (meaning t m 4133) (meaning t m 4347) (meaning t m 4737) (meaning t m 4861) source

theorem rule35000 (p1979 p2027 p2187 p2765 p2946 p2963 p3324 : Prop) (h : (¬ p2946) ∨ (¬ p2963) ∨ p2765 ∨ p2027 ∨ (¬ p1979) ∨ (¬ p3324) ∨ (¬ p2187)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2187) ∨ (p2765) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial35000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory24256 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule35000 (meaning t m 1979) (meaning t m 2027) (meaning t m 2187) (meaning t m 2765) (meaning t m 2946) (meaning t m 2963) (meaning t m 3324) source

theorem rule35003 (p1994 p2027 p2630 p2748 p2997 p3097 p3662 p3952 : Prop) (h : (¬ p2630) ∨ p2997 ∨ p2027 ∨ (¬ p3952) ∨ (¬ p1994) ∨ (¬ p2748) ∨ (¬ p3097) ∨ (¬ p3662)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial35003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory24259 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule35003 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2748) (meaning t m 2997) (meaning t m 3097) (meaning t m 3662) (meaning t m 3952) source

theorem rule35004 (p1994 p2027 p2630 p2997 p3097 p3952 p4315 : Prop) (h : (¬ p3952) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4315)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial35004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory24260 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule35004 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2997) (meaning t m 3097) (meaning t m 3952) (meaning t m 4315) source

theorem rule35006 (p2027 p2246 p2352 p2608 p2651 p2744 p3016 p3549 p3591 p4405 : Prop) (h : p2027 ∨ (¬ p4405) ∨ (¬ p3591) ∨ (¬ p2651) ∨ (¬ p3549) ∨ (¬ p3016) ∨ (¬ p2608) ∨ (¬ p2352) ∨ (¬ p2744) ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial35006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory24262 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule35006 (meaning t m 2027) (meaning t m 2246) (meaning t m 2352) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3549) (meaning t m 3591) (meaning t m 4405) source

theorem rule35011 (p2027 p2589 p2608 p2819 p2829 p3097 p4110 p4405 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p4405) ∨ (¬ p2819) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial35011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory24267 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule35011 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2819) (meaning t m 2829) (meaning t m 3097) (meaning t m 4110) (meaning t m 4405) (meaning t m 5193) source

theorem rule35017 (p1991 p2027 p2589 p2655 p2850 p3096 p3584 p4206 p4393 : Prop) (h : (¬ p1991) ∨ (¬ p2655) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2850) ∨ p4206 ∨ (¬ p4393) ∨ (¬ p3096)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (p4206) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial35017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 4206) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory24273 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10)
  exact rule35017 (meaning t m 1991) (meaning t m 2027) (meaning t m 2589) (meaning t m 2655) (meaning t m 2850) (meaning t m 3096) (meaning t m 3584) (meaning t m 4206) (meaning t m 4393) source

theorem rule35020 (p2387 p2476 p2577 p4157 : Prop) (h : (¬ p2387) ∨ (¬ p4157) ∨ (¬ p2577) ∨ p2476) : (¬ p2387) ∨ (p2476) ∨ (¬ p2577) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial35020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2387)) ∨ (meaning t m 2476) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory24276 (m.theta 0 4) (m.theta 0 6) (m.theta 4 8) (m.theta 6 8)
  exact rule35020 (meaning t m 2387) (meaning t m 2476) (meaning t m 2577) (meaning t m 4157) source

theorem rule35027 (p2027 p3146 p3266 p3773 p4455 p4529 : Prop) (h : (¬ p3146) ∨ (¬ p4455) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p3773) ∨ (¬ p4529)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3773) ∨ (¬ p4455) ∨ (¬ p4529) := by
  classical
  tauto

theorem initial35027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4455)) ∨ (¬ (meaning t m 4529)) := by
  have source := ElevenTheory.theory24283 t (m.theta 0 8) (m.theta 0 9) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule35027 (meaning t m 2027) (meaning t m 3146) (meaning t m 3266) (meaning t m 3773) (meaning t m 4455) (meaning t m 4529) source

theorem rule35028 (p1997 p2027 p2406 p2476 p2499 p2573 p3498 : Prop) (h : (¬ p2499) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2406) ∨ p3498 ∨ (¬ p2476)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (p3498) := by
  classical
  tauto

theorem initial35028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 3498) := by
  have source := ElevenTheory.theory24284 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule35028 (meaning t m 1997) (meaning t m 2027) (meaning t m 2406) (meaning t m 2476) (meaning t m 2499) (meaning t m 2573) (meaning t m 3498) source

theorem rule35029 (p2027 p3146 p3189 p3848 p4132 p4550 p5107 : Prop) (h : (¬ p3146) ∨ (¬ p4132) ∨ p2027 ∨ (¬ p5107) ∨ (¬ p3189) ∨ (¬ p4550) ∨ (¬ p3848)) : (p2027) ∨ (¬ p3146) ∨ (¬ p3189) ∨ (¬ p3848) ∨ (¬ p4132) ∨ (¬ p4550) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial35029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory24285 t (m.theta 1 3) (m.theta 3 8) (m.theta 3 9) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35029 (meaning t m 2027) (meaning t m 3146) (meaning t m 3189) (meaning t m 3848) (meaning t m 4132) (meaning t m 4550) (meaning t m 5107) source

theorem rule35034 (p2027 p2668 p2727 p3923 p4245 p4972 : Prop) (h : (¬ p4972) ∨ (¬ p2727) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p4245)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2727) ∨ (¬ p3923) ∨ (¬ p4245) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial35034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory24290 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule35034 (meaning t m 2027) (meaning t m 2668) (meaning t m 2727) (meaning t m 3923) (meaning t m 4245) (meaning t m 4972) source

theorem rule35043 (p1976 p2027 p2417 p2914 p3365 p3572 p3947 : Prop) (h : p2914 ∨ (¬ p3947) ∨ (¬ p3572) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2417)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2417) ∨ (p2914) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial35043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory24299 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule35043 (meaning t m 1976) (meaning t m 2027) (meaning t m 2417) (meaning t m 2914) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) source

theorem rule35045 (p2027 p2589 p2922 p3347 p3569 p4110 p4558 : Prop) (h : p2027 ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p4558) ∨ (¬ p4110) ∨ (¬ p3569) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p3347) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial35045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory24301 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule35045 (meaning t m 2027) (meaning t m 2589) (meaning t m 2922) (meaning t m 3347) (meaning t m 3569) (meaning t m 4110) (meaning t m 4558) source

theorem rule35048 (p2027 p2132 p2192 p2274 p2743 p2963 p3324 p3361 p4418 p4501 p4737 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2192) ∨ (¬ p4501) ∨ (¬ p4418) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p4737) ∨ (¬ p2963) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p4418) ∨ (¬ p4501) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial35048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory24304 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule35048 (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2274) (meaning t m 2743) (meaning t m 2963) (meaning t m 3324) (meaning t m 3361) (meaning t m 4418) (meaning t m 4501) (meaning t m 4737) source

theorem rule35049 (p2027 p2132 p2192 p2274 p2743 p2963 p3361 p4037 p4418 p4620 p4737 : Prop) (h : (¬ p4418) ∨ (¬ p2192) ∨ (¬ p4737) ∨ (¬ p2743) ∨ (¬ p2274) ∨ (¬ p2132) ∨ (¬ p3361) ∨ (¬ p2963) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p4037)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4418) ∨ (¬ p4620) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial35049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory24305 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule35049 (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2274) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 4037) (meaning t m 4418) (meaning t m 4620) (meaning t m 4737) source

theorem rule35050 (p2027 p2138 p3063 p3093 p3692 p3694 p3979 p4736 p5122 : Prop) (h : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3694) ∨ (¬ p2138) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p3979) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3979) ∨ (¬ p4736) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial35050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory24306 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule35050 (meaning t m 2027) (meaning t m 2138) (meaning t m 3063) (meaning t m 3093) (meaning t m 3692) (meaning t m 3694) (meaning t m 3979) (meaning t m 4736) (meaning t m 5122) source

theorem rule35053 (p2518 p2922 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p2518) ∨ p2922) : (¬ p2518) ∨ (p2922) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial35053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2518)) ∨ (meaning t m 2922) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory24309 (m.theta 1 4) (m.theta 4 7) (m.theta 4 8)
  exact rule35053 (meaning t m 2518) (meaning t m 2922) (meaning t m 4186) source

theorem rule35054 (p1977 p2027 p2662 p2766 p3266 p3346 p4111 p4425 : Prop) (h : (¬ p1977) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p3266) ∨ p2766) : (¬ p1977) ∨ (p2027) ∨ (¬ p2662) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial35054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory24310 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35054 (meaning t m 1977) (meaning t m 2027) (meaning t m 2662) (meaning t m 2766) (meaning t m 3266) (meaning t m 3346) (meaning t m 4111) (meaning t m 4425) source

theorem rule35057 (p2027 p3680 p4107 p4192 p4381 p4559 : Prop) (h : p2027 ∨ (¬ p4192) ∨ (¬ p4559) ∨ (¬ p4381) ∨ (¬ p3680) ∨ (¬ p4107)) : (p2027) ∨ (¬ p3680) ∨ (¬ p4107) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial35057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory24313 t (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule35057 (meaning t m 2027) (meaning t m 3680) (meaning t m 4107) (meaning t m 4192) (meaning t m 4381) (meaning t m 4559) source

theorem rule35060 (p3177 p3858 p5074 : Prop) (h : (¬ p5074) ∨ (¬ p3177) ∨ p3858) : (¬ p3177) ∨ (p3858) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial35060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3177)) ∨ (meaning t m 3858) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory24316 (m.theta 0 8) (m.theta 1 8) (m.theta 3 8)
  exact rule35060 (meaning t m 3177) (meaning t m 3858) (meaning t m 5074) source

theorem rule35062 (p1977 p2027 p2766 p2957 p3266 p3551 p3657 p3662 p4381 p4984 : Prop) (h : (¬ p4984) ∨ p2766 ∨ (¬ p3657) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p1977) ∨ (¬ p3266) ∨ (¬ p2957) ∨ (¬ p4381) ∨ (¬ p3551)) : (¬ p1977) ∨ (p2027) ∨ (p2766) ∨ (¬ p2957) ∨ (¬ p3266) ∨ (¬ p3551) ∨ (¬ p3657) ∨ (¬ p3662) ∨ (¬ p4381) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial35062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory24318 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule35062 (meaning t m 1977) (meaning t m 2027) (meaning t m 2766) (meaning t m 2957) (meaning t m 3266) (meaning t m 3551) (meaning t m 3657) (meaning t m 3662) (meaning t m 4381) (meaning t m 4984) source

theorem rule35065 (p1976 p2027 p2938 p3055 p3367 p3583 p4244 : Prop) (h : (¬ p3055) ∨ (¬ p4244) ∨ (¬ p3367) ∨ p2027 ∨ p2938 ∨ (¬ p1976) ∨ (¬ p3583)) : (¬ p1976) ∨ (p2027) ∨ (p2938) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial35065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory24321 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule35065 (meaning t m 1976) (meaning t m 2027) (meaning t m 2938) (meaning t m 3055) (meaning t m 3367) (meaning t m 3583) (meaning t m 4244) source

theorem rule35068 (p1994 p2027 p2651 p2952 p2997 p3097 p3952 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p3952) ∨ (¬ p1994) ∨ (¬ p3097) ∨ (¬ p2952) ∨ (¬ p2651)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial35068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory24324 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule35068 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2952) (meaning t m 2997) (meaning t m 3097) (meaning t m 3952) source

theorem rule35071 (p2476 p3540 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p3540) ∨ p2476) : (p2476) ∨ (¬ p3540) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial35071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory24327 (m.theta 0 4) (m.theta 4 7) (m.theta 4 8)
  exact rule35071 (meaning t m 2476) (meaning t m 3540) (meaning t m 4186) source

theorem rule35072 (p2027 p2255 p2662 p3166 p3256 p3540 p3644 p4111 p4133 p4347 : Prop) (h : (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4347) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p3166) ∨ (¬ p4133) ∨ (¬ p4111) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4111) ∨ (¬ p4133) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial35072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory24328 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35072 (meaning t m 2027) (meaning t m 2255) (meaning t m 2662) (meaning t m 3166) (meaning t m 3256) (meaning t m 3540) (meaning t m 3644) (meaning t m 4111) (meaning t m 4133) (meaning t m 4347) source

theorem rule35077 (p2298 p2299 p3032 p3527 : Prop) (h : (¬ p2299) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p2298)) : (¬ p2298) ∨ (¬ p2299) ∨ (¬ p3032) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial35077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory24333 (m.theta 1 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35077 (meaning t m 2298) (meaning t m 2299) (meaning t m 3032) (meaning t m 3527) source

theorem rule35079 (p1992 p2027 p2143 p2633 p3246 p3570 p3583 p3821 p4984 : Prop) (h : p2027 ∨ (¬ p2143) ∨ p2633 ∨ (¬ p3583) ∨ (¬ p1992) ∨ (¬ p3570) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4984)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3821) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial35079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory24335 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35079 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 3583) (meaning t m 3821) (meaning t m 4984) source

theorem rule35085 (p2027 p2493 p3379 p3556 p3564 p3570 p4330 p4348 p4524 : Prop) (h : (¬ p3556) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p4524) ∨ (¬ p4330) ∨ (¬ p3379) ∨ (¬ p2493) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3564) ∨ (¬ p3570) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial35085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory24341 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule35085 (meaning t m 2027) (meaning t m 2493) (meaning t m 3379) (meaning t m 3556) (meaning t m 3564) (meaning t m 3570) (meaning t m 4330) (meaning t m 4348) (meaning t m 4524) source

theorem rule35088 (p1979 p2027 p2842 p2992 p3483 p4037 p4154 p4375 : Prop) (h : p2842 ∨ (¬ p4375) ∨ (¬ p4154) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p1979) ∨ (¬ p3483)) : (¬ p1979) ∨ (p2027) ∨ (p2842) ∨ (¬ p2992) ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial35088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory24344 t (m.theta 1 3) (m.theta 2 4) (m.theta 2 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 9)
  exact rule35088 (meaning t m 1979) (meaning t m 2027) (meaning t m 2842) (meaning t m 2992) (meaning t m 3483) (meaning t m 4037) (meaning t m 4154) (meaning t m 4375) source

theorem rule35089 (p1979 p2027 p2169 p2992 p2996 p3646 p3989 p4155 p4988 : Prop) (h : (¬ p4155) ∨ (¬ p1979) ∨ (¬ p2996) ∨ (¬ p2992) ∨ p2169 ∨ (¬ p3646) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p3989)) : (¬ p1979) ∨ (p2027) ∨ (p2169) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4155) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial35089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory24345 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8)
  exact rule35089 (meaning t m 1979) (meaning t m 2027) (meaning t m 2169) (meaning t m 2992) (meaning t m 2996) (meaning t m 3646) (meaning t m 3989) (meaning t m 4155) (meaning t m 4988) source

theorem rule35093 (p2027 p2274 p2313 p2534 p3073 p3379 p3989 p4198 p4524 p4596 p4688 : Prop) (h : (¬ p3379) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p4688) ∨ (¬ p3989) ∨ (¬ p3073) ∨ (¬ p4596) ∨ (¬ p4524) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p4198)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3379) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4524) ∨ (¬ p4596) ∨ (¬ p4688) := by
  classical
  tauto

theorem initial35093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4688)) := by
  have source := ElevenTheory.theory24349 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule35093 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2534) (meaning t m 3073) (meaning t m 3379) (meaning t m 3989) (meaning t m 4198) (meaning t m 4524) (meaning t m 4596) (meaning t m 4688) source

theorem rule35096 (p1985 p2027 p2177 p2210 p2699 p3309 p3570 p4338 : Prop) (h : p2699 ∨ (¬ p3309) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p2210) ∨ (¬ p3570) ∨ (¬ p4338) ∨ (¬ p2177)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3309) ∨ (¬ p3570) ∨ (¬ p4338) := by
  classical
  tauto

theorem initial35096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4338)) := by
  have source := ElevenTheory.theory24352 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35096 (meaning t m 1985) (meaning t m 2027) (meaning t m 2177) (meaning t m 2210) (meaning t m 2699) (meaning t m 3309) (meaning t m 3570) (meaning t m 4338) source

theorem rule35097 (p2005 p2027 p2274 p2588 p2766 p3989 p4138 p4348 : Prop) (h : (¬ p2588) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p4138) ∨ p2766 ∨ (¬ p2005) ∨ (¬ p3989)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (p2766) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial35097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory24353 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35097 (meaning t m 2005) (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2766) (meaning t m 3989) (meaning t m 4138) (meaning t m 4348) source

theorem rule35109 (p2027 p2476 p2493 p2553 p3347 p4432 p4501 : Prop) (h : (¬ p4501) ∨ (¬ p2476) ∨ (¬ p4432) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3347)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p3347) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial35109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory24365 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule35109 (meaning t m 2027) (meaning t m 2476) (meaning t m 2493) (meaning t m 2553) (meaning t m 3347) (meaning t m 4432) (meaning t m 4501) source

theorem rule35113 (p2027 p2177 p2255 p2295 p2331 p2662 p3540 p4111 p4278 p4666 : Prop) (h : p2027 ∨ (¬ p2295) ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p2255) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial35113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory24369 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35113 (meaning t m 2027) (meaning t m 2177) (meaning t m 2255) (meaning t m 2295) (meaning t m 2331) (meaning t m 2662) (meaning t m 3540) (meaning t m 4111) (meaning t m 4278) (meaning t m 4666) source

theorem rule35118 (p2027 p2255 p2331 p2662 p3309 p3346 p3791 p4111 p4319 p4425 p4826 : Prop) (h : (¬ p3346) ∨ (¬ p3791) ∨ (¬ p4826) ∨ (¬ p2662) ∨ (¬ p4425) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p3309) ∨ (¬ p4319) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3309) ∨ (¬ p3346) ∨ (¬ p3791) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial35118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory24374 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule35118 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2662) (meaning t m 3309) (meaning t m 3346) (meaning t m 3791) (meaning t m 4111) (meaning t m 4319) (meaning t m 4425) (meaning t m 4826) source

theorem rule35119 (p1994 p2027 p2202 p2563 p2727 p2957 p3646 p3662 : Prop) (h : (¬ p2957) ∨ p2202 ∨ (¬ p3662) ∨ (¬ p3646) ∨ (¬ p1994) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2563)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial35119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory24375 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule35119 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2727) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) source

theorem rule35121 (p3988 p4119 p4204 : Prop) (h : (¬ p4119) ∨ (¬ p4204) ∨ p3988) : (p3988) ∨ (¬ p4119) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial35121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3988) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory24377 (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule35121 (meaning t m 3988) (meaning t m 4119) (meaning t m 4204) source

theorem rule35123 (p1977 p2027 p2313 p2459 p2577 p2633 p2662 p3955 p4111 p4347 : Prop) (h : (¬ p2662) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p1977) ∨ p2633 ∨ (¬ p4111) ∨ (¬ p2577) ∨ (¬ p3955) ∨ (¬ p2459) ∨ (¬ p4347)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2459) ∨ (¬ p2577) ∨ (p2633) ∨ (¬ p2662) ∨ (¬ p3955) ∨ (¬ p4111) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial35123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory24379 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35123 (meaning t m 1977) (meaning t m 2027) (meaning t m 2313) (meaning t m 2459) (meaning t m 2577) (meaning t m 2633) (meaning t m 2662) (meaning t m 3955) (meaning t m 4111) (meaning t m 4347) source

theorem rule35126 (p2373 p4119 p4241 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p4241) ∨ (¬ p4119) ∨ (¬ p2373)) : (¬ p2373) ∨ (¬ p4119) ∨ (¬ p4241) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial35126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory24382 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule35126 (meaning t m 2373) (meaning t m 4119) (meaning t m 4241) (meaning t m 4320) source

theorem rule35128 (p1979 p2027 p2166 p2253 p2651 p2699 p4111 p4119 p4320 p4365 : Prop) (h : (¬ p1979) ∨ (¬ p4119) ∨ p2027 ∨ (¬ p4111) ∨ p2699 ∨ (¬ p2651) ∨ (¬ p4320) ∨ (¬ p2253) ∨ (¬ p4365) ∨ (¬ p2166)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (p2699) ∨ (¬ p4111) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial35128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory24384 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule35128 (meaning t m 1979) (meaning t m 2027) (meaning t m 2166) (meaning t m 2253) (meaning t m 2651) (meaning t m 2699) (meaning t m 4111) (meaning t m 4119) (meaning t m 4320) (meaning t m 4365) source

theorem rule35132 (p1979 p2027 p2764 p3051 p4032 p4320 p4322 : Prop) (h : (¬ p1979) ∨ p2764 ∨ p2027 ∨ (¬ p4320) ∨ (¬ p3051) ∨ (¬ p4322) ∨ (¬ p4032)) : (¬ p1979) ∨ (p2027) ∨ (p2764) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4320) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial35132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory24388 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule35132 (meaning t m 1979) (meaning t m 2027) (meaning t m 2764) (meaning t m 3051) (meaning t m 4032) (meaning t m 4320) (meaning t m 4322) source

theorem rule35142 (p2027 p2177 p2274 p3581 p3644 p3958 : Prop) (h : (¬ p2177) ∨ (¬ p3581) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3958) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial35142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory24398 t (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35142 (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 3581) (meaning t m 3644) (meaning t m 3958) source

theorem rule35143 (p2027 p2641 p3742 p3984 p4111 p4708 : Prop) (h : p2027 ∨ (¬ p2641) ∨ (¬ p4708) ∨ (¬ p4111) ∨ (¬ p3984) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2641) ∨ (¬ p3742) ∨ (¬ p3984) ∨ (¬ p4111) ∨ (¬ p4708) := by
  classical
  tauto

theorem initial35143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4708)) := by
  have source := ElevenTheory.theory24399 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7)
  exact rule35143 (meaning t m 2027) (meaning t m 2641) (meaning t m 3742) (meaning t m 3984) (meaning t m 4111) (meaning t m 4708) source

theorem rule35149 (p1977 p2027 p2563 p2938 p2957 p3646 p3662 p4235 : Prop) (h : (¬ p1977) ∨ (¬ p2957) ∨ (¬ p3662) ∨ p2027 ∨ p2938 ∨ (¬ p4235) ∨ (¬ p2563) ∨ (¬ p3646)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial35149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory24405 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule35149 (meaning t m 1977) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) (meaning t m 4235) source

theorem rule35150 (p2027 p2166 p2210 p2780 p3917 p3969 p4191 p4736 p5119 : Prop) (h : p2027 ∨ (¬ p2780) ∨ (¬ p3969) ∨ (¬ p2166) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p4191) ∨ (¬ p3917) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p3917) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4736) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial35150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory24406 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule35150 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2780) (meaning t m 3917) (meaning t m 3969) (meaning t m 4191) (meaning t m 4736) (meaning t m 5119) source

theorem rule35152 (p2027 p2318 p2510 p2528 p3097 p3857 p3961 p4718 : Prop) (h : (¬ p3097) ∨ (¬ p2318) ∨ (¬ p2528) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p3961) ∨ (¬ p4718) ∨ (¬ p2510)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3097) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial35152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory24408 t (m.theta 0 7) (m.theta 0 8) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule35152 (meaning t m 2027) (meaning t m 2318) (meaning t m 2510) (meaning t m 2528) (meaning t m 3097) (meaning t m 3857) (meaning t m 3961) (meaning t m 4718) source

theorem rule35153 (p2027 p2255 p2311 p2651 p2667 p3222 p3276 p3551 p4116 p4154 p5123 p5558 : Prop) (h : (¬ p5123) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p3222) ∨ (¬ p5558) ∨ (¬ p2311) ∨ (¬ p2667) ∨ (¬ p2651) ∨ (¬ p2255) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2311) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3551) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial35153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory24409 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule35153 (meaning t m 2027) (meaning t m 2255) (meaning t m 2311) (meaning t m 2651) (meaning t m 2667) (meaning t m 3222) (meaning t m 3276) (meaning t m 3551) (meaning t m 4116) (meaning t m 4154) (meaning t m 5123) (meaning t m 5558) source

theorem rule35154 (p2027 p2177 p2255 p2311 p2651 p2667 p3233 p3551 p3707 p4116 p4154 p4276 p4425 p4635 : Prop) (h : (¬ p4276) ∨ (¬ p2177) ∨ (¬ p4116) ∨ (¬ p4635) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p2667) ∨ (¬ p3233) ∨ (¬ p2311) ∨ (¬ p4154) ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p3707)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2311) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p3233) ∨ (¬ p3551) ∨ (¬ p3707) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4276) ∨ (¬ p4425) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial35154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory24410 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 1 9) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 9 10)
  exact rule35154 (meaning t m 2027) (meaning t m 2177) (meaning t m 2255) (meaning t m 2311) (meaning t m 2651) (meaning t m 2667) (meaning t m 3233) (meaning t m 3551) (meaning t m 3707) (meaning t m 4116) (meaning t m 4154) (meaning t m 4276) (meaning t m 4425) (meaning t m 4635) source

theorem rule35155 (p2027 p2589 p3389 p3569 p4320 p4702 : Prop) (h : (¬ p3569) ∨ (¬ p3389) ∨ (¬ p2589) ∨ (¬ p4320) ∨ (¬ p4702) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial35155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory24411 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule35155 (meaning t m 2027) (meaning t m 2589) (meaning t m 3389) (meaning t m 3569) (meaning t m 4320) (meaning t m 4702) source

theorem rule35158 (p2020 p2027 p2608 p2619 p2699 p2839 p3969 : Prop) (h : p2699 ∨ (¬ p2619) ∨ (¬ p2020) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p2608)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial35158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory24414 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10)
  exact rule35158 (meaning t m 2020) (meaning t m 2027) (meaning t m 2608) (meaning t m 2619) (meaning t m 2699) (meaning t m 2839) (meaning t m 3969) source

theorem rule35161 (p3125 p3984 p4037 p4203 : Prop) (h : (¬ p3125) ∨ (¬ p4037) ∨ (¬ p3984) ∨ (¬ p4203)) : (¬ p3125) ∨ (¬ p3984) ∨ (¬ p4037) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial35161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory24417 (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule35161 (meaning t m 3125) (meaning t m 3984) (meaning t m 4037) (meaning t m 4203) source

theorem rule35162 (p2003 p2027 p2177 p2311 p2997 p3434 p3659 p3821 : Prop) (h : (¬ p2003) ∨ (¬ p2177) ∨ (¬ p3821) ∨ (¬ p3659) ∨ p2027 ∨ p2997 ∨ (¬ p2311) ∨ (¬ p3434)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (p2997) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial35162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory24418 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35162 (meaning t m 2003) (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2997) (meaning t m 3434) (meaning t m 3659) (meaning t m 3821) source

theorem rule35176 (p1980 p2027 p2699 p2797 p3399 p3527 p3659 p4357 : Prop) (h : p2699 ∨ (¬ p1980) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p3399) ∨ (¬ p4357) ∨ (¬ p3527) ∨ (¬ p2797)) : (¬ p1980) ∨ (p2027) ∨ (p2699) ∨ (¬ p2797) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial35176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory24432 t (m.theta 0 1) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 7 8)
  exact rule35176 (meaning t m 1980) (meaning t m 2027) (meaning t m 2699) (meaning t m 2797) (meaning t m 3399) (meaning t m 3527) (meaning t m 3659) (meaning t m 4357) source

theorem rule35178 (p2027 p2313 p2651 p2667 p2745 p2811 p2972 p3680 p3948 p4116 p4154 p4260 p4831 : Prop) (h : (¬ p3680) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p2972) ∨ (¬ p4154) ∨ (¬ p3948) ∨ (¬ p2651) ∨ (¬ p4260) ∨ (¬ p2745) ∨ (¬ p2811) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p4116)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2811) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p3948) ∨ (¬ p4116) ∨ (¬ p4154) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial35178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory24434 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule35178 (meaning t m 2027) (meaning t m 2313) (meaning t m 2651) (meaning t m 2667) (meaning t m 2745) (meaning t m 2811) (meaning t m 2972) (meaning t m 3680) (meaning t m 3948) (meaning t m 4116) (meaning t m 4154) (meaning t m 4260) (meaning t m 4831) source

theorem rule35179 (p1977 p2027 p2299 p2633 p2996 p3791 p4155 p4372 : Prop) (h : (¬ p2299) ∨ p2633 ∨ (¬ p3791) ∨ (¬ p4155) ∨ (¬ p4372) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2996)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3791) ∨ (¬ p4155) ∨ (¬ p4372) := by
  classical
  tauto

theorem initial35179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4372)) := by
  have source := ElevenTheory.theory24435 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule35179 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2996) (meaning t m 3791) (meaning t m 4155) (meaning t m 4372) source

theorem rule35181 (p2027 p2274 p2312 p3527 p3546 p3659 p3689 p4889 : Prop) (h : (¬ p3546) ∨ (¬ p2312) ∨ (¬ p2274) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3689) ∨ p2027 ∨ (¬ p4889)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial35181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory24437 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 6) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35181 (meaning t m 2027) (meaning t m 2274) (meaning t m 2312) (meaning t m 3527) (meaning t m 3546) (meaning t m 3659) (meaning t m 3689) (meaning t m 4889) source

theorem rule35185 (p2027 p3027 p3497 p3662 p4333 p4901 : Prop) (h : (¬ p4901) ∨ (¬ p4333) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p3497)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4333) ∨ (¬ p4901) := by
  classical
  tauto

theorem initial35185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4901)) := by
  have source := ElevenTheory.theory24441 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 8)
  exact rule35185 (meaning t m 2027) (meaning t m 3027) (meaning t m 3497) (meaning t m 3662) (meaning t m 4333) (meaning t m 4901) source

theorem rule35187 (p2027 p2255 p2662 p2807 p3032 p3346 p3527 p3941 p4111 p4425 p5119 : Prop) (h : (¬ p2807) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p2662) ∨ (¬ p2255) ∨ (¬ p4111) ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3346) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial35187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory24443 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule35187 (meaning t m 2027) (meaning t m 2255) (meaning t m 2662) (meaning t m 2807) (meaning t m 3032) (meaning t m 3346) (meaning t m 3527) (meaning t m 3941) (meaning t m 4111) (meaning t m 4425) (meaning t m 5119) source

theorem rule35188 (p2027 p2819 p3644 p3822 p4170 p4276 p4403 : Prop) (h : (¬ p4170) ∨ (¬ p4276) ∨ (¬ p4403) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2819) ∨ (¬ p3644) ∨ (¬ p3822) ∨ (¬ p4170) ∨ (¬ p4276) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial35188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory24444 t (m.theta 0 8) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule35188 (meaning t m 2027) (meaning t m 2819) (meaning t m 3644) (meaning t m 3822) (meaning t m 4170) (meaning t m 4276) (meaning t m 4403) source

theorem rule35189 (p2027 p2255 p2331 p2662 p3063 p3346 p3979 p4111 p4319 p4425 p5119 : Prop) (h : (¬ p2331) ∨ (¬ p4319) ∨ (¬ p2662) ∨ (¬ p2255) ∨ (¬ p3979) ∨ (¬ p5119) ∨ (¬ p3063) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3346) ∨ (¬ p3979) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial35189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory24445 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule35189 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2662) (meaning t m 3063) (meaning t m 3346) (meaning t m 3979) (meaning t m 4111) (meaning t m 4319) (meaning t m 4425) (meaning t m 5119) source

theorem rule35190 (p2027 p2253 p2387 p2651 p3189 p3609 p4111 p4347 p4969 p5021 : Prop) (h : (¬ p4969) ∨ (¬ p3609) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p2253) ∨ (¬ p2387) ∨ (¬ p4347) ∨ (¬ p5021)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2387) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p3609) ∨ (¬ p4111) ∨ (¬ p4347) ∨ (¬ p4969) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial35190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4969)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory24446 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule35190 (meaning t m 2027) (meaning t m 2253) (meaning t m 2387) (meaning t m 2651) (meaning t m 3189) (meaning t m 3609) (meaning t m 4111) (meaning t m 4347) (meaning t m 4969) (meaning t m 5021) source

theorem rule35191 (p2027 p2255 p2331 p2363 p2476 p2662 p3063 p3693 p4111 p4319 p5118 p5568 : Prop) (h : (¬ p2476) ∨ (¬ p4319) ∨ (¬ p5568) ∨ (¬ p4111) ∨ (¬ p3693) ∨ (¬ p2662) ∨ (¬ p5118) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p2255) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3693) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial35191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory24447 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule35191 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2363) (meaning t m 2476) (meaning t m 2662) (meaning t m 3063) (meaning t m 3693) (meaning t m 4111) (meaning t m 4319) (meaning t m 5118) (meaning t m 5568) source

theorem rule35193 (p2027 p2191 p2255 p2946 p3156 p3368 : Prop) (h : (¬ p3368) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3368) := by
  classical
  tauto

theorem initial35193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3368)) := by
  have source := ElevenTheory.theory24449 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 8)
  exact rule35193 (meaning t m 2027) (meaning t m 2191) (meaning t m 2255) (meaning t m 2946) (meaning t m 3156) (meaning t m 3368) source

theorem rule35194 (p2027 p2449 p2995 p3569 p3952 p4278 p4558 : Prop) (h : (¬ p3569) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3952) ∨ (¬ p4558) ∨ (¬ p2995)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3569) ∨ (¬ p3952) ∨ (¬ p4278) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial35194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory24450 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule35194 (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3569) (meaning t m 3952) (meaning t m 4278) (meaning t m 4558) source

theorem rule35199 (p2027 p2441 p2449 p2870 p3699 p4278 p4885 : Prop) (h : (¬ p2449) ∨ (¬ p2441) ∨ (¬ p3699) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4885) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p2870) ∨ (¬ p3699) ∨ (¬ p4278) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial35199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory24455 t (m.theta 2 5) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule35199 (meaning t m 2027) (meaning t m 2441) (meaning t m 2449) (meaning t m 2870) (meaning t m 3699) (meaning t m 4278) (meaning t m 4885) source

theorem rule35204 (p3692 p4261 p4446 : Prop) (h : (¬ p4446) ∨ (¬ p4261) ∨ p3692) : (p3692) ∨ (¬ p4261) ∨ (¬ p4446) := by
  classical
  tauto

theorem initial35204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4446)) := by
  have source := ElevenTheory.theory24460 (m.theta 1 8) (m.theta 5 8) (m.theta 8 9)
  exact rule35204 (meaning t m 3692) (meaning t m 4261) (meaning t m 4446) source

theorem rule35208 (p2027 p2253 p2651 p2780 p3222 p3276 p3822 p4116 p4260 p4736 p4831 : Prop) (h : (¬ p4831) ∨ (¬ p2780) ∨ (¬ p4260) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2651) ∨ (¬ p3222) ∨ (¬ p2253) ∨ (¬ p4736) ∨ (¬ p4116) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4116) ∨ (¬ p4260) ∨ (¬ p4736) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial35208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory24464 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule35208 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2780) (meaning t m 3222) (meaning t m 3276) (meaning t m 3822) (meaning t m 4116) (meaning t m 4260) (meaning t m 4736) (meaning t m 4831) source

theorem rule35213 (p1994 p2027 p2299 p2313 p2633 p2667 p2727 p4154 : Prop) (h : (¬ p1994) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2727) ∨ (¬ p4154) ∨ p2633 ∨ (¬ p2667) ∨ (¬ p2299)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial35213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory24469 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35213 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2633) (meaning t m 2667) (meaning t m 2727) (meaning t m 4154) source

theorem rule35214 (p3027 p4067 p4245 p4319 : Prop) (h : (¬ p4319) ∨ (¬ p4245) ∨ (¬ p4067) ∨ (¬ p3027)) : (¬ p3027) ∨ (¬ p4067) ∨ (¬ p4245) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial35214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory24470 (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 7)
  exact rule35214 (meaning t m 3027) (meaning t m 4067) (meaning t m 4245) (meaning t m 4319) source

theorem rule35216 (p4845 p5264 p5460 : Prop) (h : (¬ p5264) ∨ (¬ p4845) ∨ p5460) : (¬ p4845) ∨ (¬ p5264) ∨ (p5460) := by
  classical
  tauto

theorem initial35216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4845)) ∨ (¬ (meaning t m 5264)) ∨ (meaning t m 5460) := by
  have source := ElevenTheory.theory24472 t (m.theta 2 3) (m.theta 2 6) (m.theta 2 9)
  exact rule35216 (meaning t m 4845) (meaning t m 5264) (meaning t m 5460) source

theorem rule35224 (p2027 p2331 p2657 p3584 p3984 p4750 : Prop) (h : (¬ p3584) ∨ (¬ p3984) ∨ (¬ p4750) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p3584) ∨ (¬ p3984) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial35224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory24480 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule35224 (meaning t m 2027) (meaning t m 2331) (meaning t m 2657) (meaning t m 3584) (meaning t m 3984) (meaning t m 4750) source

theorem rule35225 (p1987 p2027 p2579 p2662 p2764 p2810 p4137 p4191 : Prop) (h : (¬ p2579) ∨ p2764 ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2810) ∨ (¬ p2662) ∨ (¬ p1987) ∨ (¬ p4191)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial35225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory24481 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule35225 (meaning t m 1987) (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 2764) (meaning t m 2810) (meaning t m 4137) (meaning t m 4191) source

theorem rule35227 (p1997 p2027 p2298 p2299 p2542 p2633 p2727 p2996 : Prop) (h : (¬ p2298) ∨ p2633 ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p2299) ∨ (¬ p1997) ∨ (¬ p2542)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2298) ∨ (¬ p2299) ∨ (¬ p2542) ∨ (p2633) ∨ (¬ p2727) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial35227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory24483 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 6 7) (m.theta 7 8)
  exact rule35227 (meaning t m 1997) (meaning t m 2027) (meaning t m 2298) (meaning t m 2299) (meaning t m 2542) (meaning t m 2633) (meaning t m 2727) (meaning t m 2996) source

theorem rule35228 (p1994 p2027 p2299 p2633 p3422 p3574 p3876 p3921 : Prop) (h : (¬ p3876) ∨ (¬ p3921) ∨ (¬ p2299) ∨ (¬ p1994) ∨ (¬ p3574) ∨ p2027 ∨ p2633 ∨ (¬ p3422)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3876) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial35228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory24484 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35228 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3422) (meaning t m 3574) (meaning t m 3876) (meaning t m 3921) source

theorem rule35234 (p2005 p2027 p2573 p2633 p2656 p2727 p2996 p3553 : Prop) (h : (¬ p3553) ∨ p2027 ∨ p2633 ∨ (¬ p2573) ∨ (¬ p2005) ∨ (¬ p2996) ∨ (¬ p2656) ∨ (¬ p2727)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2573) ∨ (p2633) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial35234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory24490 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 7 8)
  exact rule35234 (meaning t m 2005) (meaning t m 2027) (meaning t m 2573) (meaning t m 2633) (meaning t m 2656) (meaning t m 2727) (meaning t m 2996) (meaning t m 3553) source

theorem rule35235 (p2027 p2641 p2657 p2807 p2996 p4975 : Prop) (h : (¬ p2996) ∨ (¬ p2657) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p4975) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial35235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory24491 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule35235 (meaning t m 2027) (meaning t m 2641) (meaning t m 2657) (meaning t m 2807) (meaning t m 2996) (meaning t m 4975) source

theorem rule35236 (p2027 p2641 p2657 p3166 p4360 p4975 : Prop) (h : (¬ p4975) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p4360) ∨ (¬ p2641) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial35236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory24492 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule35236 (meaning t m 2027) (meaning t m 2641) (meaning t m 2657) (meaning t m 3166) (meaning t m 4360) (meaning t m 4975) source

theorem rule35240 (p2027 p2191 p2641 p3156 p3368 p4566 : Prop) (h : (¬ p3156) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p3368) ∨ (¬ p4566) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2641) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p4566) := by
  classical
  tauto

theorem initial35240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4566)) := by
  have source := ElevenTheory.theory24496 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule35240 (meaning t m 2027) (meaning t m 2191) (meaning t m 2641) (meaning t m 3156) (meaning t m 3368) (meaning t m 4566) source

theorem rule35241 (p2027 p2331 p2685 p2810 p3414 p4975 : Prop) (h : (¬ p2810) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p2331) ∨ (¬ p4975) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial35241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory24497 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule35241 (meaning t m 2027) (meaning t m 2331) (meaning t m 2685) (meaning t m 2810) (meaning t m 3414) (meaning t m 4975) source

theorem rule35245 (p2027 p2230 p2373 p2748 p2996 p3365 p3367 p3553 p3759 p4734 p4902 : Prop) (h : (¬ p2996) ∨ (¬ p3553) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p2373) ∨ (¬ p3759) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p4902) ∨ (¬ p2748)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2748) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3553) ∨ (¬ p3759) ∨ (¬ p4734) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial35245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory24501 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule35245 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2748) (meaning t m 2996) (meaning t m 3365) (meaning t m 3367) (meaning t m 3553) (meaning t m 3759) (meaning t m 4734) (meaning t m 4902) source

theorem rule35246 (p3662 p3922 p4153 p4759 : Prop) (h : (¬ p4759) ∨ (¬ p3922) ∨ (¬ p3662) ∨ (¬ p4153)) : (¬ p3662) ∨ (¬ p3922) ∨ (¬ p4153) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial35246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory24502 (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6)
  exact rule35246 (meaning t m 3662) (meaning t m 3922) (meaning t m 4153) (meaning t m 4759) source

theorem rule35247 (p2027 p2579 p2641 p2659 p3984 p4111 : Prop) (h : (¬ p2659) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3984) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial35247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory24503 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule35247 (meaning t m 2027) (meaning t m 2579) (meaning t m 2641) (meaning t m 2659) (meaning t m 3984) (meaning t m 4111) source

theorem rule35250 (p2027 p2331 p3027 p3414 p4111 p4975 : Prop) (h : (¬ p2331) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p4111) ∨ (¬ p4975) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial35250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory24506 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule35250 (meaning t m 2027) (meaning t m 2331) (meaning t m 3027) (meaning t m 3414) (meaning t m 4111) (meaning t m 4975) source

theorem rule35256 (p2027 p3093 p3246 p3309 p3365 p3553 p3572 p4275 p4668 p4736 : Prop) (h : (¬ p4275) ∨ (¬ p3553) ∨ (¬ p3093) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3572) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p4668)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4275) ∨ (¬ p4668) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial35256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory24512 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule35256 (meaning t m 2027) (meaning t m 3093) (meaning t m 3246) (meaning t m 3309) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 4275) (meaning t m 4668) (meaning t m 4736) source

theorem rule35264 (p2727 p3848 p5176 : Prop) (h : (¬ p5176) ∨ (¬ p2727) ∨ (¬ p3848)) : (¬ p2727) ∨ (¬ p3848) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial35264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory24520 (m.theta 1 3) (m.theta 3 4) (m.theta 3 9)
  exact rule35264 (meaning t m 2727) (meaning t m 3848) (meaning t m 5176) source

theorem rule35266 (p2027 p2241 p2459 p2476 p2534 p2641 p2668 p4133 p5193 : Prop) (h : (¬ p2476) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p5193) ∨ (¬ p2534) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p4133)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4133) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial35266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory24522 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35266 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2641) (meaning t m 2668) (meaning t m 4133) (meaning t m 5193) source

theorem rule35267 (p1977 p2027 p2298 p2299 p2331 p2633 p3414 p4154 : Prop) (h : (¬ p2298) ∨ (¬ p4154) ∨ (¬ p2299) ∨ (¬ p1977) ∨ (¬ p2331) ∨ p2633 ∨ p2027 ∨ (¬ p3414)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2298) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (p2633) ∨ (¬ p3414) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial35267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory24523 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35267 (meaning t m 1977) (meaning t m 2027) (meaning t m 2298) (meaning t m 2299) (meaning t m 2331) (meaning t m 2633) (meaning t m 3414) (meaning t m 4154) source

theorem rule35270 (p2027 p2138 p2352 p2573 p3367 p3486 p3570 p3759 p4133 p4243 p4734 : Prop) (h : (¬ p3486) ∨ (¬ p3367) ∨ (¬ p4734) ∨ (¬ p4133) ∨ (¬ p3570) ∨ (¬ p3759) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p4243) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3759) ∨ (¬ p4133) ∨ (¬ p4243) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial35270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory24526 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule35270 (meaning t m 2027) (meaning t m 2138) (meaning t m 2352) (meaning t m 2573) (meaning t m 3367) (meaning t m 3486) (meaning t m 3570) (meaning t m 3759) (meaning t m 4133) (meaning t m 4243) (meaning t m 4734) source

theorem rule35272 (p2027 p2247 p2744 p3063 p3093 p3201 p3366 p3540 p3874 p3905 p4384 : Prop) (h : (¬ p3093) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2247) ∨ (¬ p3201) ∨ (¬ p3905) ∨ (¬ p3063) ∨ (¬ p3540) ∨ (¬ p4384) ∨ p2027 ∨ (¬ p3874)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial35272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory24528 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8)
  exact rule35272 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3063) (meaning t m 3093) (meaning t m 3201) (meaning t m 3366) (meaning t m 3540) (meaning t m 3874) (meaning t m 3905) (meaning t m 4384) source

theorem rule35274 (p2027 p3918 p4075 p4358 p4452 p4501 p4710 p5503 : Prop) (h : (¬ p3918) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p5503) ∨ (¬ p4501) ∨ (¬ p4452) ∨ (¬ p4075) ∨ (¬ p4710)) : (p2027) ∨ (¬ p3918) ∨ (¬ p4075) ∨ (¬ p4358) ∨ (¬ p4452) ∨ (¬ p4501) ∨ (¬ p4710) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial35274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory24530 t (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule35274 (meaning t m 2027) (meaning t m 3918) (meaning t m 4075) (meaning t m 4358) (meaning t m 4452) (meaning t m 4501) (meaning t m 4710) (meaning t m 5503) source

theorem rule35277 (p2027 p2241 p2295 p2641 p2881 p3540 p3644 p4559 p5193 : Prop) (h : (¬ p2881) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p3644) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p5193) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4559) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial35277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory24533 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule35277 (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2641) (meaning t m 2881) (meaning t m 3540) (meaning t m 3644) (meaning t m 4559) (meaning t m 5193) source

theorem rule35279 (p1994 p2027 p2299 p2633 p2651 p2963 p3549 p3922 : Prop) (h : (¬ p1994) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3549) ∨ p2633 ∨ (¬ p2651) ∨ (¬ p3922) ∨ (¬ p2299)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3922) := by
  classical
  tauto

theorem initial35279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) := by
  have source := ElevenTheory.theory24535 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule35279 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2651) (meaning t m 2963) (meaning t m 3549) (meaning t m 3922) source

theorem rule35280 (p2027 p2098 p2499 p3452 p3609 p3660 p3880 p4348 p4733 p4905 : Prop) (h : (¬ p2499) ∨ (¬ p3660) ∨ (¬ p4348) ∨ (¬ p3452) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p4905) ∨ (¬ p4733) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3660) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial35280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory24536 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule35280 (meaning t m 2027) (meaning t m 2098) (meaning t m 2499) (meaning t m 3452) (meaning t m 3609) (meaning t m 3660) (meaning t m 3880) (meaning t m 4348) (meaning t m 4733) (meaning t m 4905) source

theorem rule35282 (p2027 p2542 p2573 p3540 p3574 p4635 p4949 : Prop) (h : (¬ p2573) ∨ (¬ p4635) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4949) ∨ (¬ p3574) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p4635) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial35282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4635)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory24538 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 4 9)
  exact rule35282 (meaning t m 2027) (meaning t m 2542) (meaning t m 2573) (meaning t m 3540) (meaning t m 3574) (meaning t m 4635) (meaning t m 4949) source

theorem rule35292 (p2027 p2245 p2417 p2598 p3201 p3292 p3680 p3853 p3951 p4321 p4733 : Prop) (h : (¬ p2417) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p4733) ∨ (¬ p3201) ∨ (¬ p2245) ∨ (¬ p3292) ∨ (¬ p4321) ∨ (¬ p3853) ∨ (¬ p3951)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3292) ∨ (¬ p3680) ∨ (¬ p3853) ∨ (¬ p3951) ∨ (¬ p4321) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial35292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory24548 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 9) (m.theta 2 4) (m.theta 3 9) (m.theta 4 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule35292 (meaning t m 2027) (meaning t m 2245) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3292) (meaning t m 3680) (meaning t m 3853) (meaning t m 3951) (meaning t m 4321) (meaning t m 4733) source

theorem rule35294 (p2027 p2144 p2191 p2220 p3365 p4030 p4202 p4752 : Prop) (h : (¬ p2191) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4030) ∨ (¬ p2220) ∨ (¬ p4202) ∨ (¬ p2144) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial35294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory24550 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 8)
  exact rule35294 (meaning t m 2027) (meaning t m 2144) (meaning t m 2191) (meaning t m 2220) (meaning t m 3365) (meaning t m 4030) (meaning t m 4202) (meaning t m 4752) source

theorem rule35297 (p2027 p2247 p2744 p3055 p3063 p3093 p3366 p3644 p3876 p4133 : Prop) (h : (¬ p3366) ∨ (¬ p4133) ∨ (¬ p3644) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3063) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial35297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory24553 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule35297 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3055) (meaning t m 3063) (meaning t m 3093) (meaning t m 3366) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) source

theorem rule35299 (p2744 p3859 p5312 : Prop) (h : (¬ p3859) ∨ (¬ p2744) ∨ p5312) : (¬ p2744) ∨ (¬ p3859) ∨ (p5312) := by
  classical
  tauto

theorem initial35299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3859)) ∨ (meaning t m 5312) := by
  have source := ElevenTheory.theory24555 t (m.theta 1 2) (m.theta 1 3) (m.theta 1 8)
  exact rule35299 (meaning t m 2744) (meaning t m 3859) (meaning t m 5312) source

theorem rule35300 (p2027 p2247 p2579 p2744 p3073 p3366 p3449 p3905 p3956 p5118 p5580 : Prop) (h : (¬ p3073) ∨ (¬ p2579) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p5118) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p2247) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3905) ∨ (¬ p3956) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial35300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory24556 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule35300 (meaning t m 2027) (meaning t m 2247) (meaning t m 2579) (meaning t m 2744) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3905) (meaning t m 3956) (meaning t m 5118) (meaning t m 5580) source

end SunPrize.SMT
