import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory054
import SunPrize.Certificate.Theory055
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule30948 (p2027 p2191 p2241 p2717 p2750 p2753 p3516 p3555 p3819 p4324 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p2191) ∨ (¬ p2241) ∨ (¬ p3819) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p3516) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2241) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3516) ∨ (¬ p3555) ∨ (¬ p3819) ∨ (¬ p4324) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial30948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory20204 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule30948 (meaning t m 2027) (meaning t m 2191) (meaning t m 2241) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3516) (meaning t m 3555) (meaning t m 3819) (meaning t m 4324) (meaning t m 4905) source

theorem rule30950 (p2027 p3680 p4107 p4192 p4381 p4559 : Prop) (h : (¬ p4107) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p4381) ∨ (¬ p3680) ∨ (¬ p4192)) : (p2027) ∨ (¬ p3680) ∨ (¬ p4107) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial30950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory20206 t (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule30950 (meaning t m 2027) (meaning t m 3680) (meaning t m 4107) (meaning t m 4192) (meaning t m 4381) (meaning t m 4559) source

theorem rule30954 (p2027 p2249 p2641 p2952 p3323 p3461 p3486 p4282 p4831 p5660 : Prop) (h : (¬ p2249) ∨ (¬ p4831) ∨ (¬ p3486) ∨ (¬ p2952) ∨ (¬ p4282) ∨ (¬ p3323) ∨ (¬ p2641) ∨ (¬ p5660) ∨ p2027 ∨ (¬ p3461)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3486) ∨ (¬ p4282) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial30954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory20210 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule30954 (meaning t m 2027) (meaning t m 2249) (meaning t m 2641) (meaning t m 2952) (meaning t m 3323) (meaning t m 3461) (meaning t m 3486) (meaning t m 4282) (meaning t m 4831) (meaning t m 5660) source

theorem rule30955 (p2027 p3585 p3707 p4351 p4749 p5316 p5387 p5453 : Prop) (h : (¬ p5316) ∨ (¬ p5387) ∨ (¬ p3707) ∨ (¬ p4749) ∨ (¬ p4351) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p5453)) : (p2027) ∨ (¬ p3585) ∨ (¬ p3707) ∨ (¬ p4351) ∨ (¬ p4749) ∨ (¬ p5316) ∨ (¬ p5387) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial30955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5316)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory20211 t (m.theta 1 2) (m.theta 1 8) (m.theta 1 9) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 9 10)
  exact rule30955 (meaning t m 2027) (meaning t m 3585) (meaning t m 3707) (meaning t m 4351) (meaning t m 4749) (meaning t m 5316) (meaning t m 5387) (meaning t m 5453) source

theorem rule30956 (p2027 p2532 p3461 p3990 p4322 p4340 p4859 : Prop) (h : (¬ p4340) ∨ (¬ p4859) ∨ (¬ p4322) ∨ (¬ p3461) ∨ (¬ p2532) ∨ p2027 ∨ (¬ p3990)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4322) ∨ (¬ p4340) ∨ (¬ p4859) := by
  classical
  tauto

theorem initial30956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4859)) := by
  have source := ElevenTheory.theory20212 t (m.theta 2 8) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule30956 (meaning t m 2027) (meaning t m 2532) (meaning t m 3461) (meaning t m 3990) (meaning t m 4322) (meaning t m 4340) (meaning t m 4859) source

theorem rule30957 (p1997 p2027 p2850 p3170 p3286 p3982 p5160 p5175 p5590 : Prop) (h : (¬ p2850) ∨ p3982 ∨ (¬ p5590) ∨ (¬ p1997) ∨ (¬ p5175) ∨ (¬ p3170) ∨ (¬ p3286) ∨ (¬ p5160) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2850) ∨ (¬ p3170) ∨ (¬ p3286) ∨ (p3982) ∨ (¬ p5160) ∨ (¬ p5175) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial30957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3286)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5175)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory20213 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 8 10)
  exact rule30957 (meaning t m 1997) (meaning t m 2027) (meaning t m 2850) (meaning t m 3170) (meaning t m 3286) (meaning t m 3982) (meaning t m 5160) (meaning t m 5175) (meaning t m 5590) source

theorem rule30958 (p2027 p2145 p2284 p3276 p3355 p3362 p3646 p3951 p4208 p4381 : Prop) (h : (¬ p3646) ∨ (¬ p3276) ∨ (¬ p3362) ∨ (¬ p2145) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p4208) ∨ (¬ p4381) ∨ (¬ p3355) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2284) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial30958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory20214 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 3 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule30958 (meaning t m 2027) (meaning t m 2145) (meaning t m 2284) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3646) (meaning t m 3951) (meaning t m 4208) (meaning t m 4381) source

theorem rule30965 (p1992 p2027 p2132 p2633 p3425 p3583 p3659 : Prop) (h : (¬ p3583) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p1992) ∨ (¬ p2132) ∨ p2633 ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3583) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial30965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory20221 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8)
  exact rule30965 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2633) (meaning t m 3425) (meaning t m 3583) (meaning t m 3659) source

theorem rule30967 (p1999 p2027 p2202 p3276 p3333 p3684 p4191 : Prop) (h : (¬ p1999) ∨ (¬ p3684) ∨ p2202 ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p3333)) : (¬ p1999) ∨ (p2027) ∨ (p2202) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial30967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory20223 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule30967 (meaning t m 1999) (meaning t m 2027) (meaning t m 2202) (meaning t m 3276) (meaning t m 3333) (meaning t m 3684) (meaning t m 4191) source

theorem rule30968 (p1975 p2027 p2202 p2295 p3324 p3641 p3684 p4157 : Prop) (h : p2027 ∨ (¬ p1975) ∨ (¬ p3324) ∨ (¬ p2295) ∨ (¬ p3684) ∨ (¬ p4157) ∨ p2202 ∨ (¬ p3641)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial30968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory20224 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule30968 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2295) (meaning t m 3324) (meaning t m 3641) (meaning t m 3684) (meaning t m 4157) source

theorem rule30971 (p3555 p3860 p4492 : Prop) (h : (¬ p4492) ∨ (¬ p3555) ∨ p3860) : (¬ p3555) ∨ (p3860) ∨ (¬ p4492) := by
  classical
  tauto

theorem initial30971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3555)) ∨ (meaning t m 3860) ∨ (¬ (meaning t m 4492)) := by
  have source := ElevenTheory.theory20227 (m.theta 0 1) (m.theta 1 5) (m.theta 1 8)
  exact rule30971 (meaning t m 3555) (meaning t m 3860) (meaning t m 4492) source

theorem rule30975 (p2504 p3923 p3989 p4203 : Prop) (h : (¬ p3923) ∨ (¬ p2504) ∨ (¬ p4203) ∨ p3989) : (¬ p2504) ∨ (¬ p3923) ∨ (p3989) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial30975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3923)) ∨ (meaning t m 3989) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory20231 (m.theta 1 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule30975 (meaning t m 2504) (meaning t m 3923) (meaning t m 3989) (meaning t m 4203) source

theorem rule30980 (p1995 p2027 p2499 p2584 p2914 p3540 p4088 p5514 : Prop) (h : p2027 ∨ (¬ p2584) ∨ p2914 ∨ (¬ p4088) ∨ (¬ p1995) ∨ (¬ p3540) ∨ (¬ p2499) ∨ (¬ p5514)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (p2914) ∨ (¬ p3540) ∨ (¬ p4088) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial30980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2584)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4088)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory20236 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule30980 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2584) (meaning t m 2914) (meaning t m 3540) (meaning t m 4088) (meaning t m 5514) source

theorem rule30984 (p1977 p2027 p2633 p2996 p3246 p3570 p3947 : Prop) (h : p2633 ∨ (¬ p2996) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p3947) ∨ (¬ p3246)) : (¬ p1977) ∨ (p2027) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial30984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory20240 t (m.theta 1 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule30984 (meaning t m 1977) (meaning t m 2027) (meaning t m 2633) (meaning t m 2996) (meaning t m 3246) (meaning t m 3570) (meaning t m 3947) source

theorem rule30987 (p4244 p4385 p4402 : Prop) (h : (¬ p4244) ∨ (¬ p4402) ∨ p4385) : (¬ p4244) ∨ (p4385) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial30987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4244)) ∨ (meaning t m 4385) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory20243 (m.theta 2 5) (m.theta 5 7) (m.theta 5 9)
  exact rule30987 (meaning t m 4244) (meaning t m 4385) (meaning t m 4402) source

theorem rule30988 (p3556 p4032 p4402 : Prop) (h : (¬ p4402) ∨ (¬ p3556) ∨ p4032) : (¬ p3556) ∨ (p4032) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial30988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (meaning t m 4032) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory20244 (m.theta 0 5) (m.theta 5 7) (m.theta 5 9)
  exact rule30988 (meaning t m 3556) (meaning t m 4032) (meaning t m 4402) source

theorem rule30992 (p2027 p2138 p2247 p2744 p3366 p3399 p3631 p3692 p3694 p3950 : Prop) (h : (¬ p3692) ∨ (¬ p3950) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3399) ∨ (¬ p3366) ∨ (¬ p3631) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial30992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory20248 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule30992 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3631) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) source

theorem rule30993 (p2027 p2247 p2589 p2744 p3366 p3399 p3631 p3692 p3880 p3905 p3950 : Prop) (h : (¬ p3692) ∨ (¬ p3950) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3905) ∨ (¬ p3631) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3905) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial30993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory20249 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule30993 (meaning t m 2027) (meaning t m 2247) (meaning t m 2589) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3631) (meaning t m 3692) (meaning t m 3880) (meaning t m 3905) (meaning t m 3950) source

theorem rule30995 (p2027 p2707 p3055 p3238 p3609 p3880 p4030 p4348 p4734 p4805 p4905 : Prop) (h : p2027 ∨ (¬ p2707) ∨ (¬ p4734) ∨ (¬ p3238) ∨ (¬ p4805) ∨ (¬ p3609) ∨ (¬ p3055) ∨ (¬ p3880) ∨ (¬ p4905) ∨ (¬ p4030) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3609) ∨ (¬ p3880) ∨ (¬ p4030) ∨ (¬ p4348) ∨ (¬ p4734) ∨ (¬ p4805) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial30995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory20251 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule30995 (meaning t m 2027) (meaning t m 2707) (meaning t m 3055) (meaning t m 3238) (meaning t m 3609) (meaning t m 3880) (meaning t m 4030) (meaning t m 4348) (meaning t m 4734) (meaning t m 4805) (meaning t m 4905) source

theorem rule30999 (p2020 p2027 p2202 p2373 p3146 p3941 p4348 : Prop) (h : (¬ p2373) ∨ (¬ p2020) ∨ (¬ p3941) ∨ p2202 ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3146)) : (¬ p2020) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3941) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial30999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory20255 t (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule30999 (meaning t m 2020) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 3146) (meaning t m 3941) (meaning t m 4348) source

theorem rule31000 (p2027 p3276 p3956 p4191 p4422 p4603 : Prop) (h : (¬ p4422) ∨ (¬ p3956) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4603)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3956) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4603) := by
  classical
  tauto

theorem initial31000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 4603)) := by
  have source := ElevenTheory.theory20256 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule31000 (meaning t m 2027) (meaning t m 3276) (meaning t m 3956) (meaning t m 4191) (meaning t m 4422) (meaning t m 4603) source

theorem rule31005 (p2027 p2363 p3325 p3553 p3857 p4403 p4570 : Prop) (h : (¬ p4403) ∨ (¬ p3325) ∨ (¬ p4570) ∨ (¬ p3857) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3553) ∨ (¬ p3857) ∨ (¬ p4403) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial31005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory20261 t (m.theta 0 8) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31005 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3553) (meaning t m 3857) (meaning t m 4403) (meaning t m 4570) source

theorem rule31007 (p1977 p2027 p2274 p2440 p2588 p2590 p2765 p4111 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p1977) ∨ (¬ p2440) ∨ (¬ p4111) ∨ (¬ p2274) ∨ (¬ p2590) ∨ (¬ p2588)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2440) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (p2765) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial31007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory20263 t (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule31007 (meaning t m 1977) (meaning t m 2027) (meaning t m 2274) (meaning t m 2440) (meaning t m 2588) (meaning t m 2590) (meaning t m 2765) (meaning t m 4111) source

theorem rule31036 (p2022 p2027 p2766 p3551 p3979 p4347 p5558 : Prop) (h : (¬ p2022) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p5558) ∨ (¬ p3979) ∨ (¬ p4347) ∨ p2766) : (¬ p2022) ∨ (p2027) ∨ (p2766) ∨ (¬ p3551) ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial31036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20292 t (m.theta 0 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31036 (meaning t m 2022) (meaning t m 2027) (meaning t m 2766) (meaning t m 3551) (meaning t m 3979) (meaning t m 4347) (meaning t m 5558) source

theorem rule31039 (p2027 p2299 p2313 p2608 p2839 p3105 p4348 p4450 p5021 : Prop) (h : (¬ p2608) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3105) ∨ (¬ p2313) ∨ (¬ p2299) ∨ (¬ p5021) ∨ (¬ p2839) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial31039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory20295 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule31039 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 4348) (meaning t m 4450) (meaning t m 5021) source

theorem rule31040 (p1987 p2027 p2388 p2737 p3156 p3583 p3694 : Prop) (h : p2388 ∨ (¬ p1987) ∨ (¬ p3156) ∨ (¬ p3583) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p3694)) : (¬ p1987) ∨ (p2027) ∨ (p2388) ∨ (¬ p2737) ∨ (¬ p3156) ∨ (¬ p3583) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial31040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory20296 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule31040 (meaning t m 1987) (meaning t m 2027) (meaning t m 2388) (meaning t m 2737) (meaning t m 3156) (meaning t m 3583) (meaning t m 3694) source

theorem rule31043 (p2027 p2132 p3365 p4195 p4700 p4972 p5051 : Prop) (h : (¬ p4195) ∨ (¬ p4700) ∨ (¬ p4972) ∨ p2027 ∨ (¬ p5051) ∨ (¬ p3365) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4700) ∨ (¬ p4972) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial31043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4972)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory20299 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule31043 (meaning t m 2027) (meaning t m 2132) (meaning t m 3365) (meaning t m 4195) (meaning t m 4700) (meaning t m 4972) (meaning t m 5051) source

theorem rule31047 (p1992 p2027 p2143 p3128 p3461 p3583 p4032 p4322 : Prop) (h : p2027 ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p1992) ∨ p3128 ∨ (¬ p3461) ∨ (¬ p4032) ∨ (¬ p4322)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p3583) ∨ (¬ p4032) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial31047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory20303 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule31047 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 3128) (meaning t m 3461) (meaning t m 3583) (meaning t m 4032) (meaning t m 4322) source

theorem rule31048 (p2027 p2241 p2641 p3692 p4120 p4228 p4444 p4524 p5250 : Prop) (h : (¬ p2641) ∨ (¬ p5250) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p4228) ∨ (¬ p2241) ∨ (¬ p3692) ∨ (¬ p4444) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4228) ∨ (¬ p4444) ∨ (¬ p4524) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial31048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory20304 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 5 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule31048 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 3692) (meaning t m 4120) (meaning t m 4228) (meaning t m 4444) (meaning t m 4524) (meaning t m 5250) source

theorem rule31052 (p2027 p2191 p2248 p2651 p3016 p3555 p3564 p3692 p4330 : Prop) (h : (¬ p3016) ∨ (¬ p2651) ∨ (¬ p4330) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2191) ∨ (¬ p3564) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3555) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial31052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory20308 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule31052 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2651) (meaning t m 3016) (meaning t m 3555) (meaning t m 3564) (meaning t m 3692) (meaning t m 4330) source

theorem rule31053 (p1975 p2027 p2264 p2299 p2622 p2743 p2753 p3471 p4325 : Prop) (h : (¬ p1975) ∨ (¬ p2753) ∨ (¬ p4325) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2299) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p3471)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial31053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory20309 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule31053 (meaning t m 1975) (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 2622) (meaning t m 2743) (meaning t m 2753) (meaning t m 3471) (meaning t m 4325) source

theorem rule31055 (p2027 p2299 p2341 p2396 p3055 p3684 p3951 p4948 p5257 : Prop) (h : (¬ p5257) ∨ (¬ p3055) ∨ (¬ p2341) ∨ (¬ p4948) ∨ (¬ p2396) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3951) ∨ (¬ p4948) ∨ (¬ p5257) := by
  classical
  tauto

theorem initial31055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5257)) := by
  have source := ElevenTheory.theory20311 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31055 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2396) (meaning t m 3055) (meaning t m 3684) (meaning t m 3951) (meaning t m 4948) (meaning t m 5257) source

theorem rule31063 (p3917 p4137 p4342 : Prop) (h : (¬ p4137) ∨ (¬ p4342) ∨ p3917) : (p3917) ∨ (¬ p4137) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial31063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3917) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory20319 (m.theta 2 6) (m.theta 4 6) (m.theta 6 9)
  exact rule31063 (meaning t m 3917) (meaning t m 4137) (meaning t m 4342) source

theorem rule31065 (p2027 p3343 p3574 p3744 p4331 p4718 : Prop) (h : (¬ p3744) ∨ p2027 ∨ (¬ p4718) ∨ (¬ p4331) ∨ (¬ p3574) ∨ (¬ p3343)) : (p2027) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3744) ∨ (¬ p4331) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial31065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory20321 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9)
  exact rule31065 (meaning t m 2027) (meaning t m 3343) (meaning t m 3574) (meaning t m 3744) (meaning t m 4331) (meaning t m 4718) source

theorem rule31070 (p3658 p4277 p4895 : Prop) (h : (¬ p3658) ∨ (¬ p4277) ∨ p4895) : (¬ p3658) ∨ (¬ p4277) ∨ (p4895) := by
  classical
  tauto

theorem initial31070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4277)) ∨ (meaning t m 4895) := by
  have source := ElevenTheory.theory20326 t (m.theta 2 7) (m.theta 4 7) (m.theta 5 7)
  exact rule31070 (meaning t m 3658) (meaning t m 4277) (meaning t m 4895) source

theorem rule31071 (p1987 p2027 p2169 p2274 p2313 p2667 p3989 p4195 : Prop) (h : (¬ p4195) ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2667) ∨ p2169 ∨ (¬ p1987) ∨ (¬ p3989)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3989) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial31071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory20327 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31071 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2313) (meaning t m 2667) (meaning t m 3989) (meaning t m 4195) source

theorem rule31074 (p2006 p2027 p2156 p2462 p3556 p3758 p4107 p4275 : Prop) (h : p2027 ∨ p2462 ∨ (¬ p2156) ∨ (¬ p4107) ∨ (¬ p2006) ∨ (¬ p4275) ∨ (¬ p3758) ∨ (¬ p3556)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2156) ∨ (p2462) ∨ (¬ p3556) ∨ (¬ p3758) ∨ (¬ p4107) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial31074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory20330 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule31074 (meaning t m 2006) (meaning t m 2027) (meaning t m 2156) (meaning t m 2462) (meaning t m 3556) (meaning t m 3758) (meaning t m 4107) (meaning t m 4275) source

theorem rule31083 (p1983 p2027 p2114 p2137 p2839 p3212 p3680 p4381 : Prop) (h : p2114 ∨ (¬ p1983) ∨ (¬ p2839) ∨ (¬ p2137) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p3212) ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial31083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory20339 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31083 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2839) (meaning t m 3212) (meaning t m 3680) (meaning t m 4381) source

theorem rule31084 (p2027 p2137 p2307 p2962 p3097 p4385 p5043 : Prop) (h : p2027 ∨ (¬ p2962) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p2137) ∨ (¬ p5043) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4385) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial31084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory20340 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule31084 (meaning t m 2027) (meaning t m 2137) (meaning t m 2307) (meaning t m 2962) (meaning t m 3097) (meaning t m 4385) (meaning t m 5043) source

theorem rule31085 (p3412 p3486 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p3412) ∨ p3486) : (¬ p3412) ∨ (p3486) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial31085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3412)) ∨ (meaning t m 3486) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory20341 (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule31085 (meaning t m 3412) (meaning t m 3486) (meaning t m 4320) source

theorem rule31086 (p2476 p2510 p2579 : Prop) (h : (¬ p2476) ∨ (¬ p2510) ∨ p2579) : (¬ p2476) ∨ (¬ p2510) ∨ (p2579) := by
  classical
  tauto

theorem initial31086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2510)) ∨ (meaning t m 2579) := by
  have source := ElevenTheory.theory20342 (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule31086 (meaning t m 2476) (meaning t m 2510) (meaning t m 2579) source

theorem rule31090 (p2027 p2156 p2247 p2982 p2996 p3947 p4110 p4521 p4621 p5045 : Prop) (h : (¬ p2996) ∨ (¬ p4521) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4621) ∨ (¬ p2247) ∨ (¬ p3947) ∨ (¬ p4110) ∨ (¬ p2982) ∨ (¬ p5045)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2982) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4110) ∨ (¬ p4521) ∨ (¬ p4621) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial31090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory20346 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9)
  exact rule31090 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2982) (meaning t m 2996) (meaning t m 3947) (meaning t m 4110) (meaning t m 4521) (meaning t m 4621) (meaning t m 5045) source

theorem rule31091 (p3574 p3584 p3683 : Prop) (h : (¬ p3683) ∨ (¬ p3584) ∨ p3574) : (p3574) ∨ (¬ p3584) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial31091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3574) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory20347 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule31091 (meaning t m 3574) (meaning t m 3584) (meaning t m 3683) source

theorem rule31093 (p1997 p2027 p2156 p2355 p2951 p2992 p2996 p4110 : Prop) (h : p2355 ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p2951)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (p2355) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial31093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory20349 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6)
  exact rule31093 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2355) (meaning t m 2951) (meaning t m 2992) (meaning t m 2996) (meaning t m 4110) source

theorem rule31095 (p2027 p2156 p2247 p2274 p3791 p4360 p4521 p5560 p5600 : Prop) (h : (¬ p4521) ∨ (¬ p2156) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p5600) ∨ (¬ p2247) ∨ (¬ p4360) ∨ (¬ p5560) ∨ (¬ p3791)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p3791) ∨ (¬ p4360) ∨ (¬ p4521) ∨ (¬ p5560) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial31095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5560)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory20351 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 10)
  exact rule31095 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2274) (meaning t m 3791) (meaning t m 4360) (meaning t m 4521) (meaning t m 5560) (meaning t m 5600) source

theorem rule31098 (p1998 p2027 p2122 p2177 p2774 p2842 p3055 : Prop) (h : (¬ p3055) ∨ p2027 ∨ (¬ p1998) ∨ p2842 ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2774)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2774) ∨ (p2842) ∨ (¬ p3055) := by
  classical
  tauto

theorem initial31098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) := by
  have source := ElevenTheory.theory20354 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule31098 (meaning t m 1998) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2774) (meaning t m 2842) (meaning t m 3055) source

theorem rule31100 (p1994 p2027 p2630 p2952 p2997 p3097 p3361 p3952 : Prop) (h : (¬ p2952) ∨ (¬ p3361) ∨ (¬ p2630) ∨ p2997 ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3097) ∨ (¬ p3952)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3361) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial31100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory20356 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule31100 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2952) (meaning t m 2997) (meaning t m 3097) (meaning t m 3361) (meaning t m 3952) source

theorem rule31101 (p1988 p2027 p2437 p2545 p2761 p2928 p3222 p4451 : Prop) (h : (¬ p2761) ∨ (¬ p2437) ∨ p2545 ∨ p2027 ∨ (¬ p1988) ∨ (¬ p4451) ∨ (¬ p2928) ∨ (¬ p3222)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2761) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial31101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory20357 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31101 (meaning t m 1988) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2761) (meaning t m 2928) (meaning t m 3222) (meaning t m 4451) source

theorem rule31108 (p1975 p2027 p2504 p2553 p2766 p3941 p4348 p4371 p5693 : Prop) (h : (¬ p4371) ∨ p2027 ∨ (¬ p5693) ∨ (¬ p2553) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p2504) ∨ (¬ p1975) ∨ (¬ p3941)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2504) ∨ (¬ p2553) ∨ (p2766) ∨ (¬ p3941) ∨ (¬ p4348) ∨ (¬ p4371) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial31108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory20364 t (m.theta 1 6) (m.theta 1 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31108 (meaning t m 1975) (meaning t m 2027) (meaning t m 2504) (meaning t m 2553) (meaning t m 2766) (meaning t m 3941) (meaning t m 4348) (meaning t m 4371) (meaning t m 5693) source

theorem rule31109 (p2027 p2247 p2313 p2744 p2778 p3366 p3399 p3547 : Prop) (h : (¬ p3547) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2778) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3547) := by
  classical
  tauto

theorem initial31109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) := by
  have source := ElevenTheory.theory20365 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 6 7)
  exact rule31109 (meaning t m 2027) (meaning t m 2247) (meaning t m 2313) (meaning t m 2744) (meaning t m 2778) (meaning t m 3366) (meaning t m 3399) (meaning t m 3547) source

theorem rule31111 (p2027 p2210 p2630 p2696 p2753 p3343 p3591 p4026 p4877 p5322 : Prop) (h : (¬ p4026) ∨ (¬ p3591) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p2696) ∨ (¬ p3343) ∨ (¬ p5322) ∨ p2027 ∨ (¬ p2630)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4877) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial31111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory20367 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 6 9)
  exact rule31111 (meaning t m 2027) (meaning t m 2210) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 3343) (meaning t m 3591) (meaning t m 4026) (meaning t m 4877) (meaning t m 5322) source

theorem rule31115 (p2027 p2598 p2850 p2963 p3727 p4037 p4191 p4789 p5400 : Prop) (h : (¬ p5400) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p4037) ∨ (¬ p2963) ∨ (¬ p4789) ∨ (¬ p2598) ∨ (¬ p3727)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2963) ∨ (¬ p3727) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial31115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory20371 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 10) (m.theta 6 9) (m.theta 9 10)
  exact rule31115 (meaning t m 2027) (meaning t m 2598) (meaning t m 2850) (meaning t m 2963) (meaning t m 3727) (meaning t m 4037) (meaning t m 4191) (meaning t m 4789) (meaning t m 5400) source

theorem rule31116 (p1998 p2027 p2842 p2911 p2922 p3193 p3333 : Prop) (h : (¬ p2911) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2922) ∨ p2842 ∨ (¬ p3333) ∨ (¬ p3193)) : (¬ p1998) ∨ (p2027) ∨ (p2842) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p3333) := by
  classical
  tauto

theorem initial31116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3333)) := by
  have source := ElevenTheory.theory20372 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8)
  exact rule31116 (meaning t m 1998) (meaning t m 2027) (meaning t m 2842) (meaning t m 2911) (meaning t m 2922) (meaning t m 3193) (meaning t m 3333) source

theorem rule31121 (p2027 p2299 p2657 p2743 p3361 p3471 p3527 p3742 p4424 p4712 p4737 : Prop) (h : p2027 ∨ (¬ p3742) ∨ (¬ p2743) ∨ (¬ p4424) ∨ (¬ p3361) ∨ (¬ p2657) ∨ (¬ p4712) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p4737) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3742) ∨ (¬ p4424) ∨ (¬ p4712) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial31121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20377 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule31121 (meaning t m 2027) (meaning t m 2299) (meaning t m 2657) (meaning t m 2743) (meaning t m 3361) (meaning t m 3471) (meaning t m 3527) (meaning t m 3742) (meaning t m 4424) (meaning t m 4712) (meaning t m 4737) source

theorem rule31125 (p2027 p2440 p2657 p2807 p3579 p4646 : Prop) (h : p2027 ∨ (¬ p4646) ∨ (¬ p2440) ∨ (¬ p3579) ∨ (¬ p2657) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial31125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory20381 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule31125 (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2807) (meaning t m 3579) (meaning t m 4646) source

theorem rule31126 (p2027 p2497 p2498 p2573 p3343 p3346 p4811 : Prop) (h : (¬ p2498) ∨ p2027 ∨ (¬ p2497) ∨ (¬ p3343) ∨ (¬ p2573) ∨ (¬ p3346) ∨ (¬ p4811)) : (p2027) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial31126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory20382 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule31126 (meaning t m 2027) (meaning t m 2497) (meaning t m 2498) (meaning t m 2573) (meaning t m 3343) (meaning t m 3346) (meaning t m 4811) source

theorem rule31130 (p2005 p2027 p2169 p2588 p3872 p3989 p4129 p4260 : Prop) (h : p2027 ∨ (¬ p4129) ∨ (¬ p2005) ∨ (¬ p4260) ∨ (¬ p2588) ∨ (¬ p3989) ∨ (¬ p3872) ∨ p2169) : (¬ p2005) ∨ (p2027) ∨ (p2169) ∨ (¬ p2588) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4129) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial31130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory20386 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule31130 (meaning t m 2005) (meaning t m 2027) (meaning t m 2169) (meaning t m 2588) (meaning t m 3872) (meaning t m 3989) (meaning t m 4129) (meaning t m 4260) source

theorem rule31133 (p1976 p2027 p2462 p2761 p3365 p4035 p5284 : Prop) (h : p2462 ∨ (¬ p4035) ∨ (¬ p2761) ∨ (¬ p3365) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p5284)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3365) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial31133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory20389 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31133 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3365) (meaning t m 4035) (meaning t m 5284) source

theorem rule31137 (p1994 p2027 p2169 p2307 p2578 p2630 p3822 p3956 p4841 : Prop) (h : (¬ p2630) ∨ p2169 ∨ p2027 ∨ (¬ p2578) ∨ (¬ p1994) ∨ (¬ p3822) ∨ (¬ p3956) ∨ (¬ p4841) ∨ (¬ p2307)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p2630) ∨ (¬ p3822) ∨ (¬ p3956) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial31137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory20393 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31137 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2307) (meaning t m 2578) (meaning t m 2630) (meaning t m 3822) (meaning t m 3956) (meaning t m 4841) source

theorem rule31146 (p1990 p2027 p2166 p2307 p2873 p2962 p3097 p4120 : Prop) (h : p2873 ∨ (¬ p2962) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p1990) ∨ (¬ p4120) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2307) ∨ (p2873) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial31146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory20402 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule31146 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2307) (meaning t m 2873) (meaning t m 2962) (meaning t m 3097) (meaning t m 4120) source

theorem rule31147 (p2027 p2139 p2299 p2630 p2657 p2881 p3051 p3572 p4236 p4361 : Prop) (h : (¬ p2139) ∨ (¬ p2881) ∨ (¬ p2657) ∨ (¬ p3051) ∨ (¬ p3572) ∨ (¬ p2630) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p4361) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2299) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3572) ∨ (¬ p4236) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial31147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory20403 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule31147 (meaning t m 2027) (meaning t m 2139) (meaning t m 2299) (meaning t m 2630) (meaning t m 2657) (meaning t m 2881) (meaning t m 3051) (meaning t m 3572) (meaning t m 4236) (meaning t m 4361) source

theorem rule31148 (p2027 p2166 p2427 p3880 p4173 p4558 : Prop) (h : (¬ p2427) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3880) ∨ (¬ p4558) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4173) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial31148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory20404 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule31148 (meaning t m 2027) (meaning t m 2166) (meaning t m 2427) (meaning t m 3880) (meaning t m 4173) (meaning t m 4558) source

theorem rule31149 (p2027 p2532 p2982 p3880 p5118 p5568 : Prop) (h : (¬ p5118) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p2532) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial31149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory20405 t (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10) (m.theta 8 9)
  exact rule31149 (meaning t m 2027) (meaning t m 2532) (meaning t m 2982) (meaning t m 3880) (meaning t m 5118) (meaning t m 5568) source

theorem rule31150 (p2027 p2341 p3246 p3292 p3366 p3461 p3519 p3569 p3644 p4236 p4376 p4399 p4625 p4988 p5284 : Prop) (h : (¬ p3519) ∨ (¬ p4376) ∨ (¬ p3644) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p3366) ∨ (¬ p4988) ∨ (¬ p4399) ∨ (¬ p3246) ∨ (¬ p2341) ∨ (¬ p3569) ∨ (¬ p4236) ∨ (¬ p3461) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p3644) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4625) ∨ (¬ p4988) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial31150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4988)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory20406 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 3 9) (m.theta 4 7) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule31150 (meaning t m 2027) (meaning t m 2341) (meaning t m 3246) (meaning t m 3292) (meaning t m 3366) (meaning t m 3461) (meaning t m 3519) (meaning t m 3569) (meaning t m 3644) (meaning t m 4236) (meaning t m 4376) (meaning t m 4399) (meaning t m 4625) (meaning t m 4988) (meaning t m 5284) source

theorem rule31151 (p2027 p2717 p3309 p3923 p4138 p4477 : Prop) (h : (¬ p2717) ∨ (¬ p3309) ∨ (¬ p4477) ∨ (¬ p3923) ∨ (¬ p4138) ∨ p2027) : (p2027) ∨ (¬ p2717) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4138) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial31151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory20407 t (m.theta 1 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule31151 (meaning t m 2027) (meaning t m 2717) (meaning t m 3309) (meaning t m 3923) (meaning t m 4138) (meaning t m 4477) source

theorem rule31152 (p2027 p3343 p3574 p4331 p5249 p5514 : Prop) (h : (¬ p3343) ∨ p2027 ∨ (¬ p4331) ∨ (¬ p3574) ∨ (¬ p5249) ∨ (¬ p5514)) : (p2027) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4331) ∨ (¬ p5249) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial31152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 5249)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory20408 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 10) (m.theta 6 9)
  exact rule31152 (meaning t m 2027) (meaning t m 3343) (meaning t m 3574) (meaning t m 4331) (meaning t m 5249) (meaning t m 5514) source

theorem rule31153 (p2027 p3055 p3073 p3449 p3684 p3880 p4134 p4347 p4736 : Prop) (h : (¬ p3055) ∨ (¬ p3449) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p3073) ∨ (¬ p3684) ∨ (¬ p4736)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial31153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory20409 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31153 (meaning t m 2027) (meaning t m 3055) (meaning t m 3073) (meaning t m 3449) (meaning t m 3684) (meaning t m 3880) (meaning t m 4134) (meaning t m 4347) (meaning t m 4736) source

theorem rule31154 (p2027 p2542 p3051 p3742 p4001 p4539 : Prop) (h : (¬ p4539) ∨ p2027 ∨ (¬ p4001) ∨ (¬ p3051) ∨ (¬ p2542) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3051) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial31154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory20410 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule31154 (meaning t m 2027) (meaning t m 2542) (meaning t m 3051) (meaning t m 3742) (meaning t m 4001) (meaning t m 4539) source

theorem rule31157 (p2027 p2248 p2299 p2417 p2437 p2651 p3549 p3591 p4668 : Prop) (h : (¬ p3591) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p2437) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial31157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory20413 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31157 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3549) (meaning t m 3591) (meaning t m 4668) source

theorem rule31158 (p2010 p2027 p2098 p2437 p2622 p3365 p4256 p5373 : Prop) (h : (¬ p3365) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p5373) ∨ p2622 ∨ (¬ p2010) ∨ (¬ p2098) ∨ (¬ p2437)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2437) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p4256) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial31158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory20414 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule31158 (meaning t m 2010) (meaning t m 2027) (meaning t m 2098) (meaning t m 2437) (meaning t m 2622) (meaning t m 3365) (meaning t m 4256) (meaning t m 5373) source

theorem rule31160 (p2027 p2331 p3425 p3506 p3659 p4191 p4200 p4330 p4421 p4786 p5558 : Prop) (h : (¬ p4200) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4786) ∨ (¬ p4421) ∨ (¬ p5558) ∨ (¬ p3659) ∨ (¬ p3425) ∨ (¬ p2331) ∨ (¬ p4330) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3425) ∨ (¬ p3506) ∨ (¬ p3659) ∨ (¬ p4191) ∨ (¬ p4200) ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial31160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4200)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20416 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule31160 (meaning t m 2027) (meaning t m 2331) (meaning t m 3425) (meaning t m 3506) (meaning t m 3659) (meaning t m 4191) (meaning t m 4200) (meaning t m 4330) (meaning t m 4421) (meaning t m 4786) (meaning t m 5558) source

theorem rule31168 (p2027 p3055 p3093 p3319 p3461 p3876 p4736 p4831 p5503 : Prop) (h : (¬ p4736) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p5503) ∨ (¬ p3876) ∨ (¬ p4831)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4736) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial31168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory20424 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule31168 (meaning t m 2027) (meaning t m 3055) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 3876) (meaning t m 4736) (meaning t m 4831) (meaning t m 5503) source

theorem rule31170 (p2027 p2383 p3055 p3366 p3461 p3954 p3990 p4444 p4697 p5017 p5160 : Prop) (h : (¬ p2383) ∨ (¬ p5160) ∨ (¬ p5017) ∨ (¬ p3366) ∨ (¬ p3954) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4444) ∨ (¬ p3055) ∨ (¬ p4697) ∨ p2027) : (p2027) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3954) ∨ (¬ p3990) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p5017) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial31170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory20426 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule31170 (meaning t m 2027) (meaning t m 2383) (meaning t m 3055) (meaning t m 3366) (meaning t m 3461) (meaning t m 3954) (meaning t m 3990) (meaning t m 4444) (meaning t m 4697) (meaning t m 5017) (meaning t m 5160) source

theorem rule31171 (p2027 p2098 p2313 p3204 p3365 p4019 p4024 p4278 p4381 p4710 p4845 p5119 : Prop) (h : (¬ p4019) ∨ (¬ p3365) ∨ (¬ p2098) ∨ (¬ p4845) ∨ (¬ p5119) ∨ (¬ p4278) ∨ (¬ p4024) ∨ p2027 ∨ (¬ p3204) ∨ (¬ p4710) ∨ (¬ p2313) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2313) ∨ (¬ p3204) ∨ (¬ p3365) ∨ (¬ p4019) ∨ (¬ p4024) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4710) ∨ (¬ p4845) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 4845)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20427 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31171 (meaning t m 2027) (meaning t m 2098) (meaning t m 2313) (meaning t m 3204) (meaning t m 3365) (meaning t m 4019) (meaning t m 4024) (meaning t m 4278) (meaning t m 4381) (meaning t m 4710) (meaning t m 4845) (meaning t m 5119) source

theorem rule31172 (p2027 p2187 p2230 p2563 p3588 p3659 p3954 p4133 p5190 : Prop) (h : (¬ p3954) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p2563) ∨ (¬ p2230) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial31172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory20428 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule31172 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4133) (meaning t m 5190) source

theorem rule31174 (p1986 p2027 p2459 p2598 p2633 p3425 p3544 p3576 p4261 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p1986) ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p3576) ∨ (¬ p2459) ∨ (¬ p3544) ∨ (¬ p4261)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3544) ∨ (¬ p3576) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial31174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory20430 t (m.theta 0 2) (m.theta 1 7) (m.theta 1 8) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule31174 (meaning t m 1986) (meaning t m 2027) (meaning t m 2459) (meaning t m 2598) (meaning t m 2633) (meaning t m 3425) (meaning t m 3544) (meaning t m 3576) (meaning t m 4261) source

theorem rule31175 (p2027 p2132 p2742 p3038 p3527 p3551 p3820 p5052 : Prop) (h : (¬ p2132) ∨ (¬ p3038) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p2742)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2742) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial31175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory20431 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 2 5) (m.theta 7 8)
  exact rule31175 (meaning t m 2027) (meaning t m 2132) (meaning t m 2742) (meaning t m 3038) (meaning t m 3527) (meaning t m 3551) (meaning t m 3820) (meaning t m 5052) source

theorem rule31176 (p2891 p3694 p3747 p4418 : Prop) (h : (¬ p4418) ∨ (¬ p2891) ∨ (¬ p3694) ∨ (¬ p3747)) : (¬ p2891) ∨ (¬ p3694) ∨ (¬ p3747) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial31176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory20432 (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule31176 (meaning t m 2891) (meaning t m 3694) (meaning t m 3747) (meaning t m 4418) source

theorem rule31178 (p2027 p2132 p2651 p2811 p3276 p3343 p3366 p3588 p4423 p4831 p5052 : Prop) (h : (¬ p4423) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p3588) ∨ (¬ p2132) ∨ p3366 ∨ (¬ p3343) ∨ (¬ p4831) ∨ (¬ p2811) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2651) ∨ (¬ p2811) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (p3366) ∨ (¬ p3588) ∨ (¬ p4423) ∨ (¬ p4831) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial31178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (meaning t m 3366) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory20434 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 10) (m.theta 9 10)
  exact rule31178 (meaning t m 2027) (meaning t m 2132) (meaning t m 2651) (meaning t m 2811) (meaning t m 3276) (meaning t m 3343) (meaning t m 3366) (meaning t m 3588) (meaning t m 4423) (meaning t m 4831) (meaning t m 5052) source

theorem rule31182 (p2027 p2145 p2761 p3434 p3471 p3646 p3956 p4203 p5123 p5580 : Prop) (h : (¬ p5123) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p5580) ∨ (¬ p3434) ∨ (¬ p2145) ∨ (¬ p3956) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p2761)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3646) ∨ (¬ p3956) ∨ (¬ p4203) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial31182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory20438 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31182 (meaning t m 2027) (meaning t m 2145) (meaning t m 2761) (meaning t m 3434) (meaning t m 3471) (meaning t m 3646) (meaning t m 3956) (meaning t m 4203) (meaning t m 5123) (meaning t m 5580) source

theorem rule31183 (p1983 p2027 p2264 p2323 p2807 p3434 p3659 : Prop) (h : (¬ p3659) ∨ (¬ p2264) ∨ p2323 ∨ (¬ p2807) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2807) ∨ (¬ p3434) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial31183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory20439 t (m.theta 0 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31183 (meaning t m 1983) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2807) (meaning t m 3434) (meaning t m 3659) source

theorem rule31186 (p2137 p4539 p4885 : Prop) (h : (¬ p4885) ∨ (¬ p2137) ∨ p4539) : (¬ p2137) ∨ (p4539) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial31186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (meaning t m 4539) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory20442 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5)
  exact rule31186 (meaning t m 2137) (meaning t m 4539) (meaning t m 4885) source

theorem rule31187 (p1977 p2027 p2387 p2667 p2764 p4154 p4347 p4444 : Prop) (h : (¬ p4154) ∨ (¬ p1977) ∨ p2027 ∨ p2764 ∨ (¬ p4444) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p4347)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (p2764) ∨ (¬ p4154) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial31187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory20443 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule31187 (meaning t m 1977) (meaning t m 2027) (meaning t m 2387) (meaning t m 2667) (meaning t m 2764) (meaning t m 4154) (meaning t m 4347) (meaning t m 4444) source

theorem rule31188 (p2027 p2667 p2727 p2850 p2962 p4109 p4154 p4753 : Prop) (h : (¬ p4109) ∨ (¬ p4753) ∨ (¬ p2667) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p2962) ∨ (¬ p4109) ∨ (¬ p4154) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial31188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory20444 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule31188 (meaning t m 2027) (meaning t m 2667) (meaning t m 2727) (meaning t m 2850) (meaning t m 2962) (meaning t m 4109) (meaning t m 4154) (meaning t m 4753) source

theorem rule31190 (p2027 p2246 p2663 p2744 p3343 p3389 p3645 p3646 p3742 p3989 p4332 p4347 p4874 : Prop) (h : (¬ p4332) ∨ (¬ p2744) ∨ (¬ p3645) ∨ (¬ p4874) ∨ p2027 ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p3389) ∨ (¬ p3343) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3742) ∨ (¬ p3989) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial31190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory20446 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule31190 (meaning t m 2027) (meaning t m 2246) (meaning t m 2663) (meaning t m 2744) (meaning t m 3343) (meaning t m 3389) (meaning t m 3645) (meaning t m 3646) (meaning t m 3742) (meaning t m 3989) (meaning t m 4332) (meaning t m 4347) (meaning t m 4874) source

theorem rule31193 (p1994 p2027 p2608 p2699 p3201 p3367 p3742 : Prop) (h : (¬ p3367) ∨ p2699 ∨ (¬ p2608) ∨ (¬ p1994) ∨ (¬ p3201) ∨ (¬ p3742) ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial31193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory20449 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule31193 (meaning t m 1994) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 3201) (meaning t m 3367) (meaning t m 3742) source

theorem rule31194 (p1976 p2027 p2104 p2534 p2766 p4149 p5612 : Prop) (h : (¬ p5612) ∨ (¬ p1976) ∨ p2766 ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4149) ∨ (¬ p2104)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p4149) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial31194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory20450 t (m.theta 0 2) (m.theta 2 8) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31194 (meaning t m 1976) (meaning t m 2027) (meaning t m 2104) (meaning t m 2534) (meaning t m 2766) (meaning t m 4149) (meaning t m 5612) source

theorem rule31196 (p2027 p2247 p2744 p3055 p3366 p3399 p3527 p3876 p4278 p4666 : Prop) (h : (¬ p3876) ∨ (¬ p3527) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p4666) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial31196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory20452 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31196 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3055) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3876) (meaning t m 4278) (meaning t m 4666) source

theorem rule31197 (p2027 p2132 p2753 p2860 p3125 p3379 p3860 p4261 p4330 p5216 : Prop) (h : (¬ p3125) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p3860) ∨ (¬ p2132) ∨ (¬ p5216) ∨ (¬ p2860) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2753)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory20453 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule31197 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2860) (meaning t m 3125) (meaning t m 3379) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) (meaning t m 5216) source

theorem rule31204 (p2027 p2470 p3256 p3346 p4440 p5012 : Prop) (h : (¬ p5012) ∨ p2027 ∨ (¬ p3346) ∨ (¬ p2470) ∨ (¬ p3256) ∨ (¬ p4440)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3256) ∨ (¬ p3346) ∨ (¬ p4440) ∨ (¬ p5012) := by
  classical
  tauto

theorem initial31204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 5012)) := by
  have source := ElevenTheory.theory20460 t (m.theta 0 4) (m.theta 3 8) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule31204 (meaning t m 2027) (meaning t m 2470) (meaning t m 3256) (meaning t m 3346) (meaning t m 4440) (meaning t m 5012) source

theorem rule31207 (p2027 p2249 p2641 p2657 p2928 p3487 p3506 p4191 p4278 p4421 p4621 : Prop) (h : (¬ p3506) ∨ (¬ p2928) ∨ (¬ p2641) ∨ (¬ p3487) ∨ p2027 ∨ (¬ p4421) ∨ (¬ p2657) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4191) ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4421) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial31207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory20463 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 3 9) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule31207 (meaning t m 2027) (meaning t m 2249) (meaning t m 2641) (meaning t m 2657) (meaning t m 2928) (meaning t m 3487) (meaning t m 3506) (meaning t m 4191) (meaning t m 4278) (meaning t m 4421) (meaning t m 4621) source

theorem rule31213 (p2027 p2098 p2534 p3555 p3609 p3989 p4173 p4596 p4733 : Prop) (h : (¬ p4596) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p4733) ∨ (¬ p3989) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2534) ∨ (¬ p3555) ∨ (¬ p3609) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory20469 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule31213 (meaning t m 2027) (meaning t m 2098) (meaning t m 2534) (meaning t m 3555) (meaning t m 3609) (meaning t m 3989) (meaning t m 4173) (meaning t m 4596) (meaning t m 4733) source

theorem rule31217 (p2027 p2383 p3055 p3309 p3684 p3923 p4235 p4559 p4736 p5020 : Prop) (h : (¬ p4736) ∨ (¬ p3309) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3923) ∨ (¬ p4559) ∨ (¬ p2383) ∨ (¬ p5020) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p3923) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4736) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial31217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory20473 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule31217 (meaning t m 2027) (meaning t m 2383) (meaning t m 3055) (meaning t m 3309) (meaning t m 3684) (meaning t m 3923) (meaning t m 4235) (meaning t m 4559) (meaning t m 4736) (meaning t m 5020) source

theorem rule31218 (p2717 p3570 p4169 : Prop) (h : (¬ p2717) ∨ (¬ p3570) ∨ (¬ p4169)) : (¬ p2717) ∨ (¬ p3570) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial31218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory20474 (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule31218 (meaning t m 2717) (meaning t m 3570) (meaning t m 4169) source

theorem rule31225 (p2137 p3698 p4109 : Prop) (h : (¬ p3698) ∨ (¬ p2137) ∨ p4109) : (¬ p2137) ∨ (¬ p3698) ∨ (p4109) := by
  classical
  tauto

theorem initial31225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 3698)) ∨ (meaning t m 4109) := by
  have source := ElevenTheory.theory20481 (m.theta 0 5) (m.theta 2 5) (m.theta 4 5)
  exact rule31225 (meaning t m 2137) (meaning t m 3698) (meaning t m 4109) source

theorem rule31229 (p1994 p2027 p2476 p2766 p3389 p3742 p4348 p4383 : Prop) (h : (¬ p4383) ∨ (¬ p2476) ∨ p2766 ∨ (¬ p1994) ∨ (¬ p4348) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p3389)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2476) ∨ (p2766) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4348) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial31229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory20485 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31229 (meaning t m 1994) (meaning t m 2027) (meaning t m 2476) (meaning t m 2766) (meaning t m 3389) (meaning t m 3742) (meaning t m 4348) (meaning t m 4383) source

theorem rule31231 (p2005 p2027 p2307 p2588 p2764 p3946 p4191 : Prop) (h : p2764 ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2005) ∨ (¬ p3946) ∨ (¬ p4191)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (p2764) ∨ (¬ p3946) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial31231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory20487 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule31231 (meaning t m 2005) (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 2764) (meaning t m 3946) (meaning t m 4191) source

theorem rule31234 (p2509 p2922 p3875 : Prop) (h : (¬ p3875) ∨ (¬ p2922) ∨ (¬ p2509)) : (¬ p2509) ∨ (¬ p2922) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial31234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory20490 (m.theta 1 4) (m.theta 4 7) (m.theta 4 8)
  exact rule31234 (meaning t m 2509) (meaning t m 2922) (meaning t m 3875) source

theorem rule31235 (p2518 p2922 p3875 : Prop) (h : (¬ p3875) ∨ (¬ p2922) ∨ p2518) : (p2518) ∨ (¬ p2922) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial31235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2518) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory20491 (m.theta 1 4) (m.theta 4 7) (m.theta 4 8)
  exact rule31235 (meaning t m 2518) (meaning t m 2922) (meaning t m 3875) source

theorem rule31238 (p1992 p2027 p2104 p2696 p2743 p2766 p4118 p4963 : Prop) (h : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p1992) ∨ p2766 ∨ (¬ p2743) ∨ p2027 ∨ (¬ p4963) ∨ (¬ p4118)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p4118) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial31238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory20494 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule31238 (meaning t m 1992) (meaning t m 2027) (meaning t m 2104) (meaning t m 2696) (meaning t m 2743) (meaning t m 2766) (meaning t m 4118) (meaning t m 4963) source

theorem rule31243 (p2027 p2255 p2891 p2946 p3177 p3412 p3857 p4129 p4360 p4444 p4826 : Prop) (h : (¬ p2946) ∨ (¬ p3412) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p3857) ∨ (¬ p4444) ∨ (¬ p4129) ∨ (¬ p3177) ∨ (¬ p4360) ∨ (¬ p4826) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2891) ∨ (¬ p2946) ∨ (¬ p3177) ∨ (¬ p3412) ∨ (¬ p3857) ∨ (¬ p4129) ∨ (¬ p4360) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial31243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory20499 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule31243 (meaning t m 2027) (meaning t m 2255) (meaning t m 2891) (meaning t m 2946) (meaning t m 3177) (meaning t m 3412) (meaning t m 3857) (meaning t m 4129) (meaning t m 4360) (meaning t m 4444) (meaning t m 4826) source

theorem rule31245 (p1991 p2027 p2192 p2938 p2952 p3486 p3952 : Prop) (h : (¬ p1991) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p3486) ∨ p2938) : (¬ p1991) ∨ (p2027) ∨ (¬ p2192) ∨ (p2938) ∨ (¬ p2952) ∨ (¬ p3486) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial31245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory20501 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule31245 (meaning t m 1991) (meaning t m 2027) (meaning t m 2192) (meaning t m 2938) (meaning t m 2952) (meaning t m 3486) (meaning t m 3952) source

theorem rule31248 (p1988 p2027 p2114 p2137 p2341 p2459 p2839 p3266 p4988 : Prop) (h : p2114 ∨ (¬ p2839) ∨ (¬ p3266) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p1988) ∨ (¬ p2341) ∨ (¬ p2459)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2839) ∨ (¬ p3266) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial31248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory20504 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule31248 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2341) (meaning t m 2459) (meaning t m 2839) (meaning t m 3266) (meaning t m 4988) source

theorem rule31249 (p4149 p4181 p4370 : Prop) (h : (¬ p4370) ∨ (¬ p4181) ∨ p4149) : (p4149) ∨ (¬ p4181) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial31249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4149) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory20505 (m.theta 1 8) (m.theta 4 8) (m.theta 8 10)
  exact rule31249 (meaning t m 4149) (meaning t m 4181) (meaning t m 4370) source

theorem rule31254 (p4153 p4194 p4700 : Prop) (h : (¬ p4153) ∨ (¬ p4700) ∨ p4194) : (¬ p4153) ∨ (p4194) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial31254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4153)) ∨ (meaning t m 4194) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory20510 (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule31254 (meaning t m 4153) (meaning t m 4194) (meaning t m 4700) source

theorem rule31255 (p3686 p4752 p4782 : Prop) (h : (¬ p4752) ∨ (¬ p3686) ∨ p4782) : (¬ p3686) ∨ (¬ p4752) ∨ (p4782) := by
  classical
  tauto

theorem initial31255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4752)) ∨ (meaning t m 4782) := by
  have source := ElevenTheory.theory20511 t (m.theta 2 3) (m.theta 2 4) (m.theta 2 7)
  exact rule31255 (meaning t m 3686) (meaning t m 4752) (meaning t m 4782) source

theorem rule31258 (p1984 p2027 p2202 p2499 p3422 p3452 p3684 : Prop) (h : (¬ p3452) ∨ p2202 ∨ (¬ p3684) ∨ (¬ p2499) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3422)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2499) ∨ (¬ p3422) ∨ (¬ p3452) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial31258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory20514 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule31258 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2499) (meaning t m 3422) (meaning t m 3452) (meaning t m 3684) source

theorem rule31275 (p1977 p2027 p2241 p2765 p2901 p3952 p4366 p4909 : Prop) (h : (¬ p4909) ∨ (¬ p2901) ∨ (¬ p4366) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p3952) ∨ p2765) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial31275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory20531 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule31275 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2765) (meaning t m 2901) (meaning t m 3952) (meaning t m 4366) (meaning t m 4909) source

theorem rule31284 (p2027 p2417 p2598 p3201 p3369 p3646 p3950 p3989 p4347 p4733 : Prop) (h : (¬ p3369) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3950) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p2417) ∨ (¬ p3989) ∨ (¬ p3646) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory20540 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule31284 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3369) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) (meaning t m 4733) source

theorem rule31290 (p2027 p2247 p2744 p3366 p3425 p3659 p3707 p3830 p5123 p5558 : Prop) (h : (¬ p3707) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial31290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20546 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31290 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 3707) (meaning t m 3830) (meaning t m 5123) (meaning t m 5558) source

theorem rule31296 (p2406 p2499 p3573 p4355 : Prop) (h : (¬ p2406) ∨ (¬ p3573) ∨ (¬ p2499) ∨ (¬ p4355)) : (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3573) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial31296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory20552 (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule31296 (meaning t m 2406) (meaning t m 2499) (meaning t m 3573) (meaning t m 4355) source

theorem rule31300 (p2027 p2177 p2589 p2774 p3309 p3363 p3585 p3880 p3918 p4737 p4905 : Prop) (h : (¬ p3918) ∨ (¬ p3309) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p3880) ∨ (¬ p2589) ∨ (¬ p4905) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3880) ∨ (¬ p3918) ∨ (¬ p4737) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial31300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory20556 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule31300 (meaning t m 2027) (meaning t m 2177) (meaning t m 2589) (meaning t m 2774) (meaning t m 3309) (meaning t m 3363) (meaning t m 3585) (meaning t m 3880) (meaning t m 3918) (meaning t m 4737) (meaning t m 4905) source

theorem rule31302 (p2027 p2470 p2579 p3096 p3097 p4157 p4405 : Prop) (h : (¬ p3096) ∨ (¬ p3097) ∨ (¬ p4157) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p3097) ∨ (¬ p4157) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial31302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory20558 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31302 (meaning t m 2027) (meaning t m 2470) (meaning t m 2579) (meaning t m 3096) (meaning t m 3097) (meaning t m 4157) (meaning t m 4405) source

theorem rule31304 (p2027 p2210 p2246 p2651 p3016 p3564 p3860 p4261 p4330 p4959 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p4261) ∨ (¬ p3564) ∨ (¬ p3860) ∨ (¬ p4330) ∨ (¬ p3016) ∨ (¬ p2210) ∨ (¬ p2246) ∨ (¬ p4959)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) ∨ (¬ p4959) := by
  classical
  tauto

theorem initial31304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4959)) := by
  have source := ElevenTheory.theory20560 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 1 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule31304 (meaning t m 2027) (meaning t m 2210) (meaning t m 2246) (meaning t m 2651) (meaning t m 3016) (meaning t m 3564) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) (meaning t m 4959) source

theorem rule31307 (p1982 p2027 p2103 p2363 p2765 p3698 p3998 p4110 p4744 p5580 : Prop) (h : p2027 ∨ (¬ p2103) ∨ (¬ p4744) ∨ (¬ p5580) ∨ (¬ p1982) ∨ (¬ p3698) ∨ p2765 ∨ (¬ p2363) ∨ (¬ p4110) ∨ (¬ p3998)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2103) ∨ (¬ p2363) ∨ (p2765) ∨ (¬ p3698) ∨ (¬ p3998) ∨ (¬ p4110) ∨ (¬ p4744) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial31307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2103)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory20563 t (m.theta 0 8) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31307 (meaning t m 1982) (meaning t m 2027) (meaning t m 2103) (meaning t m 2363) (meaning t m 2765) (meaning t m 3698) (meaning t m 3998) (meaning t m 4110) (meaning t m 4744) (meaning t m 5580) source

theorem rule31308 (p2027 p2957 p3073 p3156 p3949 p4032 p4498 : Prop) (h : (¬ p3949) ∨ (¬ p2957) ∨ (¬ p3156) ∨ (¬ p4032) ∨ (¬ p4498) ∨ p2027 ∨ (¬ p3073)) : (p2027) ∨ (¬ p2957) ∨ (¬ p3073) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p4032) ∨ (¬ p4498) := by
  classical
  tauto

theorem initial31308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4498)) := by
  have source := ElevenTheory.theory20564 t (m.theta 0 5) (m.theta 1 8) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule31308 (meaning t m 2027) (meaning t m 2957) (meaning t m 3073) (meaning t m 3156) (meaning t m 3949) (meaning t m 4032) (meaning t m 4498) source

theorem rule31310 (p2027 p2136 p2598 p2870 p3556 p4313 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p4313) ∨ (¬ p2136) ∨ (¬ p2598) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p2870)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2598) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4313) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial31310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory20566 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule31310 (meaning t m 2027) (meaning t m 2136) (meaning t m 2598) (meaning t m 2870) (meaning t m 3556) (meaning t m 4313) (meaning t m 4752) source

theorem rule31311 (p2027 p2241 p2313 p2459 p2992 p3156 p3955 p4347 p4902 p5021 : Prop) (h : (¬ p2241) ∨ (¬ p2459) ∨ (¬ p3156) ∨ (¬ p2992) ∨ (¬ p5021) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3955) ∨ (¬ p4902) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p2459) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial31311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory20567 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31311 (meaning t m 2027) (meaning t m 2241) (meaning t m 2313) (meaning t m 2459) (meaning t m 2992) (meaning t m 3156) (meaning t m 3955) (meaning t m 4347) (meaning t m 4902) (meaning t m 5021) source

theorem rule31312 (p1986 p2027 p2766 p3367 p3588 p3644 p4106 p4348 : Prop) (h : p2027 ∨ (¬ p1986) ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p3588) ∨ p2766 ∨ (¬ p3367) ∨ (¬ p4106)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3644) ∨ (¬ p4106) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial31312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory20568 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule31312 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 3367) (meaning t m 3588) (meaning t m 3644) (meaning t m 4106) (meaning t m 4348) source

theorem rule31313 (p2027 p2166 p2210 p2437 p3146 p3359 p3540 p4697 p5193 : Prop) (h : (¬ p3540) ∨ (¬ p2210) ∨ (¬ p5193) ∨ (¬ p3359) ∨ (¬ p2166) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p4697) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2437) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p3540) ∨ (¬ p4697) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial31313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory20569 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule31313 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2437) (meaning t m 3146) (meaning t m 3359) (meaning t m 3540) (meaning t m 4697) (meaning t m 5193) source

theorem rule31316 (p2027 p2383 p2417 p3567 p3921 p3947 p4067 p4405 : Prop) (h : (¬ p3567) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2417) ∨ (¬ p2383) ∨ (¬ p4067) ∨ (¬ p3947) ∨ (¬ p3921)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2417) ∨ (¬ p3567) ∨ (¬ p3921) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial31316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory20572 t (m.theta 0 6) (m.theta 3 6) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule31316 (meaning t m 2027) (meaning t m 2383) (meaning t m 2417) (meaning t m 3567) (meaning t m 3921) (meaning t m 3947) (meaning t m 4067) (meaning t m 4405) source

theorem rule31318 (p1998 p2027 p2622 p2743 p2881 p3631 p3687 p3690 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p2881) ∨ (¬ p1998) ∨ (¬ p3687) ∨ (¬ p2743) ∨ (¬ p3690) ∨ (¬ p3631)) : (¬ p1998) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2881) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial31318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory20574 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31318 (meaning t m 1998) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 2881) (meaning t m 3631) (meaning t m 3687) (meaning t m 3690) source

theorem rule31322 (p1975 p2027 p2295 p2766 p3093 p3542 p3860 p3922 p4348 : Prop) (h : p2766 ∨ (¬ p1975) ∨ (¬ p2295) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3542) ∨ (¬ p4348) ∨ (¬ p3922) ∨ (¬ p3860)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2766) ∨ (¬ p3093) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p3922) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial31322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory20578 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule31322 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2766) (meaning t m 3093) (meaning t m 3542) (meaning t m 3860) (meaning t m 3922) (meaning t m 4348) source

theorem rule31323 (p1994 p2027 p2230 p2387 p2440 p2577 p2766 p4347 : Prop) (h : (¬ p2577) ∨ (¬ p2387) ∨ p2766 ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2440) ∨ (¬ p2577) ∨ (p2766) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial31323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory20579 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 6 8) (m.theta 8 9)
  exact rule31323 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2387) (meaning t m 2440) (meaning t m 2577) (meaning t m 2766) (meaning t m 4347) source

theorem rule31325 (p1985 p2027 p2114 p2449 p2737 p2807 p2811 p3690 : Prop) (h : (¬ p2737) ∨ p2114 ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p2811) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial31325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory20581 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule31325 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2449) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3690) source

theorem rule31327 (p2027 p2573 p2748 p3365 p3367 p3564 p3759 p4118 p4330 p4360 p4734 : Prop) (h : (¬ p2573) ∨ (¬ p4360) ∨ (¬ p4330) ∨ (¬ p4734) ∨ (¬ p3564) ∨ (¬ p3365) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3759) ∨ (¬ p4118) ∨ (¬ p2748)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3759) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial31327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory20583 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule31327 (meaning t m 2027) (meaning t m 2573) (meaning t m 2748) (meaning t m 3365) (meaning t m 3367) (meaning t m 3564) (meaning t m 3759) (meaning t m 4118) (meaning t m 4330) (meaning t m 4360) (meaning t m 4734) source

theorem rule31328 (p1984 p2027 p2247 p2264 p2462 p3031 p3548 p3947 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2264) ∨ (¬ p3031) ∨ (¬ p3548) ∨ p2462 ∨ (¬ p3947)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2264) ∨ (p2462) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial31328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory20584 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31328 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2264) (meaning t m 2462) (meaning t m 3031) (meaning t m 3548) (meaning t m 3947) source

theorem rule31336 (p2027 p3256 p3266 p3657 p4041 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p4041) ∨ (¬ p3266) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p3657)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4041) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial31336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory20592 t (m.theta 3 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule31336 (meaning t m 2027) (meaning t m 3256) (meaning t m 3266) (meaning t m 3657) (meaning t m 4041) (meaning t m 4381) source

theorem rule31337 (p2027 p3105 p3582 p3584 p4715 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p3582) ∨ (¬ p3105) ∨ (¬ p3584)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p4715) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial31337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory20593 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule31337 (meaning t m 2027) (meaning t m 3105) (meaning t m 3582) (meaning t m 3584) (meaning t m 4715) (meaning t m 4948) source

theorem rule31344 (p2027 p2685 p2881 p3877 p4280 p4548 : Prop) (h : (¬ p4548) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p4280) ∨ (¬ p2685) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2881) ∨ (¬ p3877) ∨ (¬ p4280) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial31344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory20600 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule31344 (meaning t m 2027) (meaning t m 2685) (meaning t m 2881) (meaning t m 3877) (meaning t m 4280) (meaning t m 4548) source

theorem rule31345 (p2027 p2685 p3246 p3657 p3877 p4280 p4548 : Prop) (h : (¬ p4548) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p3246) ∨ (¬ p4280) ∨ (¬ p3657)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3246) ∨ (¬ p3657) ∨ (¬ p3877) ∨ (¬ p4280) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial31345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory20601 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31345 (meaning t m 2027) (meaning t m 2685) (meaning t m 3246) (meaning t m 3657) (meaning t m 3877) (meaning t m 4280) (meaning t m 4548) source

theorem rule31346 (p2027 p2331 p2753 p2819 p3347 p3540 p3979 p4117 p4278 p4337 p4381 p5119 p5216 : Prop) (h : p2027 ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p4381) ∨ (¬ p2819) ∨ (¬ p4337) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p3979) ∨ (¬ p5119) ∨ (¬ p4278) ∨ (¬ p5216) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2753) ∨ (¬ p2819) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3979) ∨ (¬ p4117) ∨ (¬ p4278) ∨ (¬ p4337) ∨ (¬ p4381) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial31346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory20602 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31346 (meaning t m 2027) (meaning t m 2331) (meaning t m 2753) (meaning t m 2819) (meaning t m 3347) (meaning t m 3540) (meaning t m 3979) (meaning t m 4117) (meaning t m 4278) (meaning t m 4337) (meaning t m 4381) (meaning t m 5119) (meaning t m 5216) source

theorem rule31349 (p2098 p2696 p4373 : Prop) (h : (¬ p4373) ∨ (¬ p2696) ∨ p2098) : (p2098) ∨ (¬ p2696) ∨ (¬ p4373) := by
  classical
  tauto

theorem initial31349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2098) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4373)) := by
  have source := ElevenTheory.theory20605 (m.theta 0 2) (m.theta 2 3) (m.theta 2 8)
  exact rule31349 (meaning t m 2098) (meaning t m 2696) (meaning t m 4373) source

theorem rule31357 (p2027 p2143 p2528 p2598 p3556 p3583 p3641 p3690 p4669 p4737 : Prop) (h : (¬ p3556) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2143) ∨ (¬ p3583) ∨ (¬ p4669) ∨ (¬ p3641) ∨ (¬ p3690) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3641) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial31357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20613 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule31357 (meaning t m 2027) (meaning t m 2143) (meaning t m 2528) (meaning t m 2598) (meaning t m 3556) (meaning t m 3583) (meaning t m 3641) (meaning t m 3690) (meaning t m 4669) (meaning t m 4737) source

theorem rule31358 (p2027 p2143 p2417 p2598 p2922 p3583 p3590 p3692 p3950 p4120 p4737 : Prop) (h : (¬ p3692) ∨ (¬ p4120) ∨ (¬ p3583) ∨ (¬ p2143) ∨ (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3950) ∨ (¬ p3590) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3583) ∨ (¬ p3590) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4120) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial31358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20614 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule31358 (meaning t m 2027) (meaning t m 2143) (meaning t m 2417) (meaning t m 2598) (meaning t m 2922) (meaning t m 3583) (meaning t m 3590) (meaning t m 3692) (meaning t m 3950) (meaning t m 4120) (meaning t m 4737) source

theorem rule31359 (p2027 p2352 p2387 p2753 p3204 p3286 p3670 p4117 p4137 p4322 p4397 p4870 p5454 : Prop) (h : (¬ p4397) ∨ (¬ p4137) ∨ (¬ p2753) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p3286) ∨ (¬ p4870) ∨ (¬ p5454) ∨ (¬ p2387) ∨ (¬ p3204) ∨ (¬ p4117) ∨ (¬ p3670)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2753) ∨ (¬ p3204) ∨ (¬ p3286) ∨ (¬ p3670) ∨ (¬ p4117) ∨ (¬ p4137) ∨ (¬ p4322) ∨ (¬ p4397) ∨ (¬ p4870) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial31359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory20615 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 9) (m.theta 3 9) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule31359 (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2753) (meaning t m 3204) (meaning t m 3286) (meaning t m 3670) (meaning t m 4117) (meaning t m 4137) (meaning t m 4322) (meaning t m 4397) (meaning t m 4870) (meaning t m 5454) source

theorem rule31360 (p2027 p2136 p2341 p2860 p3366 p3452 p3545 p3644 p3646 p4244 p4277 p4376 : Prop) (h : (¬ p3366) ∨ (¬ p2860) ∨ (¬ p2136) ∨ (¬ p3646) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4277) ∨ (¬ p4244) ∨ (¬ p2341) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3545)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2341) ∨ (¬ p2860) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3545) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial31360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory20616 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule31360 (meaning t m 2027) (meaning t m 2136) (meaning t m 2341) (meaning t m 2860) (meaning t m 3366) (meaning t m 3452) (meaning t m 3545) (meaning t m 3644) (meaning t m 3646) (meaning t m 4244) (meaning t m 4277) (meaning t m 4376) source

theorem rule31365 (p1997 p2542 p2997 p3568 p4972 : Prop) (h : (¬ p2542) ∨ (¬ p1997) ∨ p2997 ∨ (¬ p3568) ∨ p4972) : (¬ p1997) ∨ (¬ p2542) ∨ (p2997) ∨ (¬ p3568) ∨ (p4972) := by
  classical
  tauto

theorem initial31365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (meaning t m 4972) := by
  have source := ElevenTheory.theory20621 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 6 7)
  exact rule31365 (meaning t m 1997) (meaning t m 2542) (meaning t m 2997) (meaning t m 3568) (meaning t m 4972) source

theorem rule31368 (p2027 p2104 p2363 p2911 p2922 p3379 p4340 p4503 p4736 : Prop) (h : (¬ p3379) ∨ (¬ p2363) ∨ (¬ p4736) ∨ (¬ p4503) ∨ (¬ p4340) ∨ (¬ p2104) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial31368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory20624 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31368 (meaning t m 2027) (meaning t m 2104) (meaning t m 2363) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 4340) (meaning t m 4503) (meaning t m 4736) source

theorem rule31370 (p2027 p2156 p2553 p3556 p4275 p4718 : Prop) (h : (¬ p2156) ∨ (¬ p4275) ∨ (¬ p2553) ∨ (¬ p4718) ∨ p2027 ∨ (¬ p3556)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2553) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial31370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory20626 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule31370 (meaning t m 2027) (meaning t m 2156) (meaning t m 2553) (meaning t m 3556) (meaning t m 4275) (meaning t m 4718) source

theorem rule31372 (p1991 p2027 p2187 p2542 p2589 p2655 p2765 p4256 p4432 : Prop) (h : (¬ p2187) ∨ p2765 ∨ (¬ p1991) ∨ (¬ p2655) ∨ (¬ p4256) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p4432)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (p2765) ∨ (¬ p4256) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial31372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory20628 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule31372 (meaning t m 1991) (meaning t m 2027) (meaning t m 2187) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2765) (meaning t m 4256) (meaning t m 4432) source

theorem rule31373 (p2027 p2252 p2383 p2750 p2753 p2786 p2952 p3483 p3690 p4320 p4358 p4621 : Prop) (h : (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4621) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3483) ∨ (¬ p2786) ∨ (¬ p4320) ∨ (¬ p2952) ∨ (¬ p2383) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4358) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial31373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory20629 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule31373 (meaning t m 2027) (meaning t m 2252) (meaning t m 2383) (meaning t m 2750) (meaning t m 2753) (meaning t m 2786) (meaning t m 2952) (meaning t m 3483) (meaning t m 3690) (meaning t m 4320) (meaning t m 4358) (meaning t m 4621) source

theorem rule31378 (p2027 p2254 p2518 p2963 p3379 p3917 p4149 p4191 p4328 p5119 : Prop) (h : (¬ p3379) ∨ (¬ p4328) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p3917) ∨ (¬ p4191) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3917) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4328) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20634 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 6) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule31378 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2963) (meaning t m 3379) (meaning t m 3917) (meaning t m 4149) (meaning t m 4191) (meaning t m 4328) (meaning t m 5119) source

theorem rule31380 (p1992 p2027 p2169 p2313 p2553 p2577 p3363 p3585 p3956 : Prop) (h : (¬ p3363) ∨ p2169 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2577) ∨ (¬ p1992) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3956)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial31380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory20636 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31380 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 3363) (meaning t m 3585) (meaning t m 3956) source

theorem rule31381 (p1982 p2027 p2388 p2952 p3178 p3256 p3998 p5600 : Prop) (h : (¬ p3178) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p5600) ∨ (¬ p3998) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3256)) : (¬ p1982) ∨ (p2027) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3178) ∨ (¬ p3256) ∨ (¬ p3998) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial31381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory20637 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 5) (m.theta 3 8) (m.theta 8 10) (m.theta 8 9)
  exact rule31381 (meaning t m 1982) (meaning t m 2027) (meaning t m 2388) (meaning t m 2952) (meaning t m 3178) (meaning t m 3256) (meaning t m 3998) (meaning t m 5600) source

theorem rule31389 (p2005 p2027 p2481 p2997 p3016 p3063 p3549 p4170 p4256 : Prop) (h : p2997 ∨ (¬ p3549) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p2005) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p2481) ∨ (¬ p4170)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2481) ∨ (p2997) ∨ (¬ p3016) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p4170) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial31389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory20645 t (m.theta 0 8) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule31389 (meaning t m 2005) (meaning t m 2027) (meaning t m 2481) (meaning t m 2997) (meaning t m 3016) (meaning t m 3063) (meaning t m 3549) (meaning t m 4170) (meaning t m 4256) source

theorem rule31391 (p2027 p2246 p2284 p2534 p2744 p2946 p3055 p3125 p3366 p3874 p4330 : Prop) (h : (¬ p2246) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p3125) ∨ (¬ p3055) ∨ (¬ p2534) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3874) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial31391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory20647 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule31391 (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2534) (meaning t m 2744) (meaning t m 2946) (meaning t m 3055) (meaning t m 3125) (meaning t m 3366) (meaning t m 3874) (meaning t m 4330) source

theorem rule31393 (p2166 p2373 p4034 : Prop) (h : (¬ p4034) ∨ (¬ p2166) ∨ p2373) : (¬ p2166) ∨ (p2373) ∨ (¬ p4034) := by
  classical
  tauto

theorem initial31393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (meaning t m 2373) ∨ (¬ (meaning t m 4034)) := by
  have source := ElevenTheory.theory20649 (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule31393 (meaning t m 2166) (meaning t m 2373) (meaning t m 4034) source

theorem rule31395 (p2027 p3073 p3365 p3449 p3553 p3572 p3692 p4736 p4902 : Prop) (h : p2027 ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p4736) ∨ (¬ p3572) ∨ (¬ p3365) ∨ (¬ p4902) ∨ (¬ p3692) ∨ (¬ p3073)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3692) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial31395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory20651 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31395 (meaning t m 2027) (meaning t m 3073) (meaning t m 3365) (meaning t m 3449) (meaning t m 3553) (meaning t m 3572) (meaning t m 3692) (meaning t m 4736) (meaning t m 4902) source

theorem rule31396 (p2027 p2264 p3546 p3551 p3631 p3690 p4362 : Prop) (h : (¬ p3690) ∨ p2027 ∨ (¬ p3546) ∨ (¬ p4362) ∨ (¬ p2264) ∨ (¬ p3551) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p4362) := by
  classical
  tauto

theorem initial31396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4362)) := by
  have source := ElevenTheory.theory20652 t (m.theta 0 7) (m.theta 1 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31396 (meaning t m 2027) (meaning t m 2264) (meaning t m 3546) (meaning t m 3551) (meaning t m 3631) (meaning t m 3690) (meaning t m 4362) source

theorem rule31401 (p1976 p2027 p2588 p2780 p2997 p3564 p3917 : Prop) (h : (¬ p3564) ∨ (¬ p1976) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p2780) ∨ p2997 ∨ (¬ p2588)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial31401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory20657 t (m.theta 0 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule31401 (meaning t m 1976) (meaning t m 2027) (meaning t m 2588) (meaning t m 2780) (meaning t m 2997) (meaning t m 3564) (meaning t m 3917) source

theorem rule31402 (p2027 p3055 p3471 p3658 p3742 p4753 : Prop) (h : (¬ p4753) ∨ (¬ p3658) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3742)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3658) ∨ (¬ p3742) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial31402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory20658 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7)
  exact rule31402 (meaning t m 2027) (meaning t m 3055) (meaning t m 3471) (meaning t m 3658) (meaning t m 3742) (meaning t m 4753) source

theorem rule31405 (p3918 p4329 p4435 : Prop) (h : (¬ p3918) ∨ (¬ p4329) ∨ p4435) : (¬ p3918) ∨ (¬ p4329) ∨ (p4435) := by
  classical
  tauto

theorem initial31405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4329)) ∨ (meaning t m 4435) := by
  have source := ElevenTheory.theory20661 (m.theta 1 6) (m.theta 2 6) (m.theta 6 10)
  exact rule31405 (meaning t m 3918) (meaning t m 4329) (meaning t m 4435) source

theorem rule31412 (p2027 p3449 p3591 p3990 p4026 p4503 p5307 : Prop) (h : p2027 ∨ (¬ p4026) ∨ (¬ p3990) ∨ (¬ p3591) ∨ (¬ p4503) ∨ (¬ p5307) ∨ (¬ p3449)) : (p2027) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3990) ∨ (¬ p4026) ∨ (¬ p4503) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial31412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory20668 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8)
  exact rule31412 (meaning t m 2027) (meaning t m 3449) (meaning t m 3591) (meaning t m 3990) (meaning t m 4026) (meaning t m 4503) (meaning t m 5307) source

theorem rule31414 (p2027 p3083 p3389 p3555 p3742 p3989 p4173 p4596 p5190 : Prop) (h : (¬ p3083) ∨ (¬ p4596) ∨ (¬ p3742) ∨ (¬ p5190) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p3389)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3389) ∨ (¬ p3555) ∨ (¬ p3742) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial31414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory20670 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule31414 (meaning t m 2027) (meaning t m 3083) (meaning t m 3389) (meaning t m 3555) (meaning t m 3742) (meaning t m 3989) (meaning t m 4173) (meaning t m 4596) (meaning t m 5190) source

theorem rule31416 (p1993 p2027 p2202 p2518 p2528 p3238 p4118 : Prop) (h : p2202 ∨ (¬ p3238) ∨ (¬ p1993) ∨ (¬ p2518) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p2528)) : (¬ p1993) ∨ (p2027) ∨ (p2202) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3238) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial31416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory20672 t (m.theta 1 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule31416 (meaning t m 1993) (meaning t m 2027) (meaning t m 2202) (meaning t m 2518) (meaning t m 2528) (meaning t m 3238) (meaning t m 4118) source

theorem rule31419 (p2027 p2387 p2406 p2427 p2819 p3379 p3822 p4556 p5021 : Prop) (h : p2027 ∨ (¬ p5021) ∨ (¬ p4556) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4556) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial31419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory20675 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule31419 (meaning t m 2027) (meaning t m 2387) (meaning t m 2406) (meaning t m 2427) (meaning t m 2819) (meaning t m 3379) (meaning t m 3822) (meaning t m 4556) (meaning t m 5021) source

theorem rule31425 (p1998 p2027 p2247 p2417 p2688 p2922 p3379 p3657 : Prop) (h : p2688 ∨ (¬ p2247) ∨ (¬ p2922) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p1998) ∨ (¬ p3379) ∨ (¬ p3657)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2417) ∨ (p2688) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial31425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory20681 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31425 (meaning t m 1998) (meaning t m 2027) (meaning t m 2247) (meaning t m 2417) (meaning t m 2688) (meaning t m 2922) (meaning t m 3379) (meaning t m 3657) source

theorem rule31429 (p2027 p2440 p3016 p3646 p4203 p4533 : Prop) (h : (¬ p2440) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p4203) ∨ (¬ p4533) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial31429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory20685 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule31429 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 3646) (meaning t m 4203) (meaning t m 4533) source

theorem rule31431 (p2027 p2177 p2248 p2295 p2573 p2663 p3486 p3555 p3690 p4389 p4666 : Prop) (h : (¬ p2248) ∨ (¬ p2663) ∨ (¬ p3555) ∨ (¬ p2573) ∨ (¬ p2295) ∨ (¬ p3486) ∨ (¬ p4389) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p4389) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial31431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory20687 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 5) (m.theta 3 6) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31431 (meaning t m 2027) (meaning t m 2177) (meaning t m 2248) (meaning t m 2295) (meaning t m 2573) (meaning t m 2663) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) (meaning t m 4389) (meaning t m 4666) source

theorem rule31433 (p2027 p2122 p2252 p2657 p2750 p2753 p2774 p3359 p3791 p4425 p4826 : Prop) (h : (¬ p4826) ∨ (¬ p2753) ∨ (¬ p4425) ∨ (¬ p3359) ∨ (¬ p3791) ∨ (¬ p2657) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3359) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial31433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory20689 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule31433 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3359) (meaning t m 3791) (meaning t m 4425) (meaning t m 4826) source

theorem rule31435 (p2307 p3323 p3567 p4187 : Prop) (h : (¬ p2307) ∨ (¬ p4187) ∨ (¬ p3567) ∨ p3323) : (¬ p2307) ∨ (p3323) ∨ (¬ p3567) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial31435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (meaning t m 3323) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory20691 (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule31435 (meaning t m 2307) (meaning t m 3323) (meaning t m 3567) (meaning t m 4187) source

theorem rule31438 (p2933 p3548 p3569 p3570 : Prop) (h : (¬ p3548) ∨ (¬ p3569) ∨ (¬ p2933) ∨ p3570) : (¬ p2933) ∨ (¬ p3548) ∨ (¬ p3569) ∨ (p3570) := by
  classical
  tauto

theorem initial31438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3569)) ∨ (meaning t m 3570) := by
  have source := ElevenTheory.theory20694 (m.theta 1 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule31438 (meaning t m 2933) (meaning t m 3548) (meaning t m 3569) (meaning t m 3570) source

theorem rule31444 (p2027 p2104 p2598 p3422 p4595 p5369 : Prop) (h : (¬ p5369) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4595) ∨ p2027 ∨ (¬ p3422)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4595) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial31444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4595)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory20700 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 6) (m.theta 4 8)
  exact rule31444 (meaning t m 2027) (meaning t m 2104) (meaning t m 2598) (meaning t m 3422) (meaning t m 4595) (meaning t m 5369) source

theorem rule31445 (p2253 p3987 p5020 : Prop) (h : (¬ p3987) ∨ (¬ p2253) ∨ p5020) : (¬ p2253) ∨ (¬ p3987) ∨ (p5020) := by
  classical
  tauto

theorem initial31445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 3987)) ∨ (meaning t m 5020) := by
  have source := ElevenTheory.theory20701 (m.theta 0 1) (m.theta 0 3) (m.theta 0 6)
  exact rule31445 (meaning t m 2253) (meaning t m 3987) (meaning t m 5020) source

theorem rule31449 (p1994 p2027 p2622 p2707 p2743 p3434 p3947 p4112 : Prop) (h : p2027 ∨ (¬ p3947) ∨ (¬ p1994) ∨ p2622 ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p4112) ∨ (¬ p2707)) : (¬ p1994) ∨ (p2027) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial31449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory20705 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule31449 (meaning t m 1994) (meaning t m 2027) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3434) (meaning t m 3947) (meaning t m 4112) source

theorem rule31453 (p2027 p3692 p3755 p3877 p4043 p4350 : Prop) (h : (¬ p3877) ∨ (¬ p4350) ∨ p2027 ∨ (¬ p4043) ∨ (¬ p3755) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3692) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4043) ∨ (¬ p4350) := by
  classical
  tauto

theorem initial31453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4350)) := by
  have source := ElevenTheory.theory20709 t (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 5 8) (m.theta 8 9)
  exact rule31453 (meaning t m 2027) (meaning t m 3692) (meaning t m 3755) (meaning t m 3877) (meaning t m 4043) (meaning t m 4350) source

theorem rule31454 (p1998 p2027 p2449 p2611 p2807 p3527 p3817 p4117 : Prop) (h : p2611 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3817) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3527)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2449) ∨ (p2611) ∨ (¬ p2807) ∨ (¬ p3527) ∨ (¬ p3817) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial31454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory20710 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31454 (meaning t m 1998) (meaning t m 2027) (meaning t m 2449) (meaning t m 2611) (meaning t m 2807) (meaning t m 3527) (meaning t m 3817) (meaning t m 4117) source

theorem rule31456 (p2027 p2248 p2331 p2363 p2668 p3585 p3954 p4697 p5160 : Prop) (h : (¬ p3954) ∨ (¬ p2248) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p4697) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p5160) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4697) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial31456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory20712 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule31456 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 3585) (meaning t m 3954) (meaning t m 4697) (meaning t m 5160) source

theorem rule31457 (p2027 p2241 p2630 p2748 p4319 p4366 p4452 p4972 : Prop) (h : (¬ p2241) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4972) ∨ (¬ p4452) ∨ (¬ p4319)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4319) ∨ (¬ p4366) ∨ (¬ p4452) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial31457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory20713 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule31457 (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2748) (meaning t m 4319) (meaning t m 4366) (meaning t m 4452) (meaning t m 4972) source

theorem rule31459 (p2017 p2027 p2192 p2210 p2274 p2699 p3791 : Prop) (h : (¬ p2017) ∨ (¬ p2192) ∨ p2699 ∨ (¬ p2210) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3791)) : (¬ p2017) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (p2699) ∨ (¬ p3791) := by
  classical
  tauto

theorem initial31459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3791)) := by
  have source := ElevenTheory.theory20715 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10)
  exact rule31459 (meaning t m 2017) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2699) (meaning t m 3791) source

theorem rule31460 (p2027 p2553 p3016 p3359 p4022 p4620 : Prop) (h : (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p4022) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial31460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory20716 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule31460 (meaning t m 2027) (meaning t m 2553) (meaning t m 3016) (meaning t m 3359) (meaning t m 4022) (meaning t m 4620) source

theorem rule31463 (p2027 p2255 p3178 p3998 p4360 p5600 : Prop) (h : (¬ p3998) ∨ (¬ p3178) ∨ (¬ p4360) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p5600)) : (p2027) ∨ (¬ p2255) ∨ (¬ p3178) ∨ (¬ p3998) ∨ (¬ p4360) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial31463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory20719 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 3 8) (m.theta 8 10)
  exact rule31463 (meaning t m 2027) (meaning t m 2255) (meaning t m 3178) (meaning t m 3998) (meaning t m 4360) (meaning t m 5600) source

theorem rule31464 (p1986 p2027 p2598 p2622 p2707 p2743 p3425 : Prop) (h : p2027 ∨ (¬ p2598) ∨ p2622 ∨ (¬ p1986) ∨ (¬ p3425) ∨ (¬ p2707) ∨ (¬ p2743)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3425) := by
  classical
  tauto

theorem initial31464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3425)) := by
  have source := ElevenTheory.theory20720 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7)
  exact rule31464 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3425) source

theorem rule31467 (p1984 p2027 p2553 p3008 p3583 p3822 p3954 p4193 : Prop) (h : (¬ p3583) ∨ (¬ p1984) ∨ (¬ p3954) ∨ p3008 ∨ (¬ p4193) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3822)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3583) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial31467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory20723 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule31467 (meaning t m 1984) (meaning t m 2027) (meaning t m 2553) (meaning t m 3008) (meaning t m 3583) (meaning t m 3822) (meaning t m 3954) (meaning t m 4193) source

theorem rule31478 (p1983 p2027 p2114 p2737 p2901 p3136 p3246 : Prop) (h : p2027 ∨ (¬ p2901) ∨ p2114 ∨ (¬ p1983) ∨ (¬ p2737) ∨ (¬ p3246) ∨ (¬ p3136)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial31478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory20734 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule31478 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2901) (meaning t m 3136) (meaning t m 3246) source

theorem rule31481 (p2027 p2295 p2313 p2383 p4358 p4843 : Prop) (h : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p4843) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p4358) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial31481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory20737 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule31481 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2383) (meaning t m 4358) (meaning t m 4843) source

theorem rule31482 (p2027 p2528 p2668 p2696 p2797 p3452 p3453 p4261 p4384 p4733 : Prop) (h : (¬ p3452) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4384) ∨ (¬ p2528) ∨ (¬ p2668) ∨ (¬ p3453) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4384) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial31482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory20738 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule31482 (meaning t m 2027) (meaning t m 2528) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3452) (meaning t m 3453) (meaning t m 4261) (meaning t m 4384) (meaning t m 4733) source

theorem rule31483 (p1984 p2027 p2202 p2553 p3660 p3688 p3822 p3954 : Prop) (h : (¬ p3660) ∨ (¬ p2553) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3954) ∨ p2202 ∨ (¬ p3688) ∨ (¬ p3822)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2553) ∨ (¬ p3660) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial31483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory20739 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule31483 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2553) (meaning t m 3660) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) source

theorem rule31484 (p2264 p2449 p3246 p3570 : Prop) (h : (¬ p3570) ∨ (¬ p3246) ∨ (¬ p2264) ∨ p2449) : (¬ p2264) ∨ (p2449) ∨ (¬ p3246) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial31484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (meaning t m 2449) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory20740 (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31484 (meaning t m 2264) (meaning t m 2449) (meaning t m 3246) (meaning t m 3570) source

theorem rule31487 (p1976 p2027 p2202 p2440 p2737 p3365 p3585 p4343 : Prop) (h : p2202 ∨ (¬ p4343) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3585) ∨ (¬ p1976) ∨ (¬ p3365) ∨ (¬ p2737)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial31487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory20743 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule31487 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2737) (meaning t m 3365) (meaning t m 3585) (meaning t m 4343) source

theorem rule31491 (p1990 p2027 p2156 p2166 p2938 p3486 p4120 : Prop) (h : (¬ p1990) ∨ (¬ p2156) ∨ p2938 ∨ (¬ p3486) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p2166)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (p2938) ∨ (¬ p3486) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial31491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory20747 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule31491 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 2938) (meaning t m 3486) (meaning t m 4120) source

theorem rule31494 (p2027 p2449 p2946 p3580 p3821 p4704 p4849 : Prop) (h : (¬ p4704) ∨ (¬ p2946) ∨ (¬ p3821) ∨ (¬ p4849) ∨ (¬ p3580) ∨ p2027 ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2946) ∨ (¬ p3580) ∨ (¬ p3821) ∨ (¬ p4704) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial31494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory20750 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule31494 (meaning t m 2027) (meaning t m 2449) (meaning t m 2946) (meaning t m 3580) (meaning t m 3821) (meaning t m 4704) (meaning t m 4849) source

theorem rule31501 (p2027 p2437 p2481 p2936 p3527 p3960 p4256 : Prop) (h : (¬ p3527) ∨ (¬ p2936) ∨ p2027 ∨ (¬ p3960) ∨ (¬ p2481) ∨ (¬ p2437) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p2936) ∨ (¬ p3527) ∨ (¬ p3960) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial31501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory20757 t (m.theta 0 8) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule31501 (meaning t m 2027) (meaning t m 2437) (meaning t m 2481) (meaning t m 2936) (meaning t m 3527) (meaning t m 3960) (meaning t m 4256) source

theorem rule31502 (p1978 p2027 p2169 p3556 p3570 p3979 p5558 : Prop) (h : p2027 ∨ (¬ p3570) ∨ (¬ p3556) ∨ (¬ p5558) ∨ (¬ p1978) ∨ p2169 ∨ (¬ p3979)) : (¬ p1978) ∨ (p2027) ∨ (p2169) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial31502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory20758 t (m.theta 0 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule31502 (meaning t m 1978) (meaning t m 2027) (meaning t m 2169) (meaning t m 3556) (meaning t m 3570) (meaning t m 3979) (meaning t m 5558) source

theorem rule31505 (p2579 p3016 p3363 p3683 : Prop) (h : (¬ p3683) ∨ (¬ p2579) ∨ (¬ p3363) ∨ (¬ p3016)) : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3363) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial31505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory20761 (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule31505 (meaning t m 2579) (meaning t m 3016) (meaning t m 3363) (meaning t m 3683) source

theorem rule31506 (p2027 p2387 p2459 p2608 p2619 p2839 p4347 p4902 p5021 : Prop) (h : (¬ p4902) ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p5021) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial31506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory20762 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule31506 (meaning t m 2027) (meaning t m 2387) (meaning t m 2459) (meaning t m 2608) (meaning t m 2619) (meaning t m 2839) (meaning t m 4347) (meaning t m 4902) (meaning t m 5021) source

theorem rule31510 (p1987 p2027 p2737 p2766 p3324 p3688 p4337 p4347 : Prop) (h : (¬ p4347) ∨ p2766 ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4337) ∨ (¬ p1987) ∨ (¬ p3324) ∨ (¬ p3688)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2766) ∨ (¬ p3324) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial31510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory20766 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule31510 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2766) (meaning t m 3324) (meaning t m 3688) (meaning t m 4337) (meaning t m 4347) source

theorem rule31515 (p4700 p5008 p5062 : Prop) (h : (¬ p4700) ∨ (¬ p5008) ∨ p5062) : (¬ p4700) ∨ (¬ p5008) ∨ (p5062) := by
  classical
  tauto

theorem initial31515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 5008)) ∨ (meaning t m 5062) := by
  have source := ElevenTheory.theory20771 t (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule31515 (meaning t m 4700) (meaning t m 5008) (meaning t m 5062) source

theorem rule31516 (p2027 p2138 p2246 p2307 p2598 p2742 p3323 p3568 p3987 p4368 p4385 p4752 : Prop) (h : (¬ p4368) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2246) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p3987) ∨ (¬ p3323) ∨ (¬ p4385) ∨ (¬ p4752) ∨ (¬ p3568) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2307) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4368) ∨ (¬ p4385) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial31516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory20772 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule31516 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2307) (meaning t m 2598) (meaning t m 2742) (meaning t m 3323) (meaning t m 3568) (meaning t m 3987) (meaning t m 4368) (meaning t m 4385) (meaning t m 4752) source

theorem rule31519 (p2027 p2254 p2459 p2657 p3399 p3527 p3574 p4137 p4604 : Prop) (h : (¬ p2254) ∨ (¬ p3574) ∨ (¬ p3399) ∨ (¬ p2459) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3527) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial31519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory20775 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule31519 (meaning t m 2027) (meaning t m 2254) (meaning t m 2459) (meaning t m 2657) (meaning t m 3399) (meaning t m 3527) (meaning t m 3574) (meaning t m 4137) (meaning t m 4604) source

theorem rule31521 (p1987 p2027 p2764 p2957 p3646 p3744 p4191 p4315 : Prop) (h : p2764 ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p3744) ∨ (¬ p1987) ∨ (¬ p4315) ∨ (¬ p4191)) : (¬ p1987) ∨ (p2027) ∨ (p2764) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial31521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory20777 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule31521 (meaning t m 1987) (meaning t m 2027) (meaning t m 2764) (meaning t m 2957) (meaning t m 3646) (meaning t m 3744) (meaning t m 4191) (meaning t m 4315) source

theorem rule31522 (p1998 p2027 p2148 p2717 p3051 p3246 p4324 : Prop) (h : (¬ p3051) ∨ p2148 ∨ (¬ p1998) ∨ (¬ p2717) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p3246)) : (¬ p1998) ∨ (p2027) ∨ (p2148) ∨ (¬ p2717) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial31522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory20778 t (m.theta 0 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31522 (meaning t m 1998) (meaning t m 2027) (meaning t m 2148) (meaning t m 2717) (meaning t m 3051) (meaning t m 3246) (meaning t m 4324) source

theorem rule31533 (p2027 p3027 p3552 p3822 p4154 p4843 : Prop) (h : p2027 ∨ (¬ p4843) ∨ (¬ p3822) ∨ (¬ p3552) ∨ (¬ p3027) ∨ (¬ p4154)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p3822) ∨ (¬ p4154) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial31533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory20789 t (m.theta 1 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule31533 (meaning t m 2027) (meaning t m 3027) (meaning t m 3552) (meaning t m 3822) (meaning t m 4154) (meaning t m 4843) source

theorem rule31535 (p2027 p2870 p2992 p2996 p3699 p5053 : Prop) (h : (¬ p2996) ∨ (¬ p3699) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p5053) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial31535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory20791 t (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule31535 (meaning t m 2027) (meaning t m 2870) (meaning t m 2992) (meaning t m 2996) (meaning t m 3699) (meaning t m 5053) source

theorem rule31538 (p1998 p2027 p2287 p2295 p2396 p2881 p3690 : Prop) (h : (¬ p2881) ∨ (¬ p2295) ∨ p2027 ∨ p2287 ∨ (¬ p1998) ∨ (¬ p2396) ∨ (¬ p3690)) : (¬ p1998) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial31538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory20794 t (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31538 (meaning t m 1998) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2396) (meaning t m 2881) (meaning t m 3690) source

theorem rule31539 (p1998 p2027 p2287 p2295 p2396 p2881 p3821 p4283 : Prop) (h : (¬ p2881) ∨ (¬ p2295) ∨ p2027 ∨ p2287 ∨ (¬ p2396) ∨ (¬ p4283) ∨ (¬ p1998) ∨ (¬ p3821)) : (¬ p1998) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3821) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial31539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory20795 t (m.theta 0 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule31539 (meaning t m 1998) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2396) (meaning t m 2881) (meaning t m 3821) (meaning t m 4283) source

theorem rule31544 (p2027 p2254 p2657 p3359 p3399 p3527 p3941 p4425 p5119 : Prop) (h : (¬ p4425) ∨ (¬ p3527) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p5119) ∨ (¬ p3399) ∨ (¬ p3941) ∨ p2027 ∨ (¬ p3359)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3359) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial31544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory20800 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule31544 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3359) (meaning t m 3399) (meaning t m 3527) (meaning t m 3941) (meaning t m 4425) (meaning t m 5119) source

theorem rule31548 (p1977 p2027 p2766 p2957 p3266 p3662 p4032 p4322 : Prop) (h : (¬ p1977) ∨ (¬ p4032) ∨ (¬ p2957) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p3662) ∨ p2766 ∨ (¬ p3266)) : (¬ p1977) ∨ (p2027) ∨ (p2766) ∨ (¬ p2957) ∨ (¬ p3266) ∨ (¬ p3662) ∨ (¬ p4032) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial31548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory20804 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule31548 (meaning t m 1977) (meaning t m 2027) (meaning t m 2766) (meaning t m 2957) (meaning t m 3266) (meaning t m 3662) (meaning t m 4032) (meaning t m 4322) source

theorem rule31551 (p2027 p2143 p2449 p2696 p2742 p3027 p3583 p3692 p3950 p4120 p4737 : Prop) (h : (¬ p2742) ∨ (¬ p2143) ∨ (¬ p3583) ∨ (¬ p4120) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2696) ∨ (¬ p2449) ∨ (¬ p3950) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4120) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial31551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory20807 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule31551 (meaning t m 2027) (meaning t m 2143) (meaning t m 2449) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3583) (meaning t m 3692) (meaning t m 3950) (meaning t m 4120) (meaning t m 4737) source

end SunPrize.SMT
