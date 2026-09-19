import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory030
import SunPrize.Certificate.Theory031
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule20698 (p2027 p2363 p3685 p4138 p4253 p4340 p5564 : Prop) (h : (¬ p4340) ∨ (¬ p2363) ∨ (¬ p3685) ∨ (¬ p5564) ∨ (¬ p4138) ∨ p2027 ∨ (¬ p4253)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3685) ∨ (¬ p4138) ∨ (¬ p4253) ∨ (¬ p4340) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial20698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory9954 t (m.theta 2 7) (m.theta 2 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule20698 (meaning t m 2027) (meaning t m 2363) (meaning t m 3685) (meaning t m 4138) (meaning t m 4253) (meaning t m 4340) (meaning t m 5564) source

theorem rule20711 (p1992 p2997 p3549 p4866 : Prop) (h : p2997 ∨ (¬ p3549) ∨ (¬ p1992) ∨ p4866) : (¬ p1992) ∨ (p2997) ∨ (¬ p3549) ∨ (p4866) := by
  classical
  tauto

theorem initial20711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3549)) ∨ (meaning t m 4866) := by
  have source := ElevenTheory.theory9967 t (m.theta 1 2) (m.theta 1 6) (m.theta 6 7)
  exact rule20711 (meaning t m 1992) (meaning t m 2997) (meaning t m 3549) (meaning t m 4866) source

theorem rule20717 (p2881 p3569 p3644 : Prop) (h : (¬ p3569) ∨ (¬ p2881) ∨ (¬ p3644)) : (¬ p2881) ∨ (¬ p3569) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial20717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory9973 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule20717 (meaning t m 2881) (meaning t m 3569) (meaning t m 3644) source

theorem rule20721 (p2630 p3413 p4315 : Prop) (h : (¬ p2630) ∨ (¬ p4315) ∨ (¬ p3413)) : (¬ p2630) ∨ (¬ p3413) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial20721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory9977 (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule20721 (meaning t m 2630) (meaning t m 3413) (meaning t m 4315) source

theorem rule20722 (p2156 p4032 p4334 : Prop) (h : (¬ p2156) ∨ (¬ p4334) ∨ (¬ p4032)) : (¬ p2156) ∨ (¬ p4032) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial20722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory9978 (m.theta 0 5) (m.theta 5 6) (m.theta 5 9)
  exact rule20722 (meaning t m 2156) (meaning t m 4032) (meaning t m 4334) source

theorem rule20723 (p3755 p3877 p4349 : Prop) (h : (¬ p3877) ∨ (¬ p3755) ∨ (¬ p4349)) : (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4349) := by
  classical
  tauto

theorem initial20723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4349)) := by
  have source := ElevenTheory.theory9979 (m.theta 2 3) (m.theta 3 8) (m.theta 3 9)
  exact rule20723 (meaning t m 3755) (meaning t m 3877) (meaning t m 4349) source

theorem rule20725 (p3755 p4195 p5274 : Prop) (h : (¬ p4195) ∨ (¬ p3755) ∨ (¬ p5274)) : (¬ p3755) ∨ (¬ p4195) ∨ (¬ p5274) := by
  classical
  tauto

theorem initial20725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5274)) := by
  have source := ElevenTheory.theory9981 (m.theta 2 3) (m.theta 3 6) (m.theta 3 9)
  exact rule20725 (meaning t m 3755) (meaning t m 4195) (meaning t m 5274) source

theorem rule20726 (p2685 p4315 p4386 : Prop) (h : (¬ p4315) ∨ (¬ p2685) ∨ (¬ p4386)) : (¬ p2685) ∨ (¬ p4315) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial20726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory9982 (m.theta 2 3) (m.theta 3 5) (m.theta 3 7)
  exact rule20726 (meaning t m 2685) (meaning t m 4315) (meaning t m 4386) source

theorem rule20728 (p2727 p3413 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p2727) ∨ (¬ p3413)) : (¬ p2727) ∨ (¬ p3413) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial20728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory9984 (m.theta 1 3) (m.theta 3 4) (m.theta 3 5)
  exact rule20728 (meaning t m 2727) (meaning t m 3413) (meaning t m 3662) source

theorem rule20732 (p2027 p2139 p2156 p2274 p2396 p2476 p3641 p3905 p4641 p5160 : Prop) (h : p2027 ∨ (¬ p3641) ∨ (¬ p4641) ∨ (¬ p2139) ∨ (¬ p2476) ∨ (¬ p2396) ∨ (¬ p2274) ∨ (¬ p3905) ∨ (¬ p2156) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial20732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory9988 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule20732 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2476) (meaning t m 3641) (meaning t m 3905) (meaning t m 4641) (meaning t m 5160) source

theorem rule20735 (p2027 p3073 p3692 p4119 p4320 p4496 p4960 : Prop) (h : (¬ p3692) ∨ p2027 ∨ (¬ p4496) ∨ (¬ p4320) ∨ (¬ p4119) ∨ (¬ p4960) ∨ (¬ p3073)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4496) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial20735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory9991 t (m.theta 1 5) (m.theta 1 8) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule20735 (meaning t m 2027) (meaning t m 3073) (meaning t m 3692) (meaning t m 4119) (meaning t m 4320) (meaning t m 4496) (meaning t m 4960) source

theorem rule20736 (p2191 p2891 p3747 : Prop) (h : (¬ p3747) ∨ (¬ p2191) ∨ (¬ p2891)) : (¬ p2191) ∨ (¬ p2891) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial20736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory9992 (m.theta 1 5) (m.theta 5 7) (m.theta 5 8)
  exact rule20736 (meaning t m 2191) (meaning t m 2891) (meaning t m 3747) source

theorem rule20737 (p2797 p2810 p4194 : Prop) (h : (¬ p2810) ∨ (¬ p4194) ∨ (¬ p2797)) : (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial20737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory9993 (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule20737 (meaning t m 2797) (meaning t m 2810) (meaning t m 4194) source

theorem rule20738 (p2417 p3690 p4001 : Prop) (h : (¬ p2417) ∨ (¬ p3690) ∨ (¬ p4001)) : (¬ p2417) ∨ (¬ p3690) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial20738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory9994 (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule20738 (meaning t m 2417) (meaning t m 3690) (meaning t m 4001) source

theorem rule20743 (p2245 p2608 p2657 p2727 p2749 : Prop) (h : (¬ p2749) ∨ (¬ p2657) ∨ (¬ p2245) ∨ (¬ p2727) ∨ (¬ p2608)) : (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) := by
  classical
  tauto

theorem initial20743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) := by
  have source := ElevenTheory.theory9999 (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4)
  exact rule20743 (meaning t m 2245) (meaning t m 2608) (meaning t m 2657) (meaning t m 2727) (meaning t m 2749) source

theorem rule20745 (p2027 p2138 p3471 p3694 p4344 p4901 : Prop) (h : (¬ p3471) ∨ (¬ p4901) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p4344) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3694) ∨ (¬ p4344) ∨ (¬ p4901) := by
  classical
  tauto

theorem initial20745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4901)) := by
  have source := ElevenTheory.theory10001 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 5 8)
  exact rule20745 (meaning t m 2027) (meaning t m 2138) (meaning t m 3471) (meaning t m 3694) (meaning t m 4344) (meaning t m 4901) source

theorem rule20748 (p2027 p2437 p2573 p2589 p3574 p4646 : Prop) (h : (¬ p2573) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p2589) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial20748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory10004 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule20748 (meaning t m 2027) (meaning t m 2437) (meaning t m 2573) (meaning t m 2589) (meaning t m 3574) (meaning t m 4646) source

theorem rule20751 (p2027 p3692 p3969 p4191 p4330 p5121 : Prop) (h : (¬ p4330) ∨ (¬ p3692) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p5121) ∨ (¬ p3969)) : (p2027) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p5121) := by
  classical
  tauto

theorem initial20751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 5121)) := by
  have source := ElevenTheory.theory10007 t (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule20751 (meaning t m 2027) (meaning t m 3692) (meaning t m 3969) (meaning t m 4191) (meaning t m 4330) (meaning t m 5121) source

theorem rule20753 (p2352 p3324 p3984 : Prop) (h : (¬ p2352) ∨ (¬ p3324) ∨ (¬ p3984)) : (¬ p2352) ∨ (¬ p3324) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial20753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory10009 (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule20753 (meaning t m 2352) (meaning t m 3324) (meaning t m 3984) source

theorem rule20755 (p2027 p2241 p2307 p2396 p2761 p3412 p3555 p4756 p5016 p5405 p5740 : Prop) (h : (¬ p2396) ∨ (¬ p2307) ∨ (¬ p5016) ∨ (¬ p2761) ∨ (¬ p2241) ∨ (¬ p4756) ∨ (¬ p3555) ∨ (¬ p5405) ∨ (¬ p3412) ∨ p2027 ∨ (¬ p5740)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p4756) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial20755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4756)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory10011 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20755 (meaning t m 2027) (meaning t m 2241) (meaning t m 2307) (meaning t m 2396) (meaning t m 2761) (meaning t m 3412) (meaning t m 3555) (meaning t m 4756) (meaning t m 5016) (meaning t m 5405) (meaning t m 5740) source

theorem rule20756 (p2177 p3570 p4140 : Prop) (h : (¬ p4140) ∨ (¬ p2177) ∨ (¬ p3570)) : (¬ p2177) ∨ (¬ p3570) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial20756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory10012 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20756 (meaning t m 2177) (meaning t m 3570) (meaning t m 4140) source

theorem rule20761 (p2027 p2470 p2509 p2630 p2656 p2745 p3402 : Prop) (h : (¬ p2656) ∨ (¬ p2470) ∨ (¬ p2745) ∨ p2027 ∨ (¬ p3402) ∨ (¬ p2630) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial20761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory10017 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8)
  exact rule20761 (meaning t m 2027) (meaning t m 2470) (meaning t m 2509) (meaning t m 2630) (meaning t m 2656) (meaning t m 2745) (meaning t m 3402) source

theorem rule20764 (p2027 p2298 p2383 p2797 p3567 p3572 p4405 : Prop) (h : (¬ p4405) ∨ (¬ p3567) ∨ (¬ p2797) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p2298) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3572) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial20764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory10020 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8)
  exact rule20764 (meaning t m 2027) (meaning t m 2298) (meaning t m 2383) (meaning t m 2797) (meaning t m 3567) (meaning t m 3572) (meaning t m 4405) source

theorem rule20766 (p2177 p4260 p5563 : Prop) (h : (¬ p4260) ∨ (¬ p2177) ∨ (¬ p5563)) : (¬ p2177) ∨ (¬ p4260) ∨ (¬ p5563) := by
  classical
  tauto

theorem initial20766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5563)) := by
  have source := ElevenTheory.theory10022 (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule20766 (meaning t m 2177) (meaning t m 4260) (meaning t m 5563) source

theorem rule20767 (p2027 p2230 p2373 p3365 p3877 p3969 p4118 p4419 p5122 : Prop) (h : (¬ p4419) ∨ (¬ p3877) ∨ (¬ p3365) ∨ (¬ p2373) ∨ (¬ p5122) ∨ (¬ p4118) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3969) ∨ (¬ p4118) ∨ (¬ p4419) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial20767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory10023 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule20767 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3365) (meaning t m 3877) (meaning t m 3969) (meaning t m 4118) (meaning t m 4419) (meaning t m 5122) source

theorem rule20772 (p2027 p2132 p2860 p3125 p3266 p3292 p4330 p4789 p5284 : Prop) (h : (¬ p4789) ∨ (¬ p2860) ∨ (¬ p3266) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p2132) ∨ (¬ p3125) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial20772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory10028 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20772 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3125) (meaning t m 3266) (meaning t m 3292) (meaning t m 4330) (meaning t m 4789) (meaning t m 5284) source

theorem rule20773 (p2027 p2230 p2963 p3105 p3324 p3362 p3680 p3698 p4789 p5123 p5580 : Prop) (h : (¬ p3680) ∨ (¬ p3105) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p2963) ∨ (¬ p2230) ∨ (¬ p3362) ∨ p2027 ∨ (¬ p3698) ∨ (¬ p3324) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2963) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3680) ∨ (¬ p3698) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial20773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory10029 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule20773 (meaning t m 2027) (meaning t m 2230) (meaning t m 2963) (meaning t m 3105) (meaning t m 3324) (meaning t m 3362) (meaning t m 3680) (meaning t m 3698) (meaning t m 4789) (meaning t m 5123) (meaning t m 5580) source

theorem rule20778 (p2027 p2177 p2247 p2307 p2459 p3662 p4208 p5017 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p3662) ∨ (¬ p2459) ∨ (¬ p5017) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p5017) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial20778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory10034 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule20778 (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2307) (meaning t m 2459) (meaning t m 3662) (meaning t m 4208) (meaning t m 5017) (meaning t m 5059) source

theorem rule20784 (p3309 p3325 p3923 : Prop) (h : (¬ p3325) ∨ (¬ p3923) ∨ (¬ p3309)) : (¬ p3309) ∨ (¬ p3325) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial20784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory10040 (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20784 (meaning t m 3309) (meaning t m 3325) (meaning t m 3923) source

theorem rule20786 (p2010 p2027 p2233 p2482 p3201 p3874 p3998 p4286 : Prop) (h : (¬ p2010) ∨ p2233 ∨ (¬ p3998) ∨ (¬ p2482) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p4286) ∨ p2027) : (¬ p2010) ∨ (p2027) ∨ (p2233) ∨ (¬ p2482) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3998) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial20786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory10042 t (m.theta 0 4) (m.theta 0 8) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 10)
  exact rule20786 (meaning t m 2010) (meaning t m 2027) (meaning t m 2233) (meaning t m 2482) (meaning t m 3201) (meaning t m 3874) (meaning t m 3998) (meaning t m 4286) source

theorem rule20788 (p1998 p2169 p2177 p4501 : Prop) (h : (¬ p1998) ∨ p2169 ∨ p4501 ∨ (¬ p2177)) : (¬ p1998) ∨ (p2169) ∨ (¬ p2177) ∨ (p4501) := by
  classical
  tauto

theorem initial20788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 4501) := by
  have source := ElevenTheory.theory10044 t (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule20788 (meaning t m 1998) (meaning t m 2169) (meaning t m 2177) (meaning t m 4501) source

theorem rule20789 (p2003 p2323 p2331 p4581 : Prop) (h : (¬ p2003) ∨ p2323 ∨ (¬ p2331) ∨ p4581) : (¬ p2003) ∨ (p2323) ∨ (¬ p2331) ∨ (p4581) := by
  classical
  tauto

theorem initial20789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 4581) := by
  have source := ElevenTheory.theory10045 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6)
  exact rule20789 (meaning t m 2003) (meaning t m 2323) (meaning t m 2331) (meaning t m 4581) source

theorem rule20790 (p1978 p2344 p3646 p4489 : Prop) (h : (¬ p1978) ∨ p2344 ∨ (¬ p3646) ∨ p4489) : (¬ p1978) ∨ (p2344) ∨ (¬ p3646) ∨ (p4489) := by
  classical
  tauto

theorem initial20790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 3646)) ∨ (meaning t m 4489) := by
  have source := ElevenTheory.theory10046 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6)
  exact rule20790 (meaning t m 1978) (meaning t m 2344) (meaning t m 3646) (meaning t m 4489) source

theorem rule20791 (p1992 p2608 p2611 p4733 : Prop) (h : (¬ p2608) ∨ p2611 ∨ p4733 ∨ (¬ p1992)) : (¬ p1992) ∨ (¬ p2608) ∨ (p2611) ∨ (p4733) := by
  classical
  tauto

theorem initial20791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2611) ∨ (meaning t m 4733) := by
  have source := ElevenTheory.theory10047 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule20791 (meaning t m 1992) (meaning t m 2608) (meaning t m 2611) (meaning t m 4733) source

theorem rule20792 (p1986 p2622 p2630 p4750 : Prop) (h : (¬ p1986) ∨ p2622 ∨ (¬ p2630) ∨ p4750) : (¬ p1986) ∨ (p2622) ∨ (¬ p2630) ∨ (p4750) := by
  classical
  tauto

theorem initial20792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 4750) := by
  have source := ElevenTheory.theory10048 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule20792 (meaning t m 1986) (meaning t m 2622) (meaning t m 2630) (meaning t m 4750) source

theorem rule20793 (p2027 p2743 p2807 p3572 p4117 p4737 : Prop) (h : p2027 ∨ (¬ p4117) ∨ (¬ p2743) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4737)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial20793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory10049 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7)
  exact rule20793 (meaning t m 2027) (meaning t m 2743) (meaning t m 2807) (meaning t m 3572) (meaning t m 4117) (meaning t m 4737) source

theorem rule20794 (p1984 p2611 p3954 p4737 : Prop) (h : p2611 ∨ (¬ p3954) ∨ p4737 ∨ (¬ p1984)) : (¬ p1984) ∨ (p2611) ∨ (¬ p3954) ∨ (p4737) := by
  classical
  tauto

theorem initial20794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3954)) ∨ (meaning t m 4737) := by
  have source := ElevenTheory.theory10050 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule20794 (meaning t m 1984) (meaning t m 2611) (meaning t m 3954) (meaning t m 4737) source

theorem rule20795 (p2006 p2842 p2850 p4882 : Prop) (h : (¬ p2006) ∨ p2842 ∨ (¬ p2850) ∨ p4882) : (¬ p2006) ∨ (p2842) ∨ (¬ p2850) ∨ (p4882) := by
  classical
  tauto

theorem initial20795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 4882) := by
  have source := ElevenTheory.theory10051 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule20795 (meaning t m 2006) (meaning t m 2842) (meaning t m 2850) (meaning t m 4882) source

theorem rule20796 (p1998 p2027 p2608 p2699 p2707 p3609 p4348 p4805 : Prop) (h : (¬ p2707) ∨ (¬ p1998) ∨ (¬ p4805) ∨ (¬ p3609) ∨ p2699 ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial20796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory10052 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20796 (meaning t m 1998) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 3609) (meaning t m 4348) (meaning t m 4805) source

theorem rule20797 (p1992 p2873 p3583 p4878 : Prop) (h : p2873 ∨ (¬ p1992) ∨ p4878 ∨ (¬ p3583)) : (¬ p1992) ∨ (p2873) ∨ (¬ p3583) ∨ (p4878) := by
  classical
  tauto

theorem initial20797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3583)) ∨ (meaning t m 4878) := by
  have source := ElevenTheory.theory10053 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5)
  exact rule20797 (meaning t m 1992) (meaning t m 2873) (meaning t m 3583) (meaning t m 4878) source

theorem rule20798 (p2027 p2807 p2952 p3486 p4333 p4957 : Prop) (h : (¬ p4957) ∨ (¬ p2952) ∨ (¬ p3486) ∨ p2027 ∨ (¬ p4333) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3486) ∨ (¬ p4333) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial20798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory10054 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule20798 (meaning t m 2027) (meaning t m 2807) (meaning t m 2952) (meaning t m 3486) (meaning t m 4333) (meaning t m 4957) source

theorem rule20799 (p1977 p2027 p2651 p2911 p2914 p3551 p4111 p4849 : Prop) (h : (¬ p2911) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p4849) ∨ p2914) : (¬ p1977) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial20799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory10055 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule20799 (meaning t m 1977) (meaning t m 2027) (meaning t m 2651) (meaning t m 2911) (meaning t m 2914) (meaning t m 3551) (meaning t m 4111) (meaning t m 4849) source

theorem rule20801 (p2027 p2295 p2881 p3324 p4138 p4559 : Prop) (h : p2027 ∨ (¬ p4138) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p2295) ∨ (¬ p4559)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial20801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory10057 t (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule20801 (meaning t m 2027) (meaning t m 2295) (meaning t m 2881) (meaning t m 3324) (meaning t m 4138) (meaning t m 4559) source

theorem rule20802 (p2027 p2255 p2958 p3051 p3662 p4320 : Prop) (h : (¬ p2958) ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p3662)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3662) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial20802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory10058 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7)
  exact rule20802 (meaning t m 2027) (meaning t m 2255) (meaning t m 2958) (meaning t m 3051) (meaning t m 3662) (meaning t m 4320) source

theorem rule20803 (p1976 p2114 p3954 p4736 : Prop) (h : (¬ p1976) ∨ (¬ p3954) ∨ p4736 ∨ p2114) : (¬ p1976) ∨ (p2114) ∨ (¬ p3954) ∨ (p4736) := by
  classical
  tauto

theorem initial20803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3954)) ∨ (meaning t m 4736) := by
  have source := ElevenTheory.theory10059 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule20803 (meaning t m 1976) (meaning t m 2114) (meaning t m 3954) (meaning t m 4736) source

theorem rule20804 (p2007 p3042 p3083 p5008 : Prop) (h : p3042 ∨ p5008 ∨ (¬ p2007) ∨ (¬ p3083)) : (¬ p2007) ∨ (p3042) ∨ (¬ p3083) ∨ (p5008) := by
  classical
  tauto

theorem initial20804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 3042) ∨ (¬ (meaning t m 3083)) ∨ (meaning t m 5008) := by
  have source := ElevenTheory.theory10060 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule20804 (meaning t m 2007) (meaning t m 3042) (meaning t m 3083) (meaning t m 5008) source

theorem rule20805 (p2011 p3128 p3744 p5046 : Prop) (h : p5046 ∨ (¬ p3744) ∨ (¬ p2011) ∨ p3128) : (¬ p2011) ∨ (p3128) ∨ (¬ p3744) ∨ (p5046) := by
  classical
  tauto

theorem initial20805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3744)) ∨ (meaning t m 5046) := by
  have source := ElevenTheory.theory10061 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule20805 (meaning t m 2011) (meaning t m 3128) (meaning t m 3744) (meaning t m 5046) source

theorem rule20806 (p1977 p2027 p2766 p2946 p3172 p3662 p3692 p4312 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p4312) ∨ (¬ p2946) ∨ (¬ p3692) ∨ (¬ p3172) ∨ p2766) : (¬ p1977) ∨ (p2027) ∨ (p2766) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4312) := by
  classical
  tauto

theorem initial20806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4312)) := by
  have source := ElevenTheory.theory10062 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule20806 (meaning t m 1977) (meaning t m 2027) (meaning t m 2766) (meaning t m 2946) (meaning t m 3172) (meaning t m 3662) (meaning t m 3692) (meaning t m 4312) source

theorem rule20807 (p2005 p2588 p2914 p4712 : Prop) (h : p2914 ∨ (¬ p2005) ∨ (¬ p2588) ∨ p4712) : (¬ p2005) ∨ (¬ p2588) ∨ (p2914) ∨ (p4712) := by
  classical
  tauto

theorem initial20807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2914) ∨ (meaning t m 4712) := by
  have source := ElevenTheory.theory10063 t (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule20807 (meaning t m 2005) (meaning t m 2588) (meaning t m 2914) (meaning t m 4712) source

theorem rule20808 (p2027 p2383 p2584 p2665 p3574 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2665) ∨ (¬ p2383) ∨ (¬ p2584)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3574) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial20808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory10064 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule20808 (meaning t m 2027) (meaning t m 2383) (meaning t m 2584) (meaning t m 2665) (meaning t m 3574) (meaning t m 3956) source

theorem rule20809 (p2027 p2528 p2881 p3690 p4438 p4445 : Prop) (h : (¬ p3690) ∨ (¬ p2881) ∨ (¬ p2528) ∨ (¬ p4438) ∨ p2027 ∨ (¬ p4445)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p3690) ∨ (¬ p4438) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial20809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory10065 t (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule20809 (meaning t m 2027) (meaning t m 2528) (meaning t m 2881) (meaning t m 3690) (meaning t m 4438) (meaning t m 4445) source

theorem rule20810 (p2027 p2255 p2651 p3193 p3343 p3402 : Prop) (h : (¬ p2255) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p3402) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial20810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory10066 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 9)
  exact rule20810 (meaning t m 2027) (meaning t m 2255) (meaning t m 2651) (meaning t m 3193) (meaning t m 3343) (meaning t m 3402) source

theorem rule20811 (p2027 p2321 p2341 p2459 p3955 p4347 : Prop) (h : (¬ p2341) ∨ p2027 ∨ (¬ p2321) ∨ (¬ p3955) ∨ (¬ p2459) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3955) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial20811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2321)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10067 t (m.theta 0 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20811 (meaning t m 2027) (meaning t m 2321) (meaning t m 2341) (meaning t m 2459) (meaning t m 3955) (meaning t m 4347) source

theorem rule20812 (p2000 p2842 p3055 p4729 : Prop) (h : (¬ p2000) ∨ p4729 ∨ p2842 ∨ (¬ p3055)) : (¬ p2000) ∨ (p2842) ∨ (¬ p3055) ∨ (p4729) := by
  classical
  tauto

theorem initial20812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (meaning t m 4729) := by
  have source := ElevenTheory.theory10068 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule20812 (meaning t m 2000) (meaning t m 2842) (meaning t m 3055) (meaning t m 4729) source

theorem rule20813 (p1997 p2388 p2542 p4701 : Prop) (h : p4701 ∨ p2388 ∨ (¬ p1997) ∨ (¬ p2542)) : (¬ p1997) ∨ (p2388) ∨ (¬ p2542) ∨ (p4701) := by
  classical
  tauto

theorem initial20813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 4701) := by
  have source := ElevenTheory.theory10069 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule20813 (meaning t m 1997) (meaning t m 2388) (meaning t m 2542) (meaning t m 4701) source

theorem rule20814 (p2027 p2553 p2829 p3588 p4471 p5222 : Prop) (h : (¬ p5222) ∨ p2027 ∨ (¬ p3588) ∨ (¬ p2829) ∨ (¬ p2553) ∨ (¬ p4471)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4471) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial20814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory10070 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7)
  exact rule20814 (meaning t m 2027) (meaning t m 2553) (meaning t m 2829) (meaning t m 3588) (meaning t m 4471) (meaning t m 5222) source

theorem rule20815 (p2027 p2274 p2321 p2341 p3989 p4138 : Prop) (h : p2027 ∨ (¬ p2274) ∨ (¬ p2341) ∨ (¬ p3989) ∨ (¬ p2321) ∨ (¬ p4138)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p3989) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial20815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2321)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory10071 t (m.theta 0 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule20815 (meaning t m 2027) (meaning t m 2274) (meaning t m 2321) (meaning t m 2341) (meaning t m 3989) (meaning t m 4138) source

theorem rule20817 (p1984 p2233 p3452 p5194 : Prop) (h : (¬ p1984) ∨ p5194 ∨ (¬ p3452) ∨ p2233) : (¬ p1984) ∨ (p2233) ∨ (¬ p3452) ∨ (p5194) := by
  classical
  tauto

theorem initial20817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 5194) := by
  have source := ElevenTheory.theory10073 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule20817 (meaning t m 1984) (meaning t m 2233) (meaning t m 3452) (meaning t m 5194) source

theorem rule20818 (p1977 p2409 p4111 p4814 : Prop) (h : p2409 ∨ (¬ p4111) ∨ p4814 ∨ (¬ p1977)) : (¬ p1977) ∨ (p2409) ∨ (¬ p4111) ∨ (p4814) := by
  classical
  tauto

theorem initial20818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 4111)) ∨ (meaning t m 4814) := by
  have source := ElevenTheory.theory10074 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4)
  exact rule20818 (meaning t m 1977) (meaning t m 2409) (meaning t m 4111) (meaning t m 4814) source

theorem rule20819 (p1991 p2344 p2963 p4584 : Prop) (h : p2344 ∨ p4584 ∨ (¬ p2963) ∨ (¬ p1991)) : (¬ p1991) ∨ (p2344) ∨ (¬ p2963) ∨ (p4584) := by
  classical
  tauto

theorem initial20819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 4584) := by
  have source := ElevenTheory.theory10075 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6)
  exact rule20819 (meaning t m 1991) (meaning t m 2344) (meaning t m 2963) (meaning t m 4584) source

theorem rule20820 (p2027 p2299 p2319 p2341 p3567 p4037 p4620 : Prop) (h : p2027 ∨ (¬ p4620) ∨ (¬ p4037) ∨ (¬ p3567) ∨ (¬ p2341) ∨ (¬ p2319) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3567) ∨ (¬ p4037) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial20820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory10076 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule20820 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 3567) (meaning t m 4037) (meaning t m 4620) source

theorem rule20821 (p1994 p2027 p2341 p2630 p2688 p3027 p3659 p4066 p4357 : Prop) (h : (¬ p3659) ∨ (¬ p4066) ∨ p2027 ∨ (¬ p1994) ∨ p2688 ∨ (¬ p3027) ∨ (¬ p2630) ∨ (¬ p4357) ∨ (¬ p2341)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3659) ∨ (¬ p4066) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial20821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory10077 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule20821 (meaning t m 1994) (meaning t m 2027) (meaning t m 2341) (meaning t m 2630) (meaning t m 2688) (meaning t m 3027) (meaning t m 3659) (meaning t m 4066) (meaning t m 4357) source

theorem rule20823 (p1976 p2608 p2699 p4734 : Prop) (h : p2699 ∨ (¬ p1976) ∨ (¬ p2608) ∨ p4734) : (¬ p1976) ∨ (¬ p2608) ∨ (p2699) ∨ (p4734) := by
  classical
  tauto

theorem initial20823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (meaning t m 4734) := by
  have source := ElevenTheory.theory10079 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2)
  exact rule20823 (meaning t m 1976) (meaning t m 2608) (meaning t m 2699) (meaning t m 4734) source

theorem rule20824 (p2004 p3437 p3588 p4796 : Prop) (h : p4796 ∨ (¬ p2004) ∨ p3437 ∨ (¬ p3588)) : (¬ p2004) ∨ (p3437) ∨ (¬ p3588) ∨ (p4796) := by
  classical
  tauto

theorem initial20824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3588)) ∨ (meaning t m 4796) := by
  have source := ElevenTheory.theory10080 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 7)
  exact rule20824 (meaning t m 2004) (meaning t m 3437) (meaning t m 3588) (meaning t m 4796) source

theorem rule20825 (p1984 p2344 p3591 p5022 : Prop) (h : (¬ p1984) ∨ p5022 ∨ (¬ p3591) ∨ p2344) : (¬ p1984) ∨ (p2344) ∨ (¬ p3591) ∨ (p5022) := by
  classical
  tauto

theorem initial20825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 3591)) ∨ (meaning t m 5022) := by
  have source := ElevenTheory.theory10081 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6)
  exact rule20825 (meaning t m 1984) (meaning t m 2344) (meaning t m 3591) (meaning t m 5022) source

theorem rule20826 (p1999 p2462 p4107 p4624 : Prop) (h : p2462 ∨ (¬ p1999) ∨ (¬ p4107) ∨ p4624) : (¬ p1999) ∨ (p2462) ∨ (¬ p4107) ∨ (p4624) := by
  classical
  tauto

theorem initial20826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 4107)) ∨ (meaning t m 4624) := by
  have source := ElevenTheory.theory10082 t (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule20826 (meaning t m 1999) (meaning t m 2462) (meaning t m 4107) (meaning t m 4624) source

theorem rule20827 (p2027 p2177 p2274 p3744 p4396 p4666 : Prop) (h : (¬ p3744) ∨ (¬ p4396) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3744) ∨ (¬ p4396) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial20827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10083 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule20827 (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 3744) (meaning t m 4396) (meaning t m 4666) source

theorem rule20828 (p1989 p2027 p2563 p2766 p3880 p4173 p4347 p4506 : Prop) (h : p2766 ∨ (¬ p2563) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p4506) ∨ (¬ p4173) ∨ (¬ p1989)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2563) ∨ (p2766) ∨ (¬ p3880) ∨ (¬ p4173) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial20828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory10084 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule20828 (meaning t m 1989) (meaning t m 2027) (meaning t m 2563) (meaning t m 2766) (meaning t m 3880) (meaning t m 4173) (meaning t m 4347) (meaning t m 4506) source

theorem rule20830 (p2027 p2177 p2307 p3548 p4105 p5022 : Prop) (h : p2027 ∨ (¬ p2177) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p5022) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p5022) := by
  classical
  tauto

theorem initial20830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 5022)) := by
  have source := ElevenTheory.theory10086 t (m.theta 0 6) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20830 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 3548) (meaning t m 4105) (meaning t m 5022) source

theorem rule20831 (p2027 p2982 p3097 p4110 p4624 p5045 : Prop) (h : (¬ p4624) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p5045) ∨ (¬ p3097) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4624) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial20831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory10087 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule20831 (meaning t m 2027) (meaning t m 2982) (meaning t m 3097) (meaning t m 4110) (meaning t m 4624) (meaning t m 5045) source

theorem rule20833 (p2027 p3399 p3555 p3571 p4320 p4960 : Prop) (h : (¬ p4960) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4320) ∨ (¬ p3399)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4320) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial20833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory10089 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7)
  exact rule20833 (meaning t m 2027) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) (meaning t m 4320) (meaning t m 4960) source

theorem rule20835 (p2027 p2255 p2264 p2807 p3031 p3548 : Prop) (h : (¬ p2807) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p3548) ∨ (¬ p2264) ∨ (¬ p3031)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3031) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial20835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory10091 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8)
  exact rule20835 (meaning t m 2027) (meaning t m 2255) (meaning t m 2264) (meaning t m 2807) (meaning t m 3031) (meaning t m 3548) source

theorem rule20836 (p2027 p2255 p2341 p2996 p3553 p4104 : Prop) (h : (¬ p2255) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2341) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4104) := by
  classical
  tauto

theorem initial20836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4104)) := by
  have source := ElevenTheory.theory10092 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8)
  exact rule20836 (meaning t m 2027) (meaning t m 2255) (meaning t m 2341) (meaning t m 2996) (meaning t m 3553) (meaning t m 4104) source

theorem rule20837 (p2230 p2663 p2950 p2957 p3879 : Prop) (h : (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2950) ∨ p2957 ∨ (¬ p3879)) : (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2950) ∨ (p2957) ∨ (¬ p3879) := by
  classical
  tauto

theorem initial20837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2950)) ∨ (meaning t m 2957) ∨ (¬ (meaning t m 3879)) := by
  have source := ElevenTheory.theory10093 (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 3 5) (m.theta 4 5)
  exact rule20837 (meaning t m 2230) (meaning t m 2663) (meaning t m 2950) (meaning t m 2957) (meaning t m 3879) source

theorem rule20839 (p2951 p3497 p4120 : Prop) (h : (¬ p3497) ∨ (¬ p2951) ∨ p4120) : (¬ p2951) ∨ (¬ p3497) ∨ (p4120) := by
  classical
  tauto

theorem initial20839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 4120) := by
  have source := ElevenTheory.theory10095 (m.theta 0 5) (m.theta 3 5) (m.theta 5 8)
  exact rule20839 (meaning t m 2951) (meaning t m 3497) (meaning t m 4120) source

theorem rule20840 (p2027 p2255 p2307 p3568 p3987 p4154 : Prop) (h : (¬ p3987) ∨ (¬ p2307) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2307) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial20840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory10096 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7)
  exact rule20840 (meaning t m 2027) (meaning t m 2255) (meaning t m 2307) (meaning t m 3568) (meaning t m 3987) (meaning t m 4154) source

theorem rule20841 (p2027 p2255 p2295 p2331 p3549 p4245 : Prop) (h : (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3549) ∨ (¬ p4245) ∨ p2027) : (p2027) ∨ (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3549) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial20841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory10097 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule20841 (meaning t m 2027) (meaning t m 2255) (meaning t m 2295) (meaning t m 2331) (meaning t m 3549) (meaning t m 4245) source

theorem rule20842 (p2006 p2388 p4315 p5052 : Prop) (h : p2388 ∨ p5052 ∨ (¬ p4315) ∨ (¬ p2006)) : (¬ p2006) ∨ (p2388) ∨ (¬ p4315) ∨ (p5052) := by
  classical
  tauto

theorem initial20842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 4315)) ∨ (meaning t m 5052) := by
  have source := ElevenTheory.theory10098 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 5)
  exact rule20842 (meaning t m 2006) (meaning t m 2388) (meaning t m 4315) (meaning t m 5052) source

theorem rule20844 (p2027 p2589 p2829 p3363 p3585 p4390 p4717 : Prop) (h : (¬ p3363) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p4717) ∨ (¬ p3585) ∨ (¬ p2829) ∨ (¬ p4390)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial20844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory10100 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule20844 (meaning t m 2027) (meaning t m 2589) (meaning t m 2829) (meaning t m 3363) (meaning t m 3585) (meaning t m 4390) (meaning t m 4717) source

theorem rule20847 (p2027 p2264 p2954 p2995 p3556 p3570 : Prop) (h : p2027 ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p2995) ∨ (¬ p2264) ∨ (¬ p2954)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2954) ∨ (¬ p2995) ∨ (¬ p3556) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial20847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory10103 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule20847 (meaning t m 2027) (meaning t m 2264) (meaning t m 2954) (meaning t m 2995) (meaning t m 3556) (meaning t m 3570) source

theorem rule20849 (p2002 p2622 p2797 p4843 : Prop) (h : p4843 ∨ p2622 ∨ (¬ p2797) ∨ (¬ p2002)) : (¬ p2002) ∨ (p2622) ∨ (¬ p2797) ∨ (p4843) := by
  classical
  tauto

theorem initial20849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2797)) ∨ (meaning t m 4843) := by
  have source := ElevenTheory.theory10105 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule20849 (meaning t m 2002) (meaning t m 2622) (meaning t m 2797) (meaning t m 4843) source

theorem rule20851 (p1987 p2027 p2737 p2766 p3551 p3588 p3959 p4348 : Prop) (h : (¬ p3588) ∨ (¬ p3959) ∨ (¬ p1987) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2737) ∨ p2766 ∨ (¬ p4348)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2766) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial20851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10107 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule20851 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2766) (meaning t m 3551) (meaning t m 3588) (meaning t m 3959) (meaning t m 4348) source

theorem rule20852 (p1987 p2611 p2696 p3547 p5142 : Prop) (h : p2611 ∨ (¬ p1987) ∨ (¬ p2696) ∨ p5142 ∨ (¬ p3547)) : (¬ p1987) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3547) ∨ (p5142) := by
  classical
  tauto

theorem initial20852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3547)) ∨ (meaning t m 5142) := by
  have source := ElevenTheory.theory10108 t (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 6 7)
  exact rule20852 (meaning t m 1987) (meaning t m 2611) (meaning t m 2696) (meaning t m 3547) (meaning t m 5142) source

theorem rule20853 (p1985 p2027 p2427 p2608 p2699 p2850 p3367 : Prop) (h : p2699 ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p1985) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2608)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2850) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial20853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory10109 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule20853 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2608) (meaning t m 2699) (meaning t m 2850) (meaning t m 3367) source

theorem rule20856 (p2696 p2780 p4426 : Prop) (h : (¬ p2696) ∨ (¬ p2780) ∨ (¬ p4426)) : (¬ p2696) ∨ (¬ p2780) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial20856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory10112 (m.theta 0 2) (m.theta 2 3) (m.theta 2 6)
  exact rule20856 (meaning t m 2696) (meaning t m 2780) (meaning t m 4426) source

theorem rule20857 (p2000 p2409 p3452 p5193 : Prop) (h : p2409 ∨ p5193 ∨ (¬ p2000) ∨ (¬ p3452)) : (¬ p2000) ∨ (p2409) ∨ (¬ p3452) ∨ (p5193) := by
  classical
  tauto

theorem initial20857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 5193) := by
  have source := ElevenTheory.theory10113 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4)
  exact rule20857 (meaning t m 2000) (meaning t m 2409) (meaning t m 3452) (meaning t m 5193) source

theorem rule20858 (p2027 p2396 p2761 p4473 p5228 p5387 : Prop) (h : (¬ p5228) ∨ (¬ p4473) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p5387) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4473) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial20858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4473)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory10114 t (m.theta 2 7) (m.theta 2 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20858 (meaning t m 2027) (meaning t m 2396) (meaning t m 2761) (meaning t m 4473) (meaning t m 5228) (meaning t m 5387) source

theorem rule20859 (p1995 p2027 p2499 p2766 p3266 p4137 p4191 : Prop) (h : (¬ p1995) ∨ p2766 ∨ (¬ p2499) ∨ (¬ p4137) ∨ (¬ p3266) ∨ (¬ p4191) ∨ p2027) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial20859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory10115 t (m.theta 1 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20859 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2766) (meaning t m 3266) (meaning t m 4137) (meaning t m 4191) source

theorem rule20860 (p2027 p2707 p3585 p3658 p3742 p4753 : Prop) (h : p2027 ∨ (¬ p3658) ∨ (¬ p2707) ∨ (¬ p4753) ∨ (¬ p3742) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3742) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial20860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory10116 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7)
  exact rule20860 (meaning t m 2027) (meaning t m 2707) (meaning t m 3585) (meaning t m 3658) (meaning t m 3742) (meaning t m 4753) source

theorem rule20861 (p2027 p2588 p2707 p3688 p4475 p5225 : Prop) (h : (¬ p2707) ∨ (¬ p3688) ∨ (¬ p2588) ∨ (¬ p5225) ∨ p2027 ∨ (¬ p4475)) : (p2027) ∨ (¬ p2588) ∨ (¬ p2707) ∨ (¬ p3688) ∨ (¬ p4475) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial20861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory10117 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7)
  exact rule20861 (meaning t m 2027) (meaning t m 2588) (meaning t m 2707) (meaning t m 3688) (meaning t m 4475) (meaning t m 5225) source

theorem rule20862 (p2427 p3695 p4244 : Prop) (h : (¬ p3695) ∨ (¬ p2427) ∨ (¬ p4244)) : (¬ p2427) ∨ (¬ p3695) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial20862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory10118 (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20862 (meaning t m 2427) (meaning t m 3695) (meaning t m 4244) source

theorem rule20864 (p2027 p2396 p2761 p3232 p4276 p4321 p4635 : Prop) (h : (¬ p2761) ∨ (¬ p4635) ∨ (¬ p3232) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p4321)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3232) ∨ (¬ p4276) ∨ (¬ p4321) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial20864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory10120 t (m.theta 1 9) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20864 (meaning t m 2027) (meaning t m 2396) (meaning t m 2761) (meaning t m 3232) (meaning t m 4276) (meaning t m 4321) (meaning t m 4635) source

theorem rule20865 (p2027 p2449 p2761 p3576 p4321 p4779 p5357 : Prop) (h : (¬ p5357) ∨ (¬ p3576) ∨ (¬ p2761) ∨ (¬ p4321) ∨ (¬ p4779) ∨ p2027 ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p3576) ∨ (¬ p4321) ∨ (¬ p4779) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial20865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4779)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory10121 t (m.theta 1 7) (m.theta 1 9) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20865 (meaning t m 2027) (meaning t m 2449) (meaning t m 2761) (meaning t m 3576) (meaning t m 4321) (meaning t m 4779) (meaning t m 5357) source

theorem rule20867 (p2027 p2254 p2608 p2839 p2963 p3105 p3324 p4347 p4450 : Prop) (h : (¬ p2608) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p3324) ∨ (¬ p2963) ∨ (¬ p2254) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p2963) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial20867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory10123 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule20867 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2839) (meaning t m 2963) (meaning t m 3105) (meaning t m 3324) (meaning t m 4347) (meaning t m 4450) source

theorem rule20869 (p2002 p3008 p3584 p5224 : Prop) (h : (¬ p3584) ∨ p3008 ∨ (¬ p2002) ∨ p5224) : (¬ p2002) ∨ (p3008) ∨ (¬ p3584) ∨ (p5224) := by
  classical
  tauto

theorem initial20869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 5224) := by
  have source := ElevenTheory.theory10125 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule20869 (meaning t m 2002) (meaning t m 3008) (meaning t m 3584) (meaning t m 5224) source

theorem rule20870 (p2027 p2745 p2996 p3365 p3471 p4325 : Prop) (h : (¬ p2745) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p4325)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial20870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory10126 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7)
  exact rule20870 (meaning t m 2027) (meaning t m 2745) (meaning t m 2996) (meaning t m 3365) (meaning t m 3471) (meaning t m 4325) source

theorem rule20871 (p2027 p2352 p3422 p3876 p3921 p4405 : Prop) (h : p2027 ∨ (¬ p4405) ∨ (¬ p2352) ∨ (¬ p3876) ∨ (¬ p3422) ∨ (¬ p3921)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial20871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory10127 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule20871 (meaning t m 2027) (meaning t m 2352) (meaning t m 3422) (meaning t m 3876) (meaning t m 3921) (meaning t m 4405) source

theorem rule20873 (p2027 p2156 p2440 p2665 p4110 p4399 : Prop) (h : p2027 ∨ (¬ p2440) ∨ (¬ p4110) ∨ (¬ p2156) ∨ (¬ p4399) ∨ (¬ p2665)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2440) ∨ (¬ p2665) ∨ (¬ p4110) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial20873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory10129 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule20873 (meaning t m 2027) (meaning t m 2156) (meaning t m 2440) (meaning t m 2665) (meaning t m 4110) (meaning t m 4399) source

theorem rule20874 (p2027 p2497 p3422 p3564 p4026 p5214 : Prop) (h : (¬ p5214) ∨ (¬ p3422) ∨ (¬ p2497) ∨ (¬ p4026) ∨ (¬ p3564) ∨ p2027) : (p2027) ∨ (¬ p2497) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4026) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial20874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory10130 t (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9)
  exact rule20874 (meaning t m 2027) (meaning t m 2497) (meaning t m 3422) (meaning t m 3564) (meaning t m 4026) (meaning t m 5214) source

theorem rule20875 (p2027 p2156 p2295 p2313 p4198 p4560 : Prop) (h : (¬ p4560) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p4198) ∨ (¬ p2313) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p4198) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial20875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory10131 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule20875 (meaning t m 2027) (meaning t m 2156) (meaning t m 2295) (meaning t m 2313) (meaning t m 4198) (meaning t m 4560) source

theorem rule20876 (p2027 p2383 p2960 p2962 p3952 p3989 : Prop) (h : (¬ p2960) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p2962) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2960) ∨ (¬ p2962) ∨ (¬ p3952) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial20876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory10132 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule20876 (meaning t m 2027) (meaning t m 2383) (meaning t m 2960) (meaning t m 2962) (meaning t m 3952) (meaning t m 3989) source

theorem rule20877 (p2027 p2230 p2563 p2665 p3952 p4700 : Prop) (h : p2027 ∨ (¬ p2665) ∨ (¬ p2230) ∨ (¬ p4700) ∨ (¬ p2563) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2665) ∨ (¬ p3952) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial20877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory10133 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule20877 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 2665) (meaning t m 3952) (meaning t m 4700) source

theorem rule20879 (p2012 p2417 p2914 p4638 : Prop) (h : p2914 ∨ (¬ p2417) ∨ (¬ p2012) ∨ p4638) : (¬ p2012) ∨ (¬ p2417) ∨ (p2914) ∨ (p4638) := by
  classical
  tauto

theorem initial20879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2914) ∨ (meaning t m 4638) := by
  have source := ElevenTheory.theory10135 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule20879 (meaning t m 2012) (meaning t m 2417) (meaning t m 2914) (meaning t m 4638) source

theorem rule20882 (p2027 p2230 p2493 p2665 p3238 p3574 : Prop) (h : p2027 ∨ (¬ p2665) ∨ (¬ p2493) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2665) ∨ (¬ p3238) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial20882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory10138 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule20882 (meaning t m 2027) (meaning t m 2230) (meaning t m 2493) (meaning t m 2665) (meaning t m 3238) (meaning t m 3574) source

theorem rule20883 (p2027 p2255 p2499 p2651 p3016 p3402 : Prop) (h : (¬ p3016) ∨ (¬ p2255) ∨ (¬ p2499) ∨ (¬ p2651) ∨ (¬ p3402) ∨ p2027) : (p2027) ∨ (¬ p2255) ∨ (¬ p2499) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial20883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory10139 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule20883 (meaning t m 2027) (meaning t m 2255) (meaning t m 2499) (meaning t m 2651) (meaning t m 3016) (meaning t m 3402) source

theorem rule20885 (p2027 p2230 p2427 p2665 p4320 p4700 : Prop) (h : (¬ p4320) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p4700) ∨ (¬ p2427) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2665) ∨ (¬ p4320) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial20885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory10141 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20885 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2665) (meaning t m 4320) (meaning t m 4700) source

theorem rule20886 (p2027 p2230 p2563 p2665 p4173 p4282 p4700 : Prop) (h : (¬ p2563) ∨ (¬ p2665) ∨ (¬ p4700) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4282) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2665) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial20886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory10142 t (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule20886 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 2665) (meaning t m 4173) (meaning t m 4282) (meaning t m 4700) source

theorem rule20887 (p2247 p2696 p2742 p3589 : Prop) (h : (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2247) ∨ (¬ p3589)) : (¬ p2247) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial20887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory10143 (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 3)
  exact rule20887 (meaning t m 2247) (meaning t m 2696) (meaning t m 2742) (meaning t m 3589) source

theorem rule20888 (p2027 p2665 p2727 p2996 p3389 p3740 : Prop) (h : (¬ p3740) ∨ (¬ p2665) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3389) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial20888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory10144 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule20888 (meaning t m 2027) (meaning t m 2665) (meaning t m 2727) (meaning t m 2996) (meaning t m 3389) (meaning t m 3740) source

theorem rule20891 (p3425 p3819 p3959 : Prop) (h : (¬ p3425) ∨ (¬ p3819) ∨ (¬ p3959)) : (¬ p3425) ∨ (¬ p3819) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial20891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory10147 (m.theta 0 2) (m.theta 0 7) (m.theta 2 7)
  exact rule20891 (meaning t m 3425) (meaning t m 3819) (meaning t m 3959) source

theorem rule20893 (p3506 p5387 p5458 : Prop) (h : (¬ p3506) ∨ (¬ p5458) ∨ (¬ p5387)) : (¬ p3506) ∨ (¬ p5387) ∨ (¬ p5458) := by
  classical
  tauto

theorem initial20893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5458)) := by
  have source := ElevenTheory.theory10149 (m.theta 2 9) (m.theta 3 9) (m.theta 9 10)
  exact rule20893 (meaning t m 3506) (meaning t m 5387) (meaning t m 5458) source

theorem rule20895 (p2027 p2573 p2630 p2665 p4195 p4389 : Prop) (h : (¬ p4195) ∨ (¬ p2630) ∨ (¬ p2573) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p4389)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p4195) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial20895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory10151 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule20895 (meaning t m 2027) (meaning t m 2573) (meaning t m 2630) (meaning t m 2665) (meaning t m 4195) (meaning t m 4389) source

theorem rule20896 (p2027 p2254 p2608 p2952 p3537 p3609 p3744 p3952 p4604 : Prop) (h : (¬ p2608) ∨ (¬ p3952) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p2254) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2952) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial20896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory10152 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule20896 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2952) (meaning t m 3537) (meaning t m 3609) (meaning t m 3744) (meaning t m 3952) (meaning t m 4604) source

theorem rule20897 (p2027 p2440 p2839 p3585 p3695 p4753 : Prop) (h : p2027 ∨ (¬ p3585) ∨ (¬ p4753) ∨ (¬ p2839) ∨ (¬ p3695) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial20897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory10153 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5)
  exact rule20897 (meaning t m 2027) (meaning t m 2440) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) (meaning t m 4753) source

theorem rule20898 (p2027 p2132 p3055 p3695 p3874 p4608 : Prop) (h : p2027 ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p2132) ∨ (¬ p3874) ∨ (¬ p4608)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3695) ∨ (¬ p3874) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial20898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory10154 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 8)
  exact rule20898 (meaning t m 2027) (meaning t m 2132) (meaning t m 3055) (meaning t m 3695) (meaning t m 3874) (meaning t m 4608) source

theorem rule20899 (p2027 p2870 p3582 p3584 p4235 p4715 : Prop) (h : (¬ p2870) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p4235) ∨ (¬ p3582) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p4235) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial20899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory10155 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule20899 (meaning t m 2027) (meaning t m 2870) (meaning t m 3582) (meaning t m 3584) (meaning t m 4235) (meaning t m 4715) source

theorem rule20901 (p2027 p3506 p4278 p4381 p4653 p4661 : Prop) (h : (¬ p4661) ∨ (¬ p4653) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p4381)) : (p2027) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4653) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial20901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4653)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory10157 t (m.theta 3 7) (m.theta 3 9) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20901 (meaning t m 2027) (meaning t m 3506) (meaning t m 4278) (meaning t m 4381) (meaning t m 4653) (meaning t m 4661) source

theorem rule20902 (p2027 p2255 p2958 p2962 p3654 p4037 p4154 : Prop) (h : (¬ p2958) ∨ (¬ p2255) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2962) ∨ (¬ p4037) ∨ (¬ p3654)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial20902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory10158 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9)
  exact rule20902 (meaning t m 2027) (meaning t m 2255) (meaning t m 2958) (meaning t m 2962) (meaning t m 3654) (meaning t m 4037) (meaning t m 4154) source

theorem rule20903 (p2027 p2255 p2284 p2946 p3368 p4173 : Prop) (h : (¬ p2255) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4173) ∨ (¬ p2284) ∨ (¬ p3368)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3368) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial20903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory10159 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule20903 (meaning t m 2027) (meaning t m 2255) (meaning t m 2284) (meaning t m 2946) (meaning t m 3368) (meaning t m 4173) source

theorem rule20904 (p2027 p2437 p2630 p2745 p2928 p3402 : Prop) (h : p2027 ∨ (¬ p2745) ∨ (¬ p2928) ∨ (¬ p3402) ∨ (¬ p2630) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p2928) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial20904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory10160 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule20904 (meaning t m 2027) (meaning t m 2437) (meaning t m 2630) (meaning t m 2745) (meaning t m 2928) (meaning t m 3402) source

theorem rule20906 (p1982 p2027 p2148 p2156 p2166 p3146 p4173 : Prop) (h : (¬ p3146) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2166) ∨ (¬ p4173) ∨ (¬ p2156) ∨ p2148) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial20906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory10162 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule20906 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2166) (meaning t m 3146) (meaning t m 4173) source

theorem rule20907 (p1991 p2545 p2655 p2657 p2664 : Prop) (h : (¬ p1991) ∨ (¬ p2657) ∨ p2545 ∨ p2664 ∨ (¬ p2655)) : (¬ p1991) ∨ (p2545) ∨ (¬ p2655) ∨ (¬ p2657) ∨ (p2664) := by
  classical
  tauto

theorem initial20907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2664) := by
  have source := ElevenTheory.theory10163 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4)
  exact rule20907 (meaning t m 1991) (meaning t m 2545) (meaning t m 2655) (meaning t m 2657) (meaning t m 2664) source

theorem rule20908 (p2027 p2321 p2341 p3309 p3923 p4138 : Prop) (h : (¬ p2321) ∨ p2027 ∨ (¬ p4138) ∨ (¬ p2341) ∨ (¬ p3923) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial20908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2321)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory10164 t (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule20908 (meaning t m 2027) (meaning t m 2321) (meaning t m 2341) (meaning t m 3309) (meaning t m 3923) (meaning t m 4138) source

theorem rule20909 (p2027 p3073 p3692 p3880 p4496 p4632 : Prop) (h : (¬ p3880) ∨ (¬ p4632) ∨ (¬ p4496) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4496) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial20909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory10165 t (m.theta 1 5) (m.theta 1 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule20909 (meaning t m 2027) (meaning t m 3073) (meaning t m 3692) (meaning t m 3880) (meaning t m 4496) (meaning t m 4632) source

theorem rule20911 (p2027 p2982 p3817 p4135 p4235 p4911 : Prop) (h : p2027 ∨ (¬ p2982) ∨ (¬ p4911) ∨ (¬ p3817) ∨ (¬ p4235) ∨ (¬ p4135)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3817) ∨ (¬ p4135) ∨ (¬ p4235) ∨ (¬ p4911) := by
  classical
  tauto

theorem initial20911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4911)) := by
  have source := ElevenTheory.theory10167 t (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule20911 (meaning t m 2027) (meaning t m 2982) (meaning t m 3817) (meaning t m 4135) (meaning t m 4235) (meaning t m 4911) source

theorem rule20914 (p1994 p2027 p2169 p2651 p2952 p3879 p3989 p4110 : Prop) (h : (¬ p3879) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p1994) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p4110)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial20914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory10170 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule20914 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2651) (meaning t m 2952) (meaning t m 3879) (meaning t m 3989) (meaning t m 4110) source

theorem rule20916 (p2027 p2254 p2608 p2707 p2952 p3434 p3744 p3952 p4625 : Prop) (h : (¬ p3434) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p2608) ∨ (¬ p2952) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial20916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory10172 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule20916 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2952) (meaning t m 3434) (meaning t m 3744) (meaning t m 3952) (meaning t m 4625) source

theorem rule20917 (p2011 p2166 p2873 p3146 p4450 : Prop) (h : p2873 ∨ p4450 ∨ (¬ p3146) ∨ (¬ p2166) ∨ (¬ p2011)) : (¬ p2011) ∨ (¬ p2166) ∨ (p2873) ∨ (¬ p3146) ∨ (p4450) := by
  classical
  tauto

theorem initial20917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 4450) := by
  have source := ElevenTheory.theory10173 t (m.theta 1 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule20917 (meaning t m 2011) (meaning t m 2166) (meaning t m 2873) (meaning t m 3146) (meaning t m 4450) source

theorem rule20919 (p2027 p2254 p2534 p2608 p2657 p2829 p3483 p4256 p4330 : Prop) (h : (¬ p2829) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3483) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4256) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2657) ∨ (¬ p2829) ∨ (¬ p3483) ∨ (¬ p4256) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial20919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory10175 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule20919 (meaning t m 2027) (meaning t m 2254) (meaning t m 2534) (meaning t m 2608) (meaning t m 2657) (meaning t m 2829) (meaning t m 3483) (meaning t m 4256) (meaning t m 4330) source

theorem rule20921 (p1975 p2027 p2202 p2299 p2319 p2341 p2578 p3422 p3684 : Prop) (h : (¬ p2319) ∨ (¬ p3422) ∨ (¬ p1975) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p2578) ∨ (¬ p2299) ∨ p2202 ∨ (¬ p3684)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial20921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory10177 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule20921 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2578) (meaning t m 3422) (meaning t m 3684) source

theorem rule20924 (p2008 p2707 p3623 p4793 : Prop) (h : (¬ p2707) ∨ (¬ p2008) ∨ p4793 ∨ p3623) : (¬ p2008) ∨ (¬ p2707) ∨ (p3623) ∨ (p4793) := by
  classical
  tauto

theorem initial20924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 3623) ∨ (meaning t m 4793) := by
  have source := ElevenTheory.theory10180 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 7)
  exact rule20924 (meaning t m 2008) (meaning t m 2707) (meaning t m 3623) (meaning t m 4793) source

theorem rule20925 (p2027 p2608 p3367 p4366 p4424 p5082 : Prop) (h : (¬ p2608) ∨ p2027 ∨ (¬ p4424) ∨ (¬ p3367) ∨ (¬ p4366) ∨ (¬ p5082)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p5082) := by
  classical
  tauto

theorem initial20925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 5082)) := by
  have source := ElevenTheory.theory10181 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7)
  exact rule20925 (meaning t m 2027) (meaning t m 2608) (meaning t m 3367) (meaning t m 4366) (meaning t m 4424) (meaning t m 5082) source

theorem rule20926 (p2027 p2088 p2482 p2534 p2665 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2088) ∨ (¬ p2482)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (¬ p2665) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial20926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory10182 t (m.theta 0 4) (m.theta 0 8) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule20926 (meaning t m 2027) (meaning t m 2088) (meaning t m 2482) (meaning t m 2534) (meaning t m 2665) (meaning t m 4256) source

theorem rule20929 (p2027 p2295 p2321 p3516 p4037 p4396 : Prop) (h : (¬ p4396) ∨ (¬ p2295) ∨ (¬ p2321) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2321) ∨ (¬ p3516) ∨ (¬ p4037) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial20929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2321)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory10185 t (m.theta 0 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule20929 (meaning t m 2027) (meaning t m 2295) (meaning t m 2321) (meaning t m 3516) (meaning t m 4037) (meaning t m 4396) source

theorem rule20930 (p1992 p2608 p2699 p3573 p4598 : Prop) (h : (¬ p2608) ∨ (¬ p1992) ∨ p2699 ∨ p4598 ∨ (¬ p3573)) : (¬ p1992) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3573) ∨ (p4598) := by
  classical
  tauto

theorem initial20930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3573)) ∨ (meaning t m 4598) := by
  have source := ElevenTheory.theory10186 t (m.theta 0 1) (m.theta 1 2) (m.theta 4 6) (m.theta 4 8)
  exact rule20930 (meaning t m 1992) (meaning t m 2608) (meaning t m 2699) (meaning t m 3573) (meaning t m 4598) source

theorem rule20932 (p2027 p2665 p2927 p3389 p3527 p3553 p4112 : Prop) (h : (¬ p4112) ∨ (¬ p2927) ∨ (¬ p3527) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2665) ∨ (¬ p2927) ∨ (¬ p3389) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial20932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory10188 t (m.theta 0 4) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule20932 (meaning t m 2027) (meaning t m 2665) (meaning t m 2927) (meaning t m 3389) (meaning t m 3527) (meaning t m 3553) (meaning t m 4112) source

theorem rule20933 (p2780 p3689 p3819 p3959 : Prop) (h : (¬ p2780) ∨ (¬ p3689) ∨ (¬ p3959) ∨ (¬ p3819)) : (¬ p2780) ∨ (¬ p3689) ∨ (¬ p3819) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial20933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory10189 (m.theta 0 2) (m.theta 0 7) (m.theta 2 6) (m.theta 2 7)
  exact rule20933 (meaning t m 2780) (meaning t m 3689) (meaning t m 3819) (meaning t m 3959) source

theorem rule20936 (p2005 p2027 p2307 p2387 p2588 p2766 p4138 p4348 : Prop) (h : (¬ p2005) ∨ (¬ p4348) ∨ p2766 ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p4138)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (p2766) ∨ (¬ p4138) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial20936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10192 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20936 (meaning t m 2005) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2588) (meaning t m 2766) (meaning t m 4138) (meaning t m 4348) source

theorem rule20937 (p2027 p2255 p2470 p2663 p4111 p4256 : Prop) (h : (¬ p2470) ∨ (¬ p2663) ∨ (¬ p4111) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p4256)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p4111) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial20937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory10193 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8)
  exact rule20937 (meaning t m 2027) (meaning t m 2255) (meaning t m 2470) (meaning t m 2663) (meaning t m 4111) (meaning t m 4256) source

theorem rule20940 (p1989 p3474 p3583 p4877 : Prop) (h : p4877 ∨ p3474 ∨ (¬ p1989) ∨ (¬ p3583)) : (¬ p1989) ∨ (p3474) ∨ (¬ p3583) ∨ (p4877) := by
  classical
  tauto

theorem initial20940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3583)) ∨ (meaning t m 4877) := by
  have source := ElevenTheory.theory10196 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 5)
  exact rule20940 (meaning t m 1989) (meaning t m 3474) (meaning t m 3583) (meaning t m 4877) source

theorem rule20952 (p2027 p2255 p2383 p3324 p3987 p4154 : Prop) (h : (¬ p3324) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p3987) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial20952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory10208 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8)
  exact rule20952 (meaning t m 2027) (meaning t m 2255) (meaning t m 2383) (meaning t m 3324) (meaning t m 3987) (meaning t m 4154) source

theorem rule20954 (p2027 p2383 p2437 p2578 p3324 p4194 p4711 : Prop) (h : (¬ p4194) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3324) ∨ (¬ p4711) ∨ (¬ p2578)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2437) ∨ (¬ p2578) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial20954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory10210 t (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule20954 (meaning t m 2027) (meaning t m 2383) (meaning t m 2437) (meaning t m 2578) (meaning t m 3324) (meaning t m 4194) (meaning t m 4711) source

theorem rule20955 (p2027 p2248 p2928 p2946 p3146 p3156 p3452 p4278 p4669 : Prop) (h : (¬ p4278) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p3146) ∨ (¬ p4669) ∨ (¬ p3156) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial20955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10211 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule20955 (meaning t m 2027) (meaning t m 2248) (meaning t m 2928) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3452) (meaning t m 4278) (meaning t m 4669) source

theorem rule20957 (p2248 p2958 p4521 : Prop) (h : (¬ p2248) ∨ (¬ p2958) ∨ p4521) : (¬ p2248) ∨ (¬ p2958) ∨ (p4521) := by
  classical
  tauto

theorem initial20957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2958)) ∨ (meaning t m 4521) := by
  have source := ElevenTheory.theory10213 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5)
  exact rule20957 (meaning t m 2248) (meaning t m 2958) (meaning t m 4521) source

theorem rule20959 (p2667 p3743 p3745 : Prop) (h : p3745 ∨ (¬ p2667) ∨ (¬ p3743)) : (¬ p2667) ∨ (¬ p3743) ∨ (p3745) := by
  classical
  tauto

theorem initial20959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3743)) ∨ (meaning t m 3745) := by
  have source := ElevenTheory.theory10215 (m.theta 0 6) (m.theta 3 6) (m.theta 5 6)
  exact rule20959 (meaning t m 2667) (meaning t m 3743) (meaning t m 3745) source

theorem rule20961 (p2027 p2248 p2946 p3146 p3156 p3588 p3954 p4324 p4669 : Prop) (h : (¬ p3146) ∨ (¬ p2946) ∨ (¬ p3588) ∨ (¬ p2248) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p4669) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial20961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory10217 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule20961 (meaning t m 2027) (meaning t m 2248) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4669) source

theorem rule20962 (p1975 p2027 p2202 p2417 p2922 p3238 p4107 : Prop) (h : (¬ p3238) ∨ p2202 ∨ (¬ p4107) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p1975) ∨ (¬ p2417)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial20962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory10218 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule20962 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 2922) (meaning t m 3238) (meaning t m 4107) source

theorem rule20963 (p2011 p2027 p2202 p3333 p3684 p3767 p4322 p5182 : Prop) (h : (¬ p2011) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p5182) ∨ (¬ p3333) ∨ (¬ p3767) ∨ p2202 ∨ (¬ p4322)) : (¬ p2011) ∨ (p2027) ∨ (p2202) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p5182) := by
  classical
  tauto

theorem initial20963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5182)) := by
  have source := ElevenTheory.theory10219 t (m.theta 0 9) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule20963 (meaning t m 2011) (meaning t m 2027) (meaning t m 2202) (meaning t m 3333) (meaning t m 3684) (meaning t m 3767) (meaning t m 4322) (meaning t m 5182) source

theorem rule20964 (p2027 p2753 p3471 p3585 p3658 p3742 p4753 : Prop) (h : (¬ p3658) ∨ (¬ p3585) ∨ (¬ p3471) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3742) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial20964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory10220 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7)
  exact rule20964 (meaning t m 2027) (meaning t m 2753) (meaning t m 3471) (meaning t m 3585) (meaning t m 3658) (meaning t m 3742) (meaning t m 4753) source

theorem rule20965 (p2015 p2027 p2287 p2743 p3093 p3954 p4195 : Prop) (h : (¬ p3954) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2015) ∨ (¬ p3093) ∨ p2287 ∨ (¬ p4195)) : (¬ p2015) ∨ (p2027) ∨ (p2287) ∨ (¬ p2743) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial20965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory10221 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6)
  exact rule20965 (meaning t m 2015) (meaning t m 2027) (meaning t m 2287) (meaning t m 2743) (meaning t m 3093) (meaning t m 3954) (meaning t m 4195) source

theorem rule20969 (p2027 p3063 p3461 p4321 p4430 p4601 : Prop) (h : (¬ p4601) ∨ (¬ p3063) ∨ (¬ p4430) ∨ (¬ p4321) ∨ p2027 ∨ (¬ p3461)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3461) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4601) := by
  classical
  tauto

theorem initial20969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4430)) ∨ (¬ (meaning t m 4601)) := by
  have source := ElevenTheory.theory10225 t (m.theta 1 6) (m.theta 1 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule20969 (meaning t m 2027) (meaning t m 3063) (meaning t m 3461) (meaning t m 4321) (meaning t m 4430) (meaning t m 4601) source

theorem rule20970 (p1986 p2027 p2766 p3266 p3644 p3657 p3876 p4381 : Prop) (h : (¬ p4381) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p3644) ∨ p2766 ∨ (¬ p3657) ∨ (¬ p1986) ∨ (¬ p3876)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3644) ∨ (¬ p3657) ∨ (¬ p3876) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial20970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory10226 t (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20970 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3644) (meaning t m 3657) (meaning t m 3876) (meaning t m 4381) source

theorem rule20971 (p2027 p2417 p2922 p3821 p5191 p5197 : Prop) (h : (¬ p3821) ∨ (¬ p5197) ∨ (¬ p5191) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3821) ∨ (¬ p5191) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial20971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5191)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory10227 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 4 7) (m.theta 7 9)
  exact rule20971 (meaning t m 2027) (meaning t m 2417) (meaning t m 2922) (meaning t m 3821) (meaning t m 5191) (meaning t m 5197) source

theorem rule20973 (p2023 p3360 p3527 p3546 p4832 : Prop) (h : (¬ p3527) ∨ p3360 ∨ (¬ p2023) ∨ p4832 ∨ (¬ p3546)) : (¬ p2023) ∨ (p3360) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (p4832) := by
  classical
  tauto

theorem initial20973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3546)) ∨ (meaning t m 4832) := by
  have source := ElevenTheory.theory10229 t (m.theta 0 7) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule20973 (meaning t m 2023) (meaning t m 3360) (meaning t m 3527) (meaning t m 3546) (meaning t m 4832) source

theorem rule20974 (p1992 p2027 p2449 p2633 p2743 p3361 p3553 p3821 p4849 : Prop) (h : (¬ p1992) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p4849) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p3821) ∨ (¬ p3553) ∨ p2633) : (¬ p1992) ∨ (p2027) ∨ (¬ p2449) ∨ (p2633) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial20974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory10230 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule20974 (meaning t m 1992) (meaning t m 2027) (meaning t m 2449) (meaning t m 2633) (meaning t m 2743) (meaning t m 3361) (meaning t m 3553) (meaning t m 3821) (meaning t m 4849) source

theorem rule20976 (p2027 p2743 p2810 p3599 p5177 p5458 : Prop) (h : (¬ p3599) ∨ (¬ p5458) ∨ (¬ p5177) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3599) ∨ (¬ p5177) ∨ (¬ p5458) := by
  classical
  tauto

theorem initial20976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 5177)) ∨ (¬ (meaning t m 5458)) := by
  have source := ElevenTheory.theory10232 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 9) (m.theta 3 4) (m.theta 3 9)
  exact rule20976 (meaning t m 2027) (meaning t m 2743) (meaning t m 2810) (meaning t m 3599) (meaning t m 5177) (meaning t m 5458) source

theorem rule20978 (p2027 p2307 p2584 p2588 p2589 p4717 : Prop) (h : p2027 ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p2307) ∨ (¬ p4717)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial20978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory10234 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule20978 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 2589) (meaning t m 4717) source

theorem rule20979 (p2027 p2459 p3266 p3440 p4321 p4832 : Prop) (h : (¬ p2459) ∨ (¬ p3440) ∨ (¬ p4832) ∨ p2027 ∨ (¬ p4321) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p3440) ∨ (¬ p4321) ∨ (¬ p4832) := by
  classical
  tauto

theorem initial20979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4832)) := by
  have source := ElevenTheory.theory10235 t (m.theta 1 8) (m.theta 1 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule20979 (meaning t m 2027) (meaning t m 2459) (meaning t m 3266) (meaning t m 3440) (meaning t m 4321) (meaning t m 4832) source

theorem rule20981 (p1982 p2027 p2761 p2997 p3063 p3549 p3550 p3945 p4444 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p1982) ∨ (¬ p4444) ∨ (¬ p3550) ∨ (¬ p3549) ∨ (¬ p3063)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2761) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p3945) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial20981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory10237 t (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20981 (meaning t m 1982) (meaning t m 2027) (meaning t m 2761) (meaning t m 2997) (meaning t m 3063) (meaning t m 3549) (meaning t m 3550) (meaning t m 3945) (meaning t m 4444) source

theorem rule20982 (p2015 p2027 p2307 p2387 p2766 p3549 p4347 : Prop) (h : p2766 ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2015) ∨ (¬ p4347) ∨ (¬ p3549) ∨ (¬ p2387)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (p2766) ∨ (¬ p3549) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial20982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory10238 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule20982 (meaning t m 2015) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2766) (meaning t m 3549) (meaning t m 4347) source

theorem rule20986 (p2027 p3461 p3990 p4261 p4444 p4995 : Prop) (h : (¬ p4995) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p3990) ∨ (¬ p3461)) : (p2027) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4261) ∨ (¬ p4444) ∨ (¬ p4995) := by
  classical
  tauto

theorem initial20986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4995)) := by
  have source := ElevenTheory.theory10242 t (m.theta 1 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20986 (meaning t m 2027) (meaning t m 3461) (meaning t m 3990) (meaning t m 4261) (meaning t m 4444) (meaning t m 4995) source

theorem rule20987 (p2027 p2166 p2363 p3949 p4363 p4433 : Prop) (h : (¬ p4363) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p3949) ∨ (¬ p2166) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2363) ∨ (¬ p3949) ∨ (¬ p4363) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial20987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory10243 t (m.theta 1 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule20987 (meaning t m 2027) (meaning t m 2166) (meaning t m 2363) (meaning t m 3949) (meaning t m 4363) (meaning t m 4433) source

theorem rule20988 (p2027 p2363 p3166 p3292 p4771 p5107 : Prop) (h : (¬ p2363) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p4771) ∨ (¬ p3166) ∨ (¬ p5107)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p4771) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial20988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory10244 t (m.theta 0 3) (m.theta 3 8) (m.theta 3 9) (m.theta 6 8) (m.theta 8 9)
  exact rule20988 (meaning t m 2027) (meaning t m 2363) (meaning t m 3166) (meaning t m 3292) (meaning t m 4771) (meaning t m 5107) source

theorem rule20991 (p2027 p2641 p2957 p3556 p3662 p3986 p4555 : Prop) (h : (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4555) ∨ (¬ p3986) ∨ (¬ p3556) ∨ (¬ p2641) ∨ p2027) : (p2027) ∨ (¬ p2641) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial20991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory10247 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule20991 (meaning t m 2027) (meaning t m 2641) (meaning t m 2957) (meaning t m 3556) (meaning t m 3662) (meaning t m 3986) (meaning t m 4555) source

theorem rule20992 (p1998 p2027 p2210 p2699 p2891 p3146 p3747 p4348 : Prop) (h : p2027 ∨ (¬ p1998) ∨ p2699 ∨ (¬ p2210) ∨ (¬ p4348) ∨ (¬ p3747) ∨ (¬ p2891) ∨ (¬ p3146)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial20992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory10248 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20992 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2891) (meaning t m 3146) (meaning t m 3747) (meaning t m 4348) source

theorem rule20993 (p2027 p3073 p3989 p4317 p4347 p4518 : Prop) (h : (¬ p3989) ∨ (¬ p4518) ∨ (¬ p4317) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p4347)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3989) ∨ (¬ p4317) ∨ (¬ p4347) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial20993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory10249 t (m.theta 1 6) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule20993 (meaning t m 2027) (meaning t m 3073) (meaning t m 3989) (meaning t m 4317) (meaning t m 4347) (meaning t m 4518) source

theorem rule20994 (p2027 p2254 p2470 p2528 p2797 p2963 p3692 p3877 p4041 p4042 p4079 : Prop) (h : (¬ p4079) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p2254) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p3692) ∨ (¬ p4042) ∨ p2027) : (p2027) ∨ (¬ p2254) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3692) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4042) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial20994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory10250 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20994 (meaning t m 2027) (meaning t m 2254) (meaning t m 2470) (meaning t m 2528) (meaning t m 2797) (meaning t m 2963) (meaning t m 3692) (meaning t m 3877) (meaning t m 4041) (meaning t m 4042) (meaning t m 4079) source

theorem rule20996 (p2027 p3527 p3583 p3659 p3687 p4897 : Prop) (h : (¬ p3659) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p3687) ∨ (¬ p3527) ∨ (¬ p4897)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3583) ∨ (¬ p3659) ∨ (¬ p3687) ∨ (¬ p4897) := by
  classical
  tauto

theorem initial20996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4897)) := by
  have source := ElevenTheory.theory10252 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 5) (m.theta 2 7) (m.theta 7 8)
  exact rule20996 (meaning t m 2027) (meaning t m 3527) (meaning t m 3583) (meaning t m 3659) (meaning t m 3687) (meaning t m 4897) source

theorem rule20999 (p2027 p2254 p2952 p3471 p3537 p3588 p3589 p3952 p3989 p4859 : Prop) (h : (¬ p3952) ∨ (¬ p4859) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p3537) ∨ (¬ p2952) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3589)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3471) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3589) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4859) := by
  classical
  tauto

theorem initial20999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4859)) := by
  have source := ElevenTheory.theory10255 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule20999 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3471) (meaning t m 3537) (meaning t m 3588) (meaning t m 3589) (meaning t m 3952) (meaning t m 3989) (meaning t m 4859) source

theorem rule21000 (p2027 p2254 p2952 p3097 p3399 p3527 p3659 p3952 p4473 : Prop) (h : p2027 ∨ (¬ p3527) ∨ (¬ p3952) ∨ (¬ p2254) ∨ (¬ p3399) ∨ (¬ p3097) ∨ (¬ p2952) ∨ (¬ p3659) ∨ (¬ p4473)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3952) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial21000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory10256 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule21000 (meaning t m 2027) (meaning t m 2254) (meaning t m 2952) (meaning t m 3097) (meaning t m 3399) (meaning t m 3527) (meaning t m 3659) (meaning t m 3952) (meaning t m 4473) source

theorem rule21001 (p2027 p2254 p2608 p2707 p2717 p2952 p3690 p4320 p4666 : Prop) (h : (¬ p2608) ∨ (¬ p4666) ∨ (¬ p3690) ∨ (¬ p2707) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10257 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21001 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 2952) (meaning t m 3690) (meaning t m 4320) (meaning t m 4666) source

theorem rule21002 (p2027 p2313 p2383 p3550 p4107 p4666 : Prop) (h : (¬ p4666) ∨ p2027 ∨ (¬ p3550) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10258 t (m.theta 0 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule21002 (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3550) (meaning t m 4107) (meaning t m 4666) source

theorem rule21003 (p2027 p2470 p2528 p2665 p4118 p4194 p4196 : Prop) (h : (¬ p2665) ∨ (¬ p4196) ∨ (¬ p4194) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p2528) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2665) ∨ (¬ p4118) ∨ (¬ p4194) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial21003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory10259 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule21003 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2665) (meaning t m 4118) (meaning t m 4194) (meaning t m 4196) source

theorem rule21005 (p2027 p2761 p3527 p4321 p4666 p5357 : Prop) (h : (¬ p3527) ∨ (¬ p5357) ∨ (¬ p2761) ∨ (¬ p4321) ∨ (¬ p4666) ∨ p2027) : (p2027) ∨ (¬ p2761) ∨ (¬ p3527) ∨ (¬ p4321) ∨ (¬ p4666) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial21005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory10261 t (m.theta 1 7) (m.theta 1 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule21005 (meaning t m 2027) (meaning t m 2761) (meaning t m 3527) (meaning t m 4321) (meaning t m 4666) (meaning t m 5357) source

theorem rule21006 (p2027 p2098 p2745 p3365 p4078 p4154 p4328 : Prop) (h : (¬ p4154) ∨ (¬ p2745) ∨ (¬ p4328) ∨ (¬ p2098) ∨ (¬ p4078) ∨ (¬ p3365) ∨ p2027) : (p2027) ∨ (¬ p2098) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p4078) ∨ (¬ p4154) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial21006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory10262 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 6)
  exact rule21006 (meaning t m 2027) (meaning t m 2098) (meaning t m 2745) (meaning t m 3365) (meaning t m 4078) (meaning t m 4154) (meaning t m 4328) source

theorem rule21007 (p2027 p2383 p3324 p3414 p3987 p4569 : Prop) (h : (¬ p3414) ∨ p2027 ∨ (¬ p4569) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p3414) ∨ (¬ p3987) ∨ (¬ p4569) := by
  classical
  tauto

theorem initial21007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4569)) := by
  have source := ElevenTheory.theory10263 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 8)
  exact rule21007 (meaning t m 2027) (meaning t m 2383) (meaning t m 3324) (meaning t m 3414) (meaning t m 3987) (meaning t m 4569) source

theorem rule21009 (p2027 p2470 p2501 p2656 p3574 p3923 p4157 : Prop) (h : (¬ p2656) ∨ (¬ p2501) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p4157) ∨ (¬ p3923) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2501) ∨ (¬ p2656) ∨ (¬ p3574) ∨ (¬ p3923) ∨ (¬ p4157) := by
  classical
  tauto

theorem initial21009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4157)) := by
  have source := ElevenTheory.theory10265 t (m.theta 0 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule21009 (meaning t m 2027) (meaning t m 2470) (meaning t m 2501) (meaning t m 2656) (meaning t m 3574) (meaning t m 3923) (meaning t m 4157) source

theorem rule21010 (p2027 p2254 p2608 p2707 p2952 p3434 p3497 p3692 p3950 : Prop) (h : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3950) ∨ (¬ p3692) ∨ (¬ p3434) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial21010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory10266 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21010 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2952) (meaning t m 3434) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule21011 (p2027 p3063 p3588 p4358 p4472 p4869 : Prop) (h : (¬ p3588) ∨ (¬ p4869) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p3063) ∨ (¬ p4472)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3588) ∨ (¬ p4358) ∨ (¬ p4472) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial21011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4472)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory10267 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 8)
  exact rule21011 (meaning t m 2027) (meaning t m 3063) (meaning t m 3588) (meaning t m 4358) (meaning t m 4472) (meaning t m 4869) source

theorem rule21014 (p1979 p2027 p2220 p2274 p2313 p2765 p3497 p4198 : Prop) (h : (¬ p2313) ∨ (¬ p4198) ∨ p2027 ∨ (¬ p2274) ∨ p2765 ∨ (¬ p2220) ∨ (¬ p1979) ∨ (¬ p3497)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p3497) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial21014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory10270 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule21014 (meaning t m 1979) (meaning t m 2027) (meaning t m 2220) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 3497) (meaning t m 4198) source

theorem rule21015 (p2027 p2274 p2313 p2957 p3156 p4198 p4509 : Prop) (h : (¬ p2313) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p4198) ∨ (¬ p4509) ∨ (¬ p2957)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2957) ∨ (¬ p3156) ∨ (¬ p4198) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial21015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory10271 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule21015 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2957) (meaning t m 3156) (meaning t m 4198) (meaning t m 4509) source

theorem rule21016 (p2008 p2027 p2177 p2611 p2774 p3309 p3659 p3918 : Prop) (h : p2611 ∨ (¬ p2008) ∨ (¬ p3659) ∨ (¬ p2177) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3918)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2177) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3659) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial21016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory10272 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21016 (meaning t m 2008) (meaning t m 2027) (meaning t m 2177) (meaning t m 2611) (meaning t m 2774) (meaning t m 3309) (meaning t m 3659) (meaning t m 3918) source

theorem rule21019 (p2027 p3449 p3570 p4366 p4914 p5307 : Prop) (h : (¬ p4366) ∨ (¬ p4914) ∨ p2027 ∨ (¬ p5307) ∨ (¬ p3570) ∨ (¬ p3449)) : (p2027) ∨ (¬ p3449) ∨ (¬ p3570) ∨ (¬ p4366) ∨ (¬ p4914) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial21019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4914)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory10275 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 5 7) (m.theta 7 8)
  exact rule21019 (meaning t m 2027) (meaning t m 3449) (meaning t m 3570) (meaning t m 4366) (meaning t m 4914) (meaning t m 5307) source

theorem rule21020 (p2027 p2248 p2284 p2509 p2534 p2946 p3125 p3452 p4330 : Prop) (h : (¬ p3452) ∨ (¬ p4330) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p2534) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial21020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory10276 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule21020 (meaning t m 2027) (meaning t m 2248) (meaning t m 2284) (meaning t m 2509) (meaning t m 2534) (meaning t m 2946) (meaning t m 3125) (meaning t m 3452) (meaning t m 4330) source

theorem rule21023 (p1984 p2027 p2764 p3055 p3367 p3873 p4379 p5387 : Prop) (h : (¬ p3873) ∨ p2764 ∨ (¬ p3367) ∨ (¬ p3055) ∨ (¬ p4379) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p5387)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3873) ∨ (¬ p4379) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial21023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory10279 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 9) (m.theta 9 10)
  exact rule21023 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3055) (meaning t m 3367) (meaning t m 3873) (meaning t m 4379) (meaning t m 5387) source

theorem rule21025 (p2319 p2341 p2383 p4138 : Prop) (h : (¬ p2341) ∨ (¬ p4138) ∨ (¬ p2319) ∨ p2383) : (¬ p2319) ∨ (¬ p2341) ∨ (p2383) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial21025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2383) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory10281 (m.theta 0 6) (m.theta 0 7) (m.theta 6 8) (m.theta 7 8)
  exact rule21025 (meaning t m 2319) (meaning t m 2341) (meaning t m 2383) (meaning t m 4138) source

theorem rule21027 (p1977 p2027 p2299 p2396 p2633 p2996 p3947 : Prop) (h : (¬ p2299) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3947) ∨ p2633 ∨ (¬ p1977) ∨ (¬ p2996)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial21027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory10283 t (m.theta 1 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21027 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 2996) (meaning t m 3947) source

theorem rule21030 (p2027 p2264 p2807 p3292 p4656 p4666 : Prop) (h : (¬ p4666) ∨ p2027 ∨ (¬ p3292) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p4656)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p4656) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial21030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4656)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory10286 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 8) (m.theta 7 9)
  exact rule21030 (meaning t m 2027) (meaning t m 2264) (meaning t m 2807) (meaning t m 3292) (meaning t m 4656) (meaning t m 4666) source

theorem rule21031 (p3051 p4109 p4110 p4204 : Prop) (h : (¬ p4109) ∨ (¬ p3051) ∨ (¬ p4110) ∨ (¬ p4204)) : (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4110) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial21031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory10287 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule21031 (meaning t m 3051) (meaning t m 4109) (meaning t m 4110) (meaning t m 4204) source

theorem rule21035 (p2027 p3276 p3358 p4347 p4384 p4444 : Prop) (h : (¬ p4347) ∨ (¬ p3358) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4384) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial21035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory10291 t (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule21035 (meaning t m 2027) (meaning t m 3276) (meaning t m 3358) (meaning t m 4347) (meaning t m 4384) (meaning t m 4444) source

theorem rule21036 (p1977 p2027 p2462 p2662 p2761 p3346 p4111 p4425 : Prop) (h : (¬ p3346) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p1977) ∨ (¬ p2662) ∨ p2462 ∨ (¬ p2761)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2662) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial21036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory10292 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21036 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2662) (meaning t m 2761) (meaning t m 3346) (meaning t m 4111) (meaning t m 4425) source

theorem rule21037 (p2027 p2363 p3577 p3685 p4063 p4138 p4340 p5564 : Prop) (h : (¬ p2363) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p4138) ∨ (¬ p5564) ∨ (¬ p3685) ∨ (¬ p3577) ∨ (¬ p4063)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3577) ∨ (¬ p3685) ∨ (¬ p4063) ∨ (¬ p4138) ∨ (¬ p4340) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial21037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory10293 t (m.theta 0 7) (m.theta 2 7) (m.theta 2 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule21037 (meaning t m 2027) (meaning t m 2363) (meaning t m 3577) (meaning t m 3685) (meaning t m 4063) (meaning t m 4138) (meaning t m 4340) (meaning t m 5564) source

theorem rule21038 (p2027 p2255 p2509 p2651 p3083 p3402 : Prop) (h : (¬ p2255) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3402)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2509) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial21038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory10294 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 8)
  exact rule21038 (meaning t m 2027) (meaning t m 2255) (meaning t m 2509) (meaning t m 2651) (meaning t m 3083) (meaning t m 3402) source

theorem rule21044 (p2027 p2255 p2331 p2668 p3923 p4245 : Prop) (h : (¬ p2331) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p3923) ∨ (¬ p2668) ∨ (¬ p4245)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3923) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial21044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory10300 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 8)
  exact rule21044 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2668) (meaning t m 3923) (meaning t m 4245) source

theorem rule21045 (p2027 p2255 p2573 p2663 p3574 p4111 : Prop) (h : (¬ p2255) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2573) ∨ (¬ p3574) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3574) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial21045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory10301 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6)
  exact rule21045 (meaning t m 2027) (meaning t m 2255) (meaning t m 2573) (meaning t m 2663) (meaning t m 3574) (meaning t m 4111) source

theorem rule21046 (p2027 p2255 p2957 p3073 p3166 p3556 p3570 p3662 p4133 p4347 p5074 : Prop) (h : (¬ p3662) ∨ (¬ p3166) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p5074) ∨ (¬ p3570) ∨ (¬ p2957) ∨ (¬ p4347) ∨ (¬ p3556) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2957) ∨ (¬ p3073) ∨ (¬ p3166) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial21046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory10302 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21046 (meaning t m 2027) (meaning t m 2255) (meaning t m 2957) (meaning t m 3073) (meaning t m 3166) (meaning t m 3556) (meaning t m 3570) (meaning t m 3662) (meaning t m 4133) (meaning t m 4347) (meaning t m 5074) source

theorem rule21048 (p2027 p2088 p2255 p3987 p4114 p4118 p4360 : Prop) (h : (¬ p3987) ∨ (¬ p4114) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p2255) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2255) ∨ (¬ p3987) ∨ (¬ p4114) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial21048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory10304 t (m.theta 0 3) (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 3 8) (m.theta 8 9)
  exact rule21048 (meaning t m 2027) (meaning t m 2088) (meaning t m 2255) (meaning t m 3987) (meaning t m 4114) (meaning t m 4118) (meaning t m 4360) source

theorem rule21051 (p2027 p2255 p2331 p2957 p3319 p3461 p3662 p4120 p4319 p5123 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p4120) ∨ (¬ p2957) ∨ p2027 ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p3461) ∨ (¬ p4319) ∨ (¬ p3662) ∨ (¬ p5123) ∨ (¬ p3319)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p4319) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial21051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory10307 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21051 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2957) (meaning t m 3319) (meaning t m 3461) (meaning t m 3662) (meaning t m 4120) (meaning t m 4319) (meaning t m 5123) (meaning t m 5568) source

theorem rule21054 (p1976 p2027 p2462 p2881 p3425 p3659 p3690 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p3690) ∨ p2462 ∨ (¬ p2881) ∨ (¬ p3425)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial21054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory10310 t (m.theta 0 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule21054 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2881) (meaning t m 3425) (meaning t m 3659) (meaning t m 3690) source

theorem rule21056 (p2027 p2255 p2662 p3073 p3166 p3266 p3540 p4111 p4831 p5074 p5503 : Prop) (h : (¬ p5074) ∨ (¬ p3266) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p2255) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p5503) ∨ (¬ p4831) ∨ (¬ p3073) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p3073) ∨ (¬ p3166) ∨ (¬ p3266) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4831) ∨ (¬ p5074) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial21056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5074)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory10312 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule21056 (meaning t m 2027) (meaning t m 2255) (meaning t m 2662) (meaning t m 3073) (meaning t m 3166) (meaning t m 3266) (meaning t m 3540) (meaning t m 4111) (meaning t m 4831) (meaning t m 5074) (meaning t m 5503) source

end SunPrize.SMT
