import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory037
import SunPrize.Certificate.Theory038
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule23232 (p2027 p2122 p2774 p3193 p3452 p3791 p4425 p4733 p4826 : Prop) (h : (¬ p2122) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p3193) ∨ (¬ p4826) ∨ (¬ p4733) ∨ (¬ p4425) ∨ (¬ p3452) ∨ (¬ p3791)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4733) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory12488 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule23232 (meaning t m 2027) (meaning t m 2122) (meaning t m 2774) (meaning t m 3193) (meaning t m 3452) (meaning t m 3791) (meaning t m 4425) (meaning t m 4733) (meaning t m 4826) source

theorem rule23234 (p2579 p3096 p3646 p4399 : Prop) (h : (¬ p4399) ∨ (¬ p2579) ∨ (¬ p3096) ∨ p3646) : (¬ p2579) ∨ (¬ p3096) ∨ (p3646) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial23234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (meaning t m 3646) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory12490 (m.theta 0 4) (m.theta 0 5) (m.theta 4 6) (m.theta 5 6)
  exact rule23234 (meaning t m 2579) (meaning t m 3096) (meaning t m 3646) (meaning t m 4399) source

theorem rule23235 (p2027 p2140 p2860 p2901 p3556 p3952 : Prop) (h : p2027 ∨ (¬ p3952) ∨ (¬ p2860) ∨ (¬ p2140) ∨ (¬ p3556) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2140) ∨ (¬ p2860) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial23235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory12491 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule23235 (meaning t m 2027) (meaning t m 2140) (meaning t m 2860) (meaning t m 2901) (meaning t m 3556) (meaning t m 3952) source

theorem rule23237 (p2027 p2950 p3115 p3136 p4032 p4787 : Prop) (h : (¬ p4032) ∨ (¬ p4787) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p3115) ∨ (¬ p2950)) : (p2027) ∨ (¬ p2950) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p4032) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12493 t (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9)
  exact rule23237 (meaning t m 2027) (meaning t m 2950) (meaning t m 3115) (meaning t m 3136) (meaning t m 4032) (meaning t m 4787) source

theorem rule23239 (p2027 p2138 p2177 p3093 p3146 p3309 p4340 p4359 p4736 p4905 : Prop) (h : (¬ p4359) ∨ (¬ p4736) ∨ (¬ p2138) ∨ (¬ p4340) ∨ (¬ p3309) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4905)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3309) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4736) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial23239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory12495 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule23239 (meaning t m 2027) (meaning t m 2138) (meaning t m 2177) (meaning t m 3093) (meaning t m 3146) (meaning t m 3309) (meaning t m 4340) (meaning t m 4359) (meaning t m 4736) (meaning t m 4905) source

theorem rule23240 (p2027 p2138 p2363 p3063 p3093 p3694 p4736 p5118 p5568 : Prop) (h : (¬ p5118) ∨ (¬ p5568) ∨ (¬ p2363) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p2138) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3063)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3694) ∨ (¬ p4736) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial23240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory12496 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23240 (meaning t m 2027) (meaning t m 2138) (meaning t m 2363) (meaning t m 3063) (meaning t m 3093) (meaning t m 3694) (meaning t m 4736) (meaning t m 5118) (meaning t m 5568) source

theorem rule23242 (p2027 p2499 p2662 p2810 p3136 p3519 p4241 p4715 : Prop) (h : (¬ p3519) ∨ (¬ p4241) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p3136) ∨ (¬ p2499) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3519) ∨ (¬ p4241) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12498 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule23242 (meaning t m 2027) (meaning t m 2499) (meaning t m 2662) (meaning t m 2810) (meaning t m 3136) (meaning t m 3519) (meaning t m 4241) (meaning t m 4715) source

theorem rule23244 (p2027 p2210 p3452 p3584 p3590 p4241 p4282 p4715 : Prop) (h : (¬ p4282) ∨ (¬ p3452) ∨ (¬ p4241) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p2210) ∨ (¬ p3584) ∨ (¬ p3590)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3584) ∨ (¬ p3590) ∨ (¬ p4241) ∨ (¬ p4282) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12500 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule23244 (meaning t m 2027) (meaning t m 2210) (meaning t m 3452) (meaning t m 3584) (meaning t m 3590) (meaning t m 4241) (meaning t m 4282) (meaning t m 4715) source

theorem rule23245 (p2027 p2542 p2579 p3389 p3742 p4715 : Prop) (h : (¬ p2579) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p2542) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12501 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule23245 (meaning t m 2027) (meaning t m 2542) (meaning t m 2579) (meaning t m 3389) (meaning t m 3742) (meaning t m 4715) source

theorem rule23246 (p2027 p2579 p2850 p3389 p3876 p4715 : Prop) (h : (¬ p3876) ∨ (¬ p2850) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2850) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12502 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule23246 (meaning t m 2027) (meaning t m 2579) (meaning t m 2850) (meaning t m 3389) (meaning t m 3876) (meaning t m 4715) source

theorem rule23247 (p2807 p3286 p4661 : Prop) (h : (¬ p4661) ∨ (¬ p2807) ∨ p3286) : (¬ p2807) ∨ (p3286) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial23247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (meaning t m 3286) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory12503 (m.theta 0 3) (m.theta 3 7) (m.theta 3 9)
  exact rule23247 (meaning t m 2807) (meaning t m 3286) (meaning t m 4661) source

theorem rule23248 (p1983 p2027 p2114 p2685 p2737 p3506 p4381 p4661 : Prop) (h : (¬ p2685) ∨ (¬ p1983) ∨ p2114 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p4661) ∨ (¬ p3506) ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial23248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory12504 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23248 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2685) (meaning t m 2737) (meaning t m 3506) (meaning t m 4381) (meaning t m 4661) source

theorem rule23250 (p2027 p2657 p2946 p3359 p4241 p4949 : Prop) (h : (¬ p4949) ∨ (¬ p2946) ∨ (¬ p4241) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p3359)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3359) ∨ (¬ p4241) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial23250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory12506 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9)
  exact rule23250 (meaning t m 2027) (meaning t m 2657) (meaning t m 2946) (meaning t m 3359) (meaning t m 4241) (meaning t m 4949) source

theorem rule23251 (p1997 p2027 p2323 p2542 p2727 p2807 p2996 : Prop) (h : p2323 ∨ (¬ p1997) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p2807) ∨ (¬ p2542) ∨ (¬ p2727)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p2807) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial23251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory12507 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule23251 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2542) (meaning t m 2727) (meaning t m 2807) (meaning t m 2996) source

theorem rule23252 (p2027 p3323 p3747 p3969 p4196 p4275 p4624 p5600 : Prop) (h : (¬ p5600) ∨ (¬ p3747) ∨ (¬ p4275) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p4624) ∨ (¬ p4196)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p4196) ∨ (¬ p4275) ∨ (¬ p4624) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial23252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory12508 t (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 10)
  exact rule23252 (meaning t m 2027) (meaning t m 3323) (meaning t m 3747) (meaning t m 3969) (meaning t m 4196) (meaning t m 4275) (meaning t m 4624) (meaning t m 5600) source

theorem rule23254 (p2027 p2542 p2927 p3379 p3487 p4366 p4644 : Prop) (h : (¬ p4366) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2927) ∨ (¬ p2542) ∨ (¬ p4644) ∨ (¬ p3487)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4366) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12510 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule23254 (meaning t m 2027) (meaning t m 2542) (meaning t m 2927) (meaning t m 3379) (meaning t m 3487) (meaning t m 4366) (meaning t m 4644) source

theorem rule23255 (p2807 p3166 p4044 : Prop) (h : (¬ p2807) ∨ (¬ p4044) ∨ p3166) : (¬ p2807) ∨ (p3166) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial23255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (meaning t m 3166) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory12511 (m.theta 0 3) (m.theta 3 7) (m.theta 3 8)
  exact rule23255 (meaning t m 2807) (meaning t m 3166) (meaning t m 4044) source

theorem rule23256 (p2027 p2542 p3888 p4194 p4715 p5717 : Prop) (h : (¬ p2542) ∨ (¬ p5717) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p4194) ∨ (¬ p3888)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3888) ∨ (¬ p4194) ∨ (¬ p4715) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial23256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory12512 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 10)
  exact rule23256 (meaning t m 2027) (meaning t m 2542) (meaning t m 3888) (meaning t m 4194) (meaning t m 4715) (meaning t m 5717) source

theorem rule23258 (p2027 p2499 p2588 p3222 p4331 p4624 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4331) ∨ (¬ p4624) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3222) ∨ (¬ p4331) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial23258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory12514 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule23258 (meaning t m 2027) (meaning t m 2499) (meaning t m 2588) (meaning t m 3222) (meaning t m 4331) (meaning t m 4624) source

theorem rule23259 (p2246 p2807 p3189 p4044 : Prop) (h : (¬ p2807) ∨ (¬ p2246) ∨ (¬ p4044) ∨ p3189) : (¬ p2246) ∨ (¬ p2807) ∨ (p3189) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial23259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2807)) ∨ (meaning t m 3189) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory12515 (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule23259 (meaning t m 2246) (meaning t m 2807) (meaning t m 3189) (meaning t m 4044) source

theorem rule23260 (p2027 p2509 p2534 p2774 p2819 p3452 p3979 p4733 p5122 : Prop) (h : (¬ p3452) ∨ (¬ p3979) ∨ (¬ p2509) ∨ (¬ p2819) ∨ (¬ p2534) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3452) ∨ (¬ p3979) ∨ (¬ p4733) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial23260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory12516 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23260 (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2774) (meaning t m 2819) (meaning t m 3452) (meaning t m 3979) (meaning t m 4733) (meaning t m 5122) source

theorem rule23261 (p1982 p2027 p2331 p2363 p2611 p3005 p4117 p4195 p4417 : Prop) (h : p2611 ∨ (¬ p2363) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2331) ∨ (¬ p4417) ∨ (¬ p3005) ∨ (¬ p4195)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p3005) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial23261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory12517 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23261 (meaning t m 1982) (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2611) (meaning t m 3005) (meaning t m 4117) (meaning t m 4195) (meaning t m 4417) source

theorem rule23262 (p2027 p2341 p2579 p3553 p4241 p4386 p4715 p5201 : Prop) (h : (¬ p4241) ∨ p2027 ∨ (¬ p4386) ∨ (¬ p3553) ∨ (¬ p2579) ∨ (¬ p4715) ∨ (¬ p5201) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2579) ∨ (¬ p3553) ∨ (¬ p4241) ∨ (¬ p4386) ∨ (¬ p4715) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial23262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory12518 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 8)
  exact rule23262 (meaning t m 2027) (meaning t m 2341) (meaning t m 2579) (meaning t m 3553) (meaning t m 4241) (meaning t m 4386) (meaning t m 4715) (meaning t m 5201) source

theorem rule23263 (p2027 p2191 p2696 p2797 p3323 p3555 p3692 p4330 p4733 : Prop) (h : p2027 ∨ (¬ p4330) ∨ (¬ p2797) ∨ (¬ p3555) ∨ (¬ p2696) ∨ (¬ p4733) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p4330) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12519 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule23263 (meaning t m 2027) (meaning t m 2191) (meaning t m 2696) (meaning t m 2797) (meaning t m 3323) (meaning t m 3555) (meaning t m 3692) (meaning t m 4330) (meaning t m 4733) source

theorem rule23265 (p2499 p3584 p3590 : Prop) (h : (¬ p3590) ∨ (¬ p3584) ∨ p2499) : (p2499) ∨ (¬ p3584) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial23265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2499) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory12521 (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule23265 (meaning t m 2499) (meaning t m 3584) (meaning t m 3590) source

theorem rule23266 (p3553 p3945 p3947 : Prop) (h : (¬ p3945) ∨ (¬ p3947) ∨ p3553) : (p3553) ∨ (¬ p3945) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial23266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3553) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory12522 (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23266 (meaning t m 3553) (meaning t m 3945) (meaning t m 3947) source

theorem rule23269 (p2191 p3486 p3747 : Prop) (h : (¬ p3747) ∨ (¬ p2191) ∨ p3486) : (¬ p2191) ∨ (p3486) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial23269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (meaning t m 3486) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory12525 (m.theta 1 5) (m.theta 5 7) (m.theta 5 8)
  exact rule23269 (meaning t m 2191) (meaning t m 3486) (meaning t m 3747) source

theorem rule23270 (p2027 p2241 p2641 p2881 p3323 p3551 p3690 p4621 p5210 : Prop) (h : (¬ p3323) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3551) ∨ (¬ p5210) ∨ (¬ p2881) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2881) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p3690) ∨ (¬ p4621) ∨ (¬ p5210) := by
  classical
  tauto

theorem initial23270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5210)) := by
  have source := ElevenTheory.theory12526 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule23270 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2881) (meaning t m 3323) (meaning t m 3551) (meaning t m 3690) (meaning t m 4621) (meaning t m 5210) source

theorem rule23272 (p2027 p2248 p2295 p2331 p3791 p3860 p4261 p4444 p4826 : Prop) (h : p2027 ∨ (¬ p4444) ∨ (¬ p2295) ∨ (¬ p2248) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p3791) ∨ (¬ p4826) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3791) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial23272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory12528 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 8) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23272 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 3791) (meaning t m 3860) (meaning t m 4261) (meaning t m 4444) (meaning t m 4826) source

theorem rule23275 (p2027 p2449 p2651 p2753 p2761 p3580 p3645 p3646 p3989 p4117 p4877 p5123 p5580 : Prop) (h : (¬ p2761) ∨ (¬ p3645) ∨ (¬ p2753) ∨ (¬ p4117) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3580) ∨ (¬ p2651) ∨ (¬ p2449) ∨ (¬ p5123) ∨ (¬ p4877) ∨ (¬ p3646) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3580) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4117) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory12531 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule23275 (meaning t m 2027) (meaning t m 2449) (meaning t m 2651) (meaning t m 2753) (meaning t m 2761) (meaning t m 3580) (meaning t m 3645) (meaning t m 3646) (meaning t m 3989) (meaning t m 4117) (meaning t m 4877) (meaning t m 5123) (meaning t m 5580) source

theorem rule23276 (p2027 p2177 p3516 p3551 p4276 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3516) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4276) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4276) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial23276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory12532 t (m.theta 0 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23276 (meaning t m 2027) (meaning t m 2177) (meaning t m 3516) (meaning t m 3551) (meaning t m 4276) (meaning t m 4278) source

theorem rule23277 (p2027 p2210 p2246 p2528 p2651 p3083 p3860 p4959 p5118 p5693 : Prop) (h : (¬ p2651) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p5693) ∨ (¬ p3860) ∨ (¬ p2210) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p4959)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3860) ∨ (¬ p4959) ∨ (¬ p5118) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial23277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4959)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory12533 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 1 8) (m.theta 3 4) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23277 (meaning t m 2027) (meaning t m 2210) (meaning t m 2246) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3860) (meaning t m 4959) (meaning t m 5118) (meaning t m 5693) source

theorem rule23278 (p2027 p2901 p2946 p4244 p4392 p4790 : Prop) (h : (¬ p4790) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4244) ∨ (¬ p2901) ∨ (¬ p4392)) : (p2027) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4244) ∨ (¬ p4392) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial23278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory12534 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule23278 (meaning t m 2027) (meaning t m 2901) (meaning t m 2946) (meaning t m 4244) (meaning t m 4392) (meaning t m 4790) source

theorem rule23280 (p2027 p2248 p3166 p3256 p3583 p3694 p3954 p4134 p4347 : Prop) (h : (¬ p4134) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4347) ∨ (¬ p3166) ∨ (¬ p3694) ∨ (¬ p2248) ∨ (¬ p3954) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) ∨ (¬ p4134) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial23280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory12536 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 5) (m.theta 3 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23280 (meaning t m 2027) (meaning t m 2248) (meaning t m 3166) (meaning t m 3256) (meaning t m 3583) (meaning t m 3694) (meaning t m 3954) (meaning t m 4134) (meaning t m 4347) source

theorem rule23281 (p1998 p2027 p2264 p2409 p2417 p2922 p3947 : Prop) (h : (¬ p2922) ∨ p2409 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p2264) ∨ (¬ p2417)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2409) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial23281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory12537 t (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23281 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2409) (meaning t m 2417) (meaning t m 2922) (meaning t m 3947) source

theorem rule23282 (p1992 p2027 p2509 p2534 p2608 p2766 p3452 : Prop) (h : (¬ p3452) ∨ (¬ p2608) ∨ (¬ p1992) ∨ (¬ p2509) ∨ p2027 ∨ p2766 ∨ (¬ p2534)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial23282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory12538 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9)
  exact rule23282 (meaning t m 1992) (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2608) (meaning t m 2766) (meaning t m 3452) source

theorem rule23284 (p2027 p2248 p2928 p3286 p3452 p3506 p4191 p4278 p4621 : Prop) (h : (¬ p4191) ∨ (¬ p3286) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p2248) ∨ (¬ p4621) ∨ (¬ p3452) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4191) ∨ (¬ p4278) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial23284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory12540 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23284 (meaning t m 2027) (meaning t m 2248) (meaning t m 2928) (meaning t m 3286) (meaning t m 3452) (meaning t m 3506) (meaning t m 4191) (meaning t m 4278) (meaning t m 4621) source

theorem rule23285 (p2027 p2928 p3222 p4107 p4451 p4712 : Prop) (h : (¬ p3222) ∨ (¬ p4451) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p4107) ∨ (¬ p4712)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3222) ∨ (¬ p4107) ∨ (¬ p4451) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial23285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory12541 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule23285 (meaning t m 2027) (meaning t m 2928) (meaning t m 3222) (meaning t m 4107) (meaning t m 4451) (meaning t m 4712) source

theorem rule23286 (p2027 p2427 p2542 p2579 p2662 p3096 p4558 : Prop) (h : (¬ p2579) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p4558) ∨ (¬ p2427) ∨ (¬ p3096)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3096) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12542 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule23286 (meaning t m 2027) (meaning t m 2427) (meaning t m 2542) (meaning t m 2579) (meaning t m 2662) (meaning t m 3096) (meaning t m 4558) source

theorem rule23287 (p2441 p4711 p4715 : Prop) (h : (¬ p2441) ∨ (¬ p4715) ∨ p4711) : (¬ p2441) ∨ (p4711) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (meaning t m 4711) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12543 t (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule23287 (meaning t m 2441) (meaning t m 4711) (meaning t m 4715) source

theorem rule23291 (p2210 p3379 p3948 : Prop) (h : (¬ p3948) ∨ (¬ p3379) ∨ p2210) : (p2210) ∨ (¬ p3379) ∨ (¬ p3948) := by
  classical
  tauto

theorem initial23291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2210) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3948)) := by
  have source := ElevenTheory.theory12547 (m.theta 0 1) (m.theta 1 4) (m.theta 1 5)
  exact rule23291 (meaning t m 2210) (meaning t m 3379) (meaning t m 3948) source

theorem rule23292 (p2027 p2493 p3055 p3541 p3584 p4734 : Prop) (h : (¬ p3541) ∨ (¬ p3584) ∨ (¬ p3055) ∨ (¬ p2493) ∨ (¬ p4734) ∨ p2027) : (p2027) ∨ (¬ p2493) ∨ (¬ p3055) ∨ (¬ p3541) ∨ (¬ p3584) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12548 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule23292 (meaning t m 2027) (meaning t m 2493) (meaning t m 3055) (meaning t m 3541) (meaning t m 3584) (meaning t m 4734) source

theorem rule23294 (p2027 p2972 p3486 p4135 p4277 p4278 : Prop) (h : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p4135) ∨ (¬ p4277)) : (p2027) ∨ (¬ p2972) ∨ (¬ p3486) ∨ (¬ p4135) ∨ (¬ p4277) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial23294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory12550 t (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule23294 (meaning t m 2027) (meaning t m 2972) (meaning t m 3486) (meaning t m 4135) (meaning t m 4277) (meaning t m 4278) source

theorem rule23296 (p2027 p2476 p2534 p3347 p3399 p3954 p4075 p4444 p4826 p5216 : Prop) (h : (¬ p3347) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p4075)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12552 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule23296 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 3347) (meaning t m 3399) (meaning t m 3954) (meaning t m 4075) (meaning t m 4444) (meaning t m 4826) (meaning t m 5216) source

theorem rule23297 (p4381 p4444 p4445 : Prop) (h : (¬ p4445) ∨ (¬ p4444) ∨ p4381) : (p4381) ∨ (¬ p4444) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial23297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4381) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory12553 (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23297 (meaning t m 4381) (meaning t m 4444) (meaning t m 4445) source

theorem rule23300 (p2027 p3379 p3631 p3687 p3821 p5206 p5216 : Prop) (h : (¬ p3379) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p5206)) : (p2027) ∨ (¬ p3379) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p5206) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5206)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12556 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 7 9)
  exact rule23300 (meaning t m 2027) (meaning t m 3379) (meaning t m 3631) (meaning t m 3687) (meaning t m 3821) (meaning t m 5206) (meaning t m 5216) source

theorem rule23304 (p2027 p2264 p2995 p3136 p3551 p4787 p4849 : Prop) (h : (¬ p3136) ∨ p2027 ∨ (¬ p4787) ∨ (¬ p2995) ∨ (¬ p2264) ∨ (¬ p4849) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3136) ∨ (¬ p3551) ∨ (¬ p4787) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial23304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory12560 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule23304 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3136) (meaning t m 3551) (meaning t m 4787) (meaning t m 4849) source

theorem rule23305 (p2027 p2476 p2630 p2655 p3083 p4787 : Prop) (h : p2027 ∨ (¬ p3083) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p4787) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p3083) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial23305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory12561 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8)
  exact rule23305 (meaning t m 2027) (meaning t m 2476) (meaning t m 2630) (meaning t m 2655) (meaning t m 3083) (meaning t m 4787) source

theorem rule23307 (p2027 p2299 p3093 p3365 p3527 p4315 p4320 p4452 p4559 p4736 : Prop) (h : (¬ p4559) ∨ (¬ p2299) ∨ (¬ p4315) ∨ (¬ p3365) ∨ (¬ p4320) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3093) ∨ (¬ p4452)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3527) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4452) ∨ (¬ p4559) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12563 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23307 (meaning t m 2027) (meaning t m 2299) (meaning t m 3093) (meaning t m 3365) (meaning t m 3527) (meaning t m 4315) (meaning t m 4320) (meaning t m 4452) (meaning t m 4559) (meaning t m 4736) source

theorem rule23308 (p2027 p2264 p2928 p3019 p3644 p4156 p4811 : Prop) (h : p2027 ∨ (¬ p4156) ∨ (¬ p2928) ∨ (¬ p4811) ∨ (¬ p2264) ∨ (¬ p3019) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2928) ∨ (¬ p3019) ∨ (¬ p3644) ∨ (¬ p4156) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial23308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory12564 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule23308 (meaning t m 2027) (meaning t m 2264) (meaning t m 2928) (meaning t m 3019) (meaning t m 3644) (meaning t m 4156) (meaning t m 4811) source

theorem rule23309 (p2027 p2307 p2387 p2911 p4138 p4712 : Prop) (h : (¬ p4138) ∨ (¬ p4712) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2911) ∨ (¬ p4138) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial23309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory12565 t (m.theta 0 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23309 (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2911) (meaning t m 4138) (meaning t m 4712) source

theorem rule23310 (p2027 p2299 p2341 p2396 p3346 p3347 p3543 p3680 p3951 p4257 p4425 p4793 : Prop) (h : (¬ p2341) ∨ (¬ p2299) ∨ (¬ p3680) ∨ (¬ p4793) ∨ (¬ p3543) ∨ (¬ p2396) ∨ (¬ p3951) ∨ (¬ p4425) ∨ (¬ p3346) ∨ (¬ p4257) ∨ (¬ p3347) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3346) ∨ (¬ p3347) ∨ (¬ p3543) ∨ (¬ p3680) ∨ (¬ p3951) ∨ (¬ p4257) ∨ (¬ p4425) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial23310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory12566 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule23310 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2396) (meaning t m 3346) (meaning t m 3347) (meaning t m 3543) (meaning t m 3680) (meaning t m 3951) (meaning t m 4257) (meaning t m 4425) (meaning t m 4793) source

theorem rule23311 (p2027 p2850 p2982 p3096 p3584 p5046 : Prop) (h : (¬ p3584) ∨ (¬ p2982) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p5046) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial23311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory12567 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9)
  exact rule23311 (meaning t m 2027) (meaning t m 2850) (meaning t m 2982) (meaning t m 3096) (meaning t m 3584) (meaning t m 5046) source

theorem rule23312 (p2027 p2252 p2727 p2950 p3115 p4032 p4701 : Prop) (h : (¬ p2252) ∨ (¬ p2950) ∨ (¬ p2727) ∨ (¬ p4032) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p4701)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2727) ∨ (¬ p2950) ∨ (¬ p3115) ∨ (¬ p4032) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12568 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 9)
  exact rule23312 (meaning t m 2027) (meaning t m 2252) (meaning t m 2727) (meaning t m 2950) (meaning t m 3115) (meaning t m 4032) (meaning t m 4701) source

theorem rule23313 (p2027 p2406 p2579 p2928 p3389 p4715 : Prop) (h : (¬ p2579) ∨ (¬ p4715) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2579) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12569 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule23313 (meaning t m 2027) (meaning t m 2406) (meaning t m 2579) (meaning t m 2928) (meaning t m 3389) (meaning t m 4715) source

theorem rule23318 (p2027 p2406 p2982 p3365 p3379 p3877 p4118 p4450 p4736 : Prop) (h : (¬ p3877) ∨ (¬ p3379) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4736) ∨ (¬ p4450) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4450) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12574 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 9) (m.theta 8 9)
  exact rule23318 (meaning t m 2027) (meaning t m 2406) (meaning t m 2982) (meaning t m 3365) (meaning t m 3379) (meaning t m 3877) (meaning t m 4118) (meaning t m 4450) (meaning t m 4736) source

theorem rule23320 (p2027 p2807 p2963 p3552 p3822 p4843 : Prop) (h : (¬ p2807) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p3552) ∨ (¬ p2963) ∨ (¬ p4843)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ (¬ p3822) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial23320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory12576 t (m.theta 0 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule23320 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3552) (meaning t m 3822) (meaning t m 4843) source

theorem rule23321 (p2027 p2177 p2810 p3093 p3309 p3365 p4256 p4438 p4736 : Prop) (h : p2027 ∨ (¬ p3365) ∨ (¬ p2810) ∨ (¬ p4438) ∨ (¬ p4256) ∨ (¬ p3309) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2810) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12577 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule23321 (meaning t m 2027) (meaning t m 2177) (meaning t m 2810) (meaning t m 3093) (meaning t m 3309) (meaning t m 3365) (meaning t m 4256) (meaning t m 4438) (meaning t m 4736) source

theorem rule23322 (p2027 p2493 p3365 p3379 p3564 p3568 p4195 p4624 p4736 : Prop) (h : (¬ p3365) ∨ (¬ p4736) ∨ (¬ p4624) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3568) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4624) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12578 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule23322 (meaning t m 2027) (meaning t m 2493) (meaning t m 3365) (meaning t m 3379) (meaning t m 3564) (meaning t m 3568) (meaning t m 4195) (meaning t m 4624) (meaning t m 4736) source

theorem rule23323 (p1998 p2027 p2241 p2264 p2589 p2764 p3027 p3692 p3880 p4444 p5193 : Prop) (h : (¬ p2589) ∨ (¬ p3880) ∨ (¬ p2264) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p3027) ∨ (¬ p1998) ∨ (¬ p2241) ∨ (¬ p4444) ∨ p2764) : (¬ p1998) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (p2764) ∨ (¬ p3027) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4444) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12579 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule23323 (meaning t m 1998) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2589) (meaning t m 2764) (meaning t m 3027) (meaning t m 3692) (meaning t m 3880) (meaning t m 4444) (meaning t m 5193) source

theorem rule23324 (p2027 p2144 p2156 p3365 p3758 p5052 : Prop) (h : (¬ p5052) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2144) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p3758) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12580 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule23324 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 3365) (meaning t m 3758) (meaning t m 5052) source

theorem rule23327 (p2027 p2440 p2531 p3083 p3694 p4882 : Prop) (h : (¬ p2531) ∨ p2027 ∨ (¬ p4882) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p3694) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial23327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory12583 t (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule23327 (meaning t m 2027) (meaning t m 2440) (meaning t m 2531) (meaning t m 3083) (meaning t m 3694) (meaning t m 4882) source

theorem rule23331 (p2027 p2156 p2928 p3156 p3452 p3644 p3952 p4521 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2156) ∨ (¬ p3952) ∨ (¬ p3156) ∨ (¬ p2928) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2928) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p3952) ∨ (¬ p4521) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12587 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule23331 (meaning t m 2027) (meaning t m 2156) (meaning t m 2928) (meaning t m 3156) (meaning t m 3452) (meaning t m 3644) (meaning t m 3952) (meaning t m 4521) (meaning t m 4902) source

theorem rule23332 (p2027 p3201 p3367 p3583 p3698 p4646 : Prop) (h : p2027 ∨ (¬ p3698) ∨ (¬ p3583) ∨ (¬ p3367) ∨ (¬ p4646) ∨ (¬ p3201)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial23332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory12588 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7)
  exact rule23332 (meaning t m 2027) (meaning t m 3201) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 4646) source

theorem rule23333 (p2027 p2104 p2598 p4286 p5369 p5616 p5682 : Prop) (h : (¬ p2104) ∨ (¬ p5369) ∨ (¬ p2598) ∨ (¬ p5682) ∨ (¬ p4286) ∨ (¬ p5616) ∨ p2027) : (p2027) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4286) ∨ (¬ p5369) ∨ (¬ p5616) ∨ (¬ p5682) := by
  classical
  tauto

theorem initial23333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5369)) ∨ (¬ (meaning t m 5616)) ∨ (¬ (meaning t m 5682)) := by
  have source := ElevenTheory.theory12589 t (m.theta 0 2) (m.theta 2 10) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 8 10)
  exact rule23333 (meaning t m 2027) (meaning t m 2104) (meaning t m 2598) (meaning t m 4286) (meaning t m 5369) (meaning t m 5616) (meaning t m 5682) source

theorem rule23334 (p2027 p2717 p3941 p4119 p4898 p5568 : Prop) (h : (¬ p3941) ∨ (¬ p2717) ∨ (¬ p4898) ∨ (¬ p4119) ∨ (¬ p5568) ∨ p2027) : (p2027) ∨ (¬ p2717) ∨ (¬ p3941) ∨ (¬ p4119) ∨ (¬ p4898) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial23334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4898)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory12590 t (m.theta 2 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10)
  exact rule23334 (meaning t m 2027) (meaning t m 2717) (meaning t m 3941) (meaning t m 4119) (meaning t m 4898) (meaning t m 5568) source

theorem rule23336 (p2027 p2248 p2331 p2459 p2509 p2668 p3452 p3550 p4286 p5118 : Prop) (h : (¬ p2331) ∨ (¬ p2248) ∨ (¬ p2668) ∨ (¬ p3550) ∨ (¬ p2509) ∨ (¬ p2459) ∨ (¬ p4286) ∨ (¬ p5118) ∨ (¬ p3452) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2459) ∨ (¬ p2509) ∨ (¬ p2668) ∨ (¬ p3452) ∨ (¬ p3550) ∨ (¬ p4286) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial23336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory12592 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23336 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2459) (meaning t m 2509) (meaning t m 2668) (meaning t m 3452) (meaning t m 3550) (meaning t m 4286) (meaning t m 5118) source

theorem rule23337 (p1985 p2027 p2148 p2156 p2449 p2995 p3690 p3952 : Prop) (h : (¬ p3952) ∨ p2148 ∨ (¬ p1985) ∨ (¬ p2995) ∨ (¬ p2449) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2156)) : (¬ p1985) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial23337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory12593 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule23337 (meaning t m 1985) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2449) (meaning t m 2995) (meaning t m 3690) (meaning t m 3952) source

theorem rule23339 (p2027 p3758 p4019 p4509 p4744 p5568 : Prop) (h : (¬ p3758) ∨ p2027 ∨ (¬ p4019) ∨ (¬ p4744) ∨ (¬ p4509) ∨ (¬ p5568)) : (p2027) ∨ (¬ p3758) ∨ (¬ p4019) ∨ (¬ p4509) ∨ (¬ p4744) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial23339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory12595 t (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule23339 (meaning t m 2027) (meaning t m 3758) (meaning t m 4019) (meaning t m 4509) (meaning t m 4744) (meaning t m 5568) source

theorem rule23340 (p2860 p3698 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p3698) ∨ (¬ p2860)) : (¬ p2860) ∨ (¬ p3698) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial23340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory12596 (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule23340 (meaning t m 2860) (meaning t m 3698) (meaning t m 4110) source

theorem rule23343 (p2027 p2504 p3093 p3452 p3574 p4814 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p4814) ∨ (¬ p3093) ∨ (¬ p2504)) : (p2027) ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3574) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12599 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6)
  exact rule23343 (meaning t m 2027) (meaning t m 2504) (meaning t m 3093) (meaning t m 3452) (meaning t m 3574) (meaning t m 4814) source

theorem rule23344 (p2027 p2352 p2588 p3550 p3570 p4556 : Prop) (h : (¬ p3550) ∨ (¬ p3570) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3550) ∨ (¬ p3570) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial23344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12600 t (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23344 (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 3550) (meaning t m 3570) (meaning t m 4556) source

theorem rule23345 (p2027 p2156 p2901 p3055 p3367 p3588 p3873 p3952 p4521 p4898 : Prop) (h : (¬ p2156) ∨ (¬ p4521) ∨ (¬ p4898) ∨ (¬ p2901) ∨ (¬ p3873) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3367) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p3952) ∨ (¬ p4521) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial23345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory12601 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule23345 (meaning t m 2027) (meaning t m 2156) (meaning t m 2901) (meaning t m 3055) (meaning t m 3367) (meaning t m 3588) (meaning t m 3873) (meaning t m 3952) (meaning t m 4521) (meaning t m 4898) source

theorem rule23346 (p2027 p2140 p2707 p3556 p3583 p4344 : Prop) (h : (¬ p3583) ∨ (¬ p2707) ∨ (¬ p2140) ∨ (¬ p3556) ∨ (¬ p4344) ∨ p2027) : (p2027) ∨ (¬ p2140) ∨ (¬ p2707) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial23346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory12602 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7)
  exact rule23346 (meaning t m 2027) (meaning t m 2140) (meaning t m 2707) (meaning t m 3556) (meaning t m 3583) (meaning t m 4344) source

theorem rule23347 (p1984 p2027 p2202 p2563 p3055 p3367 p3873 p4173 p4874 : Prop) (h : p2202 ∨ (¬ p2563) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3873) ∨ (¬ p3367) ∨ (¬ p4874) ∨ (¬ p1984) ∨ (¬ p4173)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3873) ∨ (¬ p4173) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial23347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory12603 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule23347 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3055) (meaning t m 3367) (meaning t m 3873) (meaning t m 4173) (meaning t m 4874) source

theorem rule23348 (p2476 p2663 p3172 p4437 : Prop) (h : (¬ p3172) ∨ (¬ p4437) ∨ (¬ p2663) ∨ p2476) : (p2476) ∨ (¬ p2663) ∨ (¬ p3172) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial23348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory12604 (m.theta 0 3) (m.theta 0 4) (m.theta 3 8) (m.theta 4 8)
  exact rule23348 (meaning t m 2476) (meaning t m 2663) (meaning t m 3172) (meaning t m 4437) source

theorem rule23351 (p2027 p2299 p2911 p3097 p3920 p4718 : Prop) (h : (¬ p4718) ∨ (¬ p3920) ∨ (¬ p2911) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3097)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3097) ∨ (¬ p3920) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial23351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory12607 t (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23351 (meaning t m 2027) (meaning t m 2299) (meaning t m 2911) (meaning t m 3097) (meaning t m 3920) (meaning t m 4718) source

theorem rule23353 (p2027 p2960 p3051 p3246 p3947 p4386 : Prop) (h : p2027 ∨ (¬ p3947) ∨ (¬ p2960) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4386)) : (p2027) ∨ (¬ p2960) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial23353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory12609 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule23353 (meaning t m 2027) (meaning t m 2960) (meaning t m 3051) (meaning t m 3246) (meaning t m 3947) (meaning t m 4386) source

theorem rule23355 (p2476 p2509 p3519 : Prop) (h : (¬ p2509) ∨ (¬ p3519) ∨ p2476) : (p2476) ∨ (¬ p2509) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial23355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory12611 (m.theta 0 4) (m.theta 1 4) (m.theta 4 8)
  exact rule23355 (meaning t m 2476) (meaning t m 2509) (meaning t m 3519) source

theorem rule23356 (p2027 p2493 p2651 p2963 p4389 p4814 : Prop) (h : (¬ p4389) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2651) ∨ (¬ p4814) ∨ (¬ p2493)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4389) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial23356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory12612 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule23356 (meaning t m 2027) (meaning t m 2493) (meaning t m 2651) (meaning t m 2963) (meaning t m 4389) (meaning t m 4814) source

theorem rule23357 (p2027 p2210 p2579 p2881 p2891 p3422 p3874 p4438 p5193 : Prop) (h : (¬ p2891) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p5193) ∨ (¬ p4438) ∨ (¬ p3874) ∨ (¬ p2210) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p4438) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12613 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule23357 (meaning t m 2027) (meaning t m 2210) (meaning t m 2579) (meaning t m 2881) (meaning t m 2891) (meaning t m 3422) (meaning t m 3874) (meaning t m 4438) (meaning t m 5193) source

theorem rule23358 (p2027 p2727 p2951 p3051 p3368 p3486 p4701 : Prop) (h : (¬ p3368) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4701) ∨ (¬ p2951) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3368) ∨ (¬ p3486) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12614 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule23358 (meaning t m 2027) (meaning t m 2727) (meaning t m 2951) (meaning t m 3051) (meaning t m 3368) (meaning t m 3486) (meaning t m 4701) source

theorem rule23360 (p2027 p2137 p2839 p2881 p2928 p3051 p3055 p4030 p4278 p4666 p4734 : Prop) (h : (¬ p4030) ∨ (¬ p3055) ∨ (¬ p3051) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2928) ∨ (¬ p4734) ∨ (¬ p4666) ∨ (¬ p2137) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2881) ∨ (¬ p2928) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12616 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23360 (meaning t m 2027) (meaning t m 2137) (meaning t m 2839) (meaning t m 2881) (meaning t m 2928) (meaning t m 3051) (meaning t m 3055) (meaning t m 4030) (meaning t m 4278) (meaning t m 4666) (meaning t m 4734) source

theorem rule23361 (p2027 p2307 p2396 p2748 p2779 p2829 p3365 p3950 p4118 p4360 p4734 : Prop) (h : (¬ p2307) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p2829) ∨ (¬ p4118) ∨ (¬ p2779) ∨ (¬ p4360) ∨ (¬ p3950) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2396)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12617 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23361 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2748) (meaning t m 2779) (meaning t m 2829) (meaning t m 3365) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4734) source

theorem rule23363 (p3172 p3414 p4044 : Prop) (h : (¬ p4044) ∨ (¬ p3172) ∨ p3414) : (¬ p3172) ∨ (p3414) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial23363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3172)) ∨ (meaning t m 3414) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory12619 (m.theta 0 3) (m.theta 3 7) (m.theta 3 8)
  exact rule23363 (meaning t m 3172) (meaning t m 3414) (meaning t m 4044) source

theorem rule23364 (p2027 p2220 p2630 p2951 p3694 p4392 p4701 : Prop) (h : (¬ p2951) ∨ (¬ p2220) ∨ (¬ p4701) ∨ (¬ p2630) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p4392)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p3694) ∨ (¬ p4392) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12620 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule23364 (meaning t m 2027) (meaning t m 2220) (meaning t m 2630) (meaning t m 2951) (meaning t m 3694) (meaning t m 4392) (meaning t m 4701) source

theorem rule23367 (p2027 p2470 p2663 p2952 p4256 p4701 : Prop) (h : (¬ p2470) ∨ (¬ p2663) ∨ (¬ p4701) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2952)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p4256) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12623 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8)
  exact rule23367 (meaning t m 2027) (meaning t m 2470) (meaning t m 2663) (meaning t m 2952) (meaning t m 4256) (meaning t m 4701) source

theorem rule23368 (p2663 p3414 p3540 p3740 : Prop) (h : (¬ p3740) ∨ (¬ p2663) ∨ (¬ p3414) ∨ p3540) : (¬ p2663) ∨ (¬ p3414) ∨ (p3540) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial23368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3414)) ∨ (meaning t m 3540) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory12624 (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 7)
  exact rule23368 (meaning t m 2663) (meaning t m 3414) (meaning t m 3540) (meaning t m 3740) source

theorem rule23369 (p2027 p2963 p3166 p3989 p4417 p4560 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p4417) ∨ (¬ p4560) ∨ (¬ p3989) ∨ (¬ p3166)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3989) ∨ (¬ p4417) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12625 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule23369 (meaning t m 2027) (meaning t m 2963) (meaning t m 3166) (meaning t m 3989) (meaning t m 4417) (meaning t m 4560) source

theorem rule23371 (p2027 p2132 p2247 p2870 p3246 p3950 p4118 p4360 p4733 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2870) ∨ (¬ p4360) ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p4118) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12627 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23371 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2870) (meaning t m 3246) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4733) source

theorem rule23372 (p2027 p2630 p3051 p3370 p3412 p4244 p4392 p4701 : Prop) (h : (¬ p3370) ∨ (¬ p3412) ∨ (¬ p4244) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4392) ∨ (¬ p4701)) : (p2027) ∨ (¬ p2630) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3412) ∨ (¬ p4244) ∨ (¬ p4392) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12628 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule23372 (meaning t m 2027) (meaning t m 2630) (meaning t m 3051) (meaning t m 3370) (meaning t m 3412) (meaning t m 4244) (meaning t m 4392) (meaning t m 4701) source

theorem rule23375 (p2027 p2241 p2727 p3591 p4319 p4972 : Prop) (h : (¬ p2727) ∨ (¬ p2241) ∨ (¬ p4972) ∨ (¬ p4319) ∨ p2027 ∨ (¬ p3591)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3591) ∨ (¬ p4319) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial23375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory12631 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6)
  exact rule23375 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3591) (meaning t m 4319) (meaning t m 4972) source

theorem rule23377 (p2027 p2341 p2417 p3570 p3821 p4647 : Prop) (h : (¬ p3570) ∨ (¬ p3821) ∨ (¬ p2341) ∨ (¬ p4647) ∨ (¬ p2417) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3570) ∨ (¬ p3821) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial23377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory12633 t (m.theta 0 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23377 (meaning t m 2027) (meaning t m 2341) (meaning t m 2417) (meaning t m 3570) (meaning t m 3821) (meaning t m 4647) source

theorem rule23378 (p1983 p2027 p2114 p2137 p2341 p2839 p3246 p3570 p4988 : Prop) (h : p2114 ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4988) ∨ (¬ p2839) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p1983) ∨ (¬ p2137)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2137) ∨ (¬ p2341) ∨ (¬ p2839) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial23378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory12634 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23378 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2137) (meaning t m 2341) (meaning t m 2839) (meaning t m 3246) (meaning t m 3570) (meaning t m 4988) source

theorem rule23379 (p1983 p2027 p2341 p2622 p2951 p3136 p3246 p3570 p4988 : Prop) (h : p2622 ∨ (¬ p3570) ∨ (¬ p2341) ∨ (¬ p4988) ∨ (¬ p3246) ∨ (¬ p1983) ∨ (¬ p3136) ∨ (¬ p2951) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (¬ p2341) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial23379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory12635 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23379 (meaning t m 1983) (meaning t m 2027) (meaning t m 2341) (meaning t m 2622) (meaning t m 2951) (meaning t m 3136) (meaning t m 3246) (meaning t m 3570) (meaning t m 4988) source

theorem rule23380 (p3575 p3740 p4066 : Prop) (h : (¬ p3740) ∨ (¬ p4066) ∨ p3575) : (p3575) ∨ (¬ p3740) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial23380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3575) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory12636 (m.theta 0 7) (m.theta 3 7) (m.theta 4 7)
  exact rule23380 (meaning t m 3575) (meaning t m 3740) (meaning t m 4066) source

theorem rule23383 (p2027 p2210 p2588 p3055 p3527 p3570 p3584 p4431 p4556 p4736 : Prop) (h : (¬ p2210) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p4431) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p4556)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p4431) ∨ (¬ p4556) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12639 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23383 (meaning t m 2027) (meaning t m 2210) (meaning t m 2588) (meaning t m 3055) (meaning t m 3527) (meaning t m 3570) (meaning t m 3584) (meaning t m 4431) (meaning t m 4556) (meaning t m 4736) source

theorem rule23384 (p2027 p3256 p3989 p4261 p4318 p4341 p4560 : Prop) (h : (¬ p4341) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p4318) ∨ (¬ p4560) ∨ (¬ p3256) ∨ (¬ p4261)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3989) ∨ (¬ p4261) ∨ (¬ p4318) ∨ (¬ p4341) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12640 t (m.theta 1 8) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule23384 (meaning t m 2027) (meaning t m 3256) (meaning t m 3989) (meaning t m 4261) (meaning t m 4318) (meaning t m 4341) (meaning t m 4560) source

theorem rule23385 (p1987 p2027 p2633 p2651 p2810 p3414 p3644 p3740 : Prop) (h : (¬ p2651) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3740) ∨ p2633 ∨ (¬ p3414) ∨ (¬ p1987) ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3414) ∨ (¬ p3644) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial23385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory12641 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule23385 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2651) (meaning t m 2810) (meaning t m 3414) (meaning t m 3644) (meaning t m 3740) source

theorem rule23386 (p2027 p2363 p2518 p3193 p4440 p4596 : Prop) (h : (¬ p2518) ∨ (¬ p3193) ∨ (¬ p4440) ∨ (¬ p4596) ∨ p2027 ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p3193) ∨ (¬ p4440) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial23386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory12642 t (m.theta 1 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule23386 (meaning t m 2027) (meaning t m 2363) (meaning t m 2518) (meaning t m 3193) (meaning t m 4440) (meaning t m 4596) source

theorem rule23389 (p2027 p2177 p2307 p3570 p4204 p4489 : Prop) (h : (¬ p4204) ∨ (¬ p3570) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4489) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial23389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory12645 t (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23389 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 3570) (meaning t m 4204) (meaning t m 4489) source

theorem rule23392 (p2027 p2470 p3367 p3583 p3698 p3759 p4610 : Prop) (h : (¬ p3698) ∨ (¬ p3759) ∨ (¬ p3583) ∨ (¬ p3367) ∨ (¬ p4610) ∨ p2027 ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial23392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory12648 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 8)
  exact rule23392 (meaning t m 2027) (meaning t m 2470) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 3759) (meaning t m 4610) source

theorem rule23396 (p3550 p4998 p5309 : Prop) (h : (¬ p3550) ∨ (¬ p5309) ∨ p4998) : (¬ p3550) ∨ (p4998) ∨ (¬ p5309) := by
  classical
  tauto

theorem initial23396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (meaning t m 4998) ∨ (¬ (meaning t m 5309)) := by
  have source := ElevenTheory.theory12652 t (m.theta 1 8) (m.theta 6 8) (m.theta 7 8)
  exact rule23396 (meaning t m 3550) (meaning t m 4998) (meaning t m 5309) source

theorem rule23398 (p2027 p2284 p2383 p3497 p4489 p4506 : Prop) (h : (¬ p4489) ∨ p2027 ∨ (¬ p4506) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2383) ∨ (¬ p3497) ∨ (¬ p4489) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial23398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4489)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory12654 t (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule23398 (meaning t m 2027) (meaning t m 2284) (meaning t m 2383) (meaning t m 3497) (meaning t m 4489) (meaning t m 4506) source

theorem rule23399 (p4138 p4433 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p4138) ∨ p4433) : (¬ p4138) ∨ (p4433) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4138)) ∨ (meaning t m 4433) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12655 t (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule23399 (meaning t m 4138) (meaning t m 4433) (meaning t m 4902) source

theorem rule23400 (p2027 p2138 p2383 p2748 p2786 p3923 p4245 p5049 : Prop) (h : (¬ p4245) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3923) ∨ (¬ p2748) ∨ (¬ p2786) ∨ (¬ p2138) ∨ (¬ p5049)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2748) ∨ (¬ p2786) ∨ (¬ p3923) ∨ (¬ p4245) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12656 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 8)
  exact rule23400 (meaning t m 2027) (meaning t m 2138) (meaning t m 2383) (meaning t m 2748) (meaning t m 2786) (meaning t m 3923) (meaning t m 4245) (meaning t m 5049) source

theorem rule23401 (p2027 p2136 p2137 p2737 p2774 p3688 p5049 : Prop) (h : (¬ p2136) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p2737) ∨ (¬ p2137) ∨ (¬ p2774) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2137) ∨ (¬ p2737) ∨ (¬ p2774) ∨ (¬ p3688) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12657 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6)
  exact rule23401 (meaning t m 2027) (meaning t m 2136) (meaning t m 2137) (meaning t m 2737) (meaning t m 2774) (meaning t m 3688) (meaning t m 5049) source

theorem rule23402 (p2027 p2138 p2307 p2748 p2786 p3549 p4245 p5049 : Prop) (h : (¬ p2748) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p5049) ∨ (¬ p2786) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2748) ∨ (¬ p2786) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12658 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 7)
  exact rule23402 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 2748) (meaning t m 2786) (meaning t m 3549) (meaning t m 4245) (meaning t m 5049) source

theorem rule23404 (p2027 p2137 p2737 p3051 p3486 p4874 p5049 : Prop) (h : (¬ p2737) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4874) ∨ (¬ p5049) ∨ (¬ p2137) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2737) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12660 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule23404 (meaning t m 2027) (meaning t m 2137) (meaning t m 2737) (meaning t m 3051) (meaning t m 3486) (meaning t m 4874) (meaning t m 5049) source

theorem rule23405 (p2027 p2138 p2307 p2786 p3822 p4841 p5049 : Prop) (h : (¬ p2138) ∨ (¬ p4841) ∨ (¬ p5049) ∨ p2027 ∨ (¬ p2786) ∨ (¬ p2307) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3822) ∨ (¬ p4841) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4841)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12661 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 6 7)
  exact rule23405 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 2786) (meaning t m 3822) (meaning t m 4841) (meaning t m 5049) source

theorem rule23406 (p2027 p2187 p2192 p2210 p2254 p2657 p3644 p3742 p4133 : Prop) (h : (¬ p3644) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p4133) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p2254) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial23406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory12662 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule23406 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 3644) (meaning t m 3742) (meaning t m 4133) source

theorem rule23407 (p2027 p2138 p2252 p2748 p3366 p3414 p3537 p3553 p3609 p5049 p5118 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p5049) ∨ (¬ p3537) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p5118) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3537) ∨ (¬ p3553) ∨ (¬ p3609) ∨ (¬ p5049) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial23407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 5049)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory12663 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 2 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule23407 (meaning t m 2027) (meaning t m 2138) (meaning t m 2252) (meaning t m 2748) (meaning t m 3366) (meaning t m 3414) (meaning t m 3537) (meaning t m 3553) (meaning t m 3609) (meaning t m 5049) (meaning t m 5118) (meaning t m 5558) source

theorem rule23409 (p2027 p2210 p2254 p2657 p2891 p3246 p3644 p3742 p4668 : Prop) (h : (¬ p2254) ∨ (¬ p3742) ∨ (¬ p3644) ∨ (¬ p2657) ∨ (¬ p3246) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial23409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory12665 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23409 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2891) (meaning t m 3246) (meaning t m 3644) (meaning t m 3742) (meaning t m 4668) source

theorem rule23411 (p2027 p2210 p2972 p3540 p3644 p3680 p5123 p5193 p5558 : Prop) (h : (¬ p5123) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p5558) ∨ (¬ p3680) ∨ (¬ p3644) ∨ (¬ p3540) ∨ (¬ p5193) ∨ (¬ p2972)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3680) ∨ (¬ p5123) ∨ (¬ p5193) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial23411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory12667 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23411 (meaning t m 2027) (meaning t m 2210) (meaning t m 2972) (meaning t m 3540) (meaning t m 3644) (meaning t m 3680) (meaning t m 5123) (meaning t m 5193) (meaning t m 5558) source

theorem rule23413 (p2027 p2210 p2254 p2963 p2972 p3568 p3680 p4260 p4831 : Prop) (h : (¬ p2972) ∨ (¬ p2254) ∨ (¬ p3568) ∨ (¬ p2210) ∨ (¬ p4831) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p4260)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p2972) ∨ (¬ p3568) ∨ (¬ p3680) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial23413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory12669 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule23413 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2963) (meaning t m 2972) (meaning t m 3568) (meaning t m 3680) (meaning t m 4260) (meaning t m 4831) source

theorem rule23414 (p2027 p2143 p2829 p3583 p4120 p4185 p4507 : Prop) (h : (¬ p3583) ∨ (¬ p2829) ∨ (¬ p4120) ∨ (¬ p4185) ∨ (¬ p2143) ∨ (¬ p4507) ∨ p2027) : (p2027) ∨ (¬ p2143) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4120) ∨ (¬ p4185) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory12670 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 8)
  exact rule23414 (meaning t m 2027) (meaning t m 2143) (meaning t m 2829) (meaning t m 3583) (meaning t m 4120) (meaning t m 4185) (meaning t m 4507) source

theorem rule23415 (p2027 p2132 p2299 p2579 p2588 p3537 p3583 p3589 p4802 p5193 : Prop) (h : (¬ p2579) ∨ (¬ p2299) ∨ (¬ p5193) ∨ (¬ p2132) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4802) ∨ (¬ p3537)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4802) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4802)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12671 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23415 (meaning t m 2027) (meaning t m 2132) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 3537) (meaning t m 3583) (meaning t m 3589) (meaning t m 4802) (meaning t m 5193) source

theorem rule23416 (p2027 p2138 p2774 p3694 p4185 p4507 : Prop) (h : (¬ p3694) ∨ (¬ p4185) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4507) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p3694) ∨ (¬ p4185) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial23416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory12672 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 8)
  exact rule23416 (meaning t m 2027) (meaning t m 2138) (meaning t m 2774) (meaning t m 3694) (meaning t m 4185) (meaning t m 4507) source

theorem rule23418 (p2027 p2417 p3644 p3692 p4443 p4902 : Prop) (h : (¬ p2417) ∨ (¬ p4443) ∨ (¬ p4902) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3692)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12674 t (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule23418 (meaning t m 2027) (meaning t m 2417) (meaning t m 3644) (meaning t m 3692) (meaning t m 4443) (meaning t m 4902) source

theorem rule23419 (p1986 p2027 p2241 p2459 p2699 p2992 p3156 p3367 p4242 p4340 p4902 : Prop) (h : p2699 ∨ (¬ p3156) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p1986) ∨ (¬ p4340)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial23419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory12675 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23419 (meaning t m 1986) (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2699) (meaning t m 2992) (meaning t m 3156) (meaning t m 3367) (meaning t m 4242) (meaning t m 4340) (meaning t m 4902) source

theorem rule23420 (p1990 p2027 p2210 p2284 p2766 p2972 p3540 p3644 p4208 p4348 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p4208) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2972) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p2284) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2284) ∨ (p2766) ∨ (¬ p2972) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4208) ∨ (¬ p4348) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12676 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23420 (meaning t m 1990) (meaning t m 2027) (meaning t m 2210) (meaning t m 2284) (meaning t m 2766) (meaning t m 2972) (meaning t m 3540) (meaning t m 3644) (meaning t m 4208) (meaning t m 4348) (meaning t m 5193) source

theorem rule23421 (p2027 p2241 p2992 p3115 p3540 p3644 p4348 p4450 p5193 : Prop) (h : (¬ p2241) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3540) ∨ (¬ p5193) ∨ (¬ p4450) ∨ (¬ p3644) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12677 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23421 (meaning t m 2027) (meaning t m 2241) (meaning t m 2992) (meaning t m 3115) (meaning t m 3540) (meaning t m 3644) (meaning t m 4348) (meaning t m 4450) (meaning t m 5193) source

theorem rule23422 (p2027 p2210 p2860 p3591 p3957 p4875 : Prop) (h : (¬ p4875) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2210) ∨ (¬ p3957) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2860) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial23422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory12678 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6)
  exact rule23422 (meaning t m 2027) (meaning t m 2210) (meaning t m 2860) (meaning t m 3591) (meaning t m 3957) (meaning t m 4875) source

theorem rule23423 (p2027 p2299 p2579 p2588 p3073 p3449 p3692 p4902 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p2588) ∨ (¬ p4902) ∨ (¬ p2579) ∨ (¬ p2299) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p4902) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12679 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule23423 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 3073) (meaning t m 3449) (meaning t m 3692) (meaning t m 4902) (meaning t m 5193) source

theorem rule23424 (p2027 p3588 p3599 p3690 p4898 p5233 : Prop) (h : (¬ p4898) ∨ (¬ p5233) ∨ (¬ p3588) ∨ p2027 ∨ (¬ p3599) ∨ (¬ p3690)) : (p2027) ∨ (¬ p3588) ∨ (¬ p3599) ∨ (¬ p3690) ∨ (¬ p4898) ∨ (¬ p5233) := by
  classical
  tauto

theorem initial23424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4898)) ∨ (¬ (meaning t m 5233)) := by
  have source := ElevenTheory.theory12680 t (m.theta 1 2) (m.theta 2 7) (m.theta 2 9) (m.theta 5 7) (m.theta 7 9)
  exact rule23424 (meaning t m 2027) (meaning t m 3588) (meaning t m 3599) (meaning t m 3690) (meaning t m 4898) (meaning t m 5233) source

theorem rule23425 (p1975 p2027 p2210 p2699 p2891 p3246 p4107 : Prop) (h : (¬ p4107) ∨ (¬ p1975) ∨ (¬ p2210) ∨ (¬ p2891) ∨ p2027 ∨ p2699 ∨ (¬ p3246)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial23425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory12681 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule23425 (meaning t m 1975) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2891) (meaning t m 3246) (meaning t m 4107) source

theorem rule23426 (p3016 p3343 p4422 : Prop) (h : (¬ p4422) ∨ (¬ p3016) ∨ p3343) : (¬ p3016) ∨ (p3343) ∨ (¬ p4422) := by
  classical
  tauto

theorem initial23426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (meaning t m 3343) ∨ (¬ (meaning t m 4422)) := by
  have source := ElevenTheory.theory12682 (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule23426 (meaning t m 3016) (meaning t m 3343) (meaning t m 4422) source

theorem rule23427 (p2027 p2192 p2210 p2254 p2761 p3125 p3414 p4429 p4621 p5284 : Prop) (h : (¬ p2254) ∨ (¬ p3414) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p4621) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p4429) ∨ (¬ p2761) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2761) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p4429) ∨ (¬ p4621) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial23427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory12683 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23427 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2761) (meaning t m 3125) (meaning t m 3414) (meaning t m 4429) (meaning t m 4621) (meaning t m 5284) source

theorem rule23428 (p3016 p3359 p4422 : Prop) (h : (¬ p4422) ∨ (¬ p3016) ∨ (¬ p3359)) : (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4422) := by
  classical
  tauto

theorem initial23428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4422)) := by
  have source := ElevenTheory.theory12684 (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule23428 (meaning t m 3016) (meaning t m 3359) (meaning t m 4422) source

theorem rule23432 (p2027 p2138 p2252 p2299 p2748 p2963 p3434 p3471 p3568 p4668 p5049 : Prop) (h : (¬ p3434) ∨ (¬ p2748) ∨ (¬ p3471) ∨ (¬ p5049) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p2252) ∨ (¬ p3568) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2252) ∨ (¬ p2299) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p4668) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12688 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23432 (meaning t m 2027) (meaning t m 2138) (meaning t m 2252) (meaning t m 2299) (meaning t m 2748) (meaning t m 2963) (meaning t m 3434) (meaning t m 3471) (meaning t m 3568) (meaning t m 4668) (meaning t m 5049) source

theorem rule23433 (p2027 p2737 p2860 p4173 p4874 p5049 : Prop) (h : (¬ p2737) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p2860) ∨ (¬ p4874) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2860) ∨ (¬ p4173) ∨ (¬ p4874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12689 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule23433 (meaning t m 2027) (meaning t m 2737) (meaning t m 2860) (meaning t m 4173) (meaning t m 4874) (meaning t m 5049) source

theorem rule23436 (p2027 p2138 p2252 p2748 p3292 p3434 p3461 p3471 p4625 p5049 p5284 : Prop) (h : (¬ p2138) ∨ (¬ p5049) ∨ p2027 ∨ (¬ p3292) ∨ (¬ p4625) ∨ (¬ p2252) ∨ (¬ p3471) ∨ (¬ p2748) ∨ (¬ p3434) ∨ (¬ p5284) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p3292) ∨ (¬ p3434) ∨ (¬ p3461) ∨ (¬ p3471) ∨ (¬ p4625) ∨ (¬ p5049) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial23436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5049)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory12692 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7) (m.theta 3 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23436 (meaning t m 2027) (meaning t m 2138) (meaning t m 2252) (meaning t m 2748) (meaning t m 3292) (meaning t m 3434) (meaning t m 3461) (meaning t m 3471) (meaning t m 4625) (meaning t m 5049) (meaning t m 5284) source

theorem rule23439 (p2027 p2210 p2891 p3246 p3365 p3877 p3950 p4118 p4736 : Prop) (h : (¬ p3877) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p3246) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3950)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial23439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory12695 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule23439 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3246) (meaning t m 3365) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4736) source

theorem rule23441 (p2027 p3449 p3555 p4173 p4446 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p4446) ∨ (¬ p3555) ∨ (¬ p3449) ∨ (¬ p4173) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4446) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial23441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12697 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 8)
  exact rule23441 (meaning t m 2027) (meaning t m 3449) (meaning t m 3555) (meaning t m 4173) (meaning t m 4446) (meaning t m 4509) source

theorem rule23445 (p2027 p2210 p3055 p3707 p3876 p4278 p4322 p4395 p4736 p4942 : Prop) (h : (¬ p4278) ∨ (¬ p3055) ∨ (¬ p4395) ∨ (¬ p4322) ∨ (¬ p3707) ∨ (¬ p4942) ∨ (¬ p2210) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p4736)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3707) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4736) ∨ (¬ p4942) := by
  classical
  tauto

theorem initial23445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4942)) := by
  have source := ElevenTheory.theory12701 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 1 9) (m.theta 2 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23445 (meaning t m 2027) (meaning t m 2210) (meaning t m 3055) (meaning t m 3707) (meaning t m 3876) (meaning t m 4278) (meaning t m 4322) (meaning t m 4395) (meaning t m 4736) (meaning t m 4942) source

theorem rule23448 (p2027 p2476 p2518 p2655 p3361 p3541 p3583 p5049 : Prop) (h : (¬ p2655) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p3361) ∨ (¬ p2476) ∨ (¬ p3541) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12704 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 5) (m.theta 4 8)
  exact rule23448 (meaning t m 2027) (meaning t m 2476) (meaning t m 2518) (meaning t m 2655) (meaning t m 3361) (meaning t m 3541) (meaning t m 3583) (meaning t m 5049) source

theorem rule23451 (p3692 p4347 p4506 : Prop) (h : (¬ p4506) ∨ (¬ p4347) ∨ p3692) : (p3692) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial23451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory12707 (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule23451 (meaning t m 3692) (meaning t m 4347) (meaning t m 4506) source

theorem rule23455 (p2027 p2138 p2748 p2928 p3362 p3389 p3402 p5049 : Prop) (h : p2027 ∨ (¬ p5049) ∨ (¬ p2138) ∨ (¬ p3402) ∨ (¬ p3362) ∨ (¬ p2748) ∨ (¬ p3389) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2748) ∨ (¬ p2928) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3402) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial23455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory12711 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 5) (m.theta 4 7)
  exact rule23455 (meaning t m 2027) (meaning t m 2138) (meaning t m 2748) (meaning t m 2928) (meaning t m 3362) (meaning t m 3389) (meaning t m 3402) (meaning t m 5049) source

theorem rule23456 (p2027 p3659 p3670 p4381 p4668 p5234 : Prop) (h : p2027 ∨ (¬ p3659) ∨ (¬ p5234) ∨ (¬ p4668) ∨ (¬ p4381) ∨ (¬ p3670)) : (p2027) ∨ (¬ p3659) ∨ (¬ p3670) ∨ (¬ p4381) ∨ (¬ p4668) ∨ (¬ p5234) := by
  classical
  tauto

theorem initial23456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5234)) := by
  have source := ElevenTheory.theory12712 t (m.theta 2 7) (m.theta 2 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule23456 (meaning t m 2027) (meaning t m 3659) (meaning t m 3670) (meaning t m 4381) (meaning t m 4668) (meaning t m 5234) source

theorem rule23461 (p2027 p2579 p3016 p3399 p3527 p3570 p3742 p4647 p5193 : Prop) (h : (¬ p4647) ∨ (¬ p5193) ∨ (¬ p3742) ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4647) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial23461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory12717 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule23461 (meaning t m 2027) (meaning t m 2579) (meaning t m 3016) (meaning t m 3399) (meaning t m 3527) (meaning t m 3570) (meaning t m 3742) (meaning t m 4647) (meaning t m 5193) source

theorem rule23464 (p2027 p2295 p2737 p2797 p3055 p3584 p3956 p4501 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p2737) ∨ (¬ p2295) ∨ (¬ p2797) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p3584) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12720 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule23464 (meaning t m 2027) (meaning t m 2295) (meaning t m 2737) (meaning t m 2797) (meaning t m 3055) (meaning t m 3584) (meaning t m 3956) (meaning t m 4501) (meaning t m 4734) source

theorem rule23465 (p2027 p2668 p2696 p2797 p3486 p3555 p3570 p4133 p4733 : Prop) (h : (¬ p4133) ∨ (¬ p3570) ∨ (¬ p3486) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2797) ∨ (¬ p2668) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial23465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory12721 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23465 (meaning t m 2027) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4133) (meaning t m 4733) source

theorem rule23467 (p4138 p4347 p4348 : Prop) (h : (¬ p4138) ∨ (¬ p4348) ∨ p4347) : (¬ p4138) ∨ (p4347) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial23467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4138)) ∨ (meaning t m 4347) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory12723 (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23467 (meaning t m 4138) (meaning t m 4347) (meaning t m 4348) source

theorem rule23469 (p2137 p2220 p2619 : Prop) (h : (¬ p2137) ∨ (¬ p2220) ∨ p2619) : (¬ p2137) ∨ (¬ p2220) ∨ (p2619) := by
  classical
  tauto

theorem initial23469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2619) := by
  have source := ElevenTheory.theory12725 (m.theta 0 5) (m.theta 2 5) (m.theta 5 8)
  exact rule23469 (meaning t m 2137) (meaning t m 2220) (meaning t m 2619) source

theorem rule23470 (p2027 p2542 p3367 p3583 p3698 p4750 : Prop) (h : (¬ p3698) ∨ (¬ p3583) ∨ (¬ p3367) ∨ (¬ p4750) ∨ p2027 ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial23470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory12726 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5)
  exact rule23470 (meaning t m 2027) (meaning t m 2542) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 4750) source

theorem rule23471 (p2027 p2220 p2528 p3949 p4032 p4434 : Prop) (h : (¬ p3949) ∨ (¬ p4032) ∨ (¬ p4434) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2528) ∨ (¬ p3949) ∨ (¬ p4032) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial23471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory12727 t (m.theta 0 5) (m.theta 4 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule23471 (meaning t m 2027) (meaning t m 2220) (meaning t m 2528) (meaning t m 3949) (meaning t m 4032) (meaning t m 4434) source

theorem rule23473 (p2027 p2274 p3156 p3568 p4153 p4509 : Prop) (h : p2027 ∨ (¬ p4509) ∨ (¬ p3568) ∨ (¬ p4153) ∨ (¬ p2274) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2274) ∨ (¬ p3156) ∨ (¬ p3568) ∨ (¬ p4153) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial23473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12729 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule23473 (meaning t m 2027) (meaning t m 2274) (meaning t m 3156) (meaning t m 3568) (meaning t m 4153) (meaning t m 4509) source

theorem rule23474 (p2027 p2104 p2598 p3083 p4750 p5369 : Prop) (h : (¬ p5369) ∨ (¬ p2104) ∨ (¬ p4750) ∨ (¬ p2598) ∨ (¬ p3083) ∨ p2027) : (p2027) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (¬ p3083) ∨ (¬ p4750) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial23474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory12730 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 8) (m.theta 3 4) (m.theta 4 8)
  exact rule23474 (meaning t m 2027) (meaning t m 2104) (meaning t m 2598) (meaning t m 3083) (meaning t m 4750) (meaning t m 5369) source

theorem rule23476 (p2027 p2177 p2922 p3379 p3556 p3570 p3645 p3954 p4276 p4877 : Prop) (h : p2027 ∨ (¬ p2922) ∨ (¬ p3954) ∨ (¬ p4877) ∨ (¬ p3379) ∨ (¬ p4276) ∨ (¬ p3645) ∨ (¬ p3556) ∨ (¬ p2177) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3645) ∨ (¬ p3954) ∨ (¬ p4276) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12732 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule23476 (meaning t m 2027) (meaning t m 2177) (meaning t m 2922) (meaning t m 3379) (meaning t m 3556) (meaning t m 3570) (meaning t m 3645) (meaning t m 3954) (meaning t m 4276) (meaning t m 4877) source

theorem rule23477 (p2484 p4113 p4596 : Prop) (h : p4596 ∨ (¬ p2484) ∨ (¬ p4113)) : (¬ p2484) ∨ (¬ p4113) ∨ (p4596) := by
  classical
  tauto

theorem initial23477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2484)) ∨ (¬ (meaning t m 4113)) ∨ (meaning t m 4596) := by
  have source := ElevenTheory.theory12733 t (m.theta 0 8) (m.theta 4 8) (m.theta 6 8)
  exact rule23477 (meaning t m 2484) (meaning t m 4113) (meaning t m 4596) source

theorem rule23480 (p2930 p4001 p4911 : Prop) (h : (¬ p4911) ∨ (¬ p4001) ∨ p2930) : (p2930) ∨ (¬ p4001) ∨ (¬ p4911) := by
  classical
  tauto

theorem initial23480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2930) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4911)) := by
  have source := ElevenTheory.theory12736 t (m.theta 1 7) (m.theta 4 7) (m.theta 5 7)
  exact rule23480 (meaning t m 2930) (meaning t m 4001) (meaning t m 4911) source

theorem rule23482 (p2027 p3005 p3146 p3297 p4035 p4456 p5063 : Prop) (h : p2027 ∨ (¬ p5063) ∨ (¬ p4035) ∨ (¬ p3146) ∨ (¬ p4456) ∨ (¬ p3297) ∨ (¬ p3005)) : (p2027) ∨ (¬ p3005) ∨ (¬ p3146) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4456) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial23482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4456)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory12738 t (m.theta 0 9) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 5 8) (m.theta 8 9)
  exact rule23482 (meaning t m 2027) (meaning t m 3005) (meaning t m 3146) (meaning t m 3297) (meaning t m 4035) (meaning t m 4456) (meaning t m 5063) source

theorem rule23483 (p2027 p2685 p2957 p3646 p4315 p4333 p4558 : Prop) (h : p2027 ∨ (¬ p4333) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p2685) ∨ (¬ p2957) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p4315) ∨ (¬ p4333) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12739 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule23483 (meaning t m 2027) (meaning t m 2685) (meaning t m 2957) (meaning t m 3646) (meaning t m 4315) (meaning t m 4333) (meaning t m 4558) source

theorem rule23484 (p2027 p2210 p2891 p3591 p3957 p4558 : Prop) (h : (¬ p3591) ∨ (¬ p2210) ∨ (¬ p3957) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4558)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12740 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 7)
  exact rule23484 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3591) (meaning t m 3957) (meaning t m 4558) source

theorem rule23485 (p2027 p2427 p2598 p2753 p2850 p4796 p4909 : Prop) (h : p2027 ∨ (¬ p2850) ∨ (¬ p2598) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p4909) ∨ (¬ p4796)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p4796) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial23485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4796)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory12741 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule23485 (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 4796) (meaning t m 4909) source

theorem rule23487 (p2027 p3755 p4195 p4367 p5249 p5717 : Prop) (h : (¬ p4195) ∨ p2027 ∨ (¬ p4367) ∨ (¬ p5249) ∨ (¬ p5717) ∨ (¬ p3755)) : (p2027) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p4367) ∨ (¬ p5249) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial23487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4367)) ∨ (¬ (meaning t m 5249)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory12743 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 10) (m.theta 6 9)
  exact rule23487 (meaning t m 2027) (meaning t m 3755) (meaning t m 4195) (meaning t m 4367) (meaning t m 5249) (meaning t m 5717) source

theorem rule23488 (p2027 p2651 p2753 p3016 p3486 p3564 p3570 p4117 p4330 p4348 p4877 : Prop) (h : (¬ p3486) ∨ (¬ p4348) ∨ (¬ p4330) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3570) ∨ (¬ p2753) ∨ (¬ p4877)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3486) ∨ (¬ p3564) ∨ (¬ p3570) ∨ (¬ p4117) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12744 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23488 (meaning t m 2027) (meaning t m 2651) (meaning t m 2753) (meaning t m 3016) (meaning t m 3486) (meaning t m 3564) (meaning t m 3570) (meaning t m 4117) (meaning t m 4330) (meaning t m 4348) (meaning t m 4877) source

theorem rule23489 (p2027 p2246 p2651 p2749 p3016 p3266 p3564 p3645 p4120 p4322 p4330 p4335 p4877 : Prop) (h : p2027 ∨ (¬ p4120) ∨ (¬ p4877) ∨ (¬ p2246) ∨ (¬ p4330) ∨ (¬ p2749) ∨ (¬ p3645) ∨ (¬ p2651) ∨ (¬ p3564) ∨ (¬ p3016) ∨ (¬ p4322) ∨ (¬ p3266) ∨ (¬ p4335)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3016) ∨ (¬ p3266) ∨ (¬ p3564) ∨ (¬ p3645) ∨ (¬ p4120) ∨ (¬ p4322) ∨ (¬ p4330) ∨ (¬ p4335) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12745 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23489 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2749) (meaning t m 3016) (meaning t m 3266) (meaning t m 3564) (meaning t m 3645) (meaning t m 4120) (meaning t m 4322) (meaning t m 4330) (meaning t m 4335) (meaning t m 4877) source

theorem rule23490 (p2027 p3399 p3547 p3591 p3923 p4501 : Prop) (h : (¬ p3591) ∨ (¬ p3547) ∨ (¬ p3399) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p3923)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial23490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory12746 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 8)
  exact rule23490 (meaning t m 2027) (meaning t m 3399) (meaning t m 3547) (meaning t m 3591) (meaning t m 3923) (meaning t m 4501) source

theorem rule23492 (p2027 p2668 p3550 p3568 p3570 p4556 : Prop) (h : (¬ p2668) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p3550) ∨ (¬ p4556) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial23492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory12748 t (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule23492 (meaning t m 2027) (meaning t m 2668) (meaning t m 3550) (meaning t m 3568) (meaning t m 3570) (meaning t m 4556) source

theorem rule23495 (p2027 p2662 p2810 p3136 p3540 p4241 p4644 : Prop) (h : (¬ p2810) ∨ (¬ p4241) ∨ p2027 ∨ (¬ p4644) ∨ (¬ p3136) ∨ (¬ p3540) ∨ (¬ p2662)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p3540) ∨ (¬ p4241) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial23495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory12751 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7)
  exact rule23495 (meaning t m 2027) (meaning t m 2662) (meaning t m 2810) (meaning t m 3136) (meaning t m 3540) (meaning t m 4241) (meaning t m 4644) source

theorem rule23496 (p2027 p2132 p2427 p3425 p4169 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4169) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2427) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial23496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory12752 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7)
  exact rule23496 (meaning t m 2027) (meaning t m 2132) (meaning t m 2427) (meaning t m 3425) (meaning t m 4169) (meaning t m 4882) source

theorem rule23498 (p2027 p2608 p2753 p2774 p3540 p3914 p4278 p4381 p5193 p5250 : Prop) (h : (¬ p2753) ∨ (¬ p2774) ∨ (¬ p5193) ∨ (¬ p3914) ∨ (¬ p5250) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3540) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3540) ∨ (¬ p3914) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p5193) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial23498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory12754 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule23498 (meaning t m 2027) (meaning t m 2608) (meaning t m 2753) (meaning t m 2774) (meaning t m 3540) (meaning t m 3914) (meaning t m 4278) (meaning t m 4381) (meaning t m 5193) (meaning t m 5250) source

theorem rule23499 (p2027 p2295 p2475 p3998 p4196 p4432 p4501 p5600 : Prop) (h : (¬ p2295) ∨ (¬ p3998) ∨ (¬ p4196) ∨ (¬ p2475) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p4432) ∨ (¬ p5600)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2475) ∨ (¬ p3998) ∨ (¬ p4196) ∨ (¬ p4432) ∨ (¬ p4501) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial23499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory12755 t (m.theta 0 8) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule23499 (meaning t m 2027) (meaning t m 2295) (meaning t m 2475) (meaning t m 3998) (meaning t m 4196) (meaning t m 4432) (meaning t m 4501) (meaning t m 5600) source

theorem rule23500 (p1987 p2027 p2427 p2662 p2765 p2810 p3556 p3904 p4110 : Prop) (h : (¬ p3904) ∨ (¬ p2662) ∨ (¬ p1987) ∨ (¬ p3556) ∨ (¬ p2427) ∨ (¬ p4110) ∨ p2765 ∨ p2027 ∨ (¬ p2810)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2662) ∨ (p2765) ∨ (¬ p2810) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial23500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory12756 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule23500 (meaning t m 1987) (meaning t m 2027) (meaning t m 2427) (meaning t m 2662) (meaning t m 2765) (meaning t m 2810) (meaning t m 3556) (meaning t m 3904) (meaning t m 4110) source

theorem rule23505 (p2027 p2963 p3166 p4358 p4417 p4843 : Prop) (h : (¬ p2963) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4417) ∨ (¬ p4843)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4358) ∨ (¬ p4417) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial23505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory12761 t (m.theta 0 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule23505 (meaning t m 2027) (meaning t m 2963) (meaning t m 3166) (meaning t m 4358) (meaning t m 4417) (meaning t m 4843) source

theorem rule23506 (p2027 p2663 p2952 p3355 p3359 p4701 : Prop) (h : (¬ p2663) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p4701) ∨ (¬ p2952) ∨ (¬ p3355)) : (p2027) ∨ (¬ p2663) ∨ (¬ p2952) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12762 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9)
  exact rule23506 (meaning t m 2027) (meaning t m 2663) (meaning t m 2952) (meaning t m 3355) (meaning t m 3359) (meaning t m 4701) source

theorem rule23507 (p2027 p2651 p3027 p3414 p3662 p4701 : Prop) (h : (¬ p4701) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12763 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule23507 (meaning t m 2027) (meaning t m 2651) (meaning t m 3027) (meaning t m 3414) (meaning t m 3662) (meaning t m 4701) source

theorem rule23510 (p2027 p3506 p3952 p4425 p4952 p5038 p5046 : Prop) (h : (¬ p4425) ∨ (¬ p5046) ∨ p2027 ∨ (¬ p5038) ∨ (¬ p3506) ∨ (¬ p3952) ∨ (¬ p4952)) : (p2027) ∨ (¬ p3506) ∨ (¬ p3952) ∨ (¬ p4425) ∨ (¬ p4952) ∨ (¬ p5038) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial23510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4952)) ∨ (¬ (meaning t m 5038)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory12766 t (m.theta 3 5) (m.theta 3 9) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule23510 (meaning t m 2027) (meaning t m 3506) (meaning t m 3952) (meaning t m 4425) (meaning t m 4952) (meaning t m 5038) (meaning t m 5046) source

theorem rule23511 (p2027 p2951 p2992 p3212 p3745 p4154 p5046 : Prop) (h : (¬ p2992) ∨ (¬ p2951) ∨ (¬ p3212) ∨ p2027 ∨ (¬ p5046) ∨ (¬ p4154) ∨ (¬ p3745)) : (p2027) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3212) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial23511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory12767 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9)
  exact rule23511 (meaning t m 2027) (meaning t m 2951) (meaning t m 2992) (meaning t m 3212) (meaning t m 3745) (meaning t m 4154) (meaning t m 5046) source

theorem rule23512 (p2027 p2264 p2299 p3097 p4156 p4560 : Prop) (h : (¬ p4156) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4560) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p4156) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial23512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory12768 t (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule23512 (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 3097) (meaning t m 4156) (meaning t m 4560) source

theorem rule23515 (p2027 p2662 p3222 p3346 p3662 p4281 p4701 : Prop) (h : (¬ p4281) ∨ (¬ p3346) ∨ (¬ p3222) ∨ (¬ p2662) ∨ (¬ p3662) ∨ (¬ p4701) ∨ p2027) : (p2027) ∨ (¬ p2662) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3662) ∨ (¬ p4281) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial23515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory12771 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9)
  exact rule23515 (meaning t m 2027) (meaning t m 2662) (meaning t m 3222) (meaning t m 3346) (meaning t m 3662) (meaning t m 4281) (meaning t m 4701) source

theorem rule23518 (p2027 p2132 p2663 p2891 p3246 p3363 p3414 p3553 p3585 p4418 p4668 p4737 : Prop) (h : (¬ p4418) ∨ (¬ p4668) ∨ (¬ p2132) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2663) ∨ (¬ p3363) ∨ (¬ p4737) ∨ (¬ p2891) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2663) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3363) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3585) ∨ (¬ p4418) ∨ (¬ p4668) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial23518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory12774 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule23518 (meaning t m 2027) (meaning t m 2132) (meaning t m 2663) (meaning t m 2891) (meaning t m 3246) (meaning t m 3363) (meaning t m 3414) (meaning t m 3553) (meaning t m 3585) (meaning t m 4418) (meaning t m 4668) (meaning t m 4737) source

theorem rule23520 (p2027 p2190 p2427 p2534 p3146 p4558 p4607 : Prop) (h : (¬ p4607) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p2534) ∨ (¬ p2190) ∨ p2027 ∨ (¬ p4558)) : (p2027) ∨ (¬ p2190) ∨ (¬ p2427) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p4558) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial23520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory12776 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule23520 (meaning t m 2027) (meaning t m 2190) (meaning t m 2427) (meaning t m 2534) (meaning t m 3146) (meaning t m 4558) (meaning t m 4607) source

theorem rule23522 (p2027 p2696 p2761 p2797 p3323 p3346 p4425 p4621 p4729 : Prop) (h : (¬ p2761) ∨ (¬ p3323) ∨ (¬ p4425) ∨ (¬ p2696) ∨ (¬ p4621) ∨ p2027 ∨ (¬ p3346) ∨ (¬ p2797) ∨ (¬ p4729)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2761) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p4621) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory12778 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule23522 (meaning t m 2027) (meaning t m 2696) (meaning t m 2761) (meaning t m 2797) (meaning t m 3323) (meaning t m 3346) (meaning t m 4425) (meaning t m 4621) (meaning t m 4729) source

theorem rule23523 (p2027 p2459 p2476 p2534 p2668 p2696 p2797 p4133 p4729 : Prop) (h : (¬ p2476) ∨ (¬ p4729) ∨ (¬ p2696) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p2534) ∨ (¬ p2459) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4133) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial23523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory12779 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule23523 (meaning t m 2027) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2668) (meaning t m 2696) (meaning t m 2797) (meaning t m 4133) (meaning t m 4729) source

theorem rule23524 (p2027 p2589 p3347 p3707 p3830 p3880 p3954 p5123 p5216 p5568 : Prop) (h : (¬ p2589) ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p3954) ∨ (¬ p3707) ∨ (¬ p3880) ∨ (¬ p3830) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p5123)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial23524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory12780 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23524 (meaning t m 2027) (meaning t m 2589) (meaning t m 3347) (meaning t m 3707) (meaning t m 3830) (meaning t m 3880) (meaning t m 3954) (meaning t m 5123) (meaning t m 5216) (meaning t m 5568) source

theorem rule23525 (p2027 p3516 p3545 p3817 p3954 p4796 : Prop) (h : p2027 ∨ (¬ p3954) ∨ (¬ p4796) ∨ (¬ p3545) ∨ (¬ p3817) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3817) ∨ (¬ p3954) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial23525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory12781 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 7 9)
  exact rule23525 (meaning t m 2027) (meaning t m 3516) (meaning t m 3545) (meaning t m 3817) (meaning t m 3954) (meaning t m 4796) source

theorem rule23526 (p2027 p2579 p3347 p3707 p3830 p3954 p3956 p5123 p5216 p5580 : Prop) (h : (¬ p3830) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3707) ∨ (¬ p3954) ∨ (¬ p3347) ∨ (¬ p3956) ∨ (¬ p2579) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial23526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory12782 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23526 (meaning t m 2027) (meaning t m 2579) (meaning t m 3347) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 3956) (meaning t m 5123) (meaning t m 5216) (meaning t m 5580) source

theorem rule23533 (p2027 p2727 p3506 p3846 p4321 p5008 p5111 : Prop) (h : (¬ p4321) ∨ p2027 ∨ (¬ p5008) ∨ (¬ p3506) ∨ (¬ p5111) ∨ (¬ p3846) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3506) ∨ (¬ p3846) ∨ (¬ p4321) ∨ (¬ p5008) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial23533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3846)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5008)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory12789 t (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 3 8) (m.theta 3 9) (m.theta 9 10)
  exact rule23533 (meaning t m 2027) (meaning t m 2727) (meaning t m 3506) (meaning t m 3846) (meaning t m 4321) (meaning t m 5008) (meaning t m 5111) source

theorem rule23535 (p2027 p2156 p3362 p3365 p3758 p4399 p5052 : Prop) (h : (¬ p3362) ∨ (¬ p5052) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3758) ∨ (¬ p4399) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3758) ∨ (¬ p4399) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial23535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory12791 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule23535 (meaning t m 2027) (meaning t m 2156) (meaning t m 3362) (meaning t m 3365) (meaning t m 3758) (meaning t m 4399) (meaning t m 5052) source

theorem rule23543 (p2510 p4608 p4715 : Prop) (h : (¬ p2510) ∨ (¬ p4715) ∨ p4608) : (¬ p2510) ∨ (p4608) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial23543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (meaning t m 4608) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory12799 t (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule23543 (meaning t m 2510) (meaning t m 4608) (meaning t m 4715) source

theorem rule23544 (p2027 p2156 p3309 p3957 p4120 p4501 p4506 : Prop) (h : (¬ p3957) ∨ (¬ p4501) ∨ (¬ p4120) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p4506) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3309) ∨ (¬ p3957) ∨ (¬ p4120) ∨ (¬ p4501) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial23544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory12800 t (m.theta 0 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule23544 (meaning t m 2027) (meaning t m 2156) (meaning t m 3309) (meaning t m 3957) (meaning t m 4120) (meaning t m 4501) (meaning t m 4506) source

theorem rule23545 (p2027 p2132 p2780 p2870 p3096 p4342 p4558 : Prop) (h : (¬ p2132) ∨ (¬ p4342) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p3096) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4342) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial23545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory12801 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule23545 (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 2870) (meaning t m 3096) (meaning t m 4342) (meaning t m 4558) source

theorem rule23546 (p3365 p3619 p5453 : Prop) (h : (¬ p3619) ∨ (¬ p3365) ∨ (¬ p5453)) : (¬ p3365) ∨ (¬ p3619) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial23546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory12802 (m.theta 0 2) (m.theta 2 3) (m.theta 2 9)
  exact rule23546 (meaning t m 3365) (meaning t m 3619) (meaning t m 5453) source

theorem rule23551 (p2027 p2619 p3246 p3872 p4136 p4324 p4509 : Prop) (h : (¬ p4136) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p3872) ∨ (¬ p4324) ∨ (¬ p3246) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial23551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory12807 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule23551 (meaning t m 2027) (meaning t m 2619) (meaning t m 3246) (meaning t m 3872) (meaning t m 4136) (meaning t m 4324) (meaning t m 4509) source

theorem rule23552 (p2027 p2210 p3238 p3695 p3954 p4243 p5216 : Prop) (h : (¬ p3695) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3954) ∨ (¬ p2210) ∨ (¬ p3238) ∨ (¬ p4243)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3238) ∨ (¬ p3695) ∨ (¬ p3954) ∨ (¬ p4243) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12808 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 5) (m.theta 4 5)
  exact rule23552 (meaning t m 2027) (meaning t m 2210) (meaning t m 3238) (meaning t m 3695) (meaning t m 3954) (meaning t m 4243) (meaning t m 5216) source

theorem rule23553 (p2027 p2696 p2753 p2797 p3347 p3540 p4228 p4278 p4381 p5216 p5250 : Prop) (h : p2027 ∨ (¬ p5216) ∨ (¬ p4381) ∨ (¬ p4278) ∨ (¬ p3540) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p5250) ∨ (¬ p4228)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4228) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p5216) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial23553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory12809 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule23553 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3347) (meaning t m 3540) (meaning t m 4228) (meaning t m 4278) (meaning t m 4381) (meaning t m 5216) (meaning t m 5250) source

theorem rule23554 (p2027 p2427 p2696 p2753 p3005 p3256 p3556 p3645 p4877 p4948 p5059 : Prop) (h : (¬ p2753) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p2696) ∨ (¬ p5059) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p4877) ∨ (¬ p2427) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4877) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial23554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory12810 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule23554 (meaning t m 2027) (meaning t m 2427) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3256) (meaning t m 3556) (meaning t m 3645) (meaning t m 4877) (meaning t m 4948) (meaning t m 5059) source

theorem rule23556 (p2027 p2417 p2870 p4385 p4387 p4647 p5358 : Prop) (h : p2027 ∨ (¬ p2870) ∨ (¬ p2417) ∨ (¬ p4387) ∨ (¬ p4385) ∨ (¬ p4647) ∨ (¬ p5358)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2870) ∨ (¬ p4385) ∨ (¬ p4387) ∨ (¬ p4647) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial23556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory12812 t (m.theta 1 9) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule23556 (meaning t m 2027) (meaning t m 2417) (meaning t m 2870) (meaning t m 4385) (meaning t m 4387) (meaning t m 4647) (meaning t m 5358) source

theorem rule23557 (p2027 p2696 p2753 p2797 p2911 p3323 p3546 p3551 p4278 p4621 p4796 : Prop) (h : (¬ p2911) ∨ (¬ p3546) ∨ (¬ p4796) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p3323) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p3323) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial23557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory12813 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule23557 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 2911) (meaning t m 3323) (meaning t m 3546) (meaning t m 3551) (meaning t m 4278) (meaning t m 4621) (meaning t m 4796) source

theorem rule23558 (p2027 p2696 p2753 p2797 p3323 p3347 p3540 p3644 p4330 p4348 p5216 : Prop) (h : (¬ p3347) ∨ (¬ p3323) ∨ (¬ p4348) ∨ (¬ p4330) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2797) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial23558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory12814 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23558 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3323) (meaning t m 3347) (meaning t m 3540) (meaning t m 3644) (meaning t m 4330) (meaning t m 4348) (meaning t m 5216) source

theorem rule23559 (p2027 p2696 p2753 p2797 p3323 p3556 p3570 p3645 p4330 p4348 p4877 : Prop) (h : (¬ p3645) ∨ (¬ p3323) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p4877) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p2753) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3645) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial23559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory12815 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule23559 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3323) (meaning t m 3556) (meaning t m 3570) (meaning t m 3645) (meaning t m 4330) (meaning t m 4348) (meaning t m 4877) source

theorem rule23560 (p2027 p2696 p2797 p2881 p3323 p3551 p3690 p4621 p5260 : Prop) (h : (¬ p5260) ∨ (¬ p2696) ∨ (¬ p3323) ∨ (¬ p2797) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2881) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p2881) ∨ (¬ p3323) ∨ (¬ p3551) ∨ (¬ p3690) ∨ (¬ p4621) ∨ (¬ p5260) := by
  classical
  tauto

theorem initial23560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5260)) := by
  have source := ElevenTheory.theory12816 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule23560 (meaning t m 2027) (meaning t m 2696) (meaning t m 2797) (meaning t m 2881) (meaning t m 3323) (meaning t m 3551) (meaning t m 3690) (meaning t m 4621) (meaning t m 5260) source

theorem rule23561 (p2668 p2819 p4328 : Prop) (h : (¬ p4328) ∨ (¬ p2668) ∨ p2819) : (¬ p2668) ∨ (p2819) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial23561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (meaning t m 2819) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory12817 (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule23561 (meaning t m 2668) (meaning t m 2819) (meaning t m 4328) source

theorem rule23562 (p2027 p2696 p2753 p3347 p3506 p3540 p3644 p3755 p5123 p5216 p5558 : Prop) (h : (¬ p3644) ∨ (¬ p5558) ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p5216) ∨ (¬ p3755) ∨ (¬ p3506) ∨ p2027 ∨ (¬ p5123)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3506) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3755) ∨ (¬ p5123) ∨ (¬ p5216) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial23562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5216)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory12818 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule23562 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3347) (meaning t m 3506) (meaning t m 3540) (meaning t m 3644) (meaning t m 3755) (meaning t m 5123) (meaning t m 5216) (meaning t m 5558) source

theorem rule23563 (p2027 p2210 p3319 p3946 p4869 p4877 p5015 : Prop) (h : (¬ p2210) ∨ p2027 ∨ (¬ p4877) ∨ (¬ p5015) ∨ (¬ p3946) ∨ (¬ p3319) ∨ (¬ p4869)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4869) ∨ (¬ p4877) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial23563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory12819 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 6 9)
  exact rule23563 (meaning t m 2027) (meaning t m 2210) (meaning t m 3319) (meaning t m 3946) (meaning t m 4869) (meaning t m 4877) (meaning t m 5015) source

theorem rule23564 (p1975 p2027 p2766 p2819 p3266 p3917 p3955 p4191 : Prop) (h : p2766 ∨ (¬ p3955) ∨ (¬ p1975) ∨ (¬ p3917) ∨ (¬ p2819) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p4191)) : (¬ p1975) ∨ (p2027) ∨ (p2766) ∨ (¬ p2819) ∨ (¬ p3266) ∨ (¬ p3917) ∨ (¬ p3955) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial23564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory12820 t (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule23564 (meaning t m 1975) (meaning t m 2027) (meaning t m 2766) (meaning t m 2819) (meaning t m 3266) (meaning t m 3917) (meaning t m 3955) (meaning t m 4191) source

theorem rule23565 (p2027 p2247 p3093 p3922 p4111 p4975 : Prop) (h : (¬ p4975) ∨ (¬ p3922) ∨ (¬ p2247) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3093)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4111) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial23565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory12821 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6)
  exact rule23565 (meaning t m 2027) (meaning t m 2247) (meaning t m 3093) (meaning t m 3922) (meaning t m 4111) (meaning t m 4975) source

theorem rule23566 (p2027 p2138 p2891 p3371 p4244 p4734 : Prop) (h : p2027 ∨ (¬ p4734) ∨ (¬ p2138) ∨ (¬ p2891) ∨ (¬ p4244) ∨ (¬ p3371)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2891) ∨ (¬ p3371) ∨ (¬ p4244) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial23566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory12822 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule23566 (meaning t m 2027) (meaning t m 2138) (meaning t m 2891) (meaning t m 3371) (meaning t m 4244) (meaning t m 4734) source

end SunPrize.SMT
