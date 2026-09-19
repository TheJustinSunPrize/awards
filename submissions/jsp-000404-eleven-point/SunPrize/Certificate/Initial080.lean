import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory064
import SunPrize.Certificate.Theory065
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule37182 (p2027 p2104 p2417 p2696 p2761 p3389 p3759 p4749 p5123 p5612 : Prop) (h : (¬ p2696) ∨ (¬ p5612) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2761) ∨ (¬ p3759) ∨ (¬ p3389) ∨ (¬ p2417) ∨ (¬ p4749) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2417) ∨ (¬ p2696) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial37182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory26438 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 4 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule37182 (meaning t m 2027) (meaning t m 2104) (meaning t m 2417) (meaning t m 2696) (meaning t m 2761) (meaning t m 3389) (meaning t m 3759) (meaning t m 4749) (meaning t m 5123) (meaning t m 5612) source

theorem rule37183 (p2027 p2995 p3880 p4019 p4705 p4777 p4805 p5568 : Prop) (h : (¬ p2995) ∨ (¬ p4805) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p4019) ∨ (¬ p3880) ∨ (¬ p4777) ∨ (¬ p5568)) : (p2027) ∨ (¬ p2995) ∨ (¬ p3880) ∨ (¬ p4019) ∨ (¬ p4705) ∨ (¬ p4777) ∨ (¬ p4805) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial37183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4705)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory26439 t (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10)
  exact rule37183 (meaning t m 2027) (meaning t m 2995) (meaning t m 3880) (meaning t m 4019) (meaning t m 4705) (meaning t m 4777) (meaning t m 4805) (meaning t m 5568) source

theorem rule37187 (p2027 p2245 p2553 p2598 p2881 p3414 p3422 p3553 p4559 p4733 : Prop) (h : (¬ p2598) ∨ (¬ p2881) ∨ (¬ p4559) ∨ (¬ p3422) ∨ (¬ p4733) ∨ (¬ p2245) ∨ (¬ p2553) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p3553)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p4559) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26443 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37187 (meaning t m 2027) (meaning t m 2245) (meaning t m 2553) (meaning t m 2598) (meaning t m 2881) (meaning t m 3414) (meaning t m 3422) (meaning t m 3553) (meaning t m 4559) (meaning t m 4733) source

theorem rule37194 (p2027 p2839 p2870 p4242 p4740 p4901 : Prop) (h : (¬ p2870) ∨ (¬ p4901) ∨ (¬ p4740) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p4242)) : (p2027) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p4242) ∨ (¬ p4740) ∨ (¬ p4901) := by
  classical
  tauto

theorem initial37194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4740)) ∨ (¬ (meaning t m 4901)) := by
  have source := ElevenTheory.theory26450 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 7) (m.theta 5 8)
  exact rule37194 (meaning t m 2027) (meaning t m 2839) (meaning t m 2870) (meaning t m 4242) (meaning t m 4740) (meaning t m 4901) source

theorem rule37205 (p2027 p2753 p2829 p3363 p3365 p3540 p3914 p4278 p4381 p4752 p5250 : Prop) (h : (¬ p3914) ∨ (¬ p4752) ∨ (¬ p3363) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4381) ∨ p2753 ∨ (¬ p5250) ∨ (¬ p3365) ∨ (¬ p4278) ∨ (¬ p2829)) : (p2027) ∨ (p2753) ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3365) ∨ (¬ p3540) ∨ (¬ p3914) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4752) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial37205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (meaning t m 2753) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory26461 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule37205 (meaning t m 2027) (meaning t m 2753) (meaning t m 2829) (meaning t m 3363) (meaning t m 3365) (meaning t m 3540) (meaning t m 3914) (meaning t m 4278) (meaning t m 4381) (meaning t m 4752) (meaning t m 5250) source

theorem rule37207 (p1985 p2027 p2264 p2622 p3365 p3471 p3570 p4325 : Prop) (h : (¬ p3570) ∨ (¬ p2264) ∨ (¬ p4325) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p3471) ∨ p2622 ∨ (¬ p3365)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2264) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3570) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial37207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory26463 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule37207 (meaning t m 1985) (meaning t m 2027) (meaning t m 2264) (meaning t m 2622) (meaning t m 3365) (meaning t m 3471) (meaning t m 3570) (meaning t m 4325) source

theorem rule37208 (p2027 p2870 p3146 p4243 p4261 p4492 p4901 : Prop) (h : (¬ p3146) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p4243) ∨ (¬ p4901) ∨ (¬ p4492) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3146) ∨ (¬ p4243) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4901) := by
  classical
  tauto

theorem initial37208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4901)) := by
  have source := ElevenTheory.theory26464 t (m.theta 1 5) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule37208 (meaning t m 2027) (meaning t m 2870) (meaning t m 3146) (meaning t m 4243) (meaning t m 4261) (meaning t m 4492) (meaning t m 4901) source

theorem rule37210 (p1985 p2027 p2202 p2518 p2531 p2901 p3238 p3497 : Prop) (h : p2202 ∨ (¬ p1985) ∨ (¬ p2901) ∨ (¬ p2531) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p3238) ∨ (¬ p3497)) : (¬ p1985) ∨ (p2027) ∨ (p2202) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p2901) ∨ (¬ p3238) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial37210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory26466 t (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule37210 (meaning t m 1985) (meaning t m 2027) (meaning t m 2202) (meaning t m 2518) (meaning t m 2531) (meaning t m 2901) (meaning t m 3238) (meaning t m 3497) source

theorem rule37215 (p2027 p2230 p2440 p2663 p3292 p5172 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3292) ∨ (¬ p5172)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3292) ∨ (¬ p5172) := by
  classical
  tauto

theorem initial37215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 5172)) := by
  have source := ElevenTheory.theory26471 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5)
  exact rule37215 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 3292) (meaning t m 5172) source

theorem rule37217 (p2027 p2284 p3027 p3368 p3413 p4173 p4652 : Prop) (h : (¬ p3413) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4652) ∨ (¬ p3368) ∨ (¬ p3027) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3027) ∨ (¬ p3368) ∨ (¬ p3413) ∨ (¬ p4173) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial37217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory26473 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule37217 (meaning t m 2027) (meaning t m 2284) (meaning t m 3027) (meaning t m 3368) (meaning t m 3413) (meaning t m 4173) (meaning t m 4652) source

theorem rule37222 (p2027 p2995 p3516 p3690 p4066 p4235 p4705 : Prop) (h : (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4705) ∨ (¬ p3516) ∨ (¬ p2995) ∨ p2027 ∨ (¬ p3690)) : (p2027) ∨ (¬ p2995) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial37222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory26478 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule37222 (meaning t m 2027) (meaning t m 2995) (meaning t m 3516) (meaning t m 3690) (meaning t m 4066) (meaning t m 4235) (meaning t m 4705) source

theorem rule37223 (p2027 p2299 p2696 p2753 p3115 p3136 p3549 p4348 p4450 p4870 : Prop) (h : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3115) ∨ (¬ p3549) ∨ (¬ p4870) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p2299) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial37223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory26479 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37223 (meaning t m 2027) (meaning t m 2299) (meaning t m 2696) (meaning t m 2753) (meaning t m 3115) (meaning t m 3136) (meaning t m 3549) (meaning t m 4348) (meaning t m 4450) (meaning t m 4870) source

theorem rule37227 (p3054 p3583 p3585 : Prop) (h : (¬ p3054) ∨ (¬ p3585) ∨ p3583) : (¬ p3054) ∨ (p3583) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial37227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3054)) ∨ (meaning t m 3583) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory26483 (m.theta 1 2) (m.theta 2 4) (m.theta 2 5)
  exact rule37227 (meaning t m 3054) (meaning t m 3583) (meaning t m 3585) source

theorem rule37228 (p1997 p2027 p2246 p2651 p2685 p2688 p2810 p4235 p4333 : Prop) (h : (¬ p1997) ∨ p2027 ∨ (¬ p2651) ∨ p2688 ∨ (¬ p2246) ∨ (¬ p2810) ∨ (¬ p2685) ∨ (¬ p4235) ∨ (¬ p4333)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (p2688) ∨ (¬ p2810) ∨ (¬ p4235) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial37228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory26484 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule37228 (meaning t m 1997) (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2685) (meaning t m 2688) (meaning t m 2810) (meaning t m 4235) (meaning t m 4333) source

theorem rule37230 (p2027 p2331 p3170 p3256 p3857 p4121 p4975 : Prop) (h : (¬ p3170) ∨ (¬ p2331) ∨ (¬ p3857) ∨ (¬ p4975) ∨ (¬ p4121) ∨ (¬ p3256) ∨ p2027) : (p2027) ∨ (¬ p2331) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4121) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial37230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory26486 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule37230 (meaning t m 2027) (meaning t m 2331) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) (meaning t m 4121) (meaning t m 4975) source

theorem rule37231 (p4261 p5315 p5343 p5344 : Prop) (h : (¬ p4261) ∨ (¬ p5315) ∨ (¬ p5343) ∨ (¬ p5344)) : (¬ p4261) ∨ (¬ p5315) ∨ (¬ p5343) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial37231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5315)) ∨ (¬ (meaning t m 5343)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory26487 (m.theta 1 8) (m.theta 2 8) (m.theta 2 9) (m.theta 8 9)
  exact rule37231 (meaning t m 4261) (meaning t m 5315) (meaning t m 5343) (meaning t m 5344) source

theorem rule37232 (p4395 p4445 p4450 : Prop) (h : (¬ p4450) ∨ (¬ p4445) ∨ p4395) : (p4395) ∨ (¬ p4445) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial37232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4395) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory26488 t (m.theta 5 9) (m.theta 7 9) (m.theta 8 9)
  exact rule37232 (meaning t m 4395) (meaning t m 4445) (meaning t m 4450) source

theorem rule37233 (p2027 p2299 p2313 p2696 p3115 p3136 p4348 p4450 p4733 p5015 : Prop) (h : (¬ p2696) ∨ (¬ p5015) ∨ (¬ p4733) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p3115) ∨ (¬ p2299) ∨ (¬ p4348) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4733) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial37233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory26489 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37233 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2696) (meaning t m 3115) (meaning t m 3136) (meaning t m 4348) (meaning t m 4450) (meaning t m 4733) (meaning t m 5015) source

theorem rule37238 (p2027 p2246 p2608 p2744 p2901 p2946 p3834 p4129 p4321 p4826 : Prop) (h : (¬ p2744) ∨ (¬ p4129) ∨ (¬ p2246) ∨ (¬ p2946) ∨ (¬ p2608) ∨ (¬ p2901) ∨ (¬ p4826) ∨ (¬ p4321) ∨ p2027 ∨ (¬ p3834)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3834) ∨ (¬ p4129) ∨ (¬ p4321) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial37238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory26494 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule37238 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3834) (meaning t m 4129) (meaning t m 4321) (meaning t m 4826) source

theorem rule37240 (p1986 p2027 p2765 p2785 p3125 p3367 p3688 p3946 : Prop) (h : (¬ p2785) ∨ (¬ p1986) ∨ p2027 ∨ p2765 ∨ (¬ p3367) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p3688)) : (¬ p1986) ∨ (p2027) ∨ (p2765) ∨ (¬ p2785) ∨ (¬ p3125) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial37240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory26496 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 5 6) (m.theta 6 9)
  exact rule37240 (meaning t m 1986) (meaning t m 2027) (meaning t m 2765) (meaning t m 2785) (meaning t m 3125) (meaning t m 3367) (meaning t m 3688) (meaning t m 3946) source

theorem rule37241 (p2027 p2476 p2534 p2753 p2829 p3363 p3365 p3914 p4444 p4752 p5250 : Prop) (h : (¬ p4444) ∨ p2753 ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p5250) ∨ (¬ p3365) ∨ (¬ p3363) ∨ (¬ p3914) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2753) ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3365) ∨ (¬ p3914) ∨ (¬ p4444) ∨ (¬ p4752) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial37241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2753) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory26497 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule37241 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2753) (meaning t m 2829) (meaning t m 3363) (meaning t m 3365) (meaning t m 3914) (meaning t m 4444) (meaning t m 4752) (meaning t m 5250) source

theorem rule37242 (p4039 p4322 p5284 : Prop) (h : (¬ p4039) ∨ (¬ p5284) ∨ p4322) : (¬ p4039) ∨ (p4322) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial37242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4039)) ∨ (meaning t m 4322) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory26498 (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule37242 (meaning t m 4039) (meaning t m 4322) (meaning t m 5284) source

theorem rule37247 (p2027 p2373 p2870 p3694 p4110 p4558 : Prop) (h : (¬ p2373) ∨ (¬ p4110) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p4110) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial37247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory26503 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule37247 (meaning t m 2027) (meaning t m 2373) (meaning t m 2870) (meaning t m 3694) (meaning t m 4110) (meaning t m 4558) source

theorem rule37250 (p1987 p2027 p2737 p2764 p3583 p4322 p4385 : Prop) (h : (¬ p2737) ∨ (¬ p4322) ∨ (¬ p3583) ∨ p2027 ∨ p2764 ∨ (¬ p1987) ∨ (¬ p4385)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2764) ∨ (¬ p3583) ∨ (¬ p4322) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial37250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory26506 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 9) (m.theta 9 10)
  exact rule37250 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2764) (meaning t m 3583) (meaning t m 4322) (meaning t m 4385) source

theorem rule37255 (p2027 p2241 p2387 p2449 p3027 p3266 p3322 p3950 p4191 p5021 : Prop) (h : (¬ p2241) ∨ (¬ p3950) ∨ (¬ p5021) ∨ (¬ p2449) ∨ (¬ p3322) ∨ (¬ p2387) ∨ (¬ p3266) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4191)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3950) ∨ (¬ p4191) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial37255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory26511 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37255 (meaning t m 2027) (meaning t m 2241) (meaning t m 2387) (meaning t m 2449) (meaning t m 3027) (meaning t m 3266) (meaning t m 3322) (meaning t m 3950) (meaning t m 4191) (meaning t m 5021) source

theorem rule37259 (p2027 p2363 p3063 p3692 p3988 p4319 p4560 : Prop) (h : p2027 ∨ (¬ p4319) ∨ (¬ p3063) ∨ (¬ p4560) ∨ (¬ p2363) ∨ (¬ p3988) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4319) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial37259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory26515 t (m.theta 1 6) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37259 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 3692) (meaning t m 3988) (meaning t m 4319) (meaning t m 4560) source

theorem rule37262 (p2027 p2295 p2696 p2753 p2797 p4427 p4796 : Prop) (h : (¬ p2753) ∨ p2027 ∨ (¬ p4796) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p2295) ∨ (¬ p4427)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p4427) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial37262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory26518 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule37262 (meaning t m 2027) (meaning t m 2295) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 4427) (meaning t m 4796) source

theorem rule37264 (p3063 p3319 p3322 : Prop) (h : (¬ p3322) ∨ (¬ p3319) ∨ p3063) : (p3063) ∨ (¬ p3319) ∨ (¬ p3322) := by
  classical
  tauto

theorem initial37264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3063) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3322)) := by
  have source := ElevenTheory.theory26520 (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule37264 (meaning t m 3063) (meaning t m 3319) (meaning t m 3322) source

theorem rule37267 (p2027 p2132 p2870 p3540 p3905 p4647 : Prop) (h : (¬ p2132) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p4647) ∨ (¬ p3540) ∨ (¬ p3905)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial37267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory26523 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7)
  exact rule37267 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 3540) (meaning t m 3905) (meaning t m 4647) source

theorem rule37268 (p2132 p2707 p2753 p3587 : Prop) (h : (¬ p2753) ∨ (¬ p3587) ∨ (¬ p2132) ∨ p2707) : (¬ p2132) ∨ (p2707) ∨ (¬ p2753) ∨ (¬ p3587) := by
  classical
  tauto

theorem initial37268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (meaning t m 2707) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3587)) := by
  have source := ElevenTheory.theory26524 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule37268 (meaning t m 2132) (meaning t m 2707) (meaning t m 2753) (meaning t m 3587) source

theorem rule37269 (p3426 p3587 p3985 : Prop) (h : (¬ p3426) ∨ (¬ p3985) ∨ p3587) : (¬ p3426) ∨ (p3587) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial37269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3426)) ∨ (meaning t m 3587) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory26525 (m.theta 2 5) (m.theta 2 6) (m.theta 2 7)
  exact rule37269 (meaning t m 3426) (meaning t m 3587) (meaning t m 3985) source

theorem rule37270 (p1998 p2027 p2177 p2274 p2542 p2545 p2563 : Prop) (h : (¬ p2274) ∨ (¬ p1998) ∨ (¬ p2177) ∨ p2027 ∨ p2545 ∨ (¬ p2542) ∨ (¬ p2563)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial37270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory26526 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule37270 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2542) (meaning t m 2545) (meaning t m 2563) source

theorem rule37277 (p1976 p2027 p2545 p3016 p3055 p3367 p3688 p4342 : Prop) (h : (¬ p3367) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p1976) ∨ (¬ p3688) ∨ (¬ p4342) ∨ p2545 ∨ (¬ p3016)) : (¬ p1976) ∨ (p2027) ∨ (p2545) ∨ (¬ p3016) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial37277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory26533 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule37277 (meaning t m 1976) (meaning t m 2027) (meaning t m 2545) (meaning t m 3016) (meaning t m 3055) (meaning t m 3367) (meaning t m 3688) (meaning t m 4342) source

theorem rule37278 (p2027 p3952 p4009 p4188 p4237 p4509 p5612 : Prop) (h : (¬ p4509) ∨ (¬ p5612) ∨ (¬ p3952) ∨ (¬ p4009) ∨ p2027 ∨ (¬ p4188) ∨ (¬ p4237)) : (p2027) ∨ (¬ p3952) ∨ (¬ p4009) ∨ (¬ p4188) ∨ (¬ p4237) ∨ (¬ p4509) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial37278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory26534 t (m.theta 2 8) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule37278 (meaning t m 2027) (meaning t m 3952) (meaning t m 4009) (meaning t m 4188) (meaning t m 4237) (meaning t m 4509) (meaning t m 5612) source

theorem rule37281 (p1987 p2027 p2553 p2737 p2785 p3008 p3567 p3568 p3688 : Prop) (h : (¬ p3567) ∨ (¬ p3688) ∨ (¬ p2785) ∨ p2027 ∨ (¬ p1987) ∨ p3008 ∨ (¬ p2737) ∨ (¬ p2553) ∨ (¬ p3568)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (p3008) ∨ (¬ p3567) ∨ (¬ p3568) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial37281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory26537 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule37281 (meaning t m 1987) (meaning t m 2027) (meaning t m 2553) (meaning t m 2737) (meaning t m 2785) (meaning t m 3008) (meaning t m 3567) (meaning t m 3568) (meaning t m 3688) source

theorem rule37282 (p1987 p2027 p2313 p2553 p2737 p2785 p3008 p3688 : Prop) (h : (¬ p2785) ∨ p2027 ∨ (¬ p1987) ∨ p3008 ∨ (¬ p2553) ∨ (¬ p3688) ∨ (¬ p2737) ∨ (¬ p2313)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (p3008) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial37282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory26538 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule37282 (meaning t m 1987) (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2737) (meaning t m 2785) (meaning t m 3008) (meaning t m 3688) source

theorem rule37284 (p2027 p2249 p2307 p2396 p2509 p2534 p2641 p2657 p3487 p3567 p3950 : Prop) (h : (¬ p3567) ∨ (¬ p3950) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p3487) ∨ (¬ p2509) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2657) ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3567) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial37284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory26540 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule37284 (meaning t m 2027) (meaning t m 2249) (meaning t m 2307) (meaning t m 2396) (meaning t m 2509) (meaning t m 2534) (meaning t m 2641) (meaning t m 2657) (meaning t m 3487) (meaning t m 3567) (meaning t m 3950) source

theorem rule37290 (p2027 p2098 p2138 p3880 p4188 p4885 : Prop) (h : (¬ p2138) ∨ (¬ p3880) ∨ (¬ p4188) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p4885)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p3880) ∨ (¬ p4188) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial37290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory26546 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8)
  exact rule37290 (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 3880) (meaning t m 4188) (meaning t m 4885) source

theorem rule37292 (p2027 p2542 p2589 p3093 p3309 p3574 p3822 p5193 p5222 : Prop) (h : (¬ p5193) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p5222) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p3093) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p3822) ∨ (¬ p5193) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial37292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory26548 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule37292 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 3093) (meaning t m 3309) (meaning t m 3574) (meaning t m 3822) (meaning t m 5193) (meaning t m 5222) source

theorem rule37295 (p2027 p2780 p2901 p2946 p3917 p4129 p4191 p4786 p4826 : Prop) (h : (¬ p2946) ∨ (¬ p4129) ∨ (¬ p2901) ∨ (¬ p2780) ∨ (¬ p4786) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3917) ∨ (¬ p4129) ∨ (¬ p4191) ∨ (¬ p4786) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial37295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory26551 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule37295 (meaning t m 2027) (meaning t m 2780) (meaning t m 2901) (meaning t m 2946) (meaning t m 3917) (meaning t m 4129) (meaning t m 4191) (meaning t m 4786) (meaning t m 4826) source

theorem rule37297 (p2027 p2313 p2577 p2619 p2839 p3347 p3365 p3366 p3955 p4030 p4149 p4434 p4752 p5580 : Prop) (h : (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4752) ∨ (¬ p4030) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p2619) ∨ (¬ p4434) ∨ (¬ p4149) ∨ (¬ p2313) ∨ (¬ p3955) ∨ (¬ p5580) ∨ (¬ p2577)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3347) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3955) ∨ (¬ p4030) ∨ (¬ p4149) ∨ (¬ p4434) ∨ (¬ p4752) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial37297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory26553 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule37297 (meaning t m 2027) (meaning t m 2313) (meaning t m 2577) (meaning t m 2619) (meaning t m 2839) (meaning t m 3347) (meaning t m 3365) (meaning t m 3366) (meaning t m 3955) (meaning t m 4030) (meaning t m 4149) (meaning t m 4434) (meaning t m 4752) (meaning t m 5580) source

theorem rule37298 (p2027 p2145 p2696 p2797 p3692 p4120 p4228 p4444 p5250 : Prop) (h : (¬ p2797) ∨ (¬ p3692) ∨ (¬ p2696) ∨ (¬ p4444) ∨ (¬ p4120) ∨ (¬ p2145) ∨ p2027 ∨ (¬ p5250) ∨ (¬ p4228)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4228) ∨ (¬ p4444) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial37298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory26554 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule37298 (meaning t m 2027) (meaning t m 2145) (meaning t m 2696) (meaning t m 2797) (meaning t m 3692) (meaning t m 4120) (meaning t m 4228) (meaning t m 4444) (meaning t m 5250) source

theorem rule37302 (p2027 p2248 p2284 p2946 p3125 p3548 p4330 p4348 p4366 : Prop) (h : (¬ p4348) ∨ (¬ p3125) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p4330) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial37302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory26558 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule37302 (meaning t m 2027) (meaning t m 2248) (meaning t m 2284) (meaning t m 2946) (meaning t m 3125) (meaning t m 3548) (meaning t m 4330) (meaning t m 4348) (meaning t m 4366) source

theorem rule37303 (p1987 p2027 p2138 p2274 p2696 p2765 p3822 p4193 : Prop) (h : (¬ p4193) ∨ (¬ p3822) ∨ p2765 ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2274)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2274) ∨ (¬ p2696) ∨ (p2765) ∨ (¬ p3822) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial37303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory26559 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule37303 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2274) (meaning t m 2696) (meaning t m 2765) (meaning t m 3822) (meaning t m 4193) source

theorem rule37309 (p1991 p2027 p2202 p2657 p2727 p2982 p3368 p4363 : Prop) (h : (¬ p2657) ∨ p2202 ∨ (¬ p1991) ∨ (¬ p3368) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2982) ∨ (¬ p4363)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2982) ∨ (¬ p3368) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial37309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory26565 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9)
  exact rule37309 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2657) (meaning t m 2727) (meaning t m 2982) (meaning t m 3368) (meaning t m 4363) source

theorem rule37310 (p1991 p2027 p2202 p2427 p2657 p2727 p3368 p3486 : Prop) (h : (¬ p2657) ∨ p2202 ∨ (¬ p1991) ∨ (¬ p3368) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2427) ∨ (¬ p3486)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3368) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial37310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory26566 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule37310 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2657) (meaning t m 2727) (meaning t m 3368) (meaning t m 3486) source

theorem rule37311 (p2027 p2727 p3083 p3662 p3879 p4610 : Prop) (h : p2027 ∨ (¬ p3662) ∨ (¬ p2727) ∨ (¬ p3879) ∨ (¬ p4610) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial37311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory26567 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8)
  exact rule37311 (meaning t m 2027) (meaning t m 2727) (meaning t m 3083) (meaning t m 3662) (meaning t m 3879) (meaning t m 4610) source

theorem rule37315 (p2005 p2027 p2383 p2409 p2584 p2922 p3540 p3956 : Prop) (h : (¬ p2584) ∨ p2409 ∨ (¬ p2383) ∨ (¬ p2005) ∨ (¬ p2922) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p3540)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2383) ∨ (p2409) ∨ (¬ p2584) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial37315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory26571 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule37315 (meaning t m 2005) (meaning t m 2027) (meaning t m 2383) (meaning t m 2409) (meaning t m 2584) (meaning t m 2922) (meaning t m 3540) (meaning t m 3956) source

theorem rule37320 (p2027 p3755 p3877 p4350 p5118 p5600 : Prop) (h : (¬ p5118) ∨ (¬ p3877) ∨ (¬ p3755) ∨ (¬ p4350) ∨ p2027 ∨ (¬ p5600)) : (p2027) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4350) ∨ (¬ p5118) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial37320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4350)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory26576 t (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 8 10) (m.theta 8 9)
  exact rule37320 (meaning t m 2027) (meaning t m 3755) (meaning t m 3877) (meaning t m 4350) (meaning t m 5118) (meaning t m 5600) source

theorem rule37323 (p2027 p2122 p2396 p2509 p2534 p2774 p3452 p3950 p4733 : Prop) (h : p2027 ∨ (¬ p2534) ∨ (¬ p4733) ∨ (¬ p3452) ∨ (¬ p2509) ∨ (¬ p2774) ∨ (¬ p3950) ∨ (¬ p2396) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26579 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule37323 (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2509) (meaning t m 2534) (meaning t m 2774) (meaning t m 3452) (meaning t m 3950) (meaning t m 4733) source

theorem rule37325 (p2027 p2588 p3073 p3347 p3449 p3646 p3904 p3954 p4107 p4203 p4669 p5216 : Prop) (h : (¬ p4669) ∨ (¬ p3347) ∨ (¬ p3904) ∨ (¬ p4203) ∨ (¬ p5216) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2588) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4203) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory26581 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule37325 (meaning t m 2027) (meaning t m 2588) (meaning t m 3073) (meaning t m 3347) (meaning t m 3449) (meaning t m 3646) (meaning t m 3904) (meaning t m 3954) (meaning t m 4107) (meaning t m 4203) (meaning t m 4669) (meaning t m 5216) source

theorem rule37327 (p2027 p2630 p2641 p2963 p4111 p4787 : Prop) (h : (¬ p2630) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4787) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4111) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial37327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory26583 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule37327 (meaning t m 2027) (meaning t m 2630) (meaning t m 2641) (meaning t m 2963) (meaning t m 4111) (meaning t m 4787) source

theorem rule37328 (p1997 p2027 p2230 p2459 p2476 p2534 p2633 : Prop) (h : p2633 ∨ (¬ p2534) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p1997) ∨ (¬ p2459)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2633) := by
  classical
  tauto

theorem initial37328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) := by
  have source := ElevenTheory.theory26584 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37328 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2633) source

theorem rule37332 (p2027 p2274 p2313 p2630 p2696 p2787 p3083 p3989 p4596 : Prop) (h : (¬ p2274) ∨ (¬ p2630) ∨ (¬ p2787) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p2696) ∨ (¬ p4596) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3083) ∨ (¬ p3989) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial37332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory26588 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37332 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2630) (meaning t m 2696) (meaning t m 2787) (meaning t m 3083) (meaning t m 3989) (meaning t m 4596) source

theorem rule37335 (p2027 p2246 p2651 p2749 p3016 p3645 p3692 p3888 p4120 p4444 p4877 p5250 : Prop) (h : (¬ p3888) ∨ (¬ p5250) ∨ (¬ p3016) ∨ (¬ p3692) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4120) ∨ (¬ p4877) ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p3645)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p3016) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p3888) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4877) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial37335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory26591 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule37335 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2749) (meaning t m 3016) (meaning t m 3645) (meaning t m 3692) (meaning t m 3888) (meaning t m 4120) (meaning t m 4444) (meaning t m 4877) (meaning t m 5250) source

theorem rule37336 (p2027 p2274 p2352 p2387 p2588 p4486 : Prop) (h : (¬ p2387) ∨ (¬ p2274) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4486) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial37336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory26592 t (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37336 (meaning t m 2027) (meaning t m 2274) (meaning t m 2352) (meaning t m 2387) (meaning t m 2588) (meaning t m 4486) source

theorem rule37340 (p2027 p2264 p3037 p3097 p3399 p3645 p3646 p3954 p4107 p4666 p4877 : Prop) (h : (¬ p3097) ∨ (¬ p4107) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4877) ∨ (¬ p3037) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2264) ∨ (¬ p4666) ∨ (¬ p3645)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3037) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory26596 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37340 (meaning t m 2027) (meaning t m 2264) (meaning t m 3037) (meaning t m 3097) (meaning t m 3399) (meaning t m 3645) (meaning t m 3646) (meaning t m 3954) (meaning t m 4107) (meaning t m 4666) (meaning t m 4877) source

theorem rule37342 (p2027 p2132 p2245 p2641 p2870 p2881 p2963 p4041 p4360 p4733 : Prop) (h : (¬ p2245) ∨ p2027 ∨ (¬ p4041) ∨ (¬ p2870) ∨ (¬ p2963) ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p2881) ∨ (¬ p2641) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26598 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule37342 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2641) (meaning t m 2870) (meaning t m 2881) (meaning t m 2963) (meaning t m 4041) (meaning t m 4360) (meaning t m 4733) source

theorem rule37343 (p2027 p2295 p2363 p3325 p3692 p3988 p4560 : Prop) (h : p2027 ∨ (¬ p4560) ∨ (¬ p2295) ∨ (¬ p3988) ∨ (¬ p3692) ∨ (¬ p3325) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial37343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory26599 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule37343 (meaning t m 2027) (meaning t m 2295) (meaning t m 2363) (meaning t m 3325) (meaning t m 3692) (meaning t m 3988) (meaning t m 4560) source

theorem rule37345 (p2027 p2449 p2995 p3690 p4244 p4906 : Prop) (h : (¬ p4906) ∨ p2027 ∨ (¬ p2995) ∨ (¬ p2449) ∨ (¬ p4244) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial37345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory26601 t (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule37345 (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3690) (meaning t m 4244) (meaning t m 4906) source

theorem rule37350 (p2027 p2088 p3178 p3414 p3683 p4340 p4650 p5368 : Prop) (h : (¬ p3683) ∨ (¬ p5368) ∨ (¬ p4340) ∨ (¬ p2088) ∨ (¬ p4650) ∨ p2027 ∨ (¬ p3178) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3178) ∨ (¬ p3414) ∨ (¬ p3683) ∨ (¬ p4340) ∨ (¬ p4650) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial37350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory26606 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 4) (m.theta 2 8) (m.theta 3 4) (m.theta 3 7) (m.theta 8 9)
  exact rule37350 (meaning t m 2027) (meaning t m 2088) (meaning t m 3178) (meaning t m 3414) (meaning t m 3683) (meaning t m 4340) (meaning t m 4650) (meaning t m 5368) source

theorem rule37351 (p2027 p2352 p2588 p3550 p3553 p4570 : Prop) (h : (¬ p3550) ∨ (¬ p4570) ∨ (¬ p2588) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p3553)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3550) ∨ (¬ p3553) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial37351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory26607 t (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule37351 (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 3550) (meaning t m 3553) (meaning t m 4570) source

theorem rule37353 (p2027 p2441 p2563 p2881 p3644 p4555 : Prop) (h : (¬ p3644) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p2441) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial37353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory26609 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule37353 (meaning t m 2027) (meaning t m 2441) (meaning t m 2563) (meaning t m 2881) (meaning t m 3644) (meaning t m 4555) source

theorem rule37358 (p1979 p2027 p2352 p2588 p2997 p3952 p3989 : Prop) (h : (¬ p2352) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3989) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p3952)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3952) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial37358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory26614 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37358 (meaning t m 1979) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2997) (meaning t m 3952) (meaning t m 3989) source

theorem rule37360 (p1997 p2027 p2187 p2230 p2579 p2765 p3956 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2579) ∨ p2765 ∨ (¬ p3956) ∨ (¬ p2187)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (p2765) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial37360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory26616 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule37360 (meaning t m 1997) (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2579) (meaning t m 2765) (meaning t m 3956) source

theorem rule37365 (p2027 p2156 p2247 p2352 p3096 p3979 p4118 p4360 p4521 p5122 : Prop) (h : (¬ p3979) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p2247) ∨ (¬ p2156) ∨ (¬ p2352) ∨ (¬ p3096) ∨ (¬ p4521)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p3096) ∨ (¬ p3979) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4521) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial37365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory26621 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37365 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2352) (meaning t m 3096) (meaning t m 3979) (meaning t m 4118) (meaning t m 4360) (meaning t m 4521) (meaning t m 5122) source

theorem rule37367 (p2027 p2299 p2579 p2588 p3347 p3399 p3631 p3954 p4668 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3347) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4668) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory26623 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37367 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 3347) (meaning t m 3399) (meaning t m 3631) (meaning t m 3954) (meaning t m 4668) (meaning t m 5216) source

theorem rule37369 (p2027 p2651 p2753 p3016 p3556 p3645 p3690 p3888 p4117 p4381 p4877 p5250 : Prop) (h : (¬ p3645) ∨ (¬ p3016) ∨ (¬ p3888) ∨ (¬ p5250) ∨ (¬ p4877) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p4117) ∨ (¬ p2753) ∨ (¬ p3556) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p3888) ∨ (¬ p4117) ∨ (¬ p4381) ∨ (¬ p4877) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial37369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory26625 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule37369 (meaning t m 2027) (meaning t m 2651) (meaning t m 2753) (meaning t m 3016) (meaning t m 3556) (meaning t m 3645) (meaning t m 3690) (meaning t m 3888) (meaning t m 4117) (meaning t m 4381) (meaning t m 4877) (meaning t m 5250) source

theorem rule37370 (p2470 p2573 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p2470) ∨ p2573) : (¬ p2470) ∨ (p2573) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial37370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (meaning t m 2573) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory26626 (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule37370 (meaning t m 2470) (meaning t m 2573) (meaning t m 3573) source

theorem rule37372 (p2027 p3246 p3822 p3872 p4107 p4328 p4564 : Prop) (h : (¬ p4328) ∨ (¬ p4564) ∨ (¬ p3872) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4107)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3822) ∨ (¬ p3872) ∨ (¬ p4107) ∨ (¬ p4328) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial37372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory26628 t (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule37372 (meaning t m 2027) (meaning t m 3246) (meaning t m 3822) (meaning t m 3872) (meaning t m 4107) (meaning t m 4328) (meaning t m 4564) source

theorem rule37376 (p2027 p2248 p2651 p2850 p2982 p3548 p4343 p4348 p4366 p4450 : Prop) (h : (¬ p4366) ∨ (¬ p2982) ∨ (¬ p2850) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2651) ∨ (¬ p4343) ∨ (¬ p4450) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3548) ∨ (¬ p4343) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial37376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory26632 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule37376 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 2850) (meaning t m 2982) (meaning t m 3548) (meaning t m 4343) (meaning t m 4348) (meaning t m 4366) (meaning t m 4450) source

theorem rule37378 (p3758 p4173 p4418 : Prop) (h : (¬ p4418) ∨ (¬ p3758) ∨ p4173) : (¬ p3758) ∨ (p4173) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial37378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3758)) ∨ (meaning t m 4173) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory26634 (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule37378 (meaning t m 3758) (meaning t m 4173) (meaning t m 4418) source

theorem rule37379 (p2027 p2248 p2299 p2313 p2651 p2850 p2982 p4343 p4348 p4450 p5015 : Prop) (h : (¬ p2248) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2299) ∨ (¬ p4450) ∨ (¬ p2982) ∨ (¬ p4348) ∨ (¬ p5015) ∨ (¬ p4343) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p4343) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial37379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory26635 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37379 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2313) (meaning t m 2651) (meaning t m 2850) (meaning t m 2982) (meaning t m 4343) (meaning t m 4348) (meaning t m 4450) (meaning t m 5015) source

theorem rule37380 (p1988 p2027 p2132 p2611 p2619 p3146 p3266 : Prop) (h : p2611 ∨ (¬ p1988) ∨ (¬ p2619) ∨ (¬ p3266) ∨ (¬ p2132) ∨ (¬ p3146) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial37380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory26636 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule37380 (meaning t m 1988) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2619) (meaning t m 3146) (meaning t m 3266) source

theorem rule37382 (p2027 p3516 p3646 p3690 p4558 p4988 : Prop) (h : (¬ p4988) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p3690) ∨ (¬ p3646) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p4558) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial37382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory26638 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule37382 (meaning t m 2027) (meaning t m 3516) (meaning t m 3646) (meaning t m 3690) (meaning t m 4558) (meaning t m 4988) source

theorem rule37386 (p1997 p2027 p2230 p2764 p3540 p3690 p4001 p4381 : Prop) (h : (¬ p1997) ∨ (¬ p4001) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3540) ∨ p2764 ∨ (¬ p3690) ∨ (¬ p4381)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (p2764) ∨ (¬ p3540) ∨ (¬ p3690) ∨ (¬ p4001) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial37386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory26642 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule37386 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2764) (meaning t m 3540) (meaning t m 3690) (meaning t m 4001) (meaning t m 4381) source

theorem rule37387 (p2027 p2248 p2651 p2850 p2982 p3591 p3923 p4343 p4347 p4450 : Prop) (h : (¬ p3591) ∨ (¬ p2850) ∨ (¬ p2651) ∨ (¬ p3923) ∨ (¬ p2982) ∨ (¬ p2248) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p4343) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4343) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial37387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory26643 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule37387 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 2850) (meaning t m 2982) (meaning t m 3591) (meaning t m 3923) (meaning t m 4343) (meaning t m 4347) (meaning t m 4450) source

theorem rule37392 (p2027 p2241 p2299 p2588 p3189 p3347 p3646 p3904 p3954 p4203 p4550 p5216 : Prop) (h : (¬ p3954) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p4203) ∨ (¬ p3189) ∨ (¬ p2588) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3904) ∨ (¬ p3646) ∨ (¬ p4550) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3189) ∨ (¬ p3347) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4203) ∨ (¬ p4550) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory26648 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule37392 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2588) (meaning t m 3189) (meaning t m 3347) (meaning t m 3646) (meaning t m 3904) (meaning t m 3954) (meaning t m 4203) (meaning t m 4550) (meaning t m 5216) source

theorem rule37393 (p1988 p2027 p2156 p2842 p2850 p3125 p3461 p4109 : Prop) (h : p2842 ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p4109) ∨ (¬ p1988) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2156) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial37393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory26649 t (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule37393 (meaning t m 1988) (meaning t m 2027) (meaning t m 2156) (meaning t m 2842) (meaning t m 2850) (meaning t m 3125) (meaning t m 3461) (meaning t m 4109) source

theorem rule37395 (p1992 p2027 p2577 p2588 p2997 p3363 p3564 p3585 p3946 : Prop) (h : (¬ p3946) ∨ p2997 ∨ p2027 ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p2577) ∨ (¬ p1992) ∨ (¬ p3363) ∨ (¬ p3585)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2577) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3363) ∨ (¬ p3564) ∨ (¬ p3585) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial37395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory26651 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule37395 (meaning t m 1992) (meaning t m 2027) (meaning t m 2577) (meaning t m 2588) (meaning t m 2997) (meaning t m 3363) (meaning t m 3564) (meaning t m 3585) (meaning t m 3946) source

theorem rule37402 (p2027 p3506 p4137 p4191 p4421 p4976 : Prop) (h : (¬ p4191) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p4976) ∨ (¬ p4137) ∨ (¬ p4421)) : (p2027) ∨ (¬ p3506) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial37402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory26658 t (m.theta 3 6) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule37402 (meaning t m 2027) (meaning t m 3506) (meaning t m 4137) (meaning t m 4191) (meaning t m 4421) (meaning t m 4976) source

theorem rule37405 (p1984 p2027 p2743 p2764 p3954 p4035 p5284 : Prop) (h : p2764 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3954) ∨ (¬ p2743) ∨ (¬ p5284) ∨ (¬ p4035)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p3954) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial37405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory26661 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 9 10)
  exact rule37405 (meaning t m 1984) (meaning t m 2027) (meaning t m 2743) (meaning t m 2764) (meaning t m 3954) (meaning t m 4035) (meaning t m 5284) source

theorem rule37408 (p2027 p2247 p3276 p3355 p3950 p4118 p4360 p4381 p5190 : Prop) (h : (¬ p4118) ∨ (¬ p3355) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2247) ∨ (¬ p5190) ∨ (¬ p3276) ∨ (¬ p3950) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4381) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory26664 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37408 (meaning t m 2027) (meaning t m 2247) (meaning t m 3276) (meaning t m 3355) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4381) (meaning t m 5190) source

theorem rule37413 (p2027 p2247 p3192 p3276 p3389 p3950 p4118 p4360 p4381 p5190 : Prop) (h : (¬ p3192) ∨ (¬ p3389) ∨ (¬ p4360) ∨ (¬ p4118) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p5190) ∨ (¬ p3950) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3389) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4381) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory26669 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37413 (meaning t m 2027) (meaning t m 2247) (meaning t m 3192) (meaning t m 3276) (meaning t m 3389) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 4381) (meaning t m 5190) source

theorem rule37415 (p2027 p2774 p2819 p3955 p4232 p4620 p5265 : Prop) (h : (¬ p5265) ∨ (¬ p2819) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4620) ∨ (¬ p3955) ∨ (¬ p4232)) : (p2027) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3955) ∨ (¬ p4232) ∨ (¬ p4620) ∨ (¬ p5265) := by
  classical
  tauto

theorem initial37415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5265)) := by
  have source := ElevenTheory.theory26671 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 9) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule37415 (meaning t m 2027) (meaning t m 2774) (meaning t m 2819) (meaning t m 3955) (meaning t m 4232) (meaning t m 4620) (meaning t m 5265) source

theorem rule37418 (p2027 p3256 p3692 p4119 p4235 p4237 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p4237) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4235) ∨ (¬ p4119) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4235) ∨ (¬ p4237) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial37418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory26674 t (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule37418 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 4119) (meaning t m 4235) (meaning t m 4237) (meaning t m 4705) source

theorem rule37419 (p2027 p2230 p2891 p3540 p4001 p4632 : Prop) (h : (¬ p3540) ∨ (¬ p4632) ∨ (¬ p2230) ∨ (¬ p4001) ∨ p2027 ∨ (¬ p2891)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2891) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial37419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory26675 t (m.theta 0 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule37419 (meaning t m 2027) (meaning t m 2230) (meaning t m 2891) (meaning t m 3540) (meaning t m 4001) (meaning t m 4632) source

theorem rule37420 (p1987 p2027 p2169 p2363 p2534 p2810 p4256 : Prop) (h : (¬ p2363) ∨ p2169 ∨ (¬ p2534) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p4256)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2810) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial37420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory26676 t (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37420 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 2810) (meaning t m 4256) source

theorem rule37423 (p1987 p2027 p2169 p2363 p2534 p2810 p3573 p3574 : Prop) (h : p2169 ∨ (¬ p2534) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2363) ∨ (¬ p3573) ∨ (¬ p3574)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2810) ∨ (¬ p3573) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial37423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory26679 t (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37423 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 2810) (meaning t m 3573) (meaning t m 3574) source

theorem rule37431 (p2027 p2187 p2284 p2590 p3956 p4705 : Prop) (h : (¬ p2590) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2284) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2590) ∨ (¬ p3956) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial37431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory26687 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule37431 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2590) (meaning t m 3956) (meaning t m 4705) source

theorem rule37433 (p2027 p2459 p2911 p3692 p4119 p4647 : Prop) (h : (¬ p2459) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4647) ∨ (¬ p4119) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial37433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory26689 t (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37433 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3692) (meaning t m 4119) (meaning t m 4647) source

theorem rule37434 (p2005 p2027 p2295 p2545 p2588 p2641 p4111 : Prop) (h : (¬ p2641) ∨ (¬ p2005) ∨ (¬ p2295) ∨ (¬ p4111) ∨ p2027 ∨ p2545 ∨ (¬ p2588)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2295) ∨ (p2545) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial37434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory26690 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule37434 (meaning t m 2005) (meaning t m 2027) (meaning t m 2295) (meaning t m 2545) (meaning t m 2588) (meaning t m 2641) (meaning t m 4111) source

theorem rule37438 (p2027 p2088 p3156 p3696 p4340 p4359 p4906 : Prop) (h : (¬ p4340) ∨ (¬ p3156) ∨ (¬ p2088) ∨ (¬ p3696) ∨ (¬ p4906) ∨ (¬ p4359) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial37438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory26694 t (m.theta 0 8) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule37438 (meaning t m 2027) (meaning t m 2088) (meaning t m 3156) (meaning t m 3696) (meaning t m 4340) (meaning t m 4359) (meaning t m 4906) source

theorem rule37447 (p1983 p2027 p2417 p2499 p2545 p3016 p3389 p3519 : Prop) (h : (¬ p1983) ∨ (¬ p2417) ∨ (¬ p3519) ∨ (¬ p2499) ∨ (¬ p3389) ∨ (¬ p3016) ∨ p2545 ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2499) ∨ (p2545) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial37447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory26703 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule37447 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2499) (meaning t m 2545) (meaning t m 3016) (meaning t m 3389) (meaning t m 3519) source

theorem rule37454 (p2027 p2088 p2475 p3083 p4340 p4750 p5368 : Prop) (h : (¬ p5368) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p4750) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p4340) ∨ (¬ p4750) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial37454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory26710 t (m.theta 0 8) (m.theta 2 4) (m.theta 2 8) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule37454 (meaning t m 2027) (meaning t m 2088) (meaning t m 2475) (meaning t m 3083) (meaning t m 4340) (meaning t m 4750) (meaning t m 5368) source

theorem rule37458 (p2027 p2254 p2274 p2470 p2493 p2509 p2952 p3568 p3958 p4079 p4153 : Prop) (h : (¬ p3568) ∨ (¬ p4079) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2952) ∨ (¬ p2254) ∨ (¬ p2274) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p3958) ∨ (¬ p4153)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2274) ∨ (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2952) ∨ (¬ p3568) ∨ (¬ p3958) ∨ (¬ p4079) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial37458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory26714 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule37458 (meaning t m 2027) (meaning t m 2254) (meaning t m 2274) (meaning t m 2470) (meaning t m 2493) (meaning t m 2509) (meaning t m 2952) (meaning t m 3568) (meaning t m 3958) (meaning t m 4079) (meaning t m 4153) source

theorem rule37459 (p2027 p2264 p2553 p2573 p2748 p3031 p3365 p3367 p3548 p3759 p4361 p4734 : Prop) (h : (¬ p4361) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3031) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p2264) ∨ (¬ p3759) ∨ (¬ p3367) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p4734)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2748) ∨ (¬ p3031) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3548) ∨ (¬ p3759) ∨ (¬ p4361) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial37459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory26715 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule37459 (meaning t m 2027) (meaning t m 2264) (meaning t m 2553) (meaning t m 2573) (meaning t m 2748) (meaning t m 3031) (meaning t m 3365) (meaning t m 3367) (meaning t m 3548) (meaning t m 3759) (meaning t m 4361) (meaning t m 4734) source

theorem rule37460 (p2957 p3497 p3556 p4119 : Prop) (h : (¬ p4119) ∨ (¬ p3556) ∨ (¬ p2957) ∨ p3497) : (¬ p2957) ∨ (p3497) ∨ (¬ p3556) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial37460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (meaning t m 3497) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory26716 (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule37460 (meaning t m 2957) (meaning t m 3497) (meaning t m 3556) (meaning t m 4119) source

theorem rule37464 (p2027 p2307 p2417 p3946 p4396 p4712 : Prop) (h : (¬ p4396) ∨ (¬ p4712) ∨ (¬ p2417) ∨ (¬ p2307) ∨ (¬ p3946) ∨ p2027) : (p2027) ∨ (¬ p2307) ∨ (¬ p2417) ∨ (¬ p3946) ∨ (¬ p4396) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial37464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory26720 t (m.theta 0 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule37464 (meaning t m 2027) (meaning t m 2307) (meaning t m 2417) (meaning t m 3946) (meaning t m 4396) (meaning t m 4712) source

theorem rule37467 (p2972 p3645 p3646 p4205 : Prop) (h : (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4205) ∨ (¬ p2972)) : (¬ p2972) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4205) := by
  classical
  tauto

theorem initial37467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4205)) := by
  have source := ElevenTheory.theory26723 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 9)
  exact rule37467 (meaning t m 2972) (meaning t m 3645) (meaning t m 3646) (meaning t m 4205) source

theorem rule37469 (p2027 p2459 p3322 p3670 p4133 p4191 p5339 : Prop) (h : (¬ p3322) ∨ (¬ p3670) ∨ (¬ p4191) ∨ (¬ p2459) ∨ (¬ p5339) ∨ p2027 ∨ (¬ p4133)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3322) ∨ (¬ p3670) ∨ (¬ p4133) ∨ (¬ p4191) ∨ (¬ p5339) := by
  classical
  tauto

theorem initial37469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5339)) := by
  have source := ElevenTheory.theory26725 t (m.theta 2 9) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule37469 (meaning t m 2027) (meaning t m 2459) (meaning t m 3322) (meaning t m 3670) (meaning t m 4133) (meaning t m 4191) (meaning t m 5339) source

theorem rule37476 (p2027 p2187 p2363 p3922 p4261 p4371 p4564 : Prop) (h : (¬ p2187) ∨ (¬ p4371) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p4564) ∨ (¬ p3922) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3922) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial37476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory26732 t (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule37476 (meaning t m 2027) (meaning t m 2187) (meaning t m 2363) (meaning t m 3922) (meaning t m 4261) (meaning t m 4371) (meaning t m 4564) source

theorem rule37477 (p2027 p2187 p3979 p4196 p4564 p5600 : Prop) (h : (¬ p5600) ∨ (¬ p4196) ∨ p2027 ∨ (¬ p4564) ∨ (¬ p2187) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3979) ∨ (¬ p4196) ∨ (¬ p4564) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial37477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4564)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory26733 t (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10)
  exact rule37477 (meaning t m 2027) (meaning t m 2187) (meaning t m 3979) (meaning t m 4196) (meaning t m 4564) (meaning t m 5600) source

theorem rule37479 (p2027 p2387 p2696 p2778 p2819 p4842 : Prop) (h : (¬ p2778) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2387) ∨ (¬ p4842) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2696) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial37479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory26735 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule37479 (meaning t m 2027) (meaning t m 2387) (meaning t m 2696) (meaning t m 2778) (meaning t m 2819) (meaning t m 4842) source

theorem rule37480 (p2027 p2254 p2284 p2911 p2922 p2950 p3379 p3497 p3646 p4503 p4506 : Prop) (h : (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p3497) ∨ (¬ p4506) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p2950) ∨ (¬ p4503) ∨ (¬ p3646) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4503) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial37480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory26736 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule37480 (meaning t m 2027) (meaning t m 2254) (meaning t m 2284) (meaning t m 2911) (meaning t m 2922) (meaning t m 2950) (meaning t m 3379) (meaning t m 3497) (meaning t m 3646) (meaning t m 4503) (meaning t m 4506) source

theorem rule37481 (p2027 p2254 p2284 p2950 p3399 p3527 p3644 p3646 p4277 p4320 : Prop) (h : (¬ p2284) ∨ (¬ p2950) ∨ (¬ p4320) ∨ (¬ p3646) ∨ (¬ p4277) ∨ (¬ p2254) ∨ (¬ p3399) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3527)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4277) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial37481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory26737 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule37481 (meaning t m 2027) (meaning t m 2254) (meaning t m 2284) (meaning t m 2950) (meaning t m 3399) (meaning t m 3527) (meaning t m 3644) (meaning t m 3646) (meaning t m 4277) (meaning t m 4320) source

theorem rule37483 (p1982 p2027 p2254 p2284 p2518 p2528 p2881 p2938 p2950 p3379 p3553 p3646 p4386 : Prop) (h : p2938 ∨ (¬ p2881) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p1982) ∨ (¬ p3379) ∨ (¬ p2950) ∨ (¬ p2284) ∨ (¬ p4386) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3553)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial37483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory26739 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 3 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37483 (meaning t m 1982) (meaning t m 2027) (meaning t m 2254) (meaning t m 2284) (meaning t m 2518) (meaning t m 2528) (meaning t m 2881) (meaning t m 2938) (meaning t m 2950) (meaning t m 3379) (meaning t m 3553) (meaning t m 3646) (meaning t m 4386) source

theorem rule37487 (p2027 p2254 p2518 p2528 p2963 p3379 p3461 p4604 p5274 p5284 : Prop) (h : (¬ p5274) ∨ (¬ p2254) ∨ (¬ p5284) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p4604) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5274) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial37487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory26743 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 3 9) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37487 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2528) (meaning t m 2963) (meaning t m 3379) (meaning t m 3461) (meaning t m 4604) (meaning t m 5274) (meaning t m 5284) source

theorem rule37488 (p2027 p2440 p3055 p3471 p3658 p4030 p4116 p4646 : Prop) (h : (¬ p4030) ∨ (¬ p4646) ∨ (¬ p3658) ∨ (¬ p2440) ∨ (¬ p3471) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p3055)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3658) ∨ (¬ p4030) ∨ (¬ p4116) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial37488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory26744 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule37488 (meaning t m 2027) (meaning t m 2440) (meaning t m 3055) (meaning t m 3471) (meaning t m 3658) (meaning t m 4030) (meaning t m 4116) (meaning t m 4646) source

theorem rule37489 (p1987 p2027 p2138 p2545 p2696 p2992 p4111 p4316 : Prop) (h : p2545 ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4316) ∨ (¬ p1987) ∨ (¬ p4111) ∨ (¬ p2992)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial37489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory26745 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule37489 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2545) (meaning t m 2696) (meaning t m 2992) (meaning t m 4111) (meaning t m 4316) source

theorem rule37491 (p2027 p2104 p2177 p2807 p4117 p4570 p4800 : Prop) (h : (¬ p2807) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p4800) ∨ (¬ p4570) ∨ (¬ p2104) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2177) ∨ (¬ p2807) ∨ (¬ p4117) ∨ (¬ p4570) ∨ (¬ p4800) := by
  classical
  tauto

theorem initial37491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 4800)) := by
  have source := ElevenTheory.theory26747 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37491 (meaning t m 2027) (meaning t m 2104) (meaning t m 2177) (meaning t m 2807) (meaning t m 4117) (meaning t m 4570) (meaning t m 4800) source

theorem rule37493 (p2497 p3453 p4371 : Prop) (h : (¬ p4371) ∨ (¬ p2497) ∨ p3453) : (¬ p2497) ∨ (p3453) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial37493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2497)) ∨ (meaning t m 3453) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory26749 (m.theta 1 4) (m.theta 1 6) (m.theta 1 8)
  exact rule37493 (meaning t m 2497) (meaning t m 3453) (meaning t m 4371) source

theorem rule37498 (p2027 p2630 p3027 p3414 p4111 p4787 : Prop) (h : (¬ p3414) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p4111) ∨ (¬ p4787)) : (p2027) ∨ (¬ p2630) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial37498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory26754 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule37498 (meaning t m 2027) (meaning t m 2630) (meaning t m 3027) (meaning t m 3414) (meaning t m 4111) (meaning t m 4787) source

theorem rule37500 (p1976 p2027 p2842 p3365 p3585 p3707 p4351 p5316 p5387 p5453 : Prop) (h : (¬ p3365) ∨ (¬ p1976) ∨ p2842 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p4351) ∨ (¬ p5453) ∨ (¬ p5316) ∨ (¬ p3707) ∨ (¬ p5387)) : (¬ p1976) ∨ (p2027) ∨ (p2842) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p3707) ∨ (¬ p4351) ∨ (¬ p5316) ∨ (¬ p5387) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial37500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 5316)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory26756 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 8) (m.theta 1 9) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 9 10)
  exact rule37500 (meaning t m 1976) (meaning t m 2027) (meaning t m 2842) (meaning t m 3365) (meaning t m 3585) (meaning t m 3707) (meaning t m 4351) (meaning t m 5316) (meaning t m 5387) (meaning t m 5453) source

theorem rule37503 (p1982 p2027 p2842 p3537 p3585 p3670 p4444 p5344 : Prop) (h : (¬ p3537) ∨ (¬ p5344) ∨ (¬ p4444) ∨ (¬ p3585) ∨ p2842 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3670)) : (¬ p1982) ∨ (p2027) ∨ (p2842) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3670) ∨ (¬ p4444) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial37503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory26759 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 2 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37503 (meaning t m 1982) (meaning t m 2027) (meaning t m 2842) (meaning t m 3537) (meaning t m 3585) (meaning t m 3670) (meaning t m 4444) (meaning t m 5344) source

theorem rule37506 (p2027 p2341 p3425 p3553 p3819 p4783 : Prop) (h : (¬ p4783) ∨ (¬ p3425) ∨ (¬ p2341) ∨ (¬ p3819) ∨ (¬ p3553) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p3425) ∨ (¬ p3553) ∨ (¬ p3819) ∨ (¬ p4783) := by
  classical
  tauto

theorem initial37506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4783)) := by
  have source := ElevenTheory.theory26762 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule37506 (meaning t m 2027) (meaning t m 2341) (meaning t m 3425) (meaning t m 3553) (meaning t m 3819) (meaning t m 4783) source

theorem rule37509 (p2027 p2098 p3486 p3555 p3570 p3609 p4133 p4347 p4733 : Prop) (h : (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4733) ∨ (¬ p4347) ∨ (¬ p3486) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3609) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26765 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37509 (meaning t m 2027) (meaning t m 2098) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 3609) (meaning t m 4133) (meaning t m 4347) (meaning t m 4733) source

theorem rule37520 (p1997 p2027 p2839 p2842 p2870 p3585 p4235 : Prop) (h : (¬ p3585) ∨ p2842 ∨ (¬ p1997) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2870)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p2870) ∨ (¬ p3585) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial37520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory26776 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule37520 (meaning t m 1997) (meaning t m 2027) (meaning t m 2839) (meaning t m 2842) (meaning t m 2870) (meaning t m 3585) (meaning t m 4235) source

theorem rule37522 (p3833 p3853 p4349 p4360 : Prop) (h : (¬ p3833) ∨ (¬ p4360) ∨ (¬ p3853) ∨ (¬ p4349)) : (¬ p3833) ∨ (¬ p3853) ∨ (¬ p4349) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial37522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3833)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory26778 (m.theta 1 3) (m.theta 1 9) (m.theta 3 8) (m.theta 3 9)
  exact rule37522 (meaning t m 3833) (meaning t m 3853) (meaning t m 4349) (meaning t m 4360) source

theorem rule37523 (p3032 p4391 p4442 : Prop) (h : (¬ p4391) ∨ (¬ p3032) ∨ p4442) : (¬ p3032) ∨ (¬ p4391) ∨ (p4442) := by
  classical
  tauto

theorem initial37523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4391)) ∨ (meaning t m 4442) := by
  have source := ElevenTheory.theory26779 (m.theta 1 7) (m.theta 3 7) (m.theta 7 10)
  exact rule37523 (meaning t m 3032) (meaning t m 4391) (meaning t m 4442) source

theorem rule37527 (p2027 p2132 p2284 p3425 p3426 p4428 p4906 : Prop) (h : (¬ p2132) ∨ p2027 ∨ (¬ p4906) ∨ (¬ p4428) ∨ (¬ p3425) ∨ (¬ p2284) ∨ (¬ p3426)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2284) ∨ (¬ p3425) ∨ (¬ p3426) ∨ (¬ p4428) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial37527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory26783 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6)
  exact rule37527 (meaning t m 2027) (meaning t m 2132) (meaning t m 2284) (meaning t m 3425) (meaning t m 3426) (meaning t m 4428) (meaning t m 4906) source

theorem rule37532 (p2027 p2748 p2839 p2870 p2996 p3246 p3365 p3553 p4668 p4734 : Prop) (h : (¬ p2839) ∨ (¬ p4668) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4734) ∨ (¬ p3365) ∨ (¬ p2748) ∨ (¬ p3246) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p4668) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial37532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory26788 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37532 (meaning t m 2027) (meaning t m 2748) (meaning t m 2839) (meaning t m 2870) (meaning t m 2996) (meaning t m 3246) (meaning t m 3365) (meaning t m 3553) (meaning t m 4668) (meaning t m 4734) source

theorem rule37533 (p2027 p2241 p2553 p2598 p2750 p2753 p3422 p3591 p3923 p4501 : Prop) (h : (¬ p3923) ∨ (¬ p3591) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2553) ∨ (¬ p4501) ∨ (¬ p3422) ∨ (¬ p2750) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial37533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory26789 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37533 (meaning t m 2027) (meaning t m 2241) (meaning t m 2553) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3422) (meaning t m 3591) (meaning t m 3923) (meaning t m 4501) source

theorem rule37535 (p1998 p2027 p2122 p2177 p2287 p3323 p3917 : Prop) (h : (¬ p3323) ∨ (¬ p1998) ∨ (¬ p2177) ∨ p2027 ∨ p2287 ∨ (¬ p3917) ∨ (¬ p2122)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (p2287) ∨ (¬ p3323) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial37535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory26791 t (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule37535 (meaning t m 1998) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2287) (meaning t m 3323) (meaning t m 3917) source

theorem rule37540 (p2000 p2027 p2462 p2579 p2761 p4137 p4191 : Prop) (h : p2027 ∨ (¬ p4137) ∨ (¬ p2000) ∨ (¬ p4191) ∨ (¬ p2579) ∨ (¬ p2761) ∨ p2462) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2579) ∨ (¬ p2761) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial37540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory26796 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule37540 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2579) (meaning t m 2761) (meaning t m 4137) (meaning t m 4191) source

theorem rule37542 (p2027 p2088 p2190 p2247 p2870 p3497 p3662 p4114 p4340 p4359 p4558 p5017 : Prop) (h : (¬ p3662) ∨ (¬ p5017) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2247) ∨ (¬ p3497) ∨ (¬ p4114) ∨ (¬ p2190) ∨ (¬ p4359) ∨ (¬ p2870) ∨ (¬ p4558)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2190) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4114) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4558) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial37542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory26798 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule37542 (meaning t m 2027) (meaning t m 2088) (meaning t m 2190) (meaning t m 2247) (meaning t m 2870) (meaning t m 3497) (meaning t m 3662) (meaning t m 4114) (meaning t m 4340) (meaning t m 4359) (meaning t m 4558) (meaning t m 5017) source

theorem rule37544 (p2027 p2264 p2995 p3570 p3952 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3570) ∨ (¬ p3952) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial37544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory26800 t (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule37544 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3570) (meaning t m 3952) (meaning t m 4558) source

theorem rule37545 (p1981 p2027 p2220 p2542 p2545 p3146 p4109 p4347 : Prop) (h : (¬ p2220) ∨ p2545 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p4109) ∨ (¬ p1981) ∨ (¬ p3146) ∨ (¬ p4347)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3146) ∨ (¬ p4109) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial37545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory26801 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37545 (meaning t m 1981) (meaning t m 2027) (meaning t m 2220) (meaning t m 2542) (meaning t m 2545) (meaning t m 3146) (meaning t m 4109) (meaning t m 4347) source

theorem rule37554 (p2027 p2247 p2307 p2352 p2588 p3497 p3662 p4134 p5017 : Prop) (h : (¬ p4134) ∨ (¬ p2307) ∨ (¬ p3662) ∨ (¬ p3497) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p5017) ∨ (¬ p2588) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4134) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial37554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory26810 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule37554 (meaning t m 2027) (meaning t m 2247) (meaning t m 2307) (meaning t m 2352) (meaning t m 2588) (meaning t m 3497) (meaning t m 3662) (meaning t m 4134) (meaning t m 5017) source

theorem rule37558 (p2027 p2619 p2810 p3497 p4313 p4704 : Prop) (h : (¬ p3497) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p4313) ∨ (¬ p2619) ∨ (¬ p4704)) : (p2027) ∨ (¬ p2619) ∨ (¬ p2810) ∨ (¬ p3497) ∨ (¬ p4313) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial37558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory26814 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule37558 (meaning t m 2027) (meaning t m 2619) (meaning t m 2810) (meaning t m 3497) (meaning t m 4313) (meaning t m 4704) source

theorem rule37559 (p2027 p2299 p2608 p2911 p3389 p3486 p3519 p3555 p4376 p4559 : Prop) (h : p2027 ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4559)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3486) ∨ (¬ p3519) ∨ (¬ p3555) ∨ (¬ p4376) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial37559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory26815 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37559 (meaning t m 2027) (meaning t m 2299) (meaning t m 2608) (meaning t m 2911) (meaning t m 3389) (meaning t m 3486) (meaning t m 3519) (meaning t m 3555) (meaning t m 4376) (meaning t m 4559) source

theorem rule37561 (p2027 p2177 p2307 p2748 p2779 p2829 p3365 p4111 p4256 p4438 p4734 : Prop) (h : (¬ p2177) ∨ (¬ p3365) ∨ (¬ p2748) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p2307) ∨ (¬ p4256) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p4438) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial37561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory26817 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule37561 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2748) (meaning t m 2779) (meaning t m 2829) (meaning t m 3365) (meaning t m 4111) (meaning t m 4256) (meaning t m 4438) (meaning t m 4734) source

theorem rule37562 (p2156 p2972 p3370 p4334 : Prop) (h : (¬ p2156) ∨ (¬ p4334) ∨ (¬ p3370) ∨ p2972) : (¬ p2156) ∨ (p2972) ∨ (¬ p3370) ∨ (¬ p4334) := by
  classical
  tauto

theorem initial37562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 2972) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4334)) := by
  have source := ElevenTheory.theory26818 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 9)
  exact rule37562 (meaning t m 2156) (meaning t m 2972) (meaning t m 3370) (meaning t m 4334) source

theorem rule37564 (p2027 p2299 p3256 p4044 p4348 p4361 : Prop) (h : (¬ p4044) ∨ (¬ p4361) ∨ (¬ p2299) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3256)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial37564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory26820 t (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37564 (meaning t m 2027) (meaning t m 2299) (meaning t m 3256) (meaning t m 4044) (meaning t m 4348) (meaning t m 4361) source

theorem rule37566 (p2027 p2299 p2996 p3171 p3189 p4361 p4403 : Prop) (h : (¬ p4403) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3189) ∨ (¬ p3171) ∨ (¬ p4361) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2996) ∨ (¬ p3171) ∨ (¬ p3189) ∨ (¬ p4361) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial37566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory26822 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule37566 (meaning t m 2027) (meaning t m 2299) (meaning t m 2996) (meaning t m 3171) (meaning t m 3189) (meaning t m 4361) (meaning t m 4403) source

theorem rule37570 (p1998 p2027 p2177 p2274 p2406 p2409 p2563 : Prop) (h : (¬ p2406) ∨ p2409 ∨ (¬ p2177) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2563)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial37570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory26826 t (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule37570 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2406) (meaning t m 2409) (meaning t m 2563) source

theorem rule37572 (p2027 p2573 p2589 p4203 p4235 p4555 : Prop) (h : (¬ p4203) ∨ (¬ p2589) ∨ (¬ p2573) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p4235)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial37572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory26828 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule37572 (meaning t m 2027) (meaning t m 2573) (meaning t m 2589) (meaning t m 4203) (meaning t m 4235) (meaning t m 4555) source

theorem rule37574 (p3550 p4041 p4774 : Prop) (h : (¬ p4041) ∨ (¬ p3550) ∨ p4774) : (¬ p3550) ∨ (¬ p4041) ∨ (p4774) := by
  classical
  tauto

theorem initial37574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4041)) ∨ (meaning t m 4774) := by
  have source := ElevenTheory.theory26830 t (m.theta 3 8) (m.theta 6 8) (m.theta 7 8)
  exact rule37574 (meaning t m 3550) (meaning t m 4041) (meaning t m 4774) source

theorem rule37578 (p1991 p2027 p2545 p2810 p2819 p2963 p3324 p4426 : Prop) (h : (¬ p4426) ∨ (¬ p2810) ∨ p2545 ∨ (¬ p1991) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2819) ∨ (¬ p3324)) : (¬ p1991) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p2819) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial37578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory26834 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule37578 (meaning t m 1991) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 2819) (meaning t m 2963) (meaning t m 3324) (meaning t m 4426) source

theorem rule37579 (p1981 p2027 p2352 p2406 p2409 p2573 p2589 : Prop) (h : (¬ p2589) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p1981) ∨ p2409 ∨ (¬ p2352)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2573) ∨ (¬ p2589) := by
  classical
  tauto

theorem initial37579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) := by
  have source := ElevenTheory.theory26835 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule37579 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2406) (meaning t m 2409) (meaning t m 2573) (meaning t m 2589) source

theorem rule37581 (p1981 p2027 p2187 p2307 p2842 p2850 p2962 p3097 p4109 : Prop) (h : (¬ p4109) ∨ p2842 ∨ (¬ p2187) ∨ (¬ p2850) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial37581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory26837 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37581 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2842) (meaning t m 2850) (meaning t m 2962) (meaning t m 3097) (meaning t m 4109) source

theorem rule37589 (p2027 p2373 p2743 p3051 p3877 p3954 p4043 p4235 p4399 p5190 : Prop) (h : (¬ p2743) ∨ (¬ p4043) ∨ (¬ p5190) ∨ (¬ p4399) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p3877) ∨ (¬ p2373) ∨ (¬ p3954) ∨ p2027) : (p2027) ∨ (¬ p2373) ∨ (¬ p2743) ∨ (¬ p3051) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4043) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory26845 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule37589 (meaning t m 2027) (meaning t m 2373) (meaning t m 2743) (meaning t m 3051) (meaning t m 3877) (meaning t m 3954) (meaning t m 4043) (meaning t m 4235) (meaning t m 4399) (meaning t m 5190) source

theorem rule37590 (p1984 p2027 p2202 p2440 p3256 p3591 p4121 p4261 p4371 : Prop) (h : (¬ p4261) ∨ (¬ p3256) ∨ (¬ p4371) ∨ (¬ p2440) ∨ p2027 ∨ p2202 ∨ (¬ p1984) ∨ (¬ p4121) ∨ (¬ p3591)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3256) ∨ (¬ p3591) ∨ (¬ p4121) ∨ (¬ p4261) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial37590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory26846 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 8 9)
  exact rule37590 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3256) (meaning t m 3591) (meaning t m 4121) (meaning t m 4261) (meaning t m 4371) source

theorem rule37594 (p1976 p2027 p2406 p2409 p2737 p3051 p3246 p3365 p3950 p4109 p4118 p4242 p4963 : Prop) (h : (¬ p1976) ∨ (¬ p3950) ∨ (¬ p2737) ∨ (¬ p3365) ∨ p2027 ∨ p2409 ∨ (¬ p4963) ∨ (¬ p2406) ∨ (¬ p4118) ∨ (¬ p4109) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4242)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2737) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p4109) ∨ (¬ p4118) ∨ (¬ p4242) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial37594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory26850 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule37594 (meaning t m 1976) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2737) (meaning t m 3051) (meaning t m 3246) (meaning t m 3365) (meaning t m 3950) (meaning t m 4109) (meaning t m 4118) (meaning t m 4242) (meaning t m 4963) source

theorem rule37595 (p1998 p2027 p2839 p2842 p2870 p2881 p3585 : Prop) (h : (¬ p2881) ∨ p2842 ∨ p2027 ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p1998) ∨ (¬ p2870)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial37595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory26851 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule37595 (meaning t m 1998) (meaning t m 2027) (meaning t m 2839) (meaning t m 2842) (meaning t m 2870) (meaning t m 2881) (meaning t m 3585) source

theorem rule37596 (p1998 p2027 p2137 p2839 p2842 p2881 p3051 p3585 : Prop) (h : (¬ p2881) ∨ (¬ p2137) ∨ (¬ p1998) ∨ p2842 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2839) ∨ (¬ p3051)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial37596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory26852 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule37596 (meaning t m 1998) (meaning t m 2027) (meaning t m 2137) (meaning t m 2839) (meaning t m 2842) (meaning t m 2881) (meaning t m 3051) (meaning t m 3585) source

theorem rule37601 (p2027 p2138 p2696 p2797 p4316 p4566 : Prop) (h : (¬ p2696) ∨ (¬ p2138) ∨ (¬ p4566) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p4316)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4316) ∨ (¬ p4566) := by
  classical
  tauto

theorem initial37601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4566)) := by
  have source := ElevenTheory.theory26857 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6)
  exact rule37601 (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2797) (meaning t m 4316) (meaning t m 4566) source

theorem rule37604 (p2027 p2299 p2743 p2911 p3389 p3572 p3954 p4361 p5190 : Prop) (h : (¬ p3389) ∨ (¬ p5190) ∨ (¬ p3954) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p4361) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2743) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3572) ∨ (¬ p3954) ∨ (¬ p4361) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory26860 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37604 (meaning t m 2027) (meaning t m 2299) (meaning t m 2743) (meaning t m 2911) (meaning t m 3389) (meaning t m 3572) (meaning t m 3954) (meaning t m 4361) (meaning t m 5190) source

theorem rule37608 (p4404 p4804 p5373 : Prop) (h : (¬ p5373) ∨ (¬ p4404) ∨ p4804) : (¬ p4404) ∨ (p4804) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial37608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4404)) ∨ (meaning t m 4804) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory26864 (m.theta 2 8) (m.theta 4 8) (m.theta 7 8)
  exact rule37608 (meaning t m 4404) (meaning t m 4804) (meaning t m 5373) source

theorem rule37610 (p3573 p3584 p3874 : Prop) (h : (¬ p3584) ∨ (¬ p3573) ∨ p3874) : (¬ p3573) ∨ (¬ p3584) ∨ (p3874) := by
  classical
  tauto

theorem initial37610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 3874) := by
  have source := ElevenTheory.theory26866 (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule37610 (meaning t m 3573) (meaning t m 3584) (meaning t m 3874) source

theorem rule37611 (p2027 p2352 p2598 p3146 p3422 p3860 p4134 p4261 p4733 : Prop) (h : (¬ p2598) ∨ (¬ p2352) ∨ (¬ p4261) ∨ (¬ p3860) ∨ (¬ p3422) ∨ (¬ p4134) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4733)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3146) ∨ (¬ p3422) ∨ (¬ p3860) ∨ (¬ p4134) ∨ (¬ p4261) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26867 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37611 (meaning t m 2027) (meaning t m 2352) (meaning t m 2598) (meaning t m 3146) (meaning t m 3422) (meaning t m 3860) (meaning t m 4134) (meaning t m 4261) (meaning t m 4733) source

theorem rule37612 (p2027 p2331 p3055 p4117 p4195 p4749 : Prop) (h : (¬ p2331) ∨ (¬ p4749) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial37612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory26868 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule37612 (meaning t m 2027) (meaning t m 2331) (meaning t m 3055) (meaning t m 4117) (meaning t m 4195) (meaning t m 4749) source

theorem rule37613 (p2027 p2797 p3073 p4116 p4340 p4364 p4688 p4975 : Prop) (h : (¬ p4975) ∨ (¬ p4116) ∨ (¬ p4688) ∨ (¬ p2797) ∨ (¬ p4364) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p4340)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3073) ∨ (¬ p4116) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4688) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial37613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4688)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory26869 t (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 6) (m.theta 8 9)
  exact rule37613 (meaning t m 2027) (meaning t m 2797) (meaning t m 3073) (meaning t m 4116) (meaning t m 4340) (meaning t m 4364) (meaning t m 4688) (meaning t m 4975) source

theorem rule37615 (p1988 p2027 p2545 p2992 p3115 p3680 p4111 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3115) ∨ p2545 ∨ (¬ p4111) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (p2545) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial37615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory26871 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule37615 (meaning t m 1988) (meaning t m 2027) (meaning t m 2545) (meaning t m 2992) (meaning t m 3115) (meaning t m 3680) (meaning t m 4111) source

theorem rule37618 (p2027 p2321 p3767 p4107 p4381 p5300 : Prop) (h : p2027 ∨ (¬ p2321) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p5300) ∨ (¬ p3767)) : (p2027) ∨ (¬ p2321) ∨ (¬ p3767) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p5300) := by
  classical
  tauto

theorem initial37618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2321)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5300)) := by
  have source := ElevenTheory.theory26874 t (m.theta 0 7) (m.theta 0 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule37618 (meaning t m 2027) (meaning t m 2321) (meaning t m 3767) (meaning t m 4107) (meaning t m 4381) (meaning t m 5300) source

theorem rule37626 (p2027 p2132 p2245 p2641 p2870 p2881 p2963 p4360 p4503 p4733 p4769 : Prop) (h : (¬ p2132) ∨ (¬ p2963) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p4360) ∨ (¬ p4769) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p4503) ∨ (¬ p2245)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2641) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p4360) ∨ (¬ p4503) ∨ (¬ p4733) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial37626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory26882 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule37626 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2641) (meaning t m 2870) (meaning t m 2881) (meaning t m 2963) (meaning t m 4360) (meaning t m 4503) (meaning t m 4733) (meaning t m 4769) source

theorem rule37632 (p1984 p2027 p2169 p2743 p3324 p3954 p4195 : Prop) (h : (¬ p3324) ∨ p2169 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3954) ∨ (¬ p4195) ∨ (¬ p2743)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2743) ∨ (¬ p3324) ∨ (¬ p3954) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial37632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory26888 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8)
  exact rule37632 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2743) (meaning t m 3324) (meaning t m 3954) (meaning t m 4195) source

theorem rule37634 (p2742 p4154 p4195 : Prop) (h : (¬ p2742) ∨ (¬ p4195) ∨ p4154) : (¬ p2742) ∨ (p4154) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial37634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2742)) ∨ (meaning t m 4154) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory26890 (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule37634 (meaning t m 2742) (meaning t m 4154) (meaning t m 4195) source

theorem rule37637 (p2005 p2027 p2766 p3422 p3644 p3876 p4348 : Prop) (h : p2766 ∨ (¬ p3422) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2005) ∨ (¬ p3876)) : (¬ p2005) ∨ (p2027) ∨ (p2766) ∨ (¬ p3422) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial37637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26893 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37637 (meaning t m 2005) (meaning t m 2027) (meaning t m 2766) (meaning t m 3422) (meaning t m 3644) (meaning t m 3876) (meaning t m 4348) source

theorem rule37640 (p2027 p2245 p2598 p2641 p2911 p2963 p3201 p4360 p4503 p4733 p4769 : Prop) (h : (¬ p2245) ∨ (¬ p2911) ∨ (¬ p4360) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p4503) ∨ (¬ p4769) ∨ (¬ p4733) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2598) ∨ (¬ p2641) ∨ (¬ p2911) ∨ (¬ p2963) ∨ (¬ p3201) ∨ (¬ p4360) ∨ (¬ p4503) ∨ (¬ p4733) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial37640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory26896 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule37640 (meaning t m 2027) (meaning t m 2245) (meaning t m 2598) (meaning t m 2641) (meaning t m 2911) (meaning t m 2963) (meaning t m 3201) (meaning t m 4360) (meaning t m 4503) (meaning t m 4733) (meaning t m 4769) source

theorem rule37641 (p3322 p3923 p4026 : Prop) (h : (¬ p3322) ∨ (¬ p3923) ∨ p4026) : (¬ p3322) ∨ (¬ p3923) ∨ (p4026) := by
  classical
  tauto

theorem initial37641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3923)) ∨ (meaning t m 4026) := by
  have source := ElevenTheory.theory26897 (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule37641 (meaning t m 3322) (meaning t m 3923) (meaning t m 4026) source

theorem rule37644 (p1998 p2027 p2528 p2699 p2922 p3379 p3875 p4348 : Prop) (h : (¬ p2528) ∨ (¬ p3875) ∨ p2699 ∨ (¬ p2922) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p1998) ∨ (¬ p3379)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2528) ∨ (p2699) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3875) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial37644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26900 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37644 (meaning t m 1998) (meaning t m 2027) (meaning t m 2528) (meaning t m 2699) (meaning t m 2922) (meaning t m 3379) (meaning t m 3875) (meaning t m 4348) source

theorem rule37646 (p2027 p2528 p2608 p3389 p3519 p3591 p3875 p3923 p4348 p4376 p4503 : Prop) (h : (¬ p3875) ∨ (¬ p3923) ∨ (¬ p2528) ∨ (¬ p3519) ∨ (¬ p3389) ∨ (¬ p3591) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4503) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3875) ∨ (¬ p3923) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial37646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory26902 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37646 (meaning t m 2027) (meaning t m 2528) (meaning t m 2608) (meaning t m 3389) (meaning t m 3519) (meaning t m 3591) (meaning t m 3875) (meaning t m 3923) (meaning t m 4348) (meaning t m 4376) (meaning t m 4503) source

theorem rule37647 (p2027 p2528 p3324 p3365 p3366 p3389 p3519 p3875 p4195 p4348 p4376 p4503 : Prop) (h : (¬ p3875) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3389) ∨ (¬ p2528) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3875) ∨ (¬ p4195) ∨ (¬ p4348) ∨ (¬ p4376) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial37647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory26903 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37647 (meaning t m 2027) (meaning t m 2528) (meaning t m 3324) (meaning t m 3365) (meaning t m 3366) (meaning t m 3389) (meaning t m 3519) (meaning t m 3875) (meaning t m 4195) (meaning t m 4348) (meaning t m 4376) (meaning t m 4503) source

theorem rule37648 (p2027 p2563 p3051 p4173 p4235 p4525 : Prop) (h : (¬ p4235) ∨ p2027 ∨ (¬ p4525) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p4173) ∨ (¬ p4235) ∨ (¬ p4525) := by
  classical
  tauto

theorem initial37648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4525)) := by
  have source := ElevenTheory.theory26904 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule37648 (meaning t m 2027) (meaning t m 2563) (meaning t m 3051) (meaning t m 4173) (meaning t m 4235) (meaning t m 4525) source

theorem rule37651 (p2027 p2331 p2657 p3584 p3984 p4750 : Prop) (h : p2027 ∨ (¬ p2657) ∨ (¬ p2331) ∨ (¬ p3984) ∨ (¬ p4750) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p3584) ∨ (¬ p3984) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial37651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory26907 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule37651 (meaning t m 2027) (meaning t m 2331) (meaning t m 2657) (meaning t m 3584) (meaning t m 3984) (meaning t m 4750) source

theorem rule37653 (p1987 p2027 p2992 p2997 p3568 p4154 p4315 : Prop) (h : (¬ p1987) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p2992) ∨ p2997 ∨ (¬ p3568)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2992) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial37653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory26909 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule37653 (meaning t m 1987) (meaning t m 2027) (meaning t m 2992) (meaning t m 2997) (meaning t m 3568) (meaning t m 4154) (meaning t m 4315) source

theorem rule37654 (p2027 p2247 p2373 p3051 p3324 p4154 p4235 p4433 p4521 : Prop) (h : p2027 ∨ (¬ p4521) ∨ (¬ p3051) ∨ (¬ p2247) ∨ (¬ p4154) ∨ (¬ p4433) ∨ (¬ p3324) ∨ (¬ p2373) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p3051) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4235) ∨ (¬ p4433) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial37654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory26910 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule37654 (meaning t m 2027) (meaning t m 2247) (meaning t m 2373) (meaning t m 3051) (meaning t m 3324) (meaning t m 4154) (meaning t m 4235) (meaning t m 4433) (meaning t m 4521) source

theorem rule37656 (p2363 p2396 p3325 p4445 : Prop) (h : (¬ p4445) ∨ (¬ p3325) ∨ (¬ p2363) ∨ p2396) : (¬ p2363) ∨ (p2396) ∨ (¬ p3325) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial37656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (meaning t m 2396) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory26912 (m.theta 6 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule37656 (meaning t m 2363) (meaning t m 2396) (meaning t m 3325) (meaning t m 4445) source

theorem rule37658 (p2027 p2156 p2542 p3054 p3758 p4109 p4750 : Prop) (h : (¬ p2542) ∨ (¬ p4750) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p3054) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2542) ∨ (¬ p3054) ∨ (¬ p3758) ∨ (¬ p4109) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial37658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory26914 t (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule37658 (meaning t m 2027) (meaning t m 2156) (meaning t m 2542) (meaning t m 3054) (meaning t m 3758) (meaning t m 4109) (meaning t m 4750) source

theorem rule37662 (p2027 p2284 p2850 p3096 p3584 p4705 : Prop) (h : (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p4705) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial37662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory26918 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule37662 (meaning t m 2027) (meaning t m 2284) (meaning t m 2850) (meaning t m 3096) (meaning t m 3584) (meaning t m 4705) source

theorem rule37664 (p3946 p4026 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p4026) ∨ p3946) : (p3946) ∨ (¬ p4026) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial37664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3946) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory26920 (m.theta 0 6) (m.theta 1 6) (m.theta 6 9)
  exact rule37664 (meaning t m 3946) (meaning t m 4026) (meaning t m 5016) source

theorem rule37665 (p2027 p2247 p2619 p3051 p4111 p4244 p4256 p4434 p4521 : Prop) (h : (¬ p3051) ∨ (¬ p4256) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p4434) ∨ (¬ p4521) ∨ (¬ p2619) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4111) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4434) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial37665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory26921 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule37665 (meaning t m 2027) (meaning t m 2247) (meaning t m 2619) (meaning t m 3051) (meaning t m 4111) (meaning t m 4244) (meaning t m 4256) (meaning t m 4434) (meaning t m 4521) source

theorem rule37666 (p2027 p2248 p2437 p2651 p3868 p3954 p4379 p4826 p5387 : Prop) (h : (¬ p4379) ∨ (¬ p2248) ∨ (¬ p3954) ∨ (¬ p5387) ∨ (¬ p4826) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3868) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p4826) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial37666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory26922 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 9) (m.theta 3 4) (m.theta 4 7) (m.theta 7 10) (m.theta 9 10)
  exact rule37666 (meaning t m 2027) (meaning t m 2248) (meaning t m 2437) (meaning t m 2651) (meaning t m 3868) (meaning t m 3954) (meaning t m 4379) (meaning t m 4826) (meaning t m 5387) source

theorem rule37669 (p2027 p2122 p2177 p2247 p2774 p4111 p4256 p4438 p4733 : Prop) (h : p2027 ∨ (¬ p4111) ∨ (¬ p4733) ∨ (¬ p4438) ∨ (¬ p2247) ∨ (¬ p4256) ∨ (¬ p2774) ∨ (¬ p2177) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2774) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26925 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule37669 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2247) (meaning t m 2774) (meaning t m 4111) (meaning t m 4256) (meaning t m 4438) (meaning t m 4733) source

theorem rule37670 (p1987 p2027 p2765 p3027 p3572 p3662 p3952 : Prop) (h : (¬ p3952) ∨ p2027 ∨ (¬ p1987) ∨ p2765 ∨ (¬ p3662) ∨ (¬ p3572) ∨ (¬ p3027)) : (¬ p1987) ∨ (p2027) ∨ (p2765) ∨ (¬ p3027) ∨ (¬ p3572) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial37670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory26926 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule37670 (meaning t m 1987) (meaning t m 2027) (meaning t m 2765) (meaning t m 3027) (meaning t m 3572) (meaning t m 3662) (meaning t m 3952) source

theorem rule37673 (p2510 p3016 p3083 : Prop) (h : (¬ p2510) ∨ (¬ p3016) ∨ p3083) : (¬ p2510) ∨ (¬ p3016) ∨ (p3083) := by
  classical
  tauto

theorem initial37673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 3016)) ∨ (meaning t m 3083) := by
  have source := ElevenTheory.theory26929 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule37673 (meaning t m 2510) (meaning t m 3016) (meaning t m 3083) source

theorem rule37683 (p2027 p2247 p2299 p2911 p3389 p3662 p4320 p4559 p5190 : Prop) (h : (¬ p3662) ∨ (¬ p4320) ∨ (¬ p5190) ∨ (¬ p2247) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p4559) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p4320) ∨ (¬ p4559) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory26939 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37683 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2911) (meaning t m 3389) (meaning t m 3662) (meaning t m 4320) (meaning t m 4559) (meaning t m 5190) source

theorem rule37686 (p2027 p2248 p2352 p2651 p3016 p3688 p3822 p3954 p4405 : Prop) (h : (¬ p3688) ∨ (¬ p3954) ∨ (¬ p3016) ∨ (¬ p2248) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2651) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial37686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory26942 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37686 (meaning t m 2027) (meaning t m 2248) (meaning t m 2352) (meaning t m 2651) (meaning t m 3016) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) (meaning t m 4405) source

theorem rule37689 (p2027 p2139 p2373 p3051 p3324 p3365 p4195 p4235 p4433 : Prop) (h : (¬ p3051) ∨ (¬ p4433) ∨ (¬ p4235) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p2373) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2373) ∨ (¬ p3051) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4235) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial37689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory26945 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule37689 (meaning t m 2027) (meaning t m 2139) (meaning t m 2373) (meaning t m 3051) (meaning t m 3324) (meaning t m 3365) (meaning t m 4195) (meaning t m 4235) (meaning t m 4433) source

theorem rule37691 (p2027 p2122 p2177 p2247 p2774 p2996 p3947 p4666 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p2996) ∨ (¬ p2247) ∨ (¬ p2177) ∨ (¬ p2122) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2774) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26947 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37691 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2247) (meaning t m 2774) (meaning t m 2996) (meaning t m 3947) (meaning t m 4666) (meaning t m 4733) source

theorem rule37692 (p1981 p2027 p2088 p2166 p2765 p3412 p3696 p3952 p4347 : Prop) (h : (¬ p2088) ∨ (¬ p3412) ∨ (¬ p2166) ∨ (¬ p3696) ∨ p2765 ∨ (¬ p1981) ∨ (¬ p4347) ∨ (¬ p3952) ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2166) ∨ (p2765) ∨ (¬ p3412) ∨ (¬ p3696) ∨ (¬ p3952) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial37692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory26948 t (m.theta 0 8) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37692 (meaning t m 1981) (meaning t m 2027) (meaning t m 2088) (meaning t m 2166) (meaning t m 2765) (meaning t m 3412) (meaning t m 3696) (meaning t m 3952) (meaning t m 4347) source

theorem rule37696 (p1998 p2027 p2233 p2352 p2363 p2573 p4348 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p2573) ∨ (¬ p2352) ∨ (¬ p1998) ∨ (¬ p2363) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (p2233) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial37696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26952 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37696 (meaning t m 1998) (meaning t m 2027) (meaning t m 2233) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 4348) source

theorem rule37697 (p2027 p3156 p3413 p3574 p3880 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p3574) ∨ (¬ p3413) ∨ (¬ p3156) ∨ (¬ p3880) ∨ p2027) : (p2027) ∨ (¬ p3156) ∨ (¬ p3413) ∨ (¬ p3574) ∨ (¬ p3880) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial37697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory26953 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule37697 (meaning t m 2027) (meaning t m 3156) (meaning t m 3413) (meaning t m 3574) (meaning t m 3880) (meaning t m 4715) source

theorem rule37699 (p2027 p2247 p2299 p2608 p2911 p2996 p3389 p3519 p4361 p4376 : Prop) (h : (¬ p4361) ∨ (¬ p2299) ∨ (¬ p2247) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p2996)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4361) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial37699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory26955 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37699 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2608) (meaning t m 2911) (meaning t m 2996) (meaning t m 3389) (meaning t m 3519) (meaning t m 4361) (meaning t m 4376) source

theorem rule37702 (p2027 p2187 p2284 p4193 p4358 p4906 : Prop) (h : (¬ p2187) ∨ p2027 ∨ (¬ p4906) ∨ (¬ p2284) ∨ (¬ p4193) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial37702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory26958 t (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule37702 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 4193) (meaning t m 4358) (meaning t m 4906) source

theorem rule37703 (p2027 p2982 p3051 p3365 p3877 p4118 p4235 p4399 p4419 p4450 : Prop) (h : (¬ p3877) ∨ (¬ p4419) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4399) ∨ (¬ p4235) ∨ (¬ p4450) ∨ (¬ p4118) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4235) ∨ (¬ p4399) ∨ (¬ p4419) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial37703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory26959 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule37703 (meaning t m 2027) (meaning t m 2982) (meaning t m 3051) (meaning t m 3365) (meaning t m 3877) (meaning t m 4118) (meaning t m 4235) (meaning t m 4399) (meaning t m 4419) (meaning t m 4450) source

theorem rule37708 (p2027 p2493 p2509 p2579 p2619 p3051 p4108 p4244 p4434 p4521 : Prop) (h : (¬ p2509) ∨ (¬ p3051) ∨ (¬ p4108) ∨ (¬ p2579) ∨ (¬ p4434) ∨ (¬ p2493) ∨ (¬ p4244) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p4521)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p4108) ∨ (¬ p4244) ∨ (¬ p4434) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial37708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory26964 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule37708 (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2579) (meaning t m 2619) (meaning t m 3051) (meaning t m 4108) (meaning t m 4244) (meaning t m 4434) (meaning t m 4521) source

theorem rule37710 (p2598 p2780 p4375 : Prop) (h : (¬ p4375) ∨ (¬ p2780) ∨ (¬ p2598)) : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial37710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory26966 (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule37710 (meaning t m 2598) (meaning t m 2780) (meaning t m 4375) source

theorem rule37711 (p2027 p2156 p2187 p2590 p3956 p4539 : Prop) (h : (¬ p2187) ∨ (¬ p2590) ∨ (¬ p4539) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2590) ∨ (¬ p3956) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial37711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory26967 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule37711 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2590) (meaning t m 3956) (meaning t m 4539) source

theorem rule37716 (p2027 p2156 p2177 p2274 p3588 p3947 p3954 p4521 p4666 p4777 : Prop) (h : (¬ p4666) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p4521) ∨ (¬ p3588) ∨ (¬ p2156) ∨ (¬ p3947) ∨ (¬ p4777)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3588) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4666) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial37716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory26972 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37716 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 3588) (meaning t m 3947) (meaning t m 3954) (meaning t m 4521) (meaning t m 4666) (meaning t m 4777) source

theorem rule37717 (p2761 p4425 p4451 : Prop) (h : (¬ p4425) ∨ (¬ p2761) ∨ (¬ p4451)) : (¬ p2761) ∨ (¬ p4425) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial37717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory26973 (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule37717 (meaning t m 2761) (meaning t m 4425) (meaning t m 4451) source

theorem rule37718 (p2027 p2177 p2553 p2573 p3256 p3860 p4041 p4261 p5190 : Prop) (h : (¬ p2177) ∨ (¬ p4041) ∨ (¬ p5190) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3256) ∨ (¬ p3860) ∨ (¬ p4041) ∨ (¬ p4261) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory26974 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37718 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 3256) (meaning t m 3860) (meaning t m 4041) (meaning t m 4261) (meaning t m 5190) source

theorem rule37720 (p2027 p2761 p2911 p4425 p4635 p4666 : Prop) (h : p2027 ∨ (¬ p2761) ∨ (¬ p4635) ∨ (¬ p4666) ∨ (¬ p2911) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2761) ∨ (¬ p2911) ∨ (¬ p4425) ∨ (¬ p4635) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial37720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4635)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory26976 t (m.theta 4 7) (m.theta 4 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule37720 (meaning t m 2027) (meaning t m 2761) (meaning t m 2911) (meaning t m 4425) (meaning t m 4635) (meaning t m 4666) source

theorem rule37721 (p2027 p2156 p2249 p2951 p2992 p3037 p3125 p3414 p3548 p4330 p4348 : Prop) (h : (¬ p4330) ∨ (¬ p3548) ∨ (¬ p3037) ∨ (¬ p4348) ∨ (¬ p3414) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3037) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial37721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26977 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule37721 (meaning t m 2027) (meaning t m 2156) (meaning t m 2249) (meaning t m 2951) (meaning t m 2992) (meaning t m 3037) (meaning t m 3125) (meaning t m 3414) (meaning t m 3548) (meaning t m 4330) (meaning t m 4348) source

theorem rule37723 (p2027 p2249 p2641 p3170 p3256 p3857 p4341 : Prop) (h : (¬ p3857) ∨ (¬ p4341) ∨ (¬ p3170) ∨ (¬ p2249) ∨ (¬ p3256) ∨ (¬ p2641) ∨ p2027) : (p2027) ∨ (¬ p2249) ∨ (¬ p2641) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial37723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory26979 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule37723 (meaning t m 2027) (meaning t m 2249) (meaning t m 2641) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) (meaning t m 4341) source

theorem rule37725 (p2027 p3631 p4235 p4324 p4344 p4431 p4632 : Prop) (h : (¬ p4431) ∨ (¬ p4324) ∨ (¬ p4632) ∨ (¬ p4235) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p4344)) : (p2027) ∨ (¬ p3631) ∨ (¬ p4235) ∨ (¬ p4324) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial37725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory26981 t (m.theta 1 5) (m.theta 1 7) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule37725 (meaning t m 2027) (meaning t m 3631) (meaning t m 4235) (meaning t m 4324) (meaning t m 4344) (meaning t m 4431) (meaning t m 4632) source

theorem rule37727 (p2027 p2191 p2619 p2891 p4235 p4885 : Prop) (h : (¬ p4235) ∨ (¬ p4885) ∨ (¬ p2891) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2619) ∨ (¬ p2891) ∨ (¬ p4235) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial37727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory26983 t (m.theta 1 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule37727 (meaning t m 2027) (meaning t m 2191) (meaning t m 2619) (meaning t m 2891) (meaning t m 4235) (meaning t m 4885) source

theorem rule37729 (p2027 p2247 p2352 p2598 p3422 p3568 p4154 p4405 p4733 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p3422) ∨ (¬ p3568) ∨ (¬ p4733) ∨ (¬ p4405) ∨ (¬ p2598) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26985 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37729 (meaning t m 2027) (meaning t m 2247) (meaning t m 2352) (meaning t m 2598) (meaning t m 3422) (meaning t m 3568) (meaning t m 4154) (meaning t m 4405) (meaning t m 4733) source

theorem rule37730 (p2027 p2230 p2373 p3054 p3694 p4730 : Prop) (h : (¬ p4730) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3054) ∨ (¬ p3694) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3054) ∨ (¬ p3694) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial37730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory26986 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule37730 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3054) (meaning t m 3694) (meaning t m 4730) source

end SunPrize.SMT
