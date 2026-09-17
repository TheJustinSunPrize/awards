import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory029
import SunPrize.Certificate.Theory030
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule20249 (p2027 p2946 p3027 p3414 p4111 p4704 : Prop) (h : (¬ p4111) ∨ (¬ p2946) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial20249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory9505 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule20249 (meaning t m 2027) (meaning t m 2946) (meaning t m 3027) (meaning t m 3414) (meaning t m 4111) (meaning t m 4704) source

theorem rule20250 (p2972 p3486 p4402 : Prop) (h : (¬ p3486) ∨ (¬ p2972) ∨ (¬ p4402)) : (¬ p2972) ∨ (¬ p3486) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial20250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory9506 (m.theta 1 5) (m.theta 5 7) (m.theta 5 9)
  exact rule20250 (meaning t m 2972) (meaning t m 3486) (meaning t m 4402) source

theorem rule20254 (p2727 p2742 p2810 : Prop) (h : (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2810)) : (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2810) := by
  classical
  tauto

theorem initial20254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2810)) := by
  have source := ElevenTheory.theory9510 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule20254 (meaning t m 2727) (meaning t m 2742) (meaning t m 2810) source

theorem rule20255 (p2663 p3292 p3355 p5171 : Prop) (h : (¬ p3355) ∨ (¬ p3292) ∨ (¬ p2663) ∨ (¬ p5171)) : (¬ p2663) ∨ (¬ p3292) ∨ (¬ p3355) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial20255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory9511 (m.theta 0 3) (m.theta 0 4) (m.theta 3 9) (m.theta 4 9)
  exact rule20255 (meaning t m 2663) (meaning t m 3292) (meaning t m 3355) (meaning t m 5171) source

theorem rule20260 (p3555 p3830 p4938 : Prop) (h : (¬ p3830) ∨ (¬ p3555) ∨ (¬ p4938)) : (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4938) := by
  classical
  tauto

theorem initial20260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4938)) := by
  have source := ElevenTheory.theory9516 (m.theta 0 1) (m.theta 1 5) (m.theta 1 9)
  exact rule20260 (meaning t m 3555) (meaning t m 3830) (meaning t m 4938) source

theorem rule20261 (p2027 p2542 p2727 p4360 p4437 p4608 : Prop) (h : (¬ p2542) ∨ (¬ p4608) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p4437) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial20261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory9517 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8)
  exact rule20261 (meaning t m 2027) (meaning t m 2542) (meaning t m 2727) (meaning t m 4360) (meaning t m 4437) (meaning t m 4608) source

theorem rule20262 (p2911 p3570 p4001 : Prop) (h : (¬ p3570) ∨ (¬ p4001) ∨ (¬ p2911)) : (¬ p2911) ∨ (¬ p3570) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial20262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory9518 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule20262 (meaning t m 2911) (meaning t m 3570) (meaning t m 4001) source

theorem rule20263 (p2027 p2341 p2396 p3644 p3821 p4276 : Prop) (h : (¬ p2396) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3821) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3644) ∨ (¬ p3821) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial20263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory9519 t (m.theta 0 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule20263 (meaning t m 2027) (meaning t m 2341) (meaning t m 2396) (meaning t m 3644) (meaning t m 3821) (meaning t m 4276) source

theorem rule20264 (p2027 p3325 p3644 p3979 p4276 p5558 : Prop) (h : (¬ p4276) ∨ (¬ p3644) ∨ (¬ p3325) ∨ p2027 ∨ (¬ p3979) ∨ (¬ p5558)) : (p2027) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p3979) ∨ (¬ p4276) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial20264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory9520 t (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule20264 (meaning t m 2027) (meaning t m 3325) (meaning t m 3644) (meaning t m 3979) (meaning t m 4276) (meaning t m 5558) source

theorem rule20269 (p2957 p3156 p4120 : Prop) (h : (¬ p2957) ∨ (¬ p3156) ∨ (¬ p4120)) : (¬ p2957) ∨ (¬ p3156) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial20269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory9525 (m.theta 0 5) (m.theta 3 5) (m.theta 5 8)
  exact rule20269 (meaning t m 2957) (meaning t m 3156) (meaning t m 4120) source

theorem rule20270 (p2210 p3860 p4496 : Prop) (h : (¬ p2210) ∨ (¬ p3860) ∨ (¬ p4496)) : (¬ p2210) ∨ (¬ p3860) ∨ (¬ p4496) := by
  classical
  tauto

theorem initial20270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4496)) := by
  have source := ElevenTheory.theory9526 (m.theta 0 1) (m.theta 1 5) (m.theta 1 8)
  exact rule20270 (meaning t m 2210) (meaning t m 3860) (meaning t m 4496) source

theorem rule20272 (p2156 p4109 p4110 : Prop) (h : (¬ p2156) ∨ (¬ p4109) ∨ (¬ p4110)) : (¬ p2156) ∨ (¬ p4109) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial20272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory9528 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule20272 (meaning t m 2156) (meaning t m 4109) (meaning t m 4110) source

theorem rule20278 (p2742 p2992 p4315 : Prop) (h : (¬ p2992) ∨ (¬ p2742) ∨ (¬ p4315)) : (¬ p2742) ∨ (¬ p2992) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial20278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory9534 (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule20278 (meaning t m 2742) (meaning t m 2992) (meaning t m 4315) source

theorem rule20279 (p2253 p2331 p3591 p4319 : Prop) (h : (¬ p2253) ∨ (¬ p3591) ∨ (¬ p2331) ∨ (¬ p4319)) : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p3591) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial20279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory9535 (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 6)
  exact rule20279 (meaning t m 2253) (meaning t m 2331) (meaning t m 3591) (meaning t m 4319) source

theorem rule20280 (p2743 p2829 p4841 : Prop) (h : (¬ p2829) ∨ (¬ p2743) ∨ (¬ p4841)) : (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial20280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory9536 (m.theta 1 2) (m.theta 2 3) (m.theta 2 6)
  exact rule20280 (meaning t m 2743) (meaning t m 2829) (meaning t m 4841) source

theorem rule20283 (p3379 p3860 p4688 : Prop) (h : (¬ p3860) ∨ (¬ p3379) ∨ (¬ p4688)) : (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4688) := by
  classical
  tauto

theorem initial20283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4688)) := by
  have source := ElevenTheory.theory9539 (m.theta 0 1) (m.theta 1 4) (m.theta 1 8)
  exact rule20283 (meaning t m 3379) (meaning t m 3860) (meaning t m 4688) source

theorem rule20286 (p2860 p3872 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p2860) ∨ (¬ p3872)) : (¬ p2860) ∨ (¬ p3872) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial20286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory9542 (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20286 (meaning t m 2860) (meaning t m 3872) (meaning t m 4244) source

theorem rule20288 (p2274 p3568 p3986 : Prop) (h : (¬ p2274) ∨ (¬ p3568) ∨ (¬ p3986)) : (¬ p2274) ∨ (¬ p3568) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial20288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory9544 (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule20288 (meaning t m 2274) (meaning t m 3568) (meaning t m 3986) source

theorem rule20289 (p2829 p3583 p4193 : Prop) (h : (¬ p3583) ∨ (¬ p2829) ∨ (¬ p4193)) : (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial20289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory9545 (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule20289 (meaning t m 2829) (meaning t m 3583) (meaning t m 4193) source

theorem rule20290 (p2274 p3822 p4185 : Prop) (h : (¬ p2274) ∨ (¬ p3822) ∨ (¬ p4185)) : (¬ p2274) ∨ (¬ p3822) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial20290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory9546 (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule20290 (meaning t m 2274) (meaning t m 3822) (meaning t m 4185) source

theorem rule20291 (p2589 p2655 p2946 p4241 : Prop) (h : (¬ p2946) ∨ (¬ p2655) ∨ (¬ p2589) ∨ (¬ p4241)) : (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial20291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory9547 (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 5)
  exact rule20291 (meaning t m 2589) (meaning t m 2655) (meaning t m 2946) (meaning t m 4241) source

theorem rule20292 (p2138 p2707 p3366 p4136 : Prop) (h : (¬ p2707) ∨ (¬ p2138) ∨ (¬ p3366) ∨ (¬ p4136)) : (¬ p2138) ∨ (¬ p2707) ∨ (¬ p3366) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial20292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory9548 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule20292 (meaning t m 2138) (meaning t m 2707) (meaning t m 3366) (meaning t m 4136) source

theorem rule20294 (p2027 p2588 p2668 p3564 p4037 p4405 : Prop) (h : p2027 ∨ (¬ p2588) ∨ (¬ p4405) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2588) ∨ (¬ p2668) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial20294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory9550 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule20294 (meaning t m 2027) (meaning t m 2588) (meaning t m 2668) (meaning t m 3564) (meaning t m 4037) (meaning t m 4405) source

theorem rule20296 (p2284 p4173 p4282 : Prop) (h : (¬ p4282) ∨ (¬ p2284) ∨ (¬ p4173)) : (¬ p2284) ∨ (¬ p4173) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial20296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory9552 (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule20296 (meaning t m 2284) (meaning t m 4173) (meaning t m 4282) source

theorem rule20297 (p2427 p2957 p3556 p4241 : Prop) (h : (¬ p3556) ∨ (¬ p2957) ∨ (¬ p2427) ∨ (¬ p4241)) : (¬ p2427) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial20297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory9553 (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20297 (meaning t m 2427) (meaning t m 2957) (meaning t m 3556) (meaning t m 4241) source

theorem rule20298 (p2427 p3556 p4031 : Prop) (h : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4031)) : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial20298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory9554 (m.theta 0 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20298 (meaning t m 2427) (meaning t m 3556) (meaning t m 4031) source

theorem rule20300 (p2001 p2027 p2202 p2470 p2589 p3073 p3692 p4370 : Prop) (h : (¬ p2589) ∨ p2027 ∨ p2202 ∨ (¬ p3692) ∨ (¬ p3073) ∨ (¬ p4370) ∨ (¬ p2001) ∨ (¬ p2470)) : (¬ p2001) ∨ (p2027) ∨ (p2202) ∨ (¬ p2470) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial20300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory9556 t (m.theta 0 4) (m.theta 1 8) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule20300 (meaning t m 2001) (meaning t m 2027) (meaning t m 2202) (meaning t m 2470) (meaning t m 2589) (meaning t m 3073) (meaning t m 3692) (meaning t m 4370) source

theorem rule20301 (p2241 p3555 p4365 : Prop) (h : (¬ p2241) ∨ (¬ p4365) ∨ (¬ p3555)) : (¬ p2241) ∨ (¬ p3555) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial20301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory9557 (m.theta 0 1) (m.theta 1 3) (m.theta 1 5)
  exact rule20301 (meaning t m 2241) (meaning t m 3555) (meaning t m 4365) source

theorem rule20303 (p2780 p3366 p3367 p4375 : Prop) (h : (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4375)) : (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial20303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory9559 (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6)
  exact rule20303 (meaning t m 2780) (meaning t m 3366) (meaning t m 3367) (meaning t m 4375) source

theorem rule20304 (p2440 p2590 p3016 : Prop) (h : (¬ p3016) ∨ (¬ p2440) ∨ (¬ p2590)) : (¬ p2440) ∨ (¬ p2590) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial20304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory9560 (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule20304 (meaning t m 2440) (meaning t m 2590) (meaning t m 3016) source

theorem rule20307 (p3093 p4366 p4452 : Prop) (h : (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4452)) : (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial20307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory9563 (m.theta 0 1) (m.theta 1 6) (m.theta 1 7)
  exact rule20307 (meaning t m 3093) (meaning t m 4366) (meaning t m 4452) source

theorem rule20308 (p2241 p3591 p4759 : Prop) (h : (¬ p2241) ∨ (¬ p3591) ∨ (¬ p4759)) : (¬ p2241) ∨ (¬ p3591) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial20308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory9564 (m.theta 0 1) (m.theta 1 3) (m.theta 1 6)
  exact rule20308 (meaning t m 2241) (meaning t m 3591) (meaning t m 4759) source

theorem rule20310 (p2027 p2470 p2531 p2589 p4235 p4904 : Prop) (h : (¬ p4904) ∨ (¬ p2470) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2531)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p4235) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial20310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory9566 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule20310 (meaning t m 2027) (meaning t m 2470) (meaning t m 2531) (meaning t m 2589) (meaning t m 4235) (meaning t m 4904) source

theorem rule20311 (p2563 p3695 p3872 p4244 : Prop) (h : (¬ p3872) ∨ (¬ p2563) ∨ (¬ p4244) ∨ (¬ p3695)) : (¬ p2563) ∨ (¬ p3695) ∨ (¬ p3872) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial20311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory9567 (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20311 (meaning t m 2563) (meaning t m 3695) (meaning t m 3872) (meaning t m 4244) source

theorem rule20312 (p2563 p3872 p4235 : Prop) (h : (¬ p3872) ∨ (¬ p2563) ∨ (¬ p4235)) : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial20312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory9568 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20312 (meaning t m 2563) (meaning t m 3872) (meaning t m 4235) source

theorem rule20314 (p2437 p3875 p4256 : Prop) (h : (¬ p3875) ∨ (¬ p2437) ∨ (¬ p4256)) : (¬ p2437) ∨ (¬ p3875) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial20314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory9570 (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule20314 (meaning t m 2437) (meaning t m 3875) (meaning t m 4256) source

theorem rule20315 (p2901 p3879 p4235 : Prop) (h : (¬ p3879) ∨ (¬ p4235) ∨ (¬ p2901)) : (¬ p2901) ∨ (¬ p3879) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial20315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory9571 (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20315 (meaning t m 2901) (meaning t m 3879) (meaning t m 4235) source

theorem rule20316 (p2088 p3960 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p2088) ∨ (¬ p3960)) : (¬ p2088) ∨ (¬ p3960) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial20316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory9572 (m.theta 0 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20316 (meaning t m 2088) (meaning t m 3960) (meaning t m 4348) source

theorem rule20317 (p2579 p3389 p3581 : Prop) (h : (¬ p3581) ∨ (¬ p2579) ∨ (¬ p3389)) : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3581) := by
  classical
  tauto

theorem initial20317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3581)) := by
  have source := ElevenTheory.theory9573 (m.theta 0 4) (m.theta 4 6) (m.theta 4 7)
  exact rule20317 (meaning t m 2579) (meaning t m 3389) (meaning t m 3581) source

theorem rule20318 (p2156 p2579 p3096 p4399 : Prop) (h : (¬ p4399) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p2156)) : (¬ p2156) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial20318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory9574 (m.theta 0 4) (m.theta 0 5) (m.theta 4 6) (m.theta 5 6)
  exact rule20318 (meaning t m 2156) (meaning t m 2579) (meaning t m 3096) (meaning t m 4399) source

theorem rule20324 (p2027 p2230 p2440 p2579 p3422 p4753 : Prop) (h : p2027 ∨ (¬ p3422) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p4753) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial20324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory9580 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule20324 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2579) (meaning t m 3422) (meaning t m 4753) source

theorem rule20326 (p2027 p2850 p3367 p3583 p4885 : Prop) (h : (¬ p3367) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p4885) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial20326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory9582 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule20326 (meaning t m 2027) (meaning t m 2850) (meaning t m 3367) (meaning t m 3583) (meaning t m 4885) source

theorem rule20328 (p2608 p3591 p4869 : Prop) (h : (¬ p2608) ∨ (¬ p3591) ∨ (¬ p4869)) : (¬ p2608) ∨ (¬ p3591) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial20328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory9584 (m.theta 0 1) (m.theta 1 2) (m.theta 1 6)
  exact rule20328 (meaning t m 2608) (meaning t m 3591) (meaning t m 4869) source

theorem rule20330 (p1994 p2027 p2651 p2764 p3172 p4118 p4444 : Prop) (h : (¬ p4118) ∨ (¬ p4444) ∨ (¬ p1994) ∨ p2764 ∨ (¬ p3172) ∨ p2027 ∨ (¬ p2651)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial20330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory9586 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule20330 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 3172) (meaning t m 4118) (meaning t m 4444) source

theorem rule20333 (p2891 p4034 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p4034) ∨ (¬ p2891)) : (¬ p2891) ∨ (¬ p4034) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial20333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory9589 (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20333 (meaning t m 2891) (meaning t m 4034) (meaning t m 4235) source

theorem rule20334 (p3146 p4118 p4311 : Prop) (h : (¬ p4118) ∨ (¬ p3146) ∨ (¬ p4311)) : (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial20334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory9590 (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule20334 (meaning t m 3146) (meaning t m 4118) (meaning t m 4311) source

theorem rule20336 (p2220 p3880 p4109 : Prop) (h : (¬ p4109) ∨ (¬ p2220) ∨ (¬ p3880)) : (¬ p2220) ∨ (¬ p3880) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial20336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory9592 (m.theta 0 5) (m.theta 4 5) (m.theta 5 8)
  exact rule20336 (meaning t m 2220) (meaning t m 3880) (meaning t m 4109) source

theorem rule20338 (p2027 p2210 p2284 p3591 p3957 p4957 : Prop) (h : (¬ p4957) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2210) ∨ (¬ p3591) ∨ (¬ p3957)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2284) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial20338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory9594 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6)
  exact rule20338 (meaning t m 2027) (meaning t m 2210) (meaning t m 2284) (meaning t m 3591) (meaning t m 3957) (meaning t m 4957) source

theorem rule20343 (p2441 p2589 p3389 : Prop) (h : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p2441)) : (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial20343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory9599 (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule20343 (meaning t m 2441) (meaning t m 2589) (meaning t m 3389) source

theorem rule20345 (p2027 p2132 p2737 p3425 p3583 p4778 : Prop) (h : (¬ p4778) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3425) ∨ (¬ p3583) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial20345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory9601 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule20345 (meaning t m 2027) (meaning t m 2132) (meaning t m 2737) (meaning t m 3425) (meaning t m 3583) (meaning t m 4778) source

theorem rule20348 (p2156 p3556 p3872 : Prop) (h : (¬ p2156) ∨ (¬ p3872) ∨ (¬ p3556)) : (¬ p2156) ∨ (¬ p3556) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial20348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory9604 (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20348 (meaning t m 2156) (meaning t m 3556) (meaning t m 3872) source

theorem rule20349 (p2737 p3583 p4313 : Prop) (h : (¬ p2737) ∨ (¬ p3583) ∨ (¬ p4313)) : (¬ p2737) ∨ (¬ p3583) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial20349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory9605 (m.theta 1 2) (m.theta 2 3) (m.theta 2 5)
  exact rule20349 (meaning t m 2737) (meaning t m 3583) (meaning t m 4313) source

theorem rule20354 (p2138 p2598 p3582 : Prop) (h : (¬ p2598) ∨ (¬ p2138) ∨ (¬ p3582)) : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3582) := by
  classical
  tauto

theorem initial20354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3582)) := by
  have source := ElevenTheory.theory9610 (m.theta 0 2) (m.theta 2 4) (m.theta 2 5)
  exact rule20354 (meaning t m 2138) (meaning t m 2598) (meaning t m 3582) source

theorem rule20358 (p2598 p2743 p2753 p3364 : Prop) (h : (¬ p2743) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p3364)) : (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2753) ∨ (¬ p3364) := by
  classical
  tauto

theorem initial20358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3364)) := by
  have source := ElevenTheory.theory9614 (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4)
  exact rule20358 (meaning t m 2598) (meaning t m 2743) (meaning t m 2753) (meaning t m 3364) source

theorem rule20359 (p2122 p2588 p4342 : Prop) (h : (¬ p2588) ∨ (¬ p4342) ∨ (¬ p2122)) : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial20359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory9615 (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule20359 (meaning t m 2122) (meaning t m 2588) (meaning t m 4342) source

theorem rule20362 (p3333 p3874 p4045 : Prop) (h : (¬ p3874) ∨ (¬ p3333) ∨ (¬ p4045)) : (¬ p3333) ∨ (¬ p3874) ∨ (¬ p4045) := by
  classical
  tauto

theorem initial20362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4045)) := by
  have source := ElevenTheory.theory9618 (m.theta 2 4) (m.theta 4 8) (m.theta 4 9)
  exact rule20362 (meaning t m 3333) (meaning t m 3874) (meaning t m 4045) source

theorem rule20364 (p2417 p3644 p3657 : Prop) (h : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3657)) : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial20364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory9620 (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule20364 (meaning t m 2417) (meaning t m 3644) (meaning t m 3657) source

theorem rule20368 (p2440 p3083 p4607 : Prop) (h : (¬ p2440) ∨ (¬ p3083) ∨ (¬ p4607)) : (¬ p2440) ∨ (¬ p3083) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial20368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory9624 (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule20368 (meaning t m 2440) (meaning t m 3083) (meaning t m 4607) source

theorem rule20371 (p2510 p3016 p4256 : Prop) (h : (¬ p3016) ∨ (¬ p4256) ∨ (¬ p2510)) : (¬ p2510) ∨ (¬ p3016) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial20371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory9627 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule20371 (meaning t m 2510) (meaning t m 3016) (meaning t m 4256) source

theorem rule20374 (p3670 p4381 p5229 : Prop) (h : (¬ p4381) ∨ (¬ p3670) ∨ (¬ p5229)) : (¬ p3670) ∨ (¬ p4381) ∨ (¬ p5229) := by
  classical
  tauto

theorem initial20374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5229)) := by
  have source := ElevenTheory.theory9630 (m.theta 2 9) (m.theta 7 9) (m.theta 9 10)
  exact rule20374 (meaning t m 3670) (meaning t m 4381) (meaning t m 5229) source

theorem rule20375 (p2177 p3644 p4710 : Prop) (h : (¬ p2177) ∨ (¬ p4710) ∨ (¬ p3644)) : (¬ p2177) ∨ (¬ p3644) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial20375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory9631 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20375 (meaning t m 2177) (meaning t m 3644) (meaning t m 4710) source

theorem rule20376 (p3016 p3742 p3920 : Prop) (h : (¬ p3742) ∨ (¬ p3016) ∨ (¬ p3920)) : (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial20376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory9632 (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule20376 (meaning t m 3016) (meaning t m 3742) (meaning t m 3920) source

theorem rule20377 (p2027 p2156 p2177 p2247 p2274 p4111 p4256 p4438 p4521 : Prop) (h : (¬ p2247) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4521) ∨ (¬ p2177) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p4438) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial20377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory9633 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule20377 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2247) (meaning t m 2274) (meaning t m 4111) (meaning t m 4256) (meaning t m 4438) (meaning t m 4521) source

theorem rule20380 (p2274 p3325 p3989 : Prop) (h : (¬ p3325) ∨ (¬ p2274) ∨ (¬ p3989)) : (¬ p2274) ∨ (¬ p3325) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial20380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory9636 (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20380 (meaning t m 2274) (meaning t m 3325) (meaning t m 3989) source

theorem rule20381 (p2027 p2406 p2476 p3193 p3355 p4608 : Prop) (h : p2027 ∨ (¬ p4608) ∨ (¬ p2476) ∨ (¬ p3193) ∨ (¬ p2406) ∨ (¬ p3355)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2476) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial20381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory9637 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 4 9)
  exact rule20381 (meaning t m 2027) (meaning t m 2406) (meaning t m 2476) (meaning t m 3193) (meaning t m 3355) (meaning t m 4608) source

theorem rule20383 (p2810 p3136 p4700 : Prop) (h : (¬ p4700) ∨ (¬ p2810) ∨ (¬ p3136)) : (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial20383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory9639 (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule20383 (meaning t m 2810) (meaning t m 3136) (meaning t m 4700) source

theorem rule20385 (p2027 p2651 p2745 p2952 p3136 p4111 : Prop) (h : (¬ p4111) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2745) ∨ (¬ p2651) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial20385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory9641 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule20385 (meaning t m 2027) (meaning t m 2651) (meaning t m 2745) (meaning t m 2952) (meaning t m 3136) (meaning t m 4111) source

theorem rule20392 (p3097 p3125 p4025 : Prop) (h : (¬ p3125) ∨ (¬ p3097) ∨ (¬ p4025)) : (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial20392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory9648 (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule20392 (meaning t m 3097) (meaning t m 3125) (meaning t m 4025) source

theorem rule20393 (p3323 p3568 p4025 : Prop) (h : (¬ p4025) ∨ (¬ p3568) ∨ (¬ p3323)) : (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial20393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory9649 (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule20393 (meaning t m 3323) (meaning t m 3568) (meaning t m 4025) source

theorem rule20394 (p2753 p3471 p4379 p5234 : Prop) (h : (¬ p4379) ∨ (¬ p3471) ∨ (¬ p2753) ∨ (¬ p5234)) : (¬ p2753) ∨ (¬ p3471) ∨ (¬ p4379) ∨ (¬ p5234) := by
  classical
  tauto

theorem initial20394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5234)) := by
  have source := ElevenTheory.theory9650 (m.theta 0 2) (m.theta 1 2) (m.theta 2 7) (m.theta 2 9)
  exact rule20394 (meaning t m 2753) (meaning t m 3471) (meaning t m 4379) (meaning t m 5234) source

theorem rule20402 (p2143 p2870 p3646 p4204 : Prop) (h : (¬ p3646) ∨ (¬ p2870) ∨ (¬ p2143) ∨ (¬ p4204)) : (¬ p2143) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial20402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory9658 (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20402 (meaning t m 2143) (meaning t m 2870) (meaning t m 3646) (meaning t m 4204) source

theorem rule20403 (p2027 p2807 p2963 p3097 p3552 p4560 : Prop) (h : (¬ p3552) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2807) ∨ (¬ p4560) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial20403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory9659 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule20403 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3097) (meaning t m 3552) (meaning t m 4560) source

theorem rule20410 (p2797 p3877 p4341 : Prop) (h : (¬ p2797) ∨ (¬ p4341) ∨ (¬ p3877)) : (¬ p2797) ∨ (¬ p3877) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial20410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory9666 (m.theta 2 3) (m.theta 3 6) (m.theta 3 8)
  exact rule20410 (meaning t m 2797) (meaning t m 3877) (meaning t m 4341) source

theorem rule20411 (p2027 p2387 p2668 p2946 p3019 p3983 p4704 : Prop) (h : (¬ p2946) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p2668) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2946) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial20411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory9667 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 6 8)
  exact rule20411 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2946) (meaning t m 3019) (meaning t m 3983) (meaning t m 4704) source

theorem rule20415 (p2992 p4154 p4336 : Prop) (h : (¬ p4154) ∨ (¬ p2992) ∨ (¬ p4336)) : (¬ p2992) ∨ (¬ p4154) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial20415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory9671 (m.theta 1 3) (m.theta 3 5) (m.theta 3 6)
  exact rule20415 (meaning t m 2992) (meaning t m 4154) (meaning t m 4336) source

theorem rule20417 (p2138 p3471 p4136 : Prop) (h : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4136)) : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial20417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory9673 (m.theta 0 2) (m.theta 2 5) (m.theta 2 7)
  exact rule20417 (meaning t m 2138) (meaning t m 3471) (meaning t m 4136) source

theorem rule20425 (p2811 p2946 p4315 : Prop) (h : (¬ p2946) ∨ (¬ p2811) ∨ (¬ p4315)) : (¬ p2811) ∨ (¬ p2946) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial20425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory9681 (m.theta 0 3) (m.theta 2 3) (m.theta 3 5)
  exact rule20425 (meaning t m 2811) (meaning t m 2946) (meaning t m 4315) source

theorem rule20429 (p2027 p2717 p3027 p4360 p4548 p4783 : Prop) (h : (¬ p3027) ∨ (¬ p4783) ∨ p2027 ∨ (¬ p4548) ∨ (¬ p2717) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4783) := by
  classical
  tauto

theorem initial20429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4783)) := by
  have source := ElevenTheory.theory9685 t (m.theta 1 3) (m.theta 2 7) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule20429 (meaning t m 2027) (meaning t m 2717) (meaning t m 3027) (meaning t m 4360) (meaning t m 4548) (meaning t m 4783) source

theorem rule20430 (p2911 p3551 p4279 : Prop) (h : (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4279)) : (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial20430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory9686 (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule20430 (meaning t m 2911) (meaning t m 3551) (meaning t m 4279) source

theorem rule20431 (p2027 p2187 p2230 p2563 p3688 p3822 p3954 p4405 p5190 : Prop) (h : (¬ p3688) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4405) ∨ (¬ p2563) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p3954) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial20431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory9687 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20431 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) (meaning t m 4405) (meaning t m 5190) source

theorem rule20433 (p3189 p4154 p4196 : Prop) (h : (¬ p4154) ∨ (¬ p3189) ∨ (¬ p4196)) : (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial20433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory9689 (m.theta 1 3) (m.theta 3 6) (m.theta 3 8)
  exact rule20433 (meaning t m 3189) (meaning t m 4154) (meaning t m 4196) source

theorem rule20436 (p2850 p3741 p3876 : Prop) (h : (¬ p2850) ∨ (¬ p3876) ∨ (¬ p3741)) : (¬ p2850) ∨ (¬ p3741) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial20436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory9692 (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule20436 (meaning t m 2850) (meaning t m 3741) (meaning t m 3876) source

theorem rule20439 (p2027 p2156 p2247 p3125 p3461 p3892 p4111 p4521 p5133 : Prop) (h : (¬ p4521) ∨ (¬ p4111) ∨ (¬ p3125) ∨ (¬ p2247) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p3892) ∨ (¬ p2156) ∨ (¬ p5133)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5133) := by
  classical
  tauto

theorem initial20439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3892)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5133)) := by
  have source := ElevenTheory.theory9695 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 10) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule20439 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 3125) (meaning t m 3461) (meaning t m 3892) (meaning t m 4111) (meaning t m 4521) (meaning t m 5133) source

theorem rule20440 (p2027 p2156 p2247 p3125 p3461 p3892 p4111 p4521 p5127 : Prop) (h : (¬ p4521) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3892) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p2156) ∨ (¬ p5127)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5127) := by
  classical
  tauto

theorem initial20440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3892)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5127)) := by
  have source := ElevenTheory.theory9696 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 10) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule20440 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 3125) (meaning t m 3461) (meaning t m 3892) (meaning t m 4111) (meaning t m 4521) (meaning t m 5127) source

theorem rule20441 (p3483 p4137 p4342 : Prop) (h : (¬ p3483) ∨ (¬ p4342) ∨ (¬ p4137)) : (¬ p3483) ∨ (¬ p4137) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial20441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory9697 (m.theta 2 6) (m.theta 4 6) (m.theta 6 9)
  exact rule20441 (meaning t m 3483) (meaning t m 4137) (meaning t m 4342) source

theorem rule20443 (p2441 p3201 p3684 : Prop) (h : (¬ p3201) ∨ (¬ p3684) ∨ (¬ p2441)) : (¬ p2441) ∨ (¬ p3201) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial20443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory9699 (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule20443 (meaning t m 2441) (meaning t m 3201) (meaning t m 3684) source

theorem rule20446 (p2027 p2177 p2507 p3309 p3581 p3644 : Prop) (h : (¬ p2177) ∨ (¬ p3581) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2507) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2507) ∨ (¬ p3309) ∨ (¬ p3581) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial20446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory9702 t (m.theta 1 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20446 (meaning t m 2027) (meaning t m 2177) (meaning t m 2507) (meaning t m 3309) (meaning t m 3581) (meaning t m 3644) source

theorem rule20447 (p2027 p3051 p3549 p3591 p4140 p4399 p5190 : Prop) (h : (¬ p4140) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p4399) ∨ (¬ p3591) ∨ (¬ p3051) ∨ (¬ p3549)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4140) ∨ (¬ p4399) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial20447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory9703 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 6) (m.theta 5 7) (m.theta 6 7)
  exact rule20447 (meaning t m 2027) (meaning t m 3051) (meaning t m 3549) (meaning t m 3591) (meaning t m 4140) (meaning t m 4399) (meaning t m 5190) source

theorem rule20451 (p2870 p3758 p4204 : Prop) (h : (¬ p2870) ∨ (¬ p3758) ∨ (¬ p4204)) : (¬ p2870) ∨ (¬ p3758) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial20451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory9707 (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20451 (meaning t m 2870) (meaning t m 3758) (meaning t m 4204) source

theorem rule20452 (p3449 p3591 p4371 : Prop) (h : (¬ p3591) ∨ (¬ p3449) ∨ (¬ p4371)) : (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial20452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory9708 (m.theta 0 1) (m.theta 1 6) (m.theta 1 8)
  exact rule20452 (meaning t m 3449) (meaning t m 3591) (meaning t m 4371) source

theorem rule20453 (p2590 p3422 p3684 : Prop) (h : (¬ p2590) ∨ (¬ p3684) ∨ (¬ p3422)) : (¬ p2590) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial20453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory9709 (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule20453 (meaning t m 2590) (meaning t m 3422) (meaning t m 3684) source

theorem rule20454 (p2630 p3572 p3580 : Prop) (h : (¬ p3572) ∨ (¬ p2630) ∨ (¬ p3580)) : (¬ p2630) ∨ (¬ p3572) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial20454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory9710 (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule20454 (meaning t m 2630) (meaning t m 3572) (meaning t m 3580) source

theorem rule20456 (p2187 p3097 p3955 : Prop) (h : (¬ p3097) ∨ (¬ p3955) ∨ (¬ p2187)) : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial20456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory9712 (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20456 (meaning t m 2187) (meaning t m 3097) (meaning t m 3955) source

theorem rule20457 (p3136 p3877 p4237 : Prop) (h : (¬ p3877) ∨ (¬ p3136) ∨ (¬ p4237)) : (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial20457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory9713 (m.theta 2 3) (m.theta 3 5) (m.theta 3 8)
  exact rule20457 (meaning t m 3136) (meaning t m 3877) (meaning t m 4237) source

theorem rule20458 (p2027 p2145 p2299 p2630 p2696 p3083 p3097 p3646 p4420 : Prop) (h : (¬ p2630) ∨ (¬ p4420) ∨ (¬ p2145) ∨ (¬ p3083) ∨ (¬ p3646) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial20458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory9714 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule20458 (meaning t m 2027) (meaning t m 2145) (meaning t m 2299) (meaning t m 2630) (meaning t m 2696) (meaning t m 3083) (meaning t m 3097) (meaning t m 3646) (meaning t m 4420) source

theorem rule20459 (p2810 p3755 p5170 : Prop) (h : (¬ p2810) ∨ (¬ p3755) ∨ (¬ p5170)) : (¬ p2810) ∨ (¬ p3755) ∨ (¬ p5170) := by
  classical
  tauto

theorem initial20459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 5170)) := by
  have source := ElevenTheory.theory9715 (m.theta 2 3) (m.theta 3 4) (m.theta 3 9)
  exact rule20459 (meaning t m 2810) (meaning t m 3755) (meaning t m 5170) source

theorem rule20461 (p2027 p2284 p2954 p3125 p3946 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p2954) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p2284) ∨ (¬ p3946)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2954) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial20461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory9717 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9)
  exact rule20461 (meaning t m 2027) (meaning t m 2284) (meaning t m 2954) (meaning t m 3125) (meaning t m 3946) (meaning t m 4198) source

theorem rule20462 (p2901 p3497 p3747 : Prop) (h : (¬ p3497) ∨ (¬ p2901) ∨ (¬ p3747)) : (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial20462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory9718 (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule20462 (meaning t m 2901) (meaning t m 3497) (meaning t m 3747) source

theorem rule20464 (p3156 p4119 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p3156) ∨ (¬ p4119)) : (¬ p3156) ∨ (¬ p4119) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial20464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory9720 (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule20464 (meaning t m 3156) (meaning t m 4119) (meaning t m 4320) source

theorem rule20465 (p2027 p2373 p2850 p3876 p4001 p4904 : Prop) (h : (¬ p2850) ∨ (¬ p3876) ∨ (¬ p4001) ∨ p2027 ∨ (¬ p4904) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial20465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory9721 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8)
  exact rule20465 (meaning t m 2027) (meaning t m 2373) (meaning t m 2850) (meaning t m 3876) (meaning t m 4001) (meaning t m 4904) source

theorem rule20466 (p2027 p2901 p3549 p3952 p4140 p4514 : Prop) (h : p2027 ∨ (¬ p3549) ∨ (¬ p2901) ∨ (¬ p4514) ∨ (¬ p4140) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3549) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial20466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory9722 t (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule20466 (meaning t m 2027) (meaning t m 2901) (meaning t m 3549) (meaning t m 3952) (meaning t m 4140) (meaning t m 4514) source

theorem rule20467 (p3641 p3684 p4607 : Prop) (h : (¬ p4607) ∨ (¬ p3684) ∨ (¬ p3641)) : (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial20467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory9723 (m.theta 2 4) (m.theta 4 5) (m.theta 4 8)
  exact rule20467 (meaning t m 3641) (meaning t m 3684) (meaning t m 4607) source

theorem rule20468 (p2542 p3359 p4449 : Prop) (h : (¬ p3359) ∨ (¬ p2542) ∨ (¬ p4449)) : (¬ p2542) ∨ (¬ p3359) ∨ (¬ p4449) := by
  classical
  tauto

theorem initial20468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4449)) := by
  have source := ElevenTheory.theory9724 (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule20468 (meaning t m 2542) (meaning t m 3359) (meaning t m 4449) source

theorem rule20469 (p3005 p3572 p3919 : Prop) (h : (¬ p3572) ∨ (¬ p3005) ∨ (¬ p3919)) : (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3919) := by
  classical
  tauto

theorem initial20469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3919)) := by
  have source := ElevenTheory.theory9725 (m.theta 2 3) (m.theta 3 7) (m.theta 3 8)
  exact rule20469 (meaning t m 3005) (meaning t m 3572) (meaning t m 3919) source

theorem rule20470 (p2027 p2934 p3238 p3527 p3644 p4646 : Prop) (h : p2027 ∨ (¬ p4646) ∨ (¬ p3644) ∨ (¬ p3238) ∨ (¬ p2934) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial20470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory9726 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule20470 (meaning t m 2027) (meaning t m 2934) (meaning t m 3238) (meaning t m 3527) (meaning t m 3644) (meaning t m 4646) source

theorem rule20471 (p2630 p3877 p4121 : Prop) (h : (¬ p2630) ∨ (¬ p3877) ∨ (¬ p4121)) : (¬ p2630) ∨ (¬ p3877) ∨ (¬ p4121) := by
  classical
  tauto

theorem initial20471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4121)) := by
  have source := ElevenTheory.theory9727 (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule20471 (meaning t m 2630) (meaning t m 3877) (meaning t m 4121) source

theorem rule20472 (p2027 p2662 p2685 p2810 p3238 p3519 p3579 p4646 : Prop) (h : (¬ p3519) ∨ (¬ p3238) ∨ (¬ p2685) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3579)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3519) ∨ (¬ p3579) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial20472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory9728 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule20472 (meaning t m 2027) (meaning t m 2662) (meaning t m 2685) (meaning t m 2810) (meaning t m 3238) (meaning t m 3519) (meaning t m 3579) (meaning t m 4646) source

theorem rule20475 (p2027 p3609 p3857 p3988 p4110 p4115 p4744 p4885 : Prop) (h : (¬ p3609) ∨ (¬ p4115) ∨ (¬ p4885) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p3988) ∨ (¬ p4110) ∨ (¬ p4744)) : (p2027) ∨ (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3988) ∨ (¬ p4110) ∨ (¬ p4115) ∨ (¬ p4744) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial20475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory9731 t (m.theta 0 8) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule20475 (meaning t m 2027) (meaning t m 3609) (meaning t m 3857) (meaning t m 3988) (meaning t m 4110) (meaning t m 4115) (meaning t m 4744) (meaning t m 4885) source

theorem rule20476 (p3609 p4347 p4857 : Prop) (h : (¬ p4347) ∨ (¬ p3609) ∨ (¬ p4857)) : (¬ p3609) ∨ (¬ p4347) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial20476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory9732 (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule20476 (meaning t m 3609) (meaning t m 4347) (meaning t m 4857) source

theorem rule20482 (p2027 p2427 p2850 p2957 p3556 p4700 p4753 : Prop) (h : (¬ p3556) ∨ (¬ p4700) ∨ (¬ p2957) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4700) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial20482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory9738 t (m.theta 0 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20482 (meaning t m 2027) (meaning t m 2427) (meaning t m 2850) (meaning t m 2957) (meaning t m 3556) (meaning t m 4700) (meaning t m 4753) source

theorem rule20485 (p2027 p2373 p2992 p4312 p4360 p4702 : Prop) (h : (¬ p4702) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p2992) ∨ (¬ p4360) ∨ (¬ p4312)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2992) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial20485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory9741 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule20485 (meaning t m 2027) (meaning t m 2373) (meaning t m 2992) (meaning t m 4312) (meaning t m 4360) (meaning t m 4702) source

theorem rule20486 (p2027 p2860 p3212 p3646 p4244 p5104 : Prop) (h : (¬ p3646) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p5104) ∨ (¬ p4244) ∨ (¬ p3212)) : (p2027) ∨ (¬ p2860) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p5104) := by
  classical
  tauto

theorem initial20486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5104)) := by
  have source := ElevenTheory.theory9742 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule20486 (meaning t m 2027) (meaning t m 2860) (meaning t m 3212) (meaning t m 3646) (meaning t m 4244) (meaning t m 5104) source

theorem rule20488 (p2137 p3051 p3698 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3698)) : (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3698) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial20488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory9744 (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule20488 (meaning t m 2137) (meaning t m 3051) (meaning t m 3698) (meaning t m 4235) source

theorem rule20489 (p2027 p2295 p3097 p4110 p4336 p4705 : Prop) (h : (¬ p4336) ∨ (¬ p2295) ∨ (¬ p3097) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p4110)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial20489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory9745 t (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule20489 (meaning t m 2027) (meaning t m 2295) (meaning t m 3097) (meaning t m 4110) (meaning t m 4336) (meaning t m 4705) source

theorem rule20494 (p2819 p3324 p4337 : Prop) (h : (¬ p4337) ∨ (¬ p3324) ∨ (¬ p2819)) : (¬ p2819) ∨ (¬ p3324) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial20494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory9750 (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule20494 (meaning t m 2819) (meaning t m 3324) (meaning t m 4337) source

theorem rule20497 (p2563 p3872 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p2563) ∨ (¬ p3872)) : (¬ p2563) ∨ (¬ p3872) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial20497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory9753 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20497 (meaning t m 2563) (meaning t m 3872) (meaning t m 4235) source

theorem rule20499 (p2608 p3860 p5316 : Prop) (h : (¬ p3860) ∨ (¬ p2608) ∨ (¬ p5316)) : (¬ p2608) ∨ (¬ p3860) ∨ (¬ p5316) := by
  classical
  tauto

theorem initial20499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5316)) := by
  have source := ElevenTheory.theory9755 (m.theta 0 1) (m.theta 1 2) (m.theta 1 8)
  exact rule20499 (meaning t m 2608) (meaning t m 3860) (meaning t m 5316) source

theorem rule20502 (p3256 p4348 p4548 : Prop) (h : (¬ p3256) ∨ (¬ p4348) ∨ (¬ p4548)) : (¬ p3256) ∨ (¬ p4348) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial20502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory9758 (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20502 (meaning t m 3256) (meaning t m 4348) (meaning t m 4548) source

theorem rule20503 (p3146 p4132 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3146) ∨ (¬ p4132)) : (¬ p3146) ∨ (¬ p4132) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial20503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory9759 (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20503 (meaning t m 3146) (meaning t m 4132) (meaning t m 4348) source

theorem rule20510 (p2027 p2417 p2598 p2668 p2753 p3201 p3923 p4037 p4625 p4870 : Prop) (h : (¬ p2668) ∨ (¬ p4870) ∨ (¬ p2417) ∨ (¬ p2753) ∨ (¬ p3923) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p4037)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2668) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3923) ∨ (¬ p4037) ∨ (¬ p4625) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial20510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory9766 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule20510 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 2668) (meaning t m 2753) (meaning t m 3201) (meaning t m 3923) (meaning t m 4037) (meaning t m 4625) (meaning t m 4870) source

theorem rule20513 (p2027 p2341 p3370 p3570 p4235 p4632 p4988 : Prop) (h : (¬ p4632) ∨ (¬ p4988) ∨ (¬ p3570) ∨ (¬ p2341) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p4235)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3370) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4632) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial20513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4632)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory9769 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule20513 (meaning t m 2027) (meaning t m 2341) (meaning t m 3370) (meaning t m 3570) (meaning t m 4235) (meaning t m 4632) (meaning t m 4988) source

theorem rule20517 (p2027 p3399 p3555 p3571 p4235 p4632 : Prop) (h : (¬ p3555) ∨ p2027 ∨ (¬ p4632) ∨ (¬ p3571) ∨ (¬ p4235) ∨ (¬ p3399)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4235) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial20517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory9773 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7)
  exact rule20517 (meaning t m 2027) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) (meaning t m 4235) (meaning t m 4632) source

theorem rule20518 (p3680 p4033 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p3680) ∨ (¬ p4033)) : (¬ p3680) ∨ (¬ p4033) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial20518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory9774 (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule20518 (meaning t m 3680) (meaning t m 4033) (meaning t m 4191) source

theorem rule20521 (p2860 p3952 p4316 : Prop) (h : (¬ p4316) ∨ (¬ p3952) ∨ (¬ p2860)) : (¬ p2860) ∨ (¬ p3952) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial20521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory9777 (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule20521 (meaning t m 2860) (meaning t m 3952) (meaning t m 4316) source

theorem rule20525 (p3201 p3363 p3540 : Prop) (h : (¬ p3540) ∨ (¬ p3363) ∨ (¬ p3201)) : (¬ p3201) ∨ (¬ p3363) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial20525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory9781 (m.theta 0 4) (m.theta 2 4) (m.theta 4 7)
  exact rule20525 (meaning t m 3201) (meaning t m 3363) (meaning t m 3540) source

theorem rule20526 (p2027 p2656 p3355 p4256 p4347 p4384 p4695 : Prop) (h : (¬ p3355) ∨ (¬ p4695) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2656) ∨ (¬ p3355) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial20526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory9782 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule20526 (meaning t m 2027) (meaning t m 2656) (meaning t m 3355) (meaning t m 4256) (meaning t m 4347) (meaning t m 4384) (meaning t m 4695) source

theorem rule20527 (p2027 p2144 p2156 p2190 p2657 p3146 p3644 p3742 p4133 p4347 p4789 : Prop) (h : (¬ p4789) ∨ (¬ p3742) ∨ (¬ p2156) ∨ (¬ p4133) ∨ (¬ p3644) ∨ (¬ p2657) ∨ (¬ p4347) ∨ (¬ p3146) ∨ (¬ p2144) ∨ p2027 ∨ (¬ p2190)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial20527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory9783 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20527 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2190) (meaning t m 2657) (meaning t m 3146) (meaning t m 3644) (meaning t m 3742) (meaning t m 4133) (meaning t m 4347) (meaning t m 4789) source

theorem rule20528 (p2143 p2619 p4120 : Prop) (h : (¬ p2143) ∨ (¬ p2619) ∨ (¬ p4120)) : (¬ p2143) ∨ (¬ p2619) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial20528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory9784 (m.theta 0 5) (m.theta 2 5) (m.theta 5 8)
  exact rule20528 (meaning t m 2143) (meaning t m 2619) (meaning t m 4120) source

theorem rule20529 (p2027 p3343 p4133 p4256 p4347 p4383 p4695 : Prop) (h : p2027 ∨ (¬ p4133) ∨ (¬ p4383) ∨ (¬ p4347) ∨ (¬ p4695) ∨ (¬ p4256) ∨ (¬ p3343)) : (p2027) ∨ (¬ p3343) ∨ (¬ p4133) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4383) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial20529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory9785 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20529 (meaning t m 2027) (meaning t m 3343) (meaning t m 4133) (meaning t m 4256) (meaning t m 4347) (meaning t m 4383) (meaning t m 4695) source

theorem rule20530 (p2122 p3325 p4358 : Prop) (h : (¬ p2122) ∨ (¬ p4358) ∨ (¬ p3325)) : (¬ p2122) ∨ (¬ p3325) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial20530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory9786 (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20530 (meaning t m 2122) (meaning t m 3325) (meaning t m 4358) source

theorem rule20532 (p2027 p3246 p3570 p4133 p4347 p4443 : Prop) (h : (¬ p4133) ∨ (¬ p4347) ∨ (¬ p3570) ∨ (¬ p4443) ∨ p2027 ∨ (¬ p3246)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial20532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory9788 t (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule20532 (meaning t m 2027) (meaning t m 3246) (meaning t m 3570) (meaning t m 4133) (meaning t m 4347) (meaning t m 4443) source

theorem rule20534 (p2027 p2928 p3389 p3402 p3591 p4079 p4756 : Prop) (h : (¬ p4756) ∨ p2027 ∨ (¬ p3402) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p2928) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756) := by
  classical
  tauto

theorem initial20534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4756)) := by
  have source := ElevenTheory.theory9790 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7)
  exact rule20534 (meaning t m 2027) (meaning t m 2928) (meaning t m 3389) (meaning t m 3402) (meaning t m 3591) (meaning t m 4079) (meaning t m 4756) source

theorem rule20535 (p2518 p2928 p4186 : Prop) (h : (¬ p4186) ∨ (¬ p2928) ∨ (¬ p2518)) : (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial20535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory9791 (m.theta 1 4) (m.theta 4 7) (m.theta 4 8)
  exact rule20535 (meaning t m 2518) (meaning t m 2928) (meaning t m 4186) source

theorem rule20539 (p3055 p3619 p5158 : Prop) (h : (¬ p3619) ∨ (¬ p3055) ∨ (¬ p5158)) : (¬ p3055) ∨ (¬ p3619) ∨ (¬ p5158) := by
  classical
  tauto

theorem initial20539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 5158)) := by
  have source := ElevenTheory.theory9795 (m.theta 0 2) (m.theta 2 4) (m.theta 2 9)
  exact rule20539 (meaning t m 3055) (meaning t m 3619) (meaning t m 5158) source

theorem rule20540 (p3343 p3742 p4635 : Prop) (h : (¬ p3742) ∨ (¬ p3343) ∨ (¬ p4635)) : (¬ p3343) ∨ (¬ p3742) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial20540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory9796 (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule20540 (meaning t m 3343) (meaning t m 3742) (meaning t m 4635) source

theorem rule20541 (p2027 p2307 p2352 p2387 p3822 p5222 : Prop) (h : (¬ p5222) ∨ (¬ p2352) ∨ (¬ p2307) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p3822)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3822) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial20541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory9797 t (m.theta 0 6) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20541 (meaning t m 2027) (meaning t m 2307) (meaning t m 2352) (meaning t m 2387) (meaning t m 3822) (meaning t m 5222) source

theorem rule20542 (p2191 p2619 p4243 : Prop) (h : (¬ p2619) ∨ (¬ p4243) ∨ (¬ p2191)) : (¬ p2191) ∨ (¬ p2619) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial20542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory9798 (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule20542 (meaning t m 2191) (meaning t m 2619) (meaning t m 4243) source

theorem rule20551 (p2542 p4256 p4355 : Prop) (h : (¬ p2542) ∨ (¬ p4256) ∨ (¬ p4355)) : (¬ p2542) ∨ (¬ p4256) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial20551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory9807 (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule20551 (meaning t m 2542) (meaning t m 4256) (meaning t m 4355) source

theorem rule20553 (p2027 p2352 p2363 p2493 p2608 p3555 p4363 p4376 p5059 : Prop) (h : p2027 ∨ (¬ p2493) ∨ (¬ p2363) ∨ (¬ p3555) ∨ (¬ p2608) ∨ (¬ p2352) ∨ (¬ p5059) ∨ (¬ p4376) ∨ (¬ p4363)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2493) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p4376) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial20553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory9809 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule20553 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2493) (meaning t m 2608) (meaning t m 3555) (meaning t m 4363) (meaning t m 4376) (meaning t m 5059) source

theorem rule20554 (p2027 p2952 p3204 p3309 p3568 p3987 p4566 : Prop) (h : (¬ p4566) ∨ (¬ p3568) ∨ (¬ p3204) ∨ (¬ p2952) ∨ (¬ p3987) ∨ p2027 ∨ (¬ p3309)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4566) := by
  classical
  tauto

theorem initial20554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4566)) := by
  have source := ElevenTheory.theory9810 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule20554 (meaning t m 2027) (meaning t m 2952) (meaning t m 3204) (meaning t m 3309) (meaning t m 3568) (meaning t m 3987) (meaning t m 4566) source

theorem rule20555 (p2870 p3486 p4243 : Prop) (h : (¬ p4243) ∨ (¬ p2870) ∨ (¬ p3486)) : (¬ p2870) ∨ (¬ p3486) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial20555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory9811 (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule20555 (meaning t m 2870) (meaning t m 3486) (meaning t m 4243) source

theorem rule20556 (p2870 p4173 p4204 p4243 : Prop) (h : (¬ p4243) ∨ (¬ p4173) ∨ (¬ p2870) ∨ (¬ p4204)) : (¬ p2870) ∨ (¬ p4173) ∨ (¬ p4204) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial20556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory9812 (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20556 (meaning t m 2870) (meaning t m 4173) (meaning t m 4204) (meaning t m 4243) source

theorem rule20561 (p2027 p2138 p2598 p3641 p3698 p4610 : Prop) (h : p2027 ∨ (¬ p3698) ∨ (¬ p2138) ∨ (¬ p4610) ∨ (¬ p2598) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3698) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial20561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory9817 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 8)
  exact rule20561 (meaning t m 2027) (meaning t m 2138) (meaning t m 2598) (meaning t m 3641) (meaning t m 3698) (meaning t m 4610) source

theorem rule20562 (p2284 p3872 p4320 : Prop) (h : (¬ p2284) ∨ (¬ p4320) ∨ (¬ p3872)) : (¬ p2284) ∨ (¬ p3872) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial20562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory9818 (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20562 (meaning t m 2284) (meaning t m 3872) (meaning t m 4320) source

theorem rule20566 (p2027 p2331 p2668 p3055 p3979 p4425 p4786 p5119 p5160 : Prop) (h : p2027 ∨ (¬ p2668) ∨ (¬ p5160) ∨ (¬ p4425) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3979) ∨ (¬ p4786) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial20566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory9822 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule20566 (meaning t m 2027) (meaning t m 2331) (meaning t m 2668) (meaning t m 3055) (meaning t m 3979) (meaning t m 4425) (meaning t m 4786) (meaning t m 5119) (meaning t m 5160) source

theorem rule20568 (p2850 p3874 p4355 : Prop) (h : (¬ p3874) ∨ (¬ p2850) ∨ (¬ p4355)) : (¬ p2850) ∨ (¬ p3874) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial20568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory9824 (m.theta 2 4) (m.theta 4 5) (m.theta 4 8)
  exact rule20568 (meaning t m 2850) (meaning t m 3874) (meaning t m 4355) source

theorem rule20570 (p2138 p3366 p3537 p4359 : Prop) (h : (¬ p4359) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p3537)) : (¬ p2138) ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial20570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory9826 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8)
  exact rule20570 (meaning t m 2138) (meaning t m 3366) (meaning t m 3537) (meaning t m 4359) source

theorem rule20571 (p3083 p3742 p4186 : Prop) (h : (¬ p3742) ∨ (¬ p3083) ∨ (¬ p4186)) : (¬ p3083) ∨ (¬ p3742) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial20571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory9827 (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule20571 (meaning t m 3083) (meaning t m 3742) (meaning t m 4186) source

theorem rule20572 (p2027 p2307 p2387 p2588 p2819 p5225 : Prop) (h : (¬ p2819) ∨ (¬ p5225) ∨ (¬ p2588) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2819) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial20572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory9828 t (m.theta 0 6) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20572 (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2588) (meaning t m 2819) (meaning t m 5225) source

theorem rule20574 (p2191 p3156 p4282 : Prop) (h : (¬ p4282) ∨ (¬ p2191) ∨ (¬ p3156)) : (¬ p2191) ∨ (¬ p3156) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial20574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory9830 (m.theta 1 5) (m.theta 3 5) (m.theta 5 8)
  exact rule20574 (meaning t m 2191) (meaning t m 3156) (meaning t m 4282) source

theorem rule20578 (p2246 p2742 p2946 p4315 : Prop) (h : (¬ p2742) ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p4315)) : (¬ p2246) ∨ (¬ p2742) ∨ (¬ p2946) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial20578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory9834 (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule20578 (meaning t m 2246) (meaning t m 2742) (meaning t m 2946) (meaning t m 4315) source

theorem rule20580 (p2027 p2230 p2440 p3083 p3588 p3659 p3954 p4420 p5190 : Prop) (h : (¬ p2440) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3659) ∨ (¬ p5190) ∨ (¬ p4420) ∨ (¬ p3588) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4420) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial20580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory9836 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8)
  exact rule20580 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 3083) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4420) (meaning t m 5190) source

theorem rule20583 (p3115 p4320 p4402 : Prop) (h : (¬ p4320) ∨ (¬ p4402) ∨ (¬ p3115)) : (¬ p3115) ∨ (¬ p4320) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial20583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory9839 (m.theta 3 5) (m.theta 5 7) (m.theta 5 9)
  exact rule20583 (meaning t m 3115) (meaning t m 4320) (meaning t m 4402) source

theorem rule20586 (p2027 p2156 p2901 p3952 p4032 p5102 : Prop) (h : p2027 ∨ (¬ p5102) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4032) ∨ (¬ p5102) := by
  classical
  tauto

theorem initial20586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 5102)) := by
  have source := ElevenTheory.theory9842 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule20586 (meaning t m 2027) (meaning t m 2156) (meaning t m 2901) (meaning t m 3952) (meaning t m 4032) (meaning t m 5102) source

theorem rule20587 (p2027 p2156 p2901 p3370 p3952 p4363 p5102 : Prop) (h : (¬ p5102) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2156) ∨ (¬ p3370) ∨ (¬ p3952) ∨ (¬ p4363)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3370) ∨ (¬ p3952) ∨ (¬ p4363) ∨ (¬ p5102) := by
  classical
  tauto

theorem initial20587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5102)) := by
  have source := ElevenTheory.theory9843 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule20587 (meaning t m 2027) (meaning t m 2156) (meaning t m 2901) (meaning t m 3370) (meaning t m 3952) (meaning t m 4363) (meaning t m 5102) source

theorem rule20591 (p2027 p3692 p3830 p3860 p4352 p4498 : Prop) (h : (¬ p3860) ∨ (¬ p4352) ∨ (¬ p3692) ∨ (¬ p4498) ∨ p2027 ∨ (¬ p3830)) : (p2027) ∨ (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4498) := by
  classical
  tauto

theorem initial20591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4352)) ∨ (¬ (meaning t m 4498)) := by
  have source := ElevenTheory.theory9847 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 5 8) (m.theta 8 9)
  exact rule20591 (meaning t m 2027) (meaning t m 3692) (meaning t m 3830) (meaning t m 3860) (meaning t m 4352) (meaning t m 4498) source

theorem rule20593 (p2027 p3063 p3093 p3834 p3945 p4133 p5358 : Prop) (h : (¬ p3945) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p4133) ∨ (¬ p5358) ∨ (¬ p3063) ∨ (¬ p3834)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial20593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory9849 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule20593 (meaning t m 2027) (meaning t m 3063) (meaning t m 3093) (meaning t m 3834) (meaning t m 3945) (meaning t m 4133) (meaning t m 5358) source

theorem rule20595 (p3125 p3690 p4204 p4623 : Prop) (h : (¬ p4204) ∨ (¬ p3125) ∨ (¬ p3690) ∨ (¬ p4623)) : (¬ p3125) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial20595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory9851 (m.theta 5 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule20595 (meaning t m 3125) (meaning t m 3690) (meaning t m 4204) (meaning t m 4623) source

theorem rule20596 (p3125 p4137 p4203 : Prop) (h : (¬ p3125) ∨ (¬ p4203) ∨ (¬ p4137)) : (¬ p3125) ∨ (¬ p4137) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial20596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory9852 (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule20596 (meaning t m 3125) (meaning t m 4137) (meaning t m 4203) source

theorem rule20601 (p2264 p3945 p3947 : Prop) (h : (¬ p2264) ∨ (¬ p3945) ∨ (¬ p3947)) : (¬ p2264) ∨ (¬ p3945) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial20601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory9857 (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule20601 (meaning t m 2264) (meaning t m 3945) (meaning t m 3947) source

theorem rule20602 (p3343 p3683 p5160 : Prop) (h : (¬ p3683) ∨ (¬ p5160) ∨ (¬ p3343)) : (¬ p3343) ∨ (¬ p3683) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial20602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory9858 (m.theta 2 4) (m.theta 3 4) (m.theta 4 9)
  exact rule20602 (meaning t m 3343) (meaning t m 3683) (meaning t m 5160) source

theorem rule20603 (p2098 p2753 p3588 p3685 : Prop) (h : (¬ p3588) ∨ (¬ p2098) ∨ (¬ p2753) ∨ (¬ p3685)) : (¬ p2098) ∨ (¬ p2753) ∨ (¬ p3588) ∨ (¬ p3685) := by
  classical
  tauto

theorem initial20603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3685)) := by
  have source := ElevenTheory.theory9859 (m.theta 0 2) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8)
  exact rule20603 (meaning t m 2098) (meaning t m 2753) (meaning t m 3588) (meaning t m 3685) source

theorem rule20607 (p2027 p2542 p3051 p3486 p4109 p4202 p4811 : Prop) (h : (¬ p4202) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p4109) ∨ (¬ p3051) ∨ (¬ p2542) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial20607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory9863 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule20607 (meaning t m 2027) (meaning t m 2542) (meaning t m 3051) (meaning t m 3486) (meaning t m 4109) (meaning t m 4202) (meaning t m 4811) source

theorem rule20613 (p2668 p3568 p3955 : Prop) (h : (¬ p3568) ∨ (¬ p2668) ∨ (¬ p3955)) : (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial20613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory9869 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule20613 (meaning t m 2668) (meaning t m 3568) (meaning t m 3955) source

theorem rule20615 (p3156 p3952 p3988 : Prop) (h : (¬ p3952) ∨ (¬ p3156) ∨ (¬ p3988)) : (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial20615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory9871 (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule20615 (meaning t m 3156) (meaning t m 3952) (meaning t m 3988) source

theorem rule20616 (p2027 p2589 p2850 p3471 p3905 p5086 : Prop) (h : (¬ p3905) ∨ (¬ p2850) ∨ (¬ p2589) ∨ (¬ p5086) ∨ p2027 ∨ (¬ p3471)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3471) ∨ (¬ p3905) ∨ (¬ p5086) := by
  classical
  tauto

theorem initial20616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 5086)) := by
  have source := ElevenTheory.theory9872 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5)
  exact rule20616 (meaning t m 2027) (meaning t m 2589) (meaning t m 2850) (meaning t m 3471) (meaning t m 3905) (meaning t m 5086) source

theorem rule20622 (p2717 p3644 p4106 : Prop) (h : (¬ p3644) ∨ (¬ p4106) ∨ (¬ p2717)) : (¬ p2717) ∨ (¬ p3644) ∨ (¬ p4106) := by
  classical
  tauto

theorem initial20622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4106)) := by
  have source := ElevenTheory.theory9878 (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule20622 (meaning t m 2717) (meaning t m 3644) (meaning t m 4106) source

theorem rule20624 (p2027 p2187 p2230 p2247 p2563 p2996 p3553 p4133 p5190 : Prop) (h : (¬ p3553) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p2247) ∨ (¬ p2187) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial20624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory9880 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule20624 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2247) (meaning t m 2563) (meaning t m 2996) (meaning t m 3553) (meaning t m 4133) (meaning t m 5190) source

theorem rule20629 (p2589 p3366 p3371 p3905 p4210 : Prop) (h : (¬ p2589) ∨ (¬ p3905) ∨ (¬ p4210) ∨ (¬ p3366) ∨ (¬ p3371)) : (¬ p2589) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3905) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial20629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory9885 (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 4 5)
  exact rule20629 (meaning t m 2589) (meaning t m 3366) (meaning t m 3371) (meaning t m 3905) (meaning t m 4210) source

theorem rule20630 (p2027 p2383 p2781 p3292 p3564 p3680 p3956 p4236 p4368 p5284 : Prop) (h : (¬ p4368) ∨ (¬ p3680) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2781) ∨ (¬ p4236) ∨ (¬ p3292) ∨ (¬ p2383) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3292) ∨ (¬ p3564) ∨ (¬ p3680) ∨ (¬ p3956) ∨ (¬ p4236) ∨ (¬ p4368) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial20630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory9886 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 3 9) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule20630 (meaning t m 2027) (meaning t m 2383) (meaning t m 2781) (meaning t m 3292) (meaning t m 3564) (meaning t m 3680) (meaning t m 3956) (meaning t m 4236) (meaning t m 4368) (meaning t m 5284) source

theorem rule20634 (p2870 p4192 p4385 : Prop) (h : (¬ p4385) ∨ (¬ p2870) ∨ (¬ p4192)) : (¬ p2870) ∨ (¬ p4192) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial20634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory9890 (m.theta 2 5) (m.theta 5 7) (m.theta 5 9)
  exact rule20634 (meaning t m 2870) (meaning t m 4192) (meaning t m 4385) source

theorem rule20637 (p2295 p3325 p3990 p4037 : Prop) (h : (¬ p2295) ∨ (¬ p4037) ∨ (¬ p3990) ∨ (¬ p3325)) : (¬ p2295) ∨ (¬ p3325) ∨ (¬ p3990) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial20637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory9893 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule20637 (meaning t m 2295) (meaning t m 3325) (meaning t m 3990) (meaning t m 4037) source

theorem rule20640 (p2027 p2138 p2331 p3506 p3694 p4191 p4200 p4330 p4421 p4786 p5568 : Prop) (h : (¬ p2138) ∨ (¬ p4786) ∨ (¬ p3694) ∨ (¬ p3506) ∨ (¬ p4421) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4200)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3694) ∨ (¬ p4191) ∨ (¬ p4200) ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial20640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4200)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory9896 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 9) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule20640 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 3506) (meaning t m 3694) (meaning t m 4191) (meaning t m 4200) (meaning t m 4330) (meaning t m 4421) (meaning t m 4786) (meaning t m 5568) source

theorem rule20641 (p2027 p2138 p2331 p3506 p3694 p4421 p4786 p5117 p5568 : Prop) (h : (¬ p2138) ∨ (¬ p4786) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p3506) ∨ (¬ p2331) ∨ (¬ p4421) ∨ (¬ p5117)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3694) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5117) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial20641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5117)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory9897 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 6) (m.theta 3 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule20641 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 3506) (meaning t m 3694) (meaning t m 4421) (meaning t m 4786) (meaning t m 5117) (meaning t m 5568) source

theorem rule20642 (p3343 p3574 p3746 : Prop) (h : (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3746)) : (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3746) := by
  classical
  tauto

theorem initial20642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3746)) := by
  have source := ElevenTheory.theory9898 (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule20642 (meaning t m 3343) (meaning t m 3574) (meaning t m 3746) source

theorem rule20644 (p3083 p3573 p3574 : Prop) (h : (¬ p3574) ∨ (¬ p3083) ∨ (¬ p3573)) : (¬ p3083) ∨ (¬ p3573) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial20644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory9900 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule20644 (meaning t m 3083) (meaning t m 3573) (meaning t m 3574) source

theorem rule20645 (p2177 p3658 p3659 p4710 : Prop) (h : (¬ p2177) ∨ (¬ p3659) ∨ (¬ p4710) ∨ (¬ p3658)) : (¬ p2177) ∨ (¬ p3658) ∨ (¬ p3659) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial20645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory9901 (m.theta 2 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20645 (meaning t m 2177) (meaning t m 3658) (meaning t m 3659) (meaning t m 4710) source

theorem rule20647 (p2668 p3956 p4389 : Prop) (h : (¬ p4389) ∨ (¬ p3956) ∨ (¬ p2668)) : (¬ p2668) ∨ (¬ p3956) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial20647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory9903 (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule20647 (meaning t m 2668) (meaning t m 3956) (meaning t m 4389) source

theorem rule20649 (p2027 p2363 p2383 p3266 p3365 p3366 p4315 p4866 p5016 p5405 p5740 : Prop) (h : (¬ p2363) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p2383) ∨ (¬ p3366) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p5405) ∨ (¬ p5740)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4315) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial20649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory9905 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule20649 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 3266) (meaning t m 3365) (meaning t m 3366) (meaning t m 4315) (meaning t m 4866) (meaning t m 5016) (meaning t m 5405) (meaning t m 5740) source

theorem rule20653 (p2901 p4244 p5051 : Prop) (h : (¬ p2901) ∨ (¬ p5051) ∨ (¬ p4244)) : (¬ p2901) ∨ (¬ p4244) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial20653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory9909 (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule20653 (meaning t m 2901) (meaning t m 4244) (meaning t m 5051) source

theorem rule20657 (p2027 p2363 p3692 p4119 p4129 p4138 p5564 : Prop) (h : (¬ p4138) ∨ (¬ p2363) ∨ (¬ p4129) ∨ p2027 ∨ (¬ p4119) ∨ (¬ p5564) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4129) ∨ (¬ p4138) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial20657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory9913 t (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule20657 (meaning t m 2027) (meaning t m 2363) (meaning t m 3692) (meaning t m 4119) (meaning t m 4129) (meaning t m 4138) (meaning t m 5564) source

theorem rule20658 (p2027 p2459 p2881 p3919 p4118 p4280 : Prop) (h : (¬ p2881) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4118) ∨ (¬ p4280) ∨ (¬ p3919)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4280) := by
  classical
  tauto

theorem initial20658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4280)) := by
  have source := ElevenTheory.theory9914 t (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule20658 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3919) (meaning t m 4118) (meaning t m 4280) source

theorem rule20659 (p2459 p4118 p4378 : Prop) (h : (¬ p4118) ∨ (¬ p2459) ∨ (¬ p4378)) : (¬ p2459) ∨ (¬ p4118) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial20659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory9915 (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20659 (meaning t m 2459) (meaning t m 4118) (meaning t m 4378) source

theorem rule20661 (p2027 p2696 p2753 p3136 p3549 p4107 p4272 p4381 p4870 p5400 : Prop) (h : (¬ p3549) ∨ (¬ p4381) ∨ (¬ p4107) ∨ (¬ p2753) ∨ (¬ p4870) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p2696) ∨ (¬ p5400) ∨ (¬ p4272)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4272) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial20661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory9917 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20661 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3136) (meaning t m 3549) (meaning t m 4107) (meaning t m 4272) (meaning t m 4381) (meaning t m 4870) (meaning t m 5400) source

theorem rule20662 (p2027 p2284 p2696 p2753 p3136 p3549 p4107 p4381 p4870 p5400 p5448 : Prop) (h : (¬ p3549) ∨ (¬ p4381) ∨ (¬ p4107) ∨ (¬ p2753) ∨ (¬ p4870) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p5400) ∨ (¬ p2696) ∨ (¬ p2284) ∨ (¬ p5448)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) ∨ (¬ p5448) := by
  classical
  tauto

theorem initial20662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5400)) ∨ (¬ (meaning t m 5448)) := by
  have source := ElevenTheory.theory9918 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 10) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule20662 (meaning t m 2027) (meaning t m 2284) (meaning t m 2696) (meaning t m 2753) (meaning t m 3136) (meaning t m 3549) (meaning t m 4107) (meaning t m 4381) (meaning t m 4870) (meaning t m 5400) (meaning t m 5448) source

theorem rule20663 (p3212 p4120 p4335 : Prop) (h : (¬ p4335) ∨ (¬ p4120) ∨ (¬ p3212)) : (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial20663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory9919 (m.theta 0 5) (m.theta 5 8) (m.theta 5 9)
  exact rule20663 (meaning t m 3212) (meaning t m 4120) (meaning t m 4335) source

theorem rule20664 (p2396 p3690 p4140 : Prop) (h : (¬ p3690) ∨ (¬ p2396) ∨ (¬ p4140)) : (¬ p2396) ∨ (¬ p3690) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial20664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory9920 (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule20664 (meaning t m 2396) (meaning t m 3690) (meaning t m 4140) source

theorem rule20665 (p2027 p2122 p3097 p3985 p4110 p4885 : Prop) (h : (¬ p3097) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p4110) ∨ (¬ p4885) ∨ (¬ p3985)) : (p2027) ∨ (¬ p2122) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4110) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial20665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory9921 t (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule20665 (meaning t m 2027) (meaning t m 2122) (meaning t m 3097) (meaning t m 3985) (meaning t m 4110) (meaning t m 4885) source

theorem rule20666 (p2707 p4242 p4805 : Prop) (h : (¬ p2707) ∨ (¬ p4242) ∨ (¬ p4805)) : (¬ p2707) ∨ (¬ p4242) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial20666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory9922 (m.theta 1 2) (m.theta 2 7) (m.theta 2 8)
  exact rule20666 (meaning t m 2707) (meaning t m 4242) (meaning t m 4805) source

theorem rule20673 (p2027 p2751 p3038 p3527 p3553 p3572 : Prop) (h : (¬ p2751) ∨ p2027 ∨ (¬ p3038) ∨ (¬ p3572) ∨ (¬ p3553) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial20673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory9929 t (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule20673 (meaning t m 2027) (meaning t m 2751) (meaning t m 3038) (meaning t m 3527) (meaning t m 3553) (meaning t m 3572) source

theorem rule20674 (p2027 p3063 p3093 p4366 p4405 p4427 : Prop) (h : (¬ p4427) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p4405) ∨ (¬ p4366) ∨ (¬ p3063)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial20674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory9930 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 8)
  exact rule20674 (meaning t m 2027) (meaning t m 3063) (meaning t m 3093) (meaning t m 4366) (meaning t m 4405) (meaning t m 4427) source

theorem rule20675 (p2246 p2749 p2807 p4379 p4777 p5234 : Prop) (h : (¬ p2749) ∨ (¬ p2807) ∨ (¬ p2246) ∨ (¬ p4777) ∨ (¬ p5234) ∨ (¬ p4379)) : (¬ p2246) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p4379) ∨ (¬ p4777) ∨ (¬ p5234) := by
  classical
  tauto

theorem initial20675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 5234)) := by
  have source := ElevenTheory.theory9931 (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 2 9) (m.theta 3 7)
  exact rule20675 (meaning t m 2246) (meaning t m 2749) (meaning t m 2807) (meaning t m 4379) (meaning t m 4777) (meaning t m 5234) source

theorem rule20677 (p2027 p2145 p2563 p2717 p3471 p3553 p3646 p4235 p4280 : Prop) (h : (¬ p2563) ∨ (¬ p2145) ∨ (¬ p3471) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4280) ∨ p2027 ∨ (¬ p2717)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4280) := by
  classical
  tauto

theorem initial20677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4280)) := by
  have source := ElevenTheory.theory9933 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 7) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule20677 (meaning t m 2027) (meaning t m 2145) (meaning t m 2563) (meaning t m 2717) (meaning t m 3471) (meaning t m 3553) (meaning t m 3646) (meaning t m 4235) (meaning t m 4280) source

theorem rule20680 (p2027 p2651 p2743 p2810 p4117 p4737 : Prop) (h : (¬ p4737) ∨ (¬ p2743) ∨ (¬ p4117) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2810)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial20680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory9936 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4)
  exact rule20680 (meaning t m 2027) (meaning t m 2651) (meaning t m 2743) (meaning t m 2810) (meaning t m 4117) (meaning t m 4737) source

theorem rule20682 (p2027 p2387 p2406 p2982 p3266 p3322 p3379 p4191 p4450 p5021 : Prop) (h : (¬ p2387) ∨ (¬ p3266) ∨ (¬ p5021) ∨ (¬ p3322) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4450)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3379) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial20682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory9938 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20682 (meaning t m 2027) (meaning t m 2387) (meaning t m 2406) (meaning t m 2982) (meaning t m 3266) (meaning t m 3322) (meaning t m 3379) (meaning t m 4191) (meaning t m 4450) (meaning t m 5021) source

theorem rule20684 (p2608 p3452 p3541 : Prop) (h : (¬ p2608) ∨ (¬ p3541) ∨ (¬ p3452)) : (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3541) := by
  classical
  tauto

theorem initial20684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3541)) := by
  have source := ElevenTheory.theory9940 (m.theta 0 1) (m.theta 1 2) (m.theta 1 4)
  exact rule20684 (meaning t m 2608) (meaning t m 3452) (meaning t m 3541) source

theorem rule20688 (p2946 p2963 p4336 : Prop) (h : (¬ p2963) ∨ (¬ p2946) ∨ (¬ p4336)) : (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial20688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory9944 (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule20688 (meaning t m 2946) (meaning t m 2963) (meaning t m 4336) source

theorem rule20691 (p2027 p2363 p3266 p4321 p4335 p4387 p4433 : Prop) (h : (¬ p4321) ∨ (¬ p4335) ∨ (¬ p4387) ∨ (¬ p3266) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p4433)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p4321) ∨ (¬ p4335) ∨ (¬ p4387) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial20691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory9947 t (m.theta 1 9) (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule20691 (meaning t m 2027) (meaning t m 2363) (meaning t m 3266) (meaning t m 4321) (meaning t m 4335) (meaning t m 4387) (meaning t m 4433) source

theorem rule20692 (p2589 p2850 p3363 : Prop) (h : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3363)) : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3363) := by
  classical
  tauto

theorem initial20692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3363)) := by
  have source := ElevenTheory.theory9948 (m.theta 0 4) (m.theta 2 4) (m.theta 4 5)
  exact rule20692 (meaning t m 2589) (meaning t m 2850) (meaning t m 3363) source

theorem rule20697 (p2972 p4034 p4948 : Prop) (h : (¬ p2972) ∨ (¬ p4948) ∨ (¬ p4034)) : (¬ p2972) ∨ (¬ p4034) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial20697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory9953 (m.theta 1 5) (m.theta 4 5) (m.theta 5 9)
  exact rule20697 (meaning t m 2972) (meaning t m 4034) (meaning t m 4948) source

end SunPrize.SMT
