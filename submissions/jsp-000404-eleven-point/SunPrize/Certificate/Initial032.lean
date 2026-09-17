import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory016
import SunPrize.Certificate.Theory017
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule15297 (p1992 p2027 p2299 p2588 p2633 p3584 p3585 : Prop) (h : (¬ p2588) ∨ (¬ p3584) ∨ (¬ p1992) ∨ (¬ p2299) ∨ p2633 ∨ p2027 ∨ (¬ p3585)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (p2633) ∨ (¬ p3584) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial15297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory4665 t (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15297 (meaning t m 1992) (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 2633) (meaning t m 3584) (meaning t m 3585) source

theorem rule15298 (p1984 p2027 p2563 p2938 p3555 p4173 p4235 : Prop) (h : (¬ p1984) ∨ p2938 ∨ p2027 ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p2563) ∨ (¬ p4235)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4666 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule15298 (meaning t m 1984) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 3555) (meaning t m 4173) (meaning t m 4235) source

theorem rule15299 (p1984 p2027 p2633 p3238 p3452 p3570 p4235 : Prop) (h : (¬ p3452) ∨ (¬ p4235) ∨ p2633 ∨ (¬ p3570) ∨ (¬ p1984) ∨ (¬ p3238) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3570) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4667 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15299 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3238) (meaning t m 3452) (meaning t m 3570) (meaning t m 4235) source

theorem rule15300 (p1995 p2027 p2633 p3379 p3555 p3570 p4034 p4235 : Prop) (h : (¬ p1995) ∨ p2633 ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4034) ∨ (¬ p3379) ∨ (¬ p3555)) : (¬ p1995) ∨ (p2027) ∨ (p2633) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4034) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4668 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15300 (meaning t m 1995) (meaning t m 2027) (meaning t m 2633) (meaning t m 3379) (meaning t m 3555) (meaning t m 3570) (meaning t m 4034) (meaning t m 4235) source

theorem rule15301 (p2005 p2027 p2298 p2299 p2633 p2651 p3016 p3414 : Prop) (h : (¬ p2005) ∨ (¬ p3016) ∨ (¬ p2651) ∨ p2633 ∨ (¬ p3414) ∨ p2027 ∨ (¬ p2298) ∨ (¬ p2299)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2298) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial15301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory4669 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15301 (meaning t m 2005) (meaning t m 2027) (meaning t m 2298) (meaning t m 2299) (meaning t m 2633) (meaning t m 2651) (meaning t m 3016) (meaning t m 3414) source

theorem rule15302 (p1980 p2027 p2611 p2641 p2696 p3136 p3662 : Prop) (h : (¬ p3136) ∨ p2611 ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p1980) ∨ (¬ p3662)) : (¬ p1980) ∨ (p2027) ∨ (p2611) ∨ (¬ p2641) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial15302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory4670 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule15302 (meaning t m 1980) (meaning t m 2027) (meaning t m 2611) (meaning t m 2641) (meaning t m 2696) (meaning t m 3136) (meaning t m 3662) source

theorem rule15304 (p1979 p2027 p2545 p2657 p2807 p2992 p2996 : Prop) (h : (¬ p1979) ∨ (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p2996) ∨ (¬ p2992) ∨ (¬ p2807)) : (¬ p1979) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2992) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial15304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory4672 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule15304 (meaning t m 1979) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 2992) (meaning t m 2996) source

theorem rule15305 (p1990 p2027 p2246 p2284 p2633 p2946 p2996 p3553 : Prop) (h : (¬ p1990) ∨ (¬ p3553) ∨ p2027 ∨ p2633 ∨ (¬ p2284) ∨ (¬ p2996) ∨ (¬ p2946) ∨ (¬ p2246)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (p2633) ∨ (¬ p2946) ∨ (¬ p2996) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial15305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory4673 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 7 8)
  exact rule15305 (meaning t m 1990) (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2633) (meaning t m 2946) (meaning t m 2996) (meaning t m 3553) source

theorem rule15306 (p1976 p2027 p2138 p2299 p2633 p3097 p3758 : Prop) (h : (¬ p3758) ∨ (¬ p2299) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p1976) ∨ p2633 ∨ (¬ p2138)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial15306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory4674 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15306 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2299) (meaning t m 2633) (meaning t m 3097) (meaning t m 3758) source

theorem rule15307 (p1986 p2027 p2114 p2406 p3379 p3684 p3954 : Prop) (h : (¬ p2406) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3379) ∨ (¬ p3954) ∨ p2114) : (¬ p1986) ∨ (p2027) ∨ (p2114) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3684) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4675 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule15307 (meaning t m 1986) (meaning t m 2027) (meaning t m 2114) (meaning t m 2406) (meaning t m 3379) (meaning t m 3684) (meaning t m 3954) source

theorem rule15309 (p1984 p2027 p2299 p2633 p3097 p3555 p4173 : Prop) (h : p2027 ∨ (¬ p3555) ∨ (¬ p1984) ∨ (¬ p3097) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p4173)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial15309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory4677 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15309 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3097) (meaning t m 3555) (meaning t m 4173) source

theorem rule15311 (p3402 p3948 p4365 : Prop) (h : (¬ p4365) ∨ (¬ p3402) ∨ p3948) : (¬ p3402) ∨ (p3948) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial15311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3402)) ∨ (meaning t m 3948) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory4679 (m.theta 1 3) (m.theta 1 4) (m.theta 1 5)
  exact rule15311 (meaning t m 3402) (meaning t m 3948) (meaning t m 4365) source

theorem rule15312 (p1990 p2027 p2114 p2220 p2563 p3367 p3759 p3880 p4399 : Prop) (h : (¬ p1990) ∨ (¬ p3759) ∨ (¬ p2563) ∨ (¬ p3880) ∨ (¬ p2220) ∨ (¬ p4399) ∨ (¬ p3367) ∨ p2027 ∨ p2114) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2220) ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3880) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial15312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory4680 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule15312 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2220) (meaning t m 2563) (meaning t m 3367) (meaning t m 3759) (meaning t m 3880) (meaning t m 4399) source

theorem rule15315 (p1990 p2027 p2114 p2563 p2839 p3105 p4948 : Prop) (h : (¬ p3105) ∨ (¬ p1990) ∨ (¬ p2839) ∨ (¬ p4948) ∨ (¬ p2563) ∨ p2027 ∨ p2114) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2563) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial15315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory4683 t (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule15315 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2563) (meaning t m 2839) (meaning t m 3105) (meaning t m 4948) source

theorem rule15316 (p1990 p2027 p2459 p2563 p2633 p3692 p3880 : Prop) (h : (¬ p3880) ∨ (¬ p2563) ∨ p2633 ∨ (¬ p1990) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3692)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial15316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4684 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15316 (meaning t m 1990) (meaning t m 2027) (meaning t m 2459) (meaning t m 2563) (meaning t m 2633) (meaning t m 3692) (meaning t m 3880) source

theorem rule15317 (p1984 p2027 p2633 p2743 p3553 p3572 p3954 : Prop) (h : (¬ p1984) ∨ p2633 ∨ (¬ p3572) ∨ (¬ p3553) ∨ (¬ p2743) ∨ (¬ p3954) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p2743) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15317 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4685 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule15317 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 2743) (meaning t m 3553) (meaning t m 3572) (meaning t m 3954) source

theorem rule15318 (p1992 p2027 p2247 p2608 p2633 p2742 p3553 p3572 : Prop) (h : p2633 ∨ (¬ p2742) ∨ (¬ p2247) ∨ (¬ p3572) ∨ (¬ p1992) ∨ (¬ p2608) ∨ (¬ p3553) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p2742) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial15318 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory4686 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule15318 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2633) (meaning t m 2742) (meaning t m 3553) (meaning t m 3572) source

theorem rule15319 (p1992 p2027 p2247 p2608 p2622 p2630 p4111 : Prop) (h : (¬ p2630) ∨ (¬ p2247) ∨ (¬ p4111) ∨ p2027 ∨ p2622 ∨ (¬ p2608) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4687 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule15319 (meaning t m 1992) (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2622) (meaning t m 2630) (meaning t m 4111) source

theorem rule15320 (p1984 p2027 p2462 p2761 p3588 p3954 p5228 p5387 : Prop) (h : (¬ p3588) ∨ (¬ p3954) ∨ (¬ p5228) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p5387) ∨ p2462 ∨ (¬ p2761)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial15320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory4688 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 2 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15320 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3588) (meaning t m 3954) (meaning t m 5228) (meaning t m 5387) source

theorem rule15321 (p1984 p2027 p2764 p3588 p3954 p4324 p4381 : Prop) (h : (¬ p3588) ∨ (¬ p4324) ∨ (¬ p3954) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4381) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4689 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15321 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4381) source

theorem rule15323 (p1984 p2027 p2459 p2633 p3954 p4242 p4340 : Prop) (h : (¬ p1984) ∨ (¬ p4242) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2459) ∨ p2633) : (¬ p1984) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial15323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory4691 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15323 (meaning t m 1984) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) source

theorem rule15324 (p1980 p2027 p2331 p2766 p3414 p3553 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p1980) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p3553) ∨ p2766 ∨ p2027) : (¬ p1980) ∨ (p2027) ∨ (¬ p2331) ∨ (p2766) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4692 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15324 (meaning t m 1980) (meaning t m 2027) (meaning t m 2331) (meaning t m 2766) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) source

theorem rule15326 (p1980 p2027 p2298 p2331 p2764 p3414 p4107 p4381 : Prop) (h : (¬ p2331) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4381) ∨ p2764 ∨ (¬ p1980) ∨ (¬ p2298) ∨ (¬ p4107)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (p2764) ∨ (¬ p3414) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4694 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15326 (meaning t m 1980) (meaning t m 2027) (meaning t m 2298) (meaning t m 2331) (meaning t m 2764) (meaning t m 3414) (meaning t m 4107) (meaning t m 4381) source

theorem rule15330 (p2001 p2220 p2545 p2951 p4704 : Prop) (h : p4704 ∨ p2545 ∨ (¬ p2001) ∨ (¬ p2220) ∨ (¬ p2951)) : (¬ p2001) ∨ (¬ p2220) ∨ (p2545) ∨ (¬ p2951) ∨ (p4704) := by
  classical
  tauto

theorem initial15330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2951)) ∨ (meaning t m 4704) := by
  have source := ElevenTheory.theory4698 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule15330 (meaning t m 2001) (meaning t m 2220) (meaning t m 2545) (meaning t m 2951) (meaning t m 4704) source

theorem rule15332 (p1987 p2027 p2633 p2641 p2996 p3553 p4195 : Prop) (h : (¬ p3553) ∨ p2027 ∨ (¬ p2641) ∨ p2633 ∨ (¬ p1987) ∨ (¬ p2996) ∨ (¬ p4195)) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial15332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4700 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule15332 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2641) (meaning t m 2996) (meaning t m 3553) (meaning t m 4195) source

theorem rule15333 (p2011 p2027 p2114 p2406 p2982 p3379 p3954 : Prop) (h : (¬ p2011) ∨ (¬ p3954) ∨ (¬ p2406) ∨ (¬ p2982) ∨ p2027 ∨ p2114 ∨ (¬ p3379)) : (¬ p2011) ∨ (p2027) ∨ (p2114) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4701 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9)
  exact rule15333 (meaning t m 2011) (meaning t m 2027) (meaning t m 2114) (meaning t m 2406) (meaning t m 2982) (meaning t m 3379) (meaning t m 3954) source

theorem rule15334 (p1984 p2027 p2245 p2633 p2657 p2727 p2996 p3553 : Prop) (h : p2633 ∨ (¬ p2657) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2996) ∨ (¬ p2245) ∨ (¬ p2727) ∨ (¬ p3553)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial15334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory4702 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule15334 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2633) (meaning t m 2657) (meaning t m 2727) (meaning t m 2996) (meaning t m 3553) source

theorem rule15336 (p1980 p2233 p2573 p4973 : Prop) (h : p2233 ∨ (¬ p2573) ∨ (¬ p1980) ∨ p4973) : (¬ p1980) ∨ (p2233) ∨ (¬ p2573) ∨ (p4973) := by
  classical
  tauto

theorem initial15336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 4973) := by
  have source := ElevenTheory.theory4704 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6)
  exact rule15336 (meaning t m 1980) (meaning t m 2233) (meaning t m 2573) (meaning t m 4973) source

theorem rule15337 (p1984 p2027 p2247 p2588 p2997 p3574 p4111 : Prop) (h : p2027 ∨ (¬ p2588) ∨ (¬ p2247) ∨ p2997 ∨ (¬ p4111) ∨ (¬ p1984) ∨ (¬ p3574)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3574) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4705 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule15337 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2588) (meaning t m 2997) (meaning t m 3574) (meaning t m 4111) source

theorem rule15338 (p1998 p2027 p2499 p2518 p2528 p3008 p4348 : Prop) (h : (¬ p4348) ∨ p3008 ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2528)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p3008) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4706 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15338 (meaning t m 1998) (meaning t m 2027) (meaning t m 2499) (meaning t m 2518) (meaning t m 2528) (meaning t m 3008) (meaning t m 4348) source

theorem rule15339 (p1998 p2027 p2177 p2202 p2307 p2440 p2493 p2578 p4116 : Prop) (h : p2202 ∨ (¬ p4116) ∨ (¬ p2578) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2307) ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p2493)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2307) ∨ (¬ p2440) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial15339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory4707 t (m.theta 0 6) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15339 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2307) (meaning t m 2440) (meaning t m 2493) (meaning t m 2578) (meaning t m 4116) source

theorem rule15342 (p1986 p2027 p2202 p2563 p2891 p3054 p4173 p4244 : Prop) (h : (¬ p1986) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p4173) ∨ (¬ p4244) ∨ (¬ p3054) ∨ (¬ p2563) ∨ p2202) : (¬ p1986) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2891) ∨ (¬ p3054) ∨ (¬ p4173) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial15342 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory4710 t (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule15342 (meaning t m 1986) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2891) (meaning t m 3054) (meaning t m 4173) (meaning t m 4244) source

theorem rule15343 (p1982 p2027 p2177 p2202 p2274 p2459 p2563 : Prop) (h : (¬ p2274) ∨ p2027 ∨ (¬ p2563) ∨ p2202 ∨ (¬ p1982) ∨ (¬ p2177) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2274) ∨ (¬ p2459) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial15343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory4711 t (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15343 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2274) (meaning t m 2459) (meaning t m 2563) source

theorem rule15345 (p1984 p2027 p2202 p2440 p2499 p3016 p3452 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3452) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p3016) ∨ (¬ p2499)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial15345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory4713 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule15345 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2499) (meaning t m 3016) (meaning t m 3452) source

theorem rule15347 (p1988 p2027 p2192 p2274 p2396 p2761 p2873 : Prop) (h : (¬ p2396) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p1988) ∨ p2873 ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (p2873) := by
  classical
  tauto

theorem initial15347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2873) := by
  have source := ElevenTheory.theory4715 t (m.theta 1 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15347 (meaning t m 1988) (meaning t m 2027) (meaning t m 2192) (meaning t m 2274) (meaning t m 2396) (meaning t m 2761) (meaning t m 2873) source

theorem rule15348 (p1984 p2027 p2247 p2766 p3266 p3848 p5284 : Prop) (h : (¬ p2247) ∨ (¬ p3266) ∨ (¬ p3848) ∨ (¬ p1984) ∨ p2766 ∨ p2027 ∨ (¬ p5284)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3848) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial15348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory4716 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15348 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2766) (meaning t m 3266) (meaning t m 3848) (meaning t m 5284) source

theorem rule15349 (p1984 p2027 p2247 p2764 p4118 p4360 p4444 : Prop) (h : (¬ p4360) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p2247) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2764) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4717 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15349 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2764) (meaning t m 4118) (meaning t m 4360) (meaning t m 4444) source

theorem rule15350 (p1984 p2027 p2247 p2534 p2766 p4111 p4256 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4111) ∨ (¬ p2534) ∨ (¬ p4256) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p4111) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial15350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory4718 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule15350 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2534) (meaning t m 2766) (meaning t m 4111) (meaning t m 4256) source

theorem rule15353 (p1984 p2027 p2202 p2440 p2668 p3019 p3591 p3923 : Prop) (h : (¬ p1984) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p2668) ∨ p2027 ∨ (¬ p3019) ∨ (¬ p3923) ∨ (¬ p3591)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial15353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory4721 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 6 8)
  exact rule15353 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2668) (meaning t m 3019) (meaning t m 3591) (meaning t m 3923) source

theorem rule15355 (p2313 p2386 p2553 : Prop) (h : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2386)) : (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2553) := by
  classical
  tauto

theorem initial15355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2553)) := by
  have source := ElevenTheory.theory4723 (m.theta 0 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15355 (meaning t m 2313) (meaning t m 2386) (meaning t m 2553) source

theorem rule15356 (p1978 p2027 p2169 p3564 p3646 p3744 p3956 : Prop) (h : p2169 ∨ (¬ p3564) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3646) ∨ (¬ p1978)) : (¬ p1978) ∨ (p2027) ∨ (p2169) ∨ (¬ p3564) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4724 t (m.theta 0 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15356 (meaning t m 1978) (meaning t m 2027) (meaning t m 2169) (meaning t m 3564) (meaning t m 3646) (meaning t m 3744) (meaning t m 3956) source

theorem rule15358 (p1998 p2027 p2619 p2938 p3146 p4244 p4348 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p4348) ∨ (¬ p4244) ∨ p2938 ∨ (¬ p2619) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2619) ∨ (p2938) ∨ (¬ p3146) ∨ (¬ p4244) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4726 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15358 (meaning t m 1998) (meaning t m 2027) (meaning t m 2619) (meaning t m 2938) (meaning t m 3146) (meaning t m 4244) (meaning t m 4348) source

theorem rule15359 (p1988 p2027 p2247 p2688 p2761 p3399 p3631 : Prop) (h : p2688 ∨ (¬ p3631) ∨ (¬ p2247) ∨ (¬ p3399) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3631) := by
  classical
  tauto

theorem initial15359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) := by
  have source := ElevenTheory.theory4727 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15359 (meaning t m 1988) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 2761) (meaning t m 3399) (meaning t m 3631) source

theorem rule15361 (p1982 p2027 p2247 p2459 p2688 p3399 p3527 : Prop) (h : (¬ p2247) ∨ (¬ p3399) ∨ p2688 ∨ (¬ p3527) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (p2688) ∨ (¬ p3399) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial15361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory4729 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15361 (meaning t m 1982) (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2688) (meaning t m 3399) (meaning t m 3527) source

theorem rule15362 (p1982 p2027 p2313 p2363 p2383 p2553 p3008 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p2363) ∨ p3008 ∨ (¬ p2553) ∨ (¬ p2383) ∨ (¬ p2313)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (p3008) := by
  classical
  tauto

theorem initial15362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) := by
  have source := ElevenTheory.theory4730 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule15362 (meaning t m 1982) (meaning t m 2027) (meaning t m 2313) (meaning t m 2363) (meaning t m 2383) (meaning t m 2553) (meaning t m 3008) source

theorem rule15363 (p1995 p2027 p2177 p2997 p3238 p3570 p4235 : Prop) (h : p2027 ∨ (¬ p1995) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p3238) ∨ p2997 ∨ (¬ p4235)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3238) ∨ (¬ p3570) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4731 t (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15363 (meaning t m 1995) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3238) (meaning t m 3570) (meaning t m 4235) source

theorem rule15365 (p1983 p2027 p2247 p2688 p3399 p3707 p4381 p5363 : Prop) (h : (¬ p3399) ∨ (¬ p1983) ∨ p2688 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3707) ∨ (¬ p4381) ∨ (¬ p5363)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3399) ∨ (¬ p3707) ∨ (¬ p4381) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial15365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory4733 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15365 (meaning t m 1983) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3399) (meaning t m 3707) (meaning t m 4381) (meaning t m 5363) source

theorem rule15368 (p2295 p2311 p2312 p2667 : Prop) (h : (¬ p2667) ∨ (¬ p2312) ∨ (¬ p2311) ∨ (¬ p2295)) : (¬ p2295) ∨ (¬ p2311) ∨ (¬ p2312) ∨ (¬ p2667) := by
  classical
  tauto

theorem initial15368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2667)) := by
  have source := ElevenTheory.theory4736 (m.theta 0 6) (m.theta 0 7) (m.theta 3 6) (m.theta 6 7)
  exact rule15368 (meaning t m 2295) (meaning t m 2311) (meaning t m 2312) (meaning t m 2667) source

theorem rule15369 (p1976 p2027 p2138 p2373 p2765 p3694 p4110 : Prop) (h : (¬ p2373) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2138) ∨ (¬ p3694) ∨ (¬ p4110) ∨ p2765) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3694) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4737 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule15369 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2373) (meaning t m 2765) (meaning t m 3694) (meaning t m 4110) source

theorem rule15370 (p1984 p2027 p3193 p3343 p3452 p3498 p4256 : Prop) (h : (¬ p3343) ∨ (¬ p4256) ∨ p3498 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3193)) : (¬ p1984) ∨ (p2027) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3452) ∨ (p3498) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial15370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory4738 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9)
  exact rule15370 (meaning t m 1984) (meaning t m 2027) (meaning t m 3193) (meaning t m 3343) (meaning t m 3452) (meaning t m 3498) (meaning t m 4256) source

theorem rule15371 (p1984 p2027 p2247 p2440 p2765 p4110 p4111 : Prop) (h : p2027 ∨ (¬ p4111) ∨ (¬ p2247) ∨ p2765 ∨ (¬ p1984) ∨ (¬ p4110) ∨ (¬ p2440)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2440) ∨ (p2765) ∨ (¬ p4110) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4739 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule15371 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2440) (meaning t m 2765) (meaning t m 4110) (meaning t m 4111) source

theorem rule15372 (p1977 p2027 p2241 p2765 p3238 p3452 p4110 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p2241) ∨ (¬ p4110) ∨ p2765) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2765) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4740 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6)
  exact rule15372 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2765) (meaning t m 3238) (meaning t m 3452) (meaning t m 4110) source

theorem rule15373 (p1984 p2027 p2247 p2509 p3008 p3083 p3402 p3574 : Prop) (h : (¬ p2509) ∨ p2027 ∨ (¬ p3402) ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p3574) ∨ p3008 ∨ (¬ p3083)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2509) ∨ (p3008) ∨ (¬ p3083) ∨ (¬ p3402) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial15373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory4741 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule15373 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2509) (meaning t m 3008) (meaning t m 3083) (meaning t m 3402) (meaning t m 3574) source

theorem rule15374 (p1984 p2027 p2476 p2518 p2765 p3238 p4108 p4110 : Prop) (h : (¬ p1984) ∨ p2765 ∨ (¬ p2476) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4108) ∨ (¬ p3238)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (p2765) ∨ (¬ p3238) ∨ (¬ p4108) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4742 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule15374 (meaning t m 1984) (meaning t m 2027) (meaning t m 2476) (meaning t m 2518) (meaning t m 2765) (meaning t m 3238) (meaning t m 4108) (meaning t m 4110) source

theorem rule15376 (p1995 p2842 p3585 p5216 : Prop) (h : p2842 ∨ (¬ p1995) ∨ (¬ p3585) ∨ p5216) : (¬ p1995) ∨ (p2842) ∨ (¬ p3585) ∨ (p5216) := by
  classical
  tauto

theorem initial15376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) ∨ (meaning t m 5216) := by
  have source := ElevenTheory.theory4744 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule15376 (meaning t m 1995) (meaning t m 2842) (meaning t m 3585) (meaning t m 5216) source

theorem rule15377 (p1983 p2027 p2114 p2449 p2737 p3365 p3471 p4325 : Prop) (h : (¬ p1983) ∨ p2114 ∨ (¬ p2737) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p4325) ∨ (¬ p3471) ∨ (¬ p3365)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial15377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory4745 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule15377 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2449) (meaning t m 2737) (meaning t m 3365) (meaning t m 3471) (meaning t m 4325) source

theorem rule15378 (p1981 p2027 p2313 p2383 p3128 p3309 p4026 : Prop) (h : (¬ p2313) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p3309) ∨ p3128 ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (p3128) ∨ (¬ p3309) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial15378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory4746 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule15378 (meaning t m 1981) (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3128) (meaning t m 3309) (meaning t m 4026) source

theorem rule15379 (p1998 p2027 p2264 p2685 p2737 p3586 p3688 : Prop) (h : (¬ p1998) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2685) ∨ p3586 ∨ (¬ p3688)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (p3586) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial15379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory4747 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 7) (m.theta 7 8)
  exact rule15379 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 2737) (meaning t m 3586) (meaning t m 3688) source

theorem rule15380 (p1981 p2027 p2247 p2688 p3063 p3654 p4026 p5020 : Prop) (h : (¬ p4026) ∨ (¬ p1981) ∨ (¬ p3654) ∨ (¬ p3063) ∨ p2688 ∨ (¬ p2247) ∨ p2027 ∨ (¬ p5020)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3063) ∨ (¬ p3654) ∨ (¬ p4026) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial15380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory4748 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15380 (meaning t m 1981) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3063) (meaning t m 3654) (meaning t m 4026) (meaning t m 5020) source

theorem rule15381 (p1992 p2027 p2143 p2373 p2765 p3583 p4110 p4120 : Prop) (h : (¬ p2143) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p4120) ∨ (¬ p3583)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial15381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory4749 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule15381 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2373) (meaning t m 2765) (meaning t m 3583) (meaning t m 4110) (meaning t m 4120) source

theorem rule15386 (p1986 p2027 p2313 p2553 p2785 p3008 p3367 p3688 : Prop) (h : (¬ p3367) ∨ (¬ p2553) ∨ p3008 ∨ p2027 ∨ (¬ p2785) ∨ (¬ p2313) ∨ (¬ p1986) ∨ (¬ p3688)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2785) ∨ (p3008) ∨ (¬ p3367) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial15386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory4754 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15386 (meaning t m 1986) (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 2785) (meaning t m 3008) (meaning t m 3367) (meaning t m 3688) source

theorem rule15387 (p2252 p2657 p3487 p4281 : Prop) (h : (¬ p3487) ∨ (¬ p2252) ∨ (¬ p4281) ∨ (¬ p2657)) : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial15387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory4755 (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4)
  exact rule15387 (meaning t m 2252) (meaning t m 2657) (meaning t m 3487) (meaning t m 4281) source

theorem rule15388 (p1991 p2027 p2440 p2633 p2657 p3570 p4235 : Prop) (h : (¬ p2657) ∨ (¬ p3570) ∨ p2027 ∨ p2633 ∨ (¬ p1991) ∨ (¬ p4235) ∨ (¬ p2440)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2440) ∨ (p2633) ∨ (¬ p2657) ∨ (¬ p3570) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4756 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15388 (meaning t m 1991) (meaning t m 2027) (meaning t m 2440) (meaning t m 2633) (meaning t m 2657) (meaning t m 3570) (meaning t m 4235) source

theorem rule15389 (p1987 p2027 p2553 p2696 p2780 p3008 p3822 : Prop) (h : (¬ p2696) ∨ p2027 ∨ (¬ p1987) ∨ p3008 ∨ (¬ p2553) ∨ (¬ p3822) ∨ (¬ p2780)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (p3008) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial15389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory4757 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15389 (meaning t m 1987) (meaning t m 2027) (meaning t m 2553) (meaning t m 2696) (meaning t m 2780) (meaning t m 3008) (meaning t m 3822) source

theorem rule15390 (p1982 p2027 p2114 p2459 p3399 p3527 p3954 : Prop) (h : (¬ p3527) ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p1982) ∨ p2027 ∨ p2114 ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2459) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4758 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15390 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2459) (meaning t m 3399) (meaning t m 3527) (meaning t m 3954) source

theorem rule15391 (p1998 p2027 p2114 p3073 p3399 p3954 p4189 p4348 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3073) ∨ (¬ p4348) ∨ (¬ p3954) ∨ (¬ p1998) ∨ (¬ p4189)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p3073) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4189) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4759 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15391 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 3073) (meaning t m 3399) (meaning t m 3954) (meaning t m 4189) (meaning t m 4348) source

theorem rule15392 (p1995 p2027 p2352 p3008 p3379 p3591 p3923 : Prop) (h : (¬ p1995) ∨ (¬ p2352) ∨ p2027 ∨ p3008 ∨ (¬ p3923) ∨ (¬ p3379) ∨ (¬ p3591)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2352) ∨ (p3008) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial15392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory4760 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule15392 (meaning t m 1995) (meaning t m 2027) (meaning t m 2352) (meaning t m 3008) (meaning t m 3379) (meaning t m 3591) (meaning t m 3923) source

theorem rule15395 (p1994 p2027 p2169 p2363 p2630 p3177 p3857 p3877 : Prop) (h : (¬ p2630) ∨ (¬ p3877) ∨ (¬ p1994) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3177) ∨ (¬ p3857) ∨ p2169) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial15395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory4763 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule15395 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2630) (meaning t m 3177) (meaning t m 3857) (meaning t m 3877) source

theorem rule15396 (p1982 p2027 p2114 p3707 p3830 p3954 p4444 : Prop) (h : (¬ p3707) ∨ (¬ p3954) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p1982) ∨ p2114) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4764 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15396 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 4444) source

theorem rule15397 (p1988 p2027 p2114 p3256 p3266 p3449 p3954 p4288 : Prop) (h : (¬ p3449) ∨ p2114 ∨ (¬ p3266) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p4288) ∨ (¬ p3256) ∨ (¬ p3954)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4288) := by
  classical
  tauto

theorem initial15397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4288)) := by
  have source := ElevenTheory.theory4765 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15397 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 3256) (meaning t m 3266) (meaning t m 3449) (meaning t m 3954) (meaning t m 4288) source

theorem rule15398 (p1989 p2027 p2210 p3008 p3564 p3591 p4026 : Prop) (h : p3008 ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3591) ∨ (¬ p1989) ∨ (¬ p4026)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p3008) ∨ (¬ p3564) ∨ (¬ p3591) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial15398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory4766 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 4 6) (m.theta 6 9)
  exact rule15398 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 3008) (meaning t m 3564) (meaning t m 3591) (meaning t m 4026) source

theorem rule15399 (p1994 p2027 p2169 p2630 p3096 p3297 p3564 p3989 p4035 p5379 : Prop) (h : (¬ p1994) ∨ (¬ p5379) ∨ p2027 ∨ p2169 ∨ (¬ p2630) ∨ (¬ p3096) ∨ (¬ p3989) ∨ (¬ p4035) ∨ (¬ p3564) ∨ (¬ p3297)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2630) ∨ (¬ p3096) ∨ (¬ p3297) ∨ (¬ p3564) ∨ (¬ p3989) ∨ (¬ p4035) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial15399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory4767 t (m.theta 0 9) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15399 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2630) (meaning t m 3096) (meaning t m 3297) (meaning t m 3564) (meaning t m 3989) (meaning t m 4035) (meaning t m 5379) source

theorem rule15400 (p1994 p2027 p2608 p2699 p2707 p2727 p2996 p4325 : Prop) (h : p2699 ∨ (¬ p2707) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p4325) ∨ (¬ p1994) ∨ (¬ p2608)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial15400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory4768 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule15400 (meaning t m 1994) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 2727) (meaning t m 2996) (meaning t m 4325) source

theorem rule15402 (p2187 p2352 p3096 : Prop) (h : (¬ p3096) ∨ (¬ p2352) ∨ p2187) : (p2187) ∨ (¬ p2352) ∨ (¬ p3096) := by
  classical
  tauto

theorem initial15402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3096)) := by
  have source := ElevenTheory.theory4770 (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15402 (meaning t m 2187) (meaning t m 2352) (meaning t m 3096) source

theorem rule15403 (p1994 p2027 p2462 p2630 p2761 p4035 p5284 : Prop) (h : (¬ p2630) ∨ p2027 ∨ (¬ p1994) ∨ p2462 ∨ (¬ p2761) ∨ (¬ p4035) ∨ (¬ p5284)) : (¬ p1994) ∨ (p2027) ∨ (p2462) ∨ (¬ p2630) ∨ (¬ p2761) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial15403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory4771 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15403 (meaning t m 1994) (meaning t m 2027) (meaning t m 2462) (meaning t m 2630) (meaning t m 2761) (meaning t m 4035) (meaning t m 5284) source

theorem rule15404 (p1994 p2027 p2169 p2363 p2651 p3172 p4118 : Prop) (h : p2169 ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p2363) ∨ (¬ p4118)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial15404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory4772 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule15404 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2651) (meaning t m 3172) (meaning t m 4118) source

theorem rule15405 (p2000 p2027 p2441 p2462 p2589 p3690 p4129 p5503 : Prop) (h : (¬ p2000) ∨ (¬ p5503) ∨ (¬ p4129) ∨ (¬ p2589) ∨ p2462 ∨ p2027 ∨ (¬ p3690) ∨ (¬ p2441)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2441) ∨ (p2462) ∨ (¬ p2589) ∨ (¬ p3690) ∨ (¬ p4129) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial15405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory4773 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 9)
  exact rule15405 (meaning t m 2000) (meaning t m 2027) (meaning t m 2441) (meaning t m 2462) (meaning t m 2589) (meaning t m 3690) (meaning t m 4129) (meaning t m 5503) source

theorem rule15406 (p2000 p2027 p2589 p2764 p3690 p4235 p4381 : Prop) (h : p2027 ∨ (¬ p2000) ∨ (¬ p4381) ∨ (¬ p4235) ∨ p2764 ∨ (¬ p3690) ∨ (¬ p2589)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2589) ∨ (p2764) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4774 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15406 (meaning t m 2000) (meaning t m 2027) (meaning t m 2589) (meaning t m 2764) (meaning t m 3690) (meaning t m 4235) (meaning t m 4381) source

theorem rule15407 (p1999 p2027 p2169 p2313 p2553 p2667 p3323 p3956 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p3956) ∨ p2169 ∨ (¬ p2553) ∨ (¬ p2667) ∨ (¬ p1999)) : (¬ p1999) ∨ (p2027) ∨ (p2169) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2667) ∨ (¬ p3323) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4775 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule15407 (meaning t m 1999) (meaning t m 2027) (meaning t m 2169) (meaning t m 2313) (meaning t m 2553) (meaning t m 2667) (meaning t m 3323) (meaning t m 3956) source

theorem rule15408 (p1994 p2027 p2553 p2651 p2963 p3008 p3568 : Prop) (h : p3008 ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3568)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (p3008) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial15408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory4776 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15408 (meaning t m 1994) (meaning t m 2027) (meaning t m 2553) (meaning t m 2651) (meaning t m 2963) (meaning t m 3008) (meaning t m 3568) source

theorem rule15409 (p1988 p2027 p2114 p2737 p2797 p3323 p3461 : Prop) (h : (¬ p1988) ∨ p2114 ∨ p2027 ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p2797) ∨ (¬ p2737)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial15409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory4777 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15409 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2797) (meaning t m 3323) (meaning t m 3461) source

theorem rule15410 (p1994 p2027 p2667 p2727 p2764 p3946 p4154 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p1994) ∨ (¬ p2727) ∨ (¬ p3946) ∨ p2027 ∨ p2764 ∨ (¬ p4154) ∨ (¬ p2667)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (p2764) ∨ (¬ p3946) ∨ (¬ p4154) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4778 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15410 (meaning t m 1994) (meaning t m 2027) (meaning t m 2667) (meaning t m 2727) (meaning t m 2764) (meaning t m 3946) (meaning t m 4154) (meaning t m 4191) source

theorem rule15411 (p1994 p2027 p2553 p2630 p3008 p3568 p4195 : Prop) (h : (¬ p3568) ∨ (¬ p2553) ∨ (¬ p1994) ∨ (¬ p4195) ∨ p3008 ∨ (¬ p2630) ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2630) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial15411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4779 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15411 (meaning t m 1994) (meaning t m 2027) (meaning t m 2553) (meaning t m 2630) (meaning t m 3008) (meaning t m 3568) (meaning t m 4195) source

theorem rule15412 (p1994 p2323 p2651 p2742 p2751 : Prop) (h : (¬ p1994) ∨ p2323 ∨ (¬ p2651) ∨ (¬ p2742) ∨ p2751) : (¬ p1994) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p2742) ∨ (p2751) := by
  classical
  tauto

theorem initial15412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2742)) ∨ (meaning t m 2751) := by
  have source := ElevenTheory.theory4780 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule15412 (meaning t m 1994) (meaning t m 2323) (meaning t m 2651) (meaning t m 2742) (meaning t m 2751) source

theorem rule15413 (p1987 p2027 p2589 p2633 p2662 p2810 p3570 p4235 : Prop) (h : (¬ p1987) ∨ (¬ p2810) ∨ (¬ p2589) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p4235) ∨ p2633 ∨ (¬ p3570)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3570) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4781 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15413 (meaning t m 1987) (meaning t m 2027) (meaning t m 2589) (meaning t m 2633) (meaning t m 2662) (meaning t m 2810) (meaning t m 3570) (meaning t m 4235) source

theorem rule15414 (p2002 p2027 p2138 p2633 p2774 p3570 p4244 : Prop) (h : (¬ p2002) ∨ (¬ p4244) ∨ (¬ p2138) ∨ p2027 ∨ p2633 ∨ (¬ p3570) ∨ (¬ p2774)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2138) ∨ (p2633) ∨ (¬ p2774) ∨ (¬ p3570) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial15414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory4782 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7) (m.theta 7 8)
  exact rule15414 (meaning t m 2002) (meaning t m 2027) (meaning t m 2138) (meaning t m 2633) (meaning t m 2774) (meaning t m 3570) (meaning t m 4244) source

theorem rule15415 (p2000 p2027 p2462 p2589 p2761 p4235 p4322 p4402 : Prop) (h : p2462 ∨ (¬ p4235) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2000) ∨ (¬ p4402) ∨ (¬ p2761) ∨ (¬ p4322)) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2589) ∨ (¬ p2761) ∨ (¬ p4235) ∨ (¬ p4322) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial15415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory4783 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15415 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2589) (meaning t m 2761) (meaning t m 4235) (meaning t m 4322) (meaning t m 4402) source

theorem rule15416 (p1998 p2027 p2611 p2685 p2696 p3256 p4044 p4348 : Prop) (h : (¬ p2696) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p1998) ∨ p2611 ∨ (¬ p4348) ∨ (¬ p3256) ∨ (¬ p4044)) : (¬ p1998) ∨ (p2027) ∨ (p2611) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4784 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15416 (meaning t m 1998) (meaning t m 2027) (meaning t m 2611) (meaning t m 2685) (meaning t m 2696) (meaning t m 3256) (meaning t m 4044) (meaning t m 4348) source

theorem rule15417 (p2241 p3038 p4366 : Prop) (h : (¬ p4366) ∨ (¬ p2241) ∨ (¬ p3038)) : (¬ p2241) ∨ (¬ p3038) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial15417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory4785 (m.theta 0 1) (m.theta 1 3) (m.theta 1 7)
  exact rule15417 (meaning t m 2241) (meaning t m 3038) (meaning t m 4366) source

theorem rule15418 (p1984 p2027 p2245 p2657 p2727 p2765 p3662 p3952 : Prop) (h : (¬ p2727) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p1984) ∨ (¬ p2245) ∨ (¬ p3952) ∨ (¬ p3662) ∨ p2765) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (p2765) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial15418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory4786 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule15418 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2765) (meaning t m 3662) (meaning t m 3952) source

theorem rule15419 (p1984 p2027 p2191 p2373 p2938 p3452 p4202 p4235 : Prop) (h : (¬ p1984) ∨ (¬ p4202) ∨ p2938 ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2373) ∨ (¬ p4235)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2373) ∨ (p2938) ∨ (¬ p3452) ∨ (¬ p4202) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4787 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule15419 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2373) (meaning t m 2938) (meaning t m 3452) (meaning t m 4202) (meaning t m 4235) source

theorem rule15422 (p1984 p2027 p2534 p3146 p3238 p3452 p3578 p4607 : Prop) (h : p3578 ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p3452) ∨ (¬ p1984) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p2534)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (p3578) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial15422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory4790 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule15422 (meaning t m 1984) (meaning t m 2027) (meaning t m 2534) (meaning t m 3146) (meaning t m 3238) (meaning t m 3452) (meaning t m 3578) (meaning t m 4607) source

theorem rule15423 (p1975 p2027 p2295 p2611 p2696 p3609 p4118 p4196 p4373 : Prop) (h : (¬ p1975) ∨ (¬ p4196) ∨ p2611 ∨ p2027 ∨ (¬ p4373) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p2696) ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4373) := by
  classical
  tauto

theorem initial15423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4373)) := by
  have source := ElevenTheory.theory4791 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 8 9)
  exact rule15423 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2696) (meaning t m 3609) (meaning t m 4118) (meaning t m 4196) (meaning t m 4373) source

theorem rule15425 (p1984 p2027 p2619 p3238 p3452 p3474 p3880 : Prop) (h : p2027 ∨ (¬ p3238) ∨ (¬ p1984) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p2619) ∨ p3474) : (¬ p1984) ∨ (p2027) ∨ (¬ p2619) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (p3474) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial15425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4793 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule15425 (meaning t m 1984) (meaning t m 2027) (meaning t m 2619) (meaning t m 3238) (meaning t m 3452) (meaning t m 3474) (meaning t m 3880) source

theorem rule15426 (p1992 p2027 p2608 p3238 p3452 p3578 p3880 : Prop) (h : p2027 ∨ (¬ p3238) ∨ p3578 ∨ (¬ p3880) ∨ (¬ p1992) ∨ (¬ p2608) ∨ (¬ p3452)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (p3578) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial15426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4794 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8)
  exact rule15426 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 3238) (meaning t m 3452) (meaning t m 3578) (meaning t m 3880) source

theorem rule15428 (p1984 p2027 p2764 p3238 p3452 p4322 p4948 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p1984) ∨ (¬ p3238) ∨ (¬ p4948) ∨ (¬ p4322) ∨ (¬ p3452)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial15428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory4796 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule15428 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3238) (meaning t m 3452) (meaning t m 4322) (meaning t m 4948) source

theorem rule15429 (p1982 p2027 p2470 p2528 p2589 p2765 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p2589) ∨ p2765 ∨ (¬ p2470) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2589) ∨ (p2765) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4797 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 8 9)
  exact rule15429 (meaning t m 1982) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2589) (meaning t m 2765) (meaning t m 4110) source

theorem rule15430 (p2027 p2598 p3425 p3576 p3583 p3687 p4881 : Prop) (h : (¬ p3583) ∨ (¬ p4881) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3687) ∨ (¬ p3576) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p3576) ∨ (¬ p3583) ∨ (¬ p3687) ∨ (¬ p4881) := by
  classical
  tauto

theorem initial15430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4881)) := by
  have source := ElevenTheory.theory4798 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 5) (m.theta 2 7)
  exact rule15430 (meaning t m 2027) (meaning t m 2598) (meaning t m 3425) (meaning t m 3576) (meaning t m 3583) (meaning t m 3687) (meaning t m 4881) source

theorem rule15433 (p1984 p2027 p3055 p3367 p3578 p3583 p3698 p3873 p3880 : Prop) (h : (¬ p3873) ∨ p3578 ∨ (¬ p3698) ∨ (¬ p3367) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p1984) ∨ (¬ p3055)) : (¬ p1984) ∨ (p2027) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (p3578) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3873) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial15433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4801 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule15433 (meaning t m 1984) (meaning t m 2027) (meaning t m 3055) (meaning t m 3367) (meaning t m 3578) (meaning t m 3583) (meaning t m 3698) (meaning t m 3873) (meaning t m 3880) source

theorem rule15435 (p1984 p2027 p2850 p3008 p3238 p3452 p3584 : Prop) (h : (¬ p3452) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p2850) ∨ p3008) : (¬ p1984) ∨ (p2027) ∨ (¬ p2850) ∨ (p3008) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial15435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory4803 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule15435 (meaning t m 1984) (meaning t m 2027) (meaning t m 2850) (meaning t m 3008) (meaning t m 3238) (meaning t m 3452) (meaning t m 3584) source

theorem rule15436 (p1984 p2027 p3578 p3585 p3684 p3880 p3954 : Prop) (h : (¬ p3684) ∨ p3578 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3880) ∨ (¬ p3585) ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (p3578) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4804 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8)
  exact rule15436 (meaning t m 1984) (meaning t m 2027) (meaning t m 3578) (meaning t m 3585) (meaning t m 3684) (meaning t m 3880) (meaning t m 3954) source

theorem rule15437 (p1975 p2027 p2295 p2765 p2982 p4037 p4110 p5045 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p4110) ∨ (¬ p2295) ∨ (¬ p2982) ∨ (¬ p4037) ∨ (¬ p1975) ∨ (¬ p5045)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial15437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory4805 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule15437 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2765) (meaning t m 2982) (meaning t m 4037) (meaning t m 4110) (meaning t m 5045) source

theorem rule15438 (p1975 p2027 p2241 p2295 p2699 p3063 p3324 p4759 : Prop) (h : (¬ p2295) ∨ (¬ p2241) ∨ (¬ p1975) ∨ p2699 ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4759) ∨ (¬ p3063)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3324) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial15438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory4806 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15438 (meaning t m 1975) (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2699) (meaning t m 3063) (meaning t m 3324) (meaning t m 4759) source

theorem rule15441 (p1987 p2027 p2765 p2810 p3051 p3370 p4173 p4320 p4700 : Prop) (h : (¬ p4173) ∨ (¬ p4700) ∨ (¬ p3051) ∨ p2765 ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3370) ∨ (¬ p2810) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (p2765) ∨ (¬ p2810) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p4173) ∨ (¬ p4320) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial15441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory4809 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule15441 (meaning t m 1987) (meaning t m 2027) (meaning t m 2765) (meaning t m 2810) (meaning t m 3051) (meaning t m 3370) (meaning t m 4173) (meaning t m 4320) (meaning t m 4700) source

theorem rule15443 (p1998 p2027 p2264 p2641 p2688 p2807 p2963 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2641) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2807) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial15443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory4811 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule15443 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2641) (meaning t m 2688) (meaning t m 2807) (meaning t m 2963) source

theorem rule15445 (p1982 p2027 p2177 p2295 p2459 p2641 p2688 : Prop) (h : p2688 ∨ (¬ p1982) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2177) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (p2688) := by
  classical
  tauto

theorem initial15445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) := by
  have source := ElevenTheory.theory4813 t (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15445 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2459) (meaning t m 2641) (meaning t m 2688) source

theorem rule15446 (p1984 p2027 p2264 p2355 p2928 p3452 p3644 : Prop) (h : (¬ p1984) ∨ (¬ p2928) ∨ (¬ p3644) ∨ (¬ p3452) ∨ p2027 ∨ p2355 ∨ (¬ p2264)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2264) ∨ (p2355) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial15446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory4814 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule15446 (meaning t m 1984) (meaning t m 2027) (meaning t m 2264) (meaning t m 2355) (meaning t m 2928) (meaning t m 3452) (meaning t m 3644) source

theorem rule15447 (p1984 p2027 p2997 p3097 p3238 p3452 p4110 : Prop) (h : p2997 ∨ (¬ p4110) ∨ (¬ p3452) ∨ (¬ p3238) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3097)) : (¬ p1984) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15447 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4815 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule15447 (meaning t m 1984) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3238) (meaning t m 3452) (meaning t m 4110) source

theorem rule15448 (p1984 p2027 p2766 p2928 p3452 p3644 p4348 : Prop) (h : p2027 ∨ (¬ p1984) ∨ p2766 ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p2928) ∨ (¬ p3452)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4816 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15448 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 2928) (meaning t m 3452) (meaning t m 3644) (meaning t m 4348) source

theorem rule15449 (p1991 p2027 p2563 p2952 p3578 p3880 p3952 : Prop) (h : (¬ p1991) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2563) ∨ p3578 ∨ (¬ p3880) ∨ (¬ p2952)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (p3578) ∨ (¬ p3880) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial15449 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory4817 t (m.theta 0 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule15449 (meaning t m 1991) (meaning t m 2027) (meaning t m 2563) (meaning t m 2952) (meaning t m 3578) (meaning t m 3880) (meaning t m 3952) source

theorem rule15450 (p1991 p2027 p2542 p2545 p3027 p3238 p3402 p3414 : Prop) (h : p2545 ∨ (¬ p3402) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3027) ∨ (¬ p1991) ∨ (¬ p3238)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial15450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory4818 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule15450 (meaning t m 1991) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 3027) (meaning t m 3238) (meaning t m 3402) (meaning t m 3414) source

theorem rule15452 (p1984 p2027 p2191 p2622 p3136 p3156 p3555 : Prop) (h : (¬ p3555) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3136) ∨ p2622 ∨ (¬ p3156)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (p2622) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial15452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory4820 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8)
  exact rule15452 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2622) (meaning t m 3136) (meaning t m 3156) (meaning t m 3555) source

theorem rule15453 (p2003 p2027 p2202 p2313 p2553 p3422 p3684 : Prop) (h : (¬ p2003) ∨ p2027 ∨ (¬ p3684) ∨ p2202 ∨ (¬ p2313) ∨ (¬ p3422) ∨ (¬ p2553)) : (¬ p2003) ∨ (p2027) ∨ (p2202) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial15453 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory4821 t (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule15453 (meaning t m 2003) (meaning t m 2027) (meaning t m 2202) (meaning t m 2313) (meaning t m 2553) (meaning t m 3422) (meaning t m 3684) source

theorem rule15454 (p2000 p2027 p2169 p2274 p2579 p2588 p3989 : Prop) (h : (¬ p2000) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2588)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial15454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory4822 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15454 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2579) (meaning t m 2588) (meaning t m 3989) source

theorem rule15455 (p1979 p2027 p2355 p2641 p2946 p2963 p2996 : Prop) (h : (¬ p2996) ∨ p2355 ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p2946) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (p2355) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p2996) := by
  classical
  tauto

theorem initial15455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2996)) := by
  have source := ElevenTheory.theory4823 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 3 7)
  exact rule15455 (meaning t m 1979) (meaning t m 2027) (meaning t m 2355) (meaning t m 2641) (meaning t m 2946) (meaning t m 2963) (meaning t m 2996) source

theorem rule15460 (p1994 p2027 p2114 p2630 p2696 p2780 p2829 : Prop) (h : (¬ p2829) ∨ p2027 ∨ p2114 ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p2780) ∨ (¬ p2696)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial15460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory4828 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule15460 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2630) (meaning t m 2696) (meaning t m 2780) (meaning t m 2829) source

theorem rule15461 (p1994 p2641 p2688 p4972 : Prop) (h : (¬ p2641) ∨ (¬ p1994) ∨ p2688 ∨ p4972) : (¬ p1994) ∨ (¬ p2641) ∨ (p2688) ∨ (p4972) := by
  classical
  tauto

theorem initial15461 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (meaning t m 4972) := by
  have source := ElevenTheory.theory4829 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule15461 (meaning t m 1994) (meaning t m 2641) (meaning t m 2688) (meaning t m 4972) source

theorem rule15462 (p2008 p2027 p2641 p2688 p3365 p3471 p4195 : Prop) (h : (¬ p2008) ∨ (¬ p2641) ∨ p2688 ∨ p2027 ∨ (¬ p3471) ∨ (¬ p3365) ∨ (¬ p4195)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial15462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4830 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6)
  exact rule15462 (meaning t m 2008) (meaning t m 2027) (meaning t m 2641) (meaning t m 2688) (meaning t m 3365) (meaning t m 3471) (meaning t m 4195) source

theorem rule15465 (p1976 p2027 p2462 p2589 p2850 p3876 p3905 p4278 : Prop) (h : (¬ p3876) ∨ p2462 ∨ (¬ p4278) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p3905) ∨ (¬ p2850) ∨ (¬ p2589)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4833 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule15465 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2589) (meaning t m 2850) (meaning t m 3876) (meaning t m 3905) (meaning t m 4278) source

theorem rule15466 (p1985 p2027 p2641 p2688 p2901 p2946 p2963 : Prop) (h : p2688 ∨ (¬ p2963) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p1985) ∨ (¬ p2946)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial15466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory4834 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule15466 (meaning t m 1985) (meaning t m 2027) (meaning t m 2641) (meaning t m 2688) (meaning t m 2901) (meaning t m 2946) (meaning t m 2963) source

theorem rule15467 (p1983 p2027 p2449 p2688 p2807 p3172 p3189 : Prop) (h : (¬ p2807) ∨ (¬ p3189) ∨ p2688 ∨ p2027 ∨ (¬ p3172) ∨ (¬ p1983) ∨ (¬ p2449)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (p2688) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p3189) := by
  classical
  tauto

theorem initial15467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) := by
  have source := ElevenTheory.theory4835 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 9)
  exact rule15467 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2688) (meaning t m 2807) (meaning t m 3172) (meaning t m 3189) source

theorem rule15468 (p1984 p2027 p2427 p3486 p3555 p3578 p3880 : Prop) (h : (¬ p3555) ∨ p3578 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3880) ∨ (¬ p2427)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (p3578) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial15468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4836 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule15468 (meaning t m 1984) (meaning t m 2027) (meaning t m 2427) (meaning t m 3486) (meaning t m 3555) (meaning t m 3578) (meaning t m 3880) source

theorem rule15471 (p1982 p2027 p2641 p2688 p2963 p3166 p3256 : Prop) (h : (¬ p3166) ∨ (¬ p2641) ∨ (¬ p2963) ∨ p2688 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3256)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial15471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory4839 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule15471 (meaning t m 1982) (meaning t m 2027) (meaning t m 2641) (meaning t m 2688) (meaning t m 2963) (meaning t m 3166) (meaning t m 3256) source

theorem rule15472 (p1984 p2027 p2169 p3238 p3452 p3989 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p3452) ∨ p2169 ∨ (¬ p3989) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4840 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15472 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 3238) (meaning t m 3452) (meaning t m 3989) (meaning t m 4110) source

theorem rule15473 (p1988 p2027 p2641 p2688 p2963 p3286 p3461 p4367 : Prop) (h : (¬ p1988) ∨ (¬ p2963) ∨ p2688 ∨ p2027 ∨ (¬ p2641) ∨ (¬ p3286) ∨ (¬ p4367) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2963) ∨ (¬ p3286) ∨ (¬ p3461) ∨ (¬ p4367) := by
  classical
  tauto

theorem initial15473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4367)) := by
  have source := ElevenTheory.theory4841 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule15473 (meaning t m 1988) (meaning t m 2027) (meaning t m 2641) (meaning t m 2688) (meaning t m 2963) (meaning t m 3286) (meaning t m 3461) (meaning t m 4367) source

theorem rule15474 (p2311 p2312 p2807 p3552 p3983 : Prop) (h : (¬ p2312) ∨ (¬ p2807) ∨ (¬ p3552) ∨ (¬ p2311) ∨ (¬ p3983)) : (¬ p2311) ∨ (¬ p2312) ∨ (¬ p2807) ∨ (¬ p3552) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial15474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory4842 (m.theta 0 3) (m.theta 0 6) (m.theta 0 7) (m.theta 3 7) (m.theta 6 7)
  exact rule15474 (meaning t m 2311) (meaning t m 2312) (meaning t m 2807) (meaning t m 3552) (meaning t m 3983) source

theorem rule15476 (p1984 p2027 p2177 p2499 p2997 p3452 p3581 p3644 : Prop) (h : (¬ p3452) ∨ (¬ p2499) ∨ (¬ p2177) ∨ (¬ p3644) ∨ p2027 ∨ p2997 ∨ (¬ p1984) ∨ (¬ p3581)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2499) ∨ (p2997) ∨ (¬ p3452) ∨ (¬ p3581) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial15476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory4844 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15476 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2499) (meaning t m 2997) (meaning t m 3452) (meaning t m 3581) (meaning t m 3644) source

theorem rule15478 (p1984 p2027 p2187 p2499 p2765 p3452 p3956 : Prop) (h : (¬ p3452) ∨ p2765 ∨ (¬ p1984) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3956)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2499) ∨ (p2765) ∨ (¬ p3452) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4846 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15478 (meaning t m 1984) (meaning t m 2027) (meaning t m 2187) (meaning t m 2499) (meaning t m 2765) (meaning t m 3452) (meaning t m 3956) source

theorem rule15479 (p1988 p2027 p2688 p2761 p3027 p3286 p3414 p4660 : Prop) (h : (¬ p3414) ∨ (¬ p3286) ∨ (¬ p2761) ∨ (¬ p4660) ∨ p2688 ∨ p2027 ∨ (¬ p3027) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2688) ∨ (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial15479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory4847 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15479 (meaning t m 1988) (meaning t m 2027) (meaning t m 2688) (meaning t m 2761) (meaning t m 3027) (meaning t m 3286) (meaning t m 3414) (meaning t m 4660) source

theorem rule15481 (p1994 p2027 p2264 p2630 p2688 p3027 p3361 p3551 p4849 : Prop) (h : p2027 ∨ (¬ p3027) ∨ (¬ p3361) ∨ p2688 ∨ (¬ p1994) ∨ (¬ p2630) ∨ (¬ p2264) ∨ (¬ p4849) ∨ (¬ p3551)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3361) ∨ (¬ p3551) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial15481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory4849 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule15481 (meaning t m 1994) (meaning t m 2027) (meaning t m 2264) (meaning t m 2630) (meaning t m 2688) (meaning t m 3027) (meaning t m 3361) (meaning t m 3551) (meaning t m 4849) source

theorem rule15484 (p1984 p2027 p2765 p3115 p3555 p3872 p4320 p4363 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3872) ∨ (¬ p4363) ∨ p2765 ∨ (¬ p4320) ∨ (¬ p3115)) : (¬ p1984) ∨ (p2027) ∨ (p2765) ∨ (¬ p3115) ∨ (¬ p3555) ∨ (¬ p3872) ∨ (¬ p4320) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial15484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory4852 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule15484 (meaning t m 1984) (meaning t m 2027) (meaning t m 2765) (meaning t m 3115) (meaning t m 3555) (meaning t m 3872) (meaning t m 4320) (meaning t m 4363) source

theorem rule15485 (p1991 p2027 p2765 p2891 p2952 p4034 p4110 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p1991) ∨ p2765 ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2891) ∨ (¬ p4034) ∨ (¬ p2952)) : (¬ p1991) ∨ (p2027) ∨ (p2765) ∨ (¬ p2891) ∨ (¬ p2952) ∨ (¬ p4034) ∨ (¬ p4110) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory4853 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule15485 (meaning t m 1991) (meaning t m 2027) (meaning t m 2765) (meaning t m 2891) (meaning t m 2952) (meaning t m 4034) (meaning t m 4110) (meaning t m 4320) source

theorem rule15490 (p1988 p2027 p2553 p2761 p3008 p3323 p3568 p4623 : Prop) (h : (¬ p3323) ∨ p2027 ∨ (¬ p4623) ∨ (¬ p1988) ∨ (¬ p3568) ∨ p3008 ∨ (¬ p2761) ∨ (¬ p2553)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2761) ∨ (p3008) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial15490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory4858 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15490 (meaning t m 1988) (meaning t m 2027) (meaning t m 2553) (meaning t m 2761) (meaning t m 3008) (meaning t m 3323) (meaning t m 3568) (meaning t m 4623) source

theorem rule15498 (p1984 p2027 p2765 p2982 p3555 p4110 p4363 : Prop) (h : p2765 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p4363) ∨ (¬ p3555) ∨ (¬ p4110)) : (¬ p1984) ∨ (p2027) ∨ (p2765) ∨ (¬ p2982) ∨ (¬ p3555) ∨ (¬ p4110) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial15498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory4866 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule15498 (meaning t m 1984) (meaning t m 2027) (meaning t m 2765) (meaning t m 2982) (meaning t m 3555) (meaning t m 4110) (meaning t m 4363) source

theorem rule15500 (p1994 p2027 p2630 p2938 p3246 p3572 p3947 : Prop) (h : p2938 ∨ (¬ p3246) ∨ (¬ p3572) ∨ (¬ p1994) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p3947)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3572) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial15500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory4868 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule15500 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2938) (meaning t m 3246) (meaning t m 3572) (meaning t m 3947) source

theorem rule15501 (p1988 p2027 p2449 p2611 p2685 p2696 p2761 : Prop) (h : p2611 ∨ (¬ p2685) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p2449)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2449) ∨ (p2611) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial15501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory4869 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15501 (meaning t m 1988) (meaning t m 2027) (meaning t m 2449) (meaning t m 2611) (meaning t m 2685) (meaning t m 2696) (meaning t m 2761) source

theorem rule15502 (p1987 p2027 p2114 p2651 p2707 p2810 p3425 p4117 : Prop) (h : (¬ p2651) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p1987) ∨ (¬ p4117) ∨ (¬ p3425) ∨ (¬ p2707) ∨ p2114) : (¬ p1987) ∨ (p2027) ∨ (p2114) ∨ (¬ p2651) ∨ (¬ p2707) ∨ (¬ p2810) ∨ (¬ p3425) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial15502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory4870 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4)
  exact rule15502 (meaning t m 1987) (meaning t m 2027) (meaning t m 2114) (meaning t m 2651) (meaning t m 2707) (meaning t m 2810) (meaning t m 3425) (meaning t m 4117) source

theorem rule15505 (p1988 p2027 p2459 p2611 p2717 p3266 p3471 : Prop) (h : (¬ p2459) ∨ (¬ p2717) ∨ p2611 ∨ (¬ p3471) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2459) ∨ (p2611) ∨ (¬ p2717) ∨ (¬ p3266) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial15505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory4873 t (m.theta 0 2) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15505 (meaning t m 1988) (meaning t m 2027) (meaning t m 2459) (meaning t m 2611) (meaning t m 2717) (meaning t m 3266) (meaning t m 3471) source

theorem rule15509 (p2657 p2946 p4700 : Prop) (h : (¬ p2657) ∨ (¬ p4700) ∨ (¬ p2946)) : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial15509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory4877 (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule15509 (meaning t m 2657) (meaning t m 2946) (meaning t m 4700) source

theorem rule15511 (p2341 p3945 p5294 p5295 : Prop) (h : (¬ p5294) ∨ (¬ p2341) ∨ (¬ p3945) ∨ (¬ p5295)) : (¬ p2341) ∨ (¬ p3945) ∨ (¬ p5294) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial15511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 5294)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory4879 (m.theta 0 7) (m.theta 0 9) (m.theta 7 8) (m.theta 7 9)
  exact rule15511 (meaning t m 2341) (meaning t m 3945) (meaning t m 5294) (meaning t m 5295) source

theorem rule15512 (p1994 p2027 p2088 p2630 p3360 p3877 p4118 p4590 : Prop) (h : p2027 ∨ p3360 ∨ (¬ p4118) ∨ (¬ p2630) ∨ (¬ p4590) ∨ (¬ p3877) ∨ (¬ p1994) ∨ (¬ p2088)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2630) ∨ (p3360) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial15512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory4880 t (m.theta 0 7) (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule15512 (meaning t m 1994) (meaning t m 2027) (meaning t m 2088) (meaning t m 2630) (meaning t m 3360) (meaning t m 3877) (meaning t m 4118) (meaning t m 4590) source

theorem rule15515 (p1994 p2027 p2114 p2707 p3434 p3742 p4278 : Prop) (h : (¬ p1994) ∨ (¬ p3742) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p3434) ∨ p2114) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4883 t (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule15515 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2707) (meaning t m 3434) (meaning t m 3742) (meaning t m 4278) source

theorem rule15516 (p1983 p2027 p2313 p2997 p3461 p3654 p4381 : Prop) (h : p2997 ∨ (¬ p1983) ∨ (¬ p4381) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3654)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2313) ∨ (p2997) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4884 t (m.theta 0 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15516 (meaning t m 1983) (meaning t m 2027) (meaning t m 2313) (meaning t m 2997) (meaning t m 3461) (meaning t m 3654) (meaning t m 4381) source

theorem rule15517 (p1982 p2027 p2459 p3309 p3325 p3818 p3979 p5558 : Prop) (h : (¬ p3325) ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p5558) ∨ (¬ p3309) ∨ p2027 ∨ p3818 ∨ (¬ p3979)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p3309) ∨ (¬ p3325) ∨ (p3818) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial15517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3325)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory4885 t (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule15517 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 3309) (meaning t m 3325) (meaning t m 3818) (meaning t m 3979) (meaning t m 5558) source

theorem rule15518 (p1982 p2027 p2341 p2459 p2622 p2707 p2743 p3577 : Prop) (h : (¬ p2743) ∨ (¬ p2459) ∨ (¬ p1982) ∨ (¬ p2341) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p3577) ∨ p2622) : (¬ p1982) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) := by
  classical
  tauto

theorem initial15518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3577)) := by
  have source := ElevenTheory.theory4886 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15518 (meaning t m 1982) (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3577) source

theorem rule15521 (p2008 p2027 p2138 p2622 p2743 p2839 p3471 : Prop) (h : p2027 ∨ (¬ p2138) ∨ (¬ p2743) ∨ (¬ p3471) ∨ (¬ p2839) ∨ p2622 ∨ (¬ p2008)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2138) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial15521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory4889 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule15521 (meaning t m 2008) (meaning t m 2027) (meaning t m 2138) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 3471) source

theorem rule15523 (p2177 p2396 p3945 : Prop) (h : (¬ p2177) ∨ (¬ p3945) ∨ p2396) : (¬ p2177) ∨ (p2396) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial15523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (meaning t m 2396) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory4891 (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15523 (meaning t m 2177) (meaning t m 2396) (meaning t m 3945) source

theorem rule15527 (p1982 p2027 p2114 p2737 p3506 p3755 p4444 : Prop) (h : (¬ p3506) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3755) ∨ p2114 ∨ (¬ p2737) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4895 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15527 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 3506) (meaning t m 3755) (meaning t m 4444) source

theorem rule15529 (p1994 p2027 p2630 p2964 p3276 p4035 p5284 : Prop) (h : (¬ p4035) ∨ p2964 ∨ (¬ p1994) ∨ (¬ p3276) ∨ (¬ p5284) ∨ (¬ p2630) ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2964) ∨ (¬ p3276) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial15529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory4897 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule15529 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2964) (meaning t m 3276) (meaning t m 4035) (meaning t m 5284) source

theorem rule15534 (p1984 p2027 p2462 p2761 p3193 p3452 p4425 : Prop) (h : p2462 ∨ (¬ p3452) ∨ (¬ p3193) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4425) ∨ (¬ p2761)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial15534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory4902 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15534 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3193) (meaning t m 3452) (meaning t m 4425) source

theorem rule15536 (p1979 p2027 p3578 p3660 p3880 p3888 p3952 p4393 : Prop) (h : p3578 ∨ (¬ p3880) ∨ (¬ p3888) ∨ p2027 ∨ (¬ p3660) ∨ (¬ p1979) ∨ (¬ p3952) ∨ (¬ p4393)) : (¬ p1979) ∨ (p2027) ∨ (p3578) ∨ (¬ p3660) ∨ (¬ p3880) ∨ (¬ p3888) ∨ (¬ p3952) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial15536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory4904 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 10)
  exact rule15536 (meaning t m 1979) (meaning t m 2027) (meaning t m 3578) (meaning t m 3660) (meaning t m 3880) (meaning t m 3888) (meaning t m 3952) (meaning t m 4393) source

theorem rule15541 (p1988 p2027 p2114 p2341 p2459 p2707 p3266 p3577 : Prop) (h : (¬ p3577) ∨ (¬ p3266) ∨ (¬ p2707) ∨ p2114 ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2341) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2707) ∨ (¬ p3266) ∨ (¬ p3577) := by
  classical
  tauto

theorem initial15541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3577)) := by
  have source := ElevenTheory.theory4909 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15541 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2341) (meaning t m 2459) (meaning t m 2707) (meaning t m 3266) (meaning t m 3577) source

theorem rule15543 (p2807 p2952 p4386 : Prop) (h : (¬ p2807) ∨ (¬ p4386) ∨ (¬ p2952)) : (¬ p2807) ∨ (¬ p2952) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial15543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory4911 (m.theta 0 3) (m.theta 3 5) (m.theta 3 7)
  exact rule15543 (meaning t m 2807) (meaning t m 2952) (meaning t m 4386) source

theorem rule15544 (p1984 p2027 p2499 p2764 p3452 p4137 p4191 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p1984) ∨ (¬ p4191) ∨ (¬ p2499) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (¬ p2499) ∨ (p2764) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4912 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15544 (meaning t m 1984) (meaning t m 2027) (meaning t m 2499) (meaning t m 2764) (meaning t m 3452) (meaning t m 4137) (meaning t m 4191) source

theorem rule15546 (p1984 p2027 p2169 p3193 p3452 p3461 p3990 p4425 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p1984) ∨ (¬ p3990) ∨ p2169 ∨ (¬ p4425) ∨ (¬ p3193)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial15546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory4914 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule15546 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 3193) (meaning t m 3452) (meaning t m 3461) (meaning t m 3990) (meaning t m 4425) source

theorem rule15547 (p1975 p2027 p2295 p2331 p2688 p3172 p3189 : Prop) (h : (¬ p3189) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2331) ∨ p2688 ∨ (¬ p3172) ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2688) ∨ (¬ p3172) ∨ (¬ p3189) := by
  classical
  tauto

theorem initial15547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) := by
  have source := ElevenTheory.theory4915 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule15547 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2688) (meaning t m 3172) (meaning t m 3189) source

theorem rule15548 (p1984 p2027 p2247 p3146 p3578 p4118 p4360 : Prop) (h : (¬ p3146) ∨ p3578 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4360) ∨ (¬ p4118)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial15548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory4916 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule15548 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3146) (meaning t m 3578) (meaning t m 4118) (meaning t m 4360) source

theorem rule15549 (p1988 p2027 p2264 p2323 p2459 p2807 p3266 : Prop) (h : (¬ p2459) ∨ (¬ p1988) ∨ (¬ p2264) ∨ (¬ p3266) ∨ p2027 ∨ p2323 ∨ (¬ p2807)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2459) ∨ (¬ p2807) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial15549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory4917 t (m.theta 0 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15549 (meaning t m 1988) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2459) (meaning t m 2807) (meaning t m 3266) source

theorem rule15550 (p1982 p2027 p2323 p2331 p2449 p2761 p4156 p4444 : Prop) (h : p2323 ∨ (¬ p2331) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p1982) ∨ (¬ p2449) ∨ (¬ p4156)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p4156) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4918 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15550 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2449) (meaning t m 2761) (meaning t m 4156) (meaning t m 4444) source

theorem rule15551 (p1988 p2027 p2287 p2295 p2313 p2761 p3654 p4623 : Prop) (h : (¬ p4623) ∨ p2287 ∨ (¬ p2761) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3654) ∨ (¬ p2313) ∨ (¬ p2295)) : (¬ p1988) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2761) ∨ (¬ p3654) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial15551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory4919 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15551 (meaning t m 1988) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2313) (meaning t m 2761) (meaning t m 3654) (meaning t m 4623) source

theorem rule15552 (p1984 p2027 p2247 p3008 p3564 p4037 p4154 : Prop) (h : p3008 ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p1984) ∨ (¬ p4037) ∨ (¬ p3564)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p3008) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4920 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule15552 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3008) (meaning t m 3564) (meaning t m 4037) (meaning t m 4154) source

theorem rule15554 (p1986 p2027 p2766 p3570 p3684 p4235 p4348 : Prop) (h : (¬ p3684) ∨ (¬ p4235) ∨ (¬ p1986) ∨ (¬ p3570) ∨ p2027 ∨ p2766 ∨ (¬ p4348)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p3570) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial15554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4922 t (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15554 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 3570) (meaning t m 3684) (meaning t m 4235) (meaning t m 4348) source

theorem rule15556 (p1998 p2027 p2264 p2323 p2685 p2946 p4315 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p4315) ∨ (¬ p1998) ∨ (¬ p2685) ∨ (¬ p2264) ∨ (¬ p2946)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2685) ∨ (¬ p2946) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial15556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory4924 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule15556 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2685) (meaning t m 2946) (meaning t m 4315) source

theorem rule15557 (p1998 p2027 p2114 p2241 p2264 p2685 p2748 p3954 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3954) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2748)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2748) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4925 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule15557 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2264) (meaning t m 2685) (meaning t m 2748) (meaning t m 3954) source

theorem rule15559 (p1984 p2027 p2247 p2409 p2922 p3742 p4111 : Prop) (h : p2409 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p4111) ∨ (¬ p2247) ∨ (¬ p3742)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2409) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4927 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule15559 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2409) (meaning t m 2922) (meaning t m 3742) (meaning t m 4111) source

theorem rule15561 (p2655 p3905 p4236 : Prop) (h : (¬ p4236) ∨ (¬ p2655) ∨ p3905) : (¬ p2655) ∨ (p3905) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial15561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2655)) ∨ (meaning t m 3905) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory4929 (m.theta 0 2) (m.theta 0 3) (m.theta 0 4)
  exact rule15561 (meaning t m 2655) (meaning t m 3905) (meaning t m 4236) source

theorem rule15563 (p1984 p2027 p2406 p2589 p2633 p2928 p3644 p4108 : Prop) (h : (¬ p4108) ∨ (¬ p1984) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2928) ∨ p2027 ∨ p2633 ∨ (¬ p3644)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3644) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial15563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory4931 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule15563 (meaning t m 1984) (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2633) (meaning t m 2928) (meaning t m 3644) (meaning t m 4108) source

theorem rule15564 (p1994 p2027 p2651 p2911 p2914 p3414 p3553 : Prop) (h : p2914 ∨ (¬ p1994) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2911) ∨ (¬ p3414)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial15564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory4932 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule15564 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2911) (meaning t m 2914) (meaning t m 3414) (meaning t m 3553) source

theorem rule15567 (p1984 p2027 p2247 p2766 p3497 p3662 p3692 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p3497) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2766) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial15567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory4935 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule15567 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2766) (meaning t m 3497) (meaning t m 3662) (meaning t m 3692) source

theorem rule15571 (p2000 p2027 p2169 p2406 p2499 p2589 p3096 p3989 : Prop) (h : (¬ p2589) ∨ (¬ p2000) ∨ p2027 ∨ p2169 ∨ (¬ p3989) ∨ (¬ p2406) ∨ (¬ p3096) ∨ (¬ p2499)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3096) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial15571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory4939 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15571 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2406) (meaning t m 2499) (meaning t m 2589) (meaning t m 3096) (meaning t m 3989) source

theorem rule15574 (p1984 p2027 p2247 p2633 p3570 p3662 p4320 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p4320) ∨ (¬ p3570) ∨ (¬ p1984) ∨ (¬ p3662) ∨ (¬ p2247)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2633) ∨ (¬ p3570) ∨ (¬ p3662) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory4942 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15574 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2633) (meaning t m 3570) (meaning t m 3662) (meaning t m 4320) source

theorem rule15575 (p1982 p2027 p3008 p3276 p3343 p3574 p4444 : Prop) (h : p3008 ∨ (¬ p3276) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3574) ∨ (¬ p4444) ∨ (¬ p3343)) : (¬ p1982) ∨ (p2027) ∨ (p3008) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4943 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15575 (meaning t m 1982) (meaning t m 2027) (meaning t m 3008) (meaning t m 3276) (meaning t m 3343) (meaning t m 3574) (meaning t m 4444) source

theorem rule15577 (p1984 p2027 p2743 p2810 p3008 p3574 p3954 : Prop) (h : (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3574) ∨ (¬ p3954) ∨ p3008 ∨ p2027 ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (p3008) ∨ (¬ p3574) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4945 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule15577 (meaning t m 1984) (meaning t m 2027) (meaning t m 2743) (meaning t m 2810) (meaning t m 3008) (meaning t m 3574) (meaning t m 3954) source

theorem rule15579 (p1991 p2611 p2696 p4787 : Prop) (h : p2611 ∨ p4787 ∨ (¬ p2696) ∨ (¬ p1991)) : (¬ p1991) ∨ (p2611) ∨ (¬ p2696) ∨ (p4787) := by
  classical
  tauto

theorem initial15579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 4787) := by
  have source := ElevenTheory.theory4947 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3)
  exact rule15579 (meaning t m 1991) (meaning t m 2611) (meaning t m 2696) (meaning t m 4787) source

theorem rule15581 (p1984 p2027 p2437 p2928 p2964 p3359 p3452 : Prop) (h : (¬ p3359) ∨ p2964 ∨ (¬ p2437) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2928) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2928) ∨ (p2964) ∨ (¬ p3359) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial15581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory4949 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule15581 (meaning t m 1984) (meaning t m 2027) (meaning t m 2437) (meaning t m 2928) (meaning t m 2964) (meaning t m 3359) (meaning t m 3452) source

theorem rule15582 (p1984 p2027 p2169 p2247 p3742 p3920 p3956 p4111 : Prop) (h : (¬ p3742) ∨ (¬ p3920) ∨ (¬ p2247) ∨ p2169 ∨ (¬ p3956) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p4111)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2247) ∨ (¬ p3742) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial15582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4950 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule15582 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2247) (meaning t m 3742) (meaning t m 3920) (meaning t m 3956) (meaning t m 4111) source

theorem rule15583 (p2000 p2027 p2169 p2499 p2922 p3540 p3956 : Prop) (h : (¬ p2000) ∨ p2027 ∨ p2169 ∨ (¬ p3956) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3540)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4951 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule15583 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2499) (meaning t m 2922) (meaning t m 3540) (meaning t m 3956) source

theorem rule15585 (p1984 p2027 p2247 p2764 p3662 p4208 p4322 : Prop) (h : (¬ p1984) ∨ (¬ p2247) ∨ p2027 ∨ p2764 ∨ (¬ p4322) ∨ (¬ p3662) ∨ (¬ p4208)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2764) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial15585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory4953 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule15585 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2764) (meaning t m 3662) (meaning t m 4208) (meaning t m 4322) source

theorem rule15586 (p2000 p2027 p2406 p2499 p2589 p3096 p3128 p3744 : Prop) (h : p3128 ∨ (¬ p2000) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p2589) ∨ (¬ p2499) ∨ (¬ p2406)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p3096) ∨ (p3128) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial15586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3096)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory4954 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule15586 (meaning t m 2000) (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 2589) (meaning t m 3096) (meaning t m 3128) (meaning t m 3744) source

theorem rule15588 (p2009 p2027 p2166 p2765 p3146 p3857 p4173 : Prop) (h : (¬ p4173) ∨ p2027 ∨ (¬ p2009) ∨ (¬ p3857) ∨ p2765 ∨ (¬ p3146) ∨ (¬ p2166)) : (¬ p2009) ∨ (p2027) ∨ (¬ p2166) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p3857) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial15588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory4956 t (m.theta 0 8) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule15588 (meaning t m 2009) (meaning t m 2027) (meaning t m 2166) (meaning t m 2765) (meaning t m 3146) (meaning t m 3857) (meaning t m 4173) source

theorem rule15589 (p1984 p2027 p2247 p2462 p3742 p4111 p4278 : Prop) (h : (¬ p4111) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2247) ∨ p2462 ∨ (¬ p3742)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2462) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4957 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule15589 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2462) (meaning t m 3742) (meaning t m 4111) (meaning t m 4278) source

theorem rule15590 (p1984 p2027 p2247 p2764 p3359 p4111 p4425 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p4111) ∨ (¬ p3359) ∨ (¬ p4425) ∨ (¬ p1984) ∨ (¬ p2247)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2764) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial15590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory4958 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 9 10)
  exact rule15590 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2764) (meaning t m 3359) (meaning t m 4111) (meaning t m 4425) source

theorem rule15591 (p1994 p2027 p2287 p2651 p3027 p3414 p4154 : Prop) (h : (¬ p2651) ∨ p2287 ∨ (¬ p4154) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2287) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4959 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule15591 (meaning t m 1994) (meaning t m 2027) (meaning t m 2287) (meaning t m 2651) (meaning t m 3027) (meaning t m 3414) (meaning t m 4154) source

theorem rule15592 (p1981 p2027 p2668 p3008 p3333 p3584 p4037 p4331 : Prop) (h : p2027 ∨ p3008 ∨ (¬ p3333) ∨ (¬ p4037) ∨ (¬ p4331) ∨ (¬ p2668) ∨ (¬ p1981) ∨ (¬ p3584)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2668) ∨ (p3008) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4037) ∨ (¬ p4331) := by
  classical
  tauto

theorem initial15592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4331)) := by
  have source := ElevenTheory.theory4960 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9)
  exact rule15592 (meaning t m 1981) (meaning t m 2027) (meaning t m 2668) (meaning t m 3008) (meaning t m 3333) (meaning t m 3584) (meaning t m 4037) (meaning t m 4331) source

theorem rule15593 (p1982 p2027 p2459 p2688 p3027 p3166 p3414 p4378 : Prop) (h : (¬ p2459) ∨ (¬ p3166) ∨ (¬ p3027) ∨ p2688 ∨ (¬ p1982) ∨ p2027 ∨ (¬ p4378) ∨ (¬ p3414)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial15593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory4961 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule15593 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2688) (meaning t m 3027) (meaning t m 3166) (meaning t m 3414) (meaning t m 4378) source

theorem rule15596 (p1984 p2027 p2766 p3583 p3692 p3694 p3954 : Prop) (h : (¬ p1984) ∨ (¬ p3954) ∨ (¬ p3692) ∨ (¬ p3583) ∨ p2766 ∨ p2027 ∨ (¬ p3694)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15596 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4964 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule15596 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3583) (meaning t m 3692) (meaning t m 3694) (meaning t m 3954) source

theorem rule15598 (p1984 p2027 p2764 p3583 p3954 p4322 p4385 : Prop) (h : (¬ p1984) ∨ p2764 ∨ p2027 ∨ (¬ p4322) ∨ (¬ p3954) ∨ (¬ p3583) ∨ (¬ p4385)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4322) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial15598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory4966 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 9 10)
  exact rule15598 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3583) (meaning t m 3954) (meaning t m 4322) (meaning t m 4385) source

theorem rule15601 (p1984 p2027 p2169 p2363 p2499 p2534 p3452 p3573 : Prop) (h : p2169 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3573) ∨ (¬ p2363) ∨ (¬ p2534)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial15601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory4969 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule15601 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2499) (meaning t m 2534) (meaning t m 3452) (meaning t m 3573) source

theorem rule15602 (p1984 p2027 p2499 p2766 p3452 p3956 p4347 : Prop) (h : p2766 ∨ (¬ p3452) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p1984) ∨ (¬ p4347)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2499) ∨ (p2766) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial15602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4970 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule15602 (meaning t m 1984) (meaning t m 2027) (meaning t m 2499) (meaning t m 2766) (meaning t m 3452) (meaning t m 3956) (meaning t m 4347) source

theorem rule15603 (p1984 p2027 p2287 p2295 p2499 p2588 p3452 : Prop) (h : p2287 ∨ (¬ p3452) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2295) ∨ (¬ p2499) ∨ (¬ p2588)) : (¬ p1984) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial15603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory4971 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule15603 (meaning t m 1984) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2499) (meaning t m 2588) (meaning t m 3452) source

theorem rule15604 (p1984 p2027 p2462 p2499 p2588 p3452 p4107 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p3452) ∨ (¬ p2499) ∨ (¬ p2588) ∨ p2462) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3452) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial15604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory4972 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule15604 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2499) (meaning t m 2588) (meaning t m 3452) (meaning t m 4107) source

theorem rule15606 (p1984 p2027 p2499 p3063 p3452 p3818 p3956 : Prop) (h : (¬ p3452) ∨ (¬ p1984) ∨ (¬ p2499) ∨ (¬ p3956) ∨ p2027 ∨ p3818 ∨ (¬ p3063)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p3063) ∨ (¬ p3452) ∨ (p3818) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4974 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule15606 (meaning t m 1984) (meaning t m 2027) (meaning t m 2499) (meaning t m 3063) (meaning t m 3452) (meaning t m 3818) (meaning t m 3956) source

theorem rule15608 (p1984 p2027 p2499 p2765 p3125 p3452 p4137 : Prop) (h : (¬ p1984) ∨ p2765 ∨ (¬ p3452) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3125)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2499) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4976 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule15608 (meaning t m 1984) (meaning t m 2027) (meaning t m 2499) (meaning t m 2765) (meaning t m 3125) (meaning t m 3452) (meaning t m 4137) source

theorem rule15609 (p1984 p2027 p2928 p3452 p3644 p3982 p5558 : Prop) (h : (¬ p3452) ∨ p3982 ∨ (¬ p2928) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p5558) ∨ (¬ p3644)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial15609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory4977 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10)
  exact rule15609 (meaning t m 1984) (meaning t m 2027) (meaning t m 2928) (meaning t m 3452) (meaning t m 3644) (meaning t m 3982) (meaning t m 5558) source

theorem rule15611 (p1977 p2027 p2241 p2499 p3128 p3452 p4137 : Prop) (h : (¬ p4137) ∨ (¬ p1977) ∨ p3128 ∨ p2027 ∨ (¬ p2499) ∨ (¬ p2241) ∨ (¬ p3452)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2499) ∨ (p3128) ∨ (¬ p3452) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4979 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9)
  exact rule15611 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2499) (meaning t m 3128) (meaning t m 3452) (meaning t m 4137) source

theorem rule15612 (p1984 p2027 p2177 p2247 p2997 p3553 p4067 p4154 : Prop) (h : (¬ p3553) ∨ (¬ p4154) ∨ (¬ p2177) ∨ (¬ p1984) ∨ p2997 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4067)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (p2997) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4980 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15612 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2997) (meaning t m 3553) (meaning t m 4067) (meaning t m 4154) source

theorem rule15614 (p1984 p2027 p2764 p2928 p3452 p4278 p4381 : Prop) (h : p2764 ∨ (¬ p3452) ∨ (¬ p4381) ∨ (¬ p1984) ∨ (¬ p4278) ∨ (¬ p2928) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory4982 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15614 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) (meaning t m 4381) source

theorem rule15615 (p1991 p2027 p2169 p2963 p3309 p3568 p3923 : Prop) (h : (¬ p3568) ∨ p2169 ∨ (¬ p3309) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2963) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial15615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory4983 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15615 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2963) (meaning t m 3309) (meaning t m 3568) (meaning t m 3923) source

theorem rule15616 (p1984 p2027 p2553 p3128 p3549 p3591 p4137 : Prop) (h : (¬ p4137) ∨ (¬ p1984) ∨ (¬ p3591) ∨ p2027 ∨ p3128 ∨ (¬ p2553) ∨ (¬ p3549)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2553) ∨ (p3128) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4984 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15616 (meaning t m 1984) (meaning t m 2027) (meaning t m 2553) (meaning t m 3128) (meaning t m 3549) (meaning t m 3591) (meaning t m 4137) source

theorem rule15617 (p1984 p2027 p2247 p3128 p3574 p4111 p4137 : Prop) (h : (¬ p4137) ∨ p3128 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3574) ∨ (¬ p2247) ∨ (¬ p4111)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p3128) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4985 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9)
  exact rule15617 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3128) (meaning t m 3574) (meaning t m 4111) (meaning t m 4137) source

end SunPrize.SMT
