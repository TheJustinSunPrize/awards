import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory069
import SunPrize.Certificate.Theory070
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule39807 (p2027 p2136 p2247 p2744 p3366 p3449 p3556 p3570 p4181 p4348 p5122 : Prop) (h : (¬ p3366) ∨ (¬ p3570) ∨ (¬ p4348) ∨ (¬ p2744) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2136) ∨ (¬ p4181) ∨ (¬ p3449) ∨ (¬ p3556) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4181) ∨ (¬ p4348) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial39807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29063 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule39807 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3449) (meaning t m 3556) (meaning t m 3570) (meaning t m 4181) (meaning t m 4348) (meaning t m 5122) source

theorem rule39811 (p2012 p2027 p2247 p2688 p3707 p3830 p4425 : Prop) (h : (¬ p2012) ∨ p2027 ∨ p2688 ∨ (¬ p2247) ∨ (¬ p4425) ∨ (¬ p3830) ∨ (¬ p3707)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial39811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory29067 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 4 9) (m.theta 9 10)
  exact rule39811 (meaning t m 2012) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3707) (meaning t m 3830) (meaning t m 4425) source

theorem rule39815 (p1975 p2027 p2299 p2870 p2881 p3043 p4385 : Prop) (h : p3043 ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p4385) ∨ (¬ p1975) ∨ (¬ p2881)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (p3043) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial39815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory29071 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8)
  exact rule39815 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2870) (meaning t m 2881) (meaning t m 3043) (meaning t m 4385) source

theorem rule39818 (p3758 p4334 p4385 : Prop) (h : (¬ p4385) ∨ (¬ p4334) ∨ p3758) : (p3758) ∨ (¬ p4334) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial39818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3758) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory29074 (m.theta 2 5) (m.theta 5 6) (m.theta 5 9)
  exact rule39818 (meaning t m 3758) (meaning t m 4334) (meaning t m 4385) source

theorem rule39819 (p2027 p2246 p2608 p2651 p2744 p3016 p3542 p3564 p3860 p4330 p4348 : Prop) (h : (¬ p4330) ∨ (¬ p4348) ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p3016) ∨ (¬ p2744) ∨ (¬ p3564) ∨ (¬ p2608) ∨ (¬ p3542) ∨ p2027 ∨ (¬ p3860)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3542) ∨ (¬ p3564) ∨ (¬ p3860) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory29075 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39819 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3542) (meaning t m 3564) (meaning t m 3860) (meaning t m 4330) (meaning t m 4348) source

theorem rule39821 (p2027 p2249 p2299 p2963 p3189 p3256 p3549 p3692 p3922 p4902 : Prop) (h : (¬ p3549) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2299) ∨ (¬ p3256) ∨ (¬ p3922) ∨ (¬ p4902) ∨ (¬ p3692) ∨ (¬ p2249) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2299) ∨ (¬ p2963) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3549) ∨ (¬ p3692) ∨ (¬ p3922) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29077 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39821 (meaning t m 2027) (meaning t m 2249) (meaning t m 2299) (meaning t m 2963) (meaning t m 3189) (meaning t m 3256) (meaning t m 3549) (meaning t m 3692) (meaning t m 3922) (meaning t m 4902) source

theorem rule39825 (p2027 p2132 p2187 p2247 p2860 p2996 p3553 p4133 p4733 : Prop) (h : (¬ p2247) ∨ (¬ p4133) ∨ (¬ p2860) ∨ (¬ p4733) ∨ (¬ p2187) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2860) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29081 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule39825 (meaning t m 2027) (meaning t m 2132) (meaning t m 2187) (meaning t m 2247) (meaning t m 2860) (meaning t m 2996) (meaning t m 3553) (meaning t m 4133) (meaning t m 4733) source

theorem rule39833 (p2027 p2138 p2573 p3343 p3574 p3692 p3694 p4332 p4419 : Prop) (h : p2027 ∨ (¬ p3574) ∨ (¬ p2138) ∨ (¬ p3343) ∨ (¬ p2573) ∨ (¬ p4332) ∨ (¬ p3694) ∨ (¬ p3692) ∨ (¬ p4419)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4332) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial39833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory29089 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule39833 (meaning t m 2027) (meaning t m 2138) (meaning t m 2573) (meaning t m 3343) (meaning t m 3574) (meaning t m 3692) (meaning t m 3694) (meaning t m 4332) (meaning t m 4419) source

theorem rule39834 (p1990 p2027 p2553 p2573 p2656 p2688 p2727 p3097 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p3097) ∨ (¬ p1990) ∨ (¬ p2573) ∨ (¬ p2727) ∨ (¬ p2553) ∨ (¬ p2656)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial39834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory29090 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule39834 (meaning t m 1990) (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3097) source

theorem rule39838 (p2027 p3256 p3692 p3694 p4237 p4906 : Prop) (h : (¬ p3692) ∨ (¬ p4237) ∨ (¬ p3256) ∨ (¬ p4906) ∨ p2027 ∨ (¬ p3694)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4237) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial39838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory29094 t (m.theta 2 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule39838 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 3694) (meaning t m 4237) (meaning t m 4906) source

theorem rule39841 (p2027 p2331 p2737 p2811 p3323 p3425 p3548 p3576 p4330 p4348 p4734 : Prop) (h : (¬ p3323) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p4734) ∨ (¬ p4330) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p3425) ∨ (¬ p3576) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3323) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory29097 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39841 (meaning t m 2027) (meaning t m 2331) (meaning t m 2737) (meaning t m 2811) (meaning t m 3323) (meaning t m 3425) (meaning t m 3548) (meaning t m 3576) (meaning t m 4330) (meaning t m 4348) (meaning t m 4734) source

theorem rule39843 (p2027 p2363 p3346 p3363 p3641 p4440 p4596 : Prop) (h : p2027 ∨ (¬ p3346) ∨ (¬ p4440) ∨ (¬ p3363) ∨ (¬ p4596) ∨ (¬ p3641) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3346) ∨ (¬ p3363) ∨ (¬ p3641) ∨ (¬ p4440) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial39843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory29099 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule39843 (meaning t m 2027) (meaning t m 2363) (meaning t m 3346) (meaning t m 3363) (meaning t m 3641) (meaning t m 4440) (meaning t m 4596) source

theorem rule39847 (p2027 p2230 p2396 p3201 p3362 p3591 p3684 p3817 p4105 p4276 p4733 : Prop) (h : p2027 ∨ (¬ p3591) ∨ (¬ p3201) ∨ (¬ p3684) ∨ (¬ p3362) ∨ (¬ p2230) ∨ (¬ p4276) ∨ (¬ p3817) ∨ (¬ p4733) ∨ (¬ p4105) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2396) ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p3817) ∨ (¬ p4105) ∨ (¬ p4276) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29103 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule39847 (meaning t m 2027) (meaning t m 2230) (meaning t m 2396) (meaning t m 3201) (meaning t m 3362) (meaning t m 3591) (meaning t m 3684) (meaning t m 3817) (meaning t m 4105) (meaning t m 4276) (meaning t m 4733) source

theorem rule39849 (p1990 p2027 p2245 p2563 p2598 p2633 p2641 p2850 p2963 p2996 p3553 p4733 : Prop) (h : p2633 ∨ (¬ p2963) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p1990) ∨ (¬ p2245) ∨ (¬ p4733) ∨ (¬ p2850) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p3553) ∨ (¬ p2996)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (p2633) ∨ (¬ p2641) ∨ (¬ p2850) ∨ (¬ p2963) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29105 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 7 8)
  exact rule39849 (meaning t m 1990) (meaning t m 2027) (meaning t m 2245) (meaning t m 2563) (meaning t m 2598) (meaning t m 2633) (meaning t m 2641) (meaning t m 2850) (meaning t m 2963) (meaning t m 2996) (meaning t m 3553) (meaning t m 4733) source

theorem rule39854 (p2027 p2341 p3146 p3266 p3688 p3954 p4132 p4329 p5207 p5254 : Prop) (h : (¬ p3688) ∨ (¬ p5207) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4132) ∨ (¬ p3266) ∨ (¬ p3146) ∨ (¬ p2341) ∨ (¬ p4329) ∨ (¬ p5254)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4132) ∨ (¬ p4329) ∨ (¬ p5207) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial39854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 5207)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory29110 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 5 8) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule39854 (meaning t m 2027) (meaning t m 2341) (meaning t m 3146) (meaning t m 3266) (meaning t m 3688) (meaning t m 3954) (meaning t m 4132) (meaning t m 4329) (meaning t m 5207) (meaning t m 5254) source

theorem rule39855 (p2027 p2136 p2246 p2295 p2331 p2396 p2619 p2744 p3366 p3951 p4120 p4385 : Prop) (h : (¬ p2619) ∨ (¬ p3366) ∨ (¬ p4120) ∨ (¬ p2331) ∨ (¬ p2136) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p4385) ∨ (¬ p2295) ∨ (¬ p2246) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2619) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial39855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory29111 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule39855 (meaning t m 2027) (meaning t m 2136) (meaning t m 2246) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 2619) (meaning t m 2744) (meaning t m 3366) (meaning t m 3951) (meaning t m 4120) (meaning t m 4385) source

theorem rule39856 (p2027 p2363 p2748 p2819 p2829 p3359 p3365 p4111 p4697 p4734 : Prop) (h : p2027 ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4734) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p4697) ∨ (¬ p2819) ∨ (¬ p2363) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2748) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p4111) ∨ (¬ p4697) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory29112 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule39856 (meaning t m 2027) (meaning t m 2363) (meaning t m 2748) (meaning t m 2819) (meaning t m 2829) (meaning t m 3359) (meaning t m 3365) (meaning t m 4111) (meaning t m 4697) (meaning t m 4734) source

theorem rule39857 (p1988 p2027 p2220 p2406 p2545 p3146 p3266 p4109 p4116 : Prop) (h : (¬ p2406) ∨ (¬ p3146) ∨ (¬ p4109) ∨ (¬ p3266) ∨ p2545 ∨ (¬ p4116) ∨ (¬ p2220) ∨ (¬ p1988) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2406) ∨ (p2545) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4109) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial39857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory29113 t (m.theta 0 5) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule39857 (meaning t m 1988) (meaning t m 2027) (meaning t m 2220) (meaning t m 2406) (meaning t m 2545) (meaning t m 3146) (meaning t m 3266) (meaning t m 4109) (meaning t m 4116) source

theorem rule39863 (p2027 p2363 p3063 p4078 p4340 p4871 : Prop) (h : p2027 ∨ (¬ p4871) ∨ (¬ p3063) ∨ (¬ p2363) ∨ (¬ p4078) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4871) := by
  classical
  tauto

theorem initial39863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4871)) := by
  have source := ElevenTheory.theory29119 t (m.theta 1 6) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39863 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 4078) (meaning t m 4340) (meaning t m 4871) source

theorem rule39865 (p2027 p2177 p2248 p2295 p2331 p3588 p3954 p4324 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p3954) ∨ (¬ p3588) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2177) ∨ (¬ p2331) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial39865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory29121 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39865 (meaning t m 2027) (meaning t m 2177) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4666) source

theorem rule39868 (p2027 p2248 p2881 p2901 p2946 p3588 p3954 p4324 p4666 : Prop) (h : (¬ p2901) ∨ (¬ p2881) ∨ (¬ p3588) ∨ (¬ p2946) ∨ (¬ p4324) ∨ (¬ p3954) ∨ (¬ p4666) ∨ (¬ p2248) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4324) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial39868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory29124 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39868 (meaning t m 2027) (meaning t m 2248) (meaning t m 2881) (meaning t m 2901) (meaning t m 2946) (meaning t m 3588) (meaning t m 3954) (meaning t m 4324) (meaning t m 4666) source

theorem rule39871 (p1990 p2027 p2764 p3097 p3309 p4026 p4191 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p1990) ∨ (¬ p3097) ∨ (¬ p4026) ∨ (¬ p3309) ∨ (¬ p4191)) : (¬ p1990) ∨ (p2027) ∨ (p2764) ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4026) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial39871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory29127 t (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule39871 (meaning t m 1990) (meaning t m 2027) (meaning t m 2764) (meaning t m 3097) (meaning t m 3309) (meaning t m 4026) (meaning t m 4191) source

theorem rule39878 (p1985 p2027 p2202 p2264 p3238 p3389 p3519 p3570 p3740 : Prop) (h : (¬ p3740) ∨ p2202 ∨ (¬ p3519) ∨ (¬ p3389) ∨ (¬ p3238) ∨ (¬ p2264) ∨ (¬ p1985) ∨ (¬ p3570) ∨ p2027) : (¬ p1985) ∨ (p2027) ∨ (p2202) ∨ (¬ p2264) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3570) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial39878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory29134 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule39878 (meaning t m 1985) (meaning t m 2027) (meaning t m 2202) (meaning t m 2264) (meaning t m 3238) (meaning t m 3389) (meaning t m 3519) (meaning t m 3570) (meaning t m 3740) source

theorem rule39879 (p2027 p2191 p2249 p2363 p2383 p2641 p2952 p3567 p4282 p5118 p5568 : Prop) (h : (¬ p2191) ∨ (¬ p2641) ∨ (¬ p2383) ∨ (¬ p5568) ∨ (¬ p2249) ∨ (¬ p4282) ∨ (¬ p5118) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2249) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3567) ∨ (¬ p4282) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial39879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29135 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule39879 (meaning t m 2027) (meaning t m 2191) (meaning t m 2249) (meaning t m 2363) (meaning t m 2383) (meaning t m 2641) (meaning t m 2952) (meaning t m 3567) (meaning t m 4282) (meaning t m 5118) (meaning t m 5568) source

theorem rule39881 (p2027 p2499 p2972 p3948 p4715 p4948 : Prop) (h : (¬ p4715) ∨ (¬ p4948) ∨ (¬ p3948) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p2972)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2972) ∨ (¬ p3948) ∨ (¬ p4715) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial39881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory29137 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule39881 (meaning t m 2027) (meaning t m 2499) (meaning t m 2972) (meaning t m 3948) (meaning t m 4715) (meaning t m 4948) source

theorem rule39884 (p2331 p2573 p2663 p4389 : Prop) (h : (¬ p2663) ∨ (¬ p2573) ∨ (¬ p4389) ∨ p2331) : (p2331) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial39884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2331) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory29140 (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 6)
  exact rule39884 (meaning t m 2331) (meaning t m 2573) (meaning t m 2663) (meaning t m 4389) source

theorem rule39889 (p3872 p3952 p4320 : Prop) (h : (¬ p3872) ∨ (¬ p4320) ∨ p3952) : (¬ p3872) ∨ (p3952) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial39889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3872)) ∨ (meaning t m 3952) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory29145 (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule39889 (meaning t m 3872) (meaning t m 3952) (meaning t m 4320) source

theorem rule39890 (p2284 p3872 p4320 : Prop) (h : (¬ p3872) ∨ (¬ p4320) ∨ (¬ p2284)) : (¬ p2284) ∨ (¬ p3872) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial39890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory29146 (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule39890 (meaning t m 2284) (meaning t m 3872) (meaning t m 4320) source

theorem rule39893 (p2534 p4348 p4383 : Prop) (h : (¬ p4348) ∨ (¬ p4383) ∨ p2534) : (p2534) ∨ (¬ p4348) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial39893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2534) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory29149 (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39893 (meaning t m 2534) (meaning t m 4348) (meaning t m 4383) source

theorem rule39896 (p2027 p2248 p2331 p2509 p2534 p3452 p3755 p4195 p5109 : Prop) (h : (¬ p2534) ∨ (¬ p5109) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p3452) ∨ (¬ p4195) ∨ (¬ p2248) ∨ (¬ p3755)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p3755) ∨ (¬ p4195) ∨ (¬ p5109) := by
  classical
  tauto

theorem initial39896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5109)) := by
  have source := ElevenTheory.theory29152 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 8) (m.theta 8 9)
  exact rule39896 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2509) (meaning t m 2534) (meaning t m 3452) (meaning t m 3755) (meaning t m 4195) (meaning t m 5109) source

theorem rule39897 (p1987 p2027 p2633 p2992 p2996 p3570 p3699 p4315 : Prop) (h : (¬ p4315) ∨ (¬ p1987) ∨ (¬ p2992) ∨ p2633 ∨ (¬ p3699) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2996)) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3570) ∨ (¬ p3699) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial39897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory29153 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule39897 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 2992) (meaning t m 2996) (meaning t m 3570) (meaning t m 3699) (meaning t m 4315) source

theorem rule39898 (p2010 p2027 p2545 p3027 p3516 p4066 p4111 p4278 : Prop) (h : (¬ p4066) ∨ (¬ p2010) ∨ (¬ p3516) ∨ p2027 ∨ (¬ p4111) ∨ p2545 ∨ (¬ p3027) ∨ (¬ p4278)) : (¬ p2010) ∨ (p2027) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4111) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial39898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory29154 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule39898 (meaning t m 2010) (meaning t m 2027) (meaning t m 2545) (meaning t m 3027) (meaning t m 3516) (meaning t m 4066) (meaning t m 4111) (meaning t m 4278) source

theorem rule39904 (p1975 p2027 p2264 p2299 p2622 p2774 p3365 p4156 p4328 : Prop) (h : (¬ p3365) ∨ (¬ p4328) ∨ p2027 ∨ (¬ p1975) ∨ p2622 ∨ (¬ p2774) ∨ (¬ p2264) ∨ (¬ p4156) ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4156) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial39904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory29160 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39904 (meaning t m 1975) (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 2622) (meaning t m 2774) (meaning t m 3365) (meaning t m 4156) (meaning t m 4328) source

theorem rule39910 (p2027 p2252 p2750 p2963 p3324 p3707 p3830 p3954 p5123 p5580 : Prop) (h : (¬ p3830) ∨ (¬ p3707) ∨ (¬ p5123) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2963) ∨ (¬ p2750) ∨ (¬ p5580) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29166 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39910 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 3324) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 5123) (meaning t m 5580) source

theorem rule39912 (p1975 p2027 p2295 p2699 p3063 p3093 p3324 : Prop) (h : (¬ p2295) ∨ p2699 ∨ (¬ p3324) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3093) ∨ (¬ p3063)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial39912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory29168 t (m.theta 0 1) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39912 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 3324) source

theorem rule39914 (p2027 p3156 p3426 p3434 p3947 p4386 p4428 p4509 : Prop) (h : (¬ p4386) ∨ (¬ p3947) ∨ (¬ p3434) ∨ (¬ p4428) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p4509) ∨ (¬ p3426)) : (p2027) ∨ (¬ p3156) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4428) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory29170 t (m.theta 2 6) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9)
  exact rule39914 (meaning t m 2027) (meaning t m 3156) (meaning t m 3426) (meaning t m 3434) (meaning t m 3947) (meaning t m 4386) (meaning t m 4428) (meaning t m 4509) source

theorem rule39915 (p1984 p2114 p2247 p2750 : Prop) (h : p2750 ∨ p2114 ∨ (¬ p2247) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2114) ∨ (¬ p2247) ∨ (p2750) := by
  classical
  tauto

theorem initial39915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2750) := by
  have source := ElevenTheory.theory29171 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule39915 (meaning t m 1984) (meaning t m 2114) (meaning t m 2247) (meaning t m 2750) source

theorem rule39916 (p1994 p2027 p2230 p2440 p2476 p2766 p3692 p3693 : Prop) (h : (¬ p3693) ∨ (¬ p3692) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p1994) ∨ (¬ p2440) ∨ p2027 ∨ p2766) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3693) := by
  classical
  tauto

theorem initial39916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3693)) := by
  have source := ElevenTheory.theory29172 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule39916 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2476) (meaning t m 2766) (meaning t m 3692) (meaning t m 3693) source

theorem rule39917 (p2027 p2417 p3096 p3156 p3920 p3947 p4386 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p3920) ∨ (¬ p3947) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p4386) ∨ (¬ p2417) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3096) ∨ (¬ p3156) ∨ (¬ p3920) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory29173 t (m.theta 3 5) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 9)
  exact rule39917 (meaning t m 2027) (meaning t m 2417) (meaning t m 3096) (meaning t m 3156) (meaning t m 3920) (meaning t m 3947) (meaning t m 4386) (meaning t m 4509) source

theorem rule39918 (p2027 p2499 p3449 p3452 p4598 p4687 : Prop) (h : (¬ p4687) ∨ (¬ p4598) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2499) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4598) ∨ (¬ p4687) := by
  classical
  tauto

theorem initial39918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4598)) ∨ (¬ (meaning t m 4687)) := by
  have source := ElevenTheory.theory29174 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 6) (m.theta 4 8)
  exact rule39918 (meaning t m 2027) (meaning t m 2499) (meaning t m 3449) (meaning t m 3452) (meaning t m 4598) (meaning t m 4687) source

theorem rule39920 (p2027 p2470 p3222 p3346 p3590 p3684 p4610 : Prop) (h : p2027 ∨ (¬ p3684) ∨ (¬ p3590) ∨ (¬ p4610) ∨ (¬ p2470) ∨ (¬ p3346) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3590) ∨ (¬ p3684) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial39920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory29176 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 4 9)
  exact rule39920 (meaning t m 2027) (meaning t m 2470) (meaning t m 3222) (meaning t m 3346) (meaning t m 3590) (meaning t m 3684) (meaning t m 4610) source

theorem rule39922 (p2027 p2427 p3246 p3821 p4533 p4984 : Prop) (h : p2027 ∨ (¬ p4533) ∨ (¬ p4984) ∨ (¬ p2427) ∨ (¬ p3821) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4533) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial39922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4533)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory29178 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule39922 (meaning t m 2027) (meaning t m 2427) (meaning t m 3246) (meaning t m 3821) (meaning t m 4533) (meaning t m 4984) source

theorem rule39927 (p2027 p2249 p2509 p2534 p2641 p2657 p3487 p3506 p4191 p4330 p4421 : Prop) (h : (¬ p3487) ∨ (¬ p2657) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p3506) ∨ (¬ p2509) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4421) := by
  classical
  tauto

theorem initial39927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4421)) := by
  have source := ElevenTheory.theory29183 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 3 9) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule39927 (meaning t m 2027) (meaning t m 2249) (meaning t m 2509) (meaning t m 2534) (meaning t m 2641) (meaning t m 2657) (meaning t m 3487) (meaning t m 3506) (meaning t m 4191) (meaning t m 4330) (meaning t m 4421) source

theorem rule39928 (p2027 p2249 p2509 p2641 p2657 p3323 p3461 p3487 p4286 p5123 : Prop) (h : (¬ p2641) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p3487) ∨ (¬ p2657) ∨ (¬ p3461) ∨ (¬ p5123) ∨ (¬ p3323) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2509) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3487) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial39928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory29184 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule39928 (meaning t m 2027) (meaning t m 2249) (meaning t m 2509) (meaning t m 2641) (meaning t m 2657) (meaning t m 3323) (meaning t m 3461) (meaning t m 3487) (meaning t m 4286) (meaning t m 5123) source

theorem rule39930 (p2027 p2299 p2417 p2881 p3690 p4712 : Prop) (h : p2027 ∨ (¬ p4712) ∨ (¬ p2417) ∨ (¬ p2299) ∨ (¬ p3690) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2881) ∨ (¬ p3690) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial39930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory29186 t (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39930 (meaning t m 2027) (meaning t m 2299) (meaning t m 2417) (meaning t m 2881) (meaning t m 3690) (meaning t m 4712) source

theorem rule39931 (p2027 p2156 p2245 p2657 p2727 p2870 p2996 p3758 p4362 p4521 : Prop) (h : p2027 ∨ (¬ p3758) ∨ (¬ p2156) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p2727) ∨ (¬ p4362) ∨ (¬ p4521) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p2996) ∨ (¬ p3758) ∨ (¬ p4362) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial39931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory29187 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule39931 (meaning t m 2027) (meaning t m 2156) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2870) (meaning t m 2996) (meaning t m 3758) (meaning t m 4362) (meaning t m 4521) source

theorem rule39932 (p2027 p2449 p2995 p3821 p4244 p4283 p4906 : Prop) (h : (¬ p2995) ∨ (¬ p4283) ∨ p2027 ∨ (¬ p4906) ∨ (¬ p4244) ∨ (¬ p2449) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2995) ∨ (¬ p3821) ∨ (¬ p4244) ∨ (¬ p4283) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial39932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory29188 t (m.theta 0 7) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule39932 (meaning t m 2027) (meaning t m 2449) (meaning t m 2995) (meaning t m 3821) (meaning t m 4244) (meaning t m 4283) (meaning t m 4906) source

theorem rule39937 (p2027 p2122 p2241 p2396 p2750 p2753 p2774 p3193 p3452 p4641 : Prop) (h : (¬ p2774) ∨ (¬ p4641) ∨ (¬ p2750) ∨ (¬ p2396) ∨ (¬ p2241) ∨ (¬ p3193) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2122) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4641) := by
  classical
  tauto

theorem initial39937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4641)) := by
  have source := ElevenTheory.theory29193 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule39937 (meaning t m 2027) (meaning t m 2122) (meaning t m 2241) (meaning t m 2396) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3193) (meaning t m 3452) (meaning t m 4641) source

theorem rule39941 (p2027 p2427 p4129 p4136 p4423 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4423) ∨ (¬ p4136) ∨ (¬ p4129)) : (p2027) ∨ (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4136) ∨ (¬ p4423) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial39941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory29197 t (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10)
  exact rule39941 (meaning t m 2027) (meaning t m 2427) (meaning t m 4129) (meaning t m 4136) (meaning t m 4423) (meaning t m 4882) source

theorem rule39944 (p2027 p2499 p3222 p3917 p4331 p5222 : Prop) (h : (¬ p2499) ∨ (¬ p3222) ∨ p2027 ∨ (¬ p4331) ∨ (¬ p5222) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3917) ∨ (¬ p4331) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial39944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory29200 t (m.theta 1 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule39944 (meaning t m 2027) (meaning t m 2499) (meaning t m 3222) (meaning t m 3917) (meaning t m 4331) (meaning t m 5222) source

theorem rule39946 (p1981 p2027 p2114 p2307 p2668 p2779 p2829 p3568 : Prop) (h : p2027 ∨ (¬ p2779) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p2307) ∨ p2114 ∨ (¬ p1981) ∨ (¬ p2829)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2307) ∨ (¬ p2668) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial39946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory29202 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39946 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2307) (meaning t m 2668) (meaning t m 2779) (meaning t m 2829) (meaning t m 3568) source

theorem rule39947 (p1981 p2027 p2114 p2307 p2668 p2737 p2779 p3568 p4426 : Prop) (h : (¬ p1981) ∨ p2027 ∨ (¬ p2779) ∨ (¬ p4426) ∨ (¬ p2668) ∨ (¬ p3568) ∨ p2114 ∨ (¬ p2307) ∨ (¬ p2737)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2307) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2779) ∨ (¬ p3568) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial39947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory29203 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39947 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2307) (meaning t m 2668) (meaning t m 2737) (meaning t m 2779) (meaning t m 3568) (meaning t m 4426) source

theorem rule39949 (p2027 p2619 p2839 p3688 p4428 p4509 : Prop) (h : p2027 ∨ (¬ p3688) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p4428) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p3688) ∨ (¬ p4428) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial39949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory29205 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 8)
  exact rule39949 (meaning t m 2027) (meaning t m 2619) (meaning t m 2839) (meaning t m 3688) (meaning t m 4428) (meaning t m 4509) source

theorem rule39955 (p2027 p2132 p2252 p2657 p2750 p2753 p2870 p3359 p4129 p4425 p4826 : Prop) (h : (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2753) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3359) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory29211 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule39955 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3359) (meaning t m 4129) (meaning t m 4425) (meaning t m 4826) source

theorem rule39956 (p2027 p2252 p2657 p2741 p3359 p3399 p3555 p4075 p4377 p4425 p4826 : Prop) (h : (¬ p3555) ∨ (¬ p2252) ∨ (¬ p4377) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p4826) ∨ (¬ p2657) ∨ (¬ p3359) ∨ (¬ p4425) ∨ (¬ p4075)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2741) ∨ (¬ p3359) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p4075) ∨ (¬ p4377) ∨ (¬ p4425) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory29212 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 10) (m.theta 9 10)
  exact rule39956 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2741) (meaning t m 3359) (meaning t m 3399) (meaning t m 3555) (meaning t m 4075) (meaning t m 4377) (meaning t m 4425) (meaning t m 4826) source

theorem rule39957 (p2027 p2132 p2252 p2534 p2657 p2750 p2753 p2870 p3246 p3950 p4256 : Prop) (h : p2027 ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial39957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory29213 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule39957 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3246) (meaning t m 3950) (meaning t m 4256) source

theorem rule39958 (p2027 p2132 p2241 p2534 p2750 p2753 p2870 p3246 p3860 p3950 p4370 : Prop) (h : (¬ p2750) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4370) ∨ (¬ p2534) ∨ (¬ p3860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2534) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial39958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory29214 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule39958 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2534) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3246) (meaning t m 3860) (meaning t m 3950) (meaning t m 4370) source

theorem rule39959 (p2027 p2132 p2252 p2476 p2655 p2750 p2753 p2870 p3083 p3246 p3359 p3950 p4440 : Prop) (h : (¬ p3246) ∨ (¬ p2252) ∨ (¬ p2655) ∨ (¬ p2476) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3950) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p4440) ∨ (¬ p3083) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3083) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p3950) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial39959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory29215 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule39959 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2476) (meaning t m 2655) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3083) (meaning t m 3246) (meaning t m 3359) (meaning t m 3950) (meaning t m 4440) source

theorem rule39961 (p2027 p2156 p3125 p3366 p3370 p3371 p3414 p3461 p3553 p4789 p5123 p5558 : Prop) (h : (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5558) ∨ (¬ p3553) ∨ (¬ p3414) ∨ (¬ p3125) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2156) ∨ (¬ p3371) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3553) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial39961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29217 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39961 (meaning t m 2027) (meaning t m 2156) (meaning t m 3125) (meaning t m 3366) (meaning t m 3370) (meaning t m 3371) (meaning t m 3414) (meaning t m 3461) (meaning t m 3553) (meaning t m 4789) (meaning t m 5123) (meaning t m 5558) source

theorem rule39962 (p2027 p2476 p3083 p3212 p3359 p3366 p3370 p3371 p3680 p4191 p4729 p5325 : Prop) (h : (¬ p3359) ∨ (¬ p3371) ∨ (¬ p3366) ∨ (¬ p5325) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p3370) ∨ (¬ p2476) ∨ (¬ p4729) ∨ (¬ p4191) ∨ (¬ p3212) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p3212) ∨ (¬ p3359) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p4729) ∨ (¬ p5325) := by
  classical
  tauto

theorem initial39962 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5325)) := by
  have source := ElevenTheory.theory29218 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule39962 (meaning t m 2027) (meaning t m 2476) (meaning t m 3083) (meaning t m 3212) (meaning t m 3359) (meaning t m 3366) (meaning t m 3370) (meaning t m 3371) (meaning t m 3680) (meaning t m 4191) (meaning t m 4729) (meaning t m 5325) source

theorem rule39965 (p2027 p2122 p2252 p2396 p2534 p2657 p2750 p2753 p2774 p3950 p4256 : Prop) (h : (¬ p3950) ∨ (¬ p2396) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2122) ∨ (¬ p2534) ∨ (¬ p2753) ∨ (¬ p4256) ∨ (¬ p2750) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3950) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial39965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory29221 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule39965 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2396) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3950) (meaning t m 4256) source

theorem rule39966 (p2027 p2122 p2396 p2476 p2774 p3083 p3359 p4641 p4729 : Prop) (h : (¬ p4641) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p3359) ∨ (¬ p2476) ∨ (¬ p2774) ∨ (¬ p2396) ∨ (¬ p3083) ∨ (¬ p4729)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2476) ∨ (¬ p2774) ∨ (¬ p3083) ∨ (¬ p3359) ∨ (¬ p4641) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial39966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory29222 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule39966 (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2476) (meaning t m 2774) (meaning t m 3083) (meaning t m 3359) (meaning t m 4641) (meaning t m 4729) source

theorem rule39969 (p2027 p2139 p2307 p2534 p2657 p2962 p3097 p3125 p4236 p4256 p4330 : Prop) (h : (¬ p2962) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p4256) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p2139) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial39969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory29225 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule39969 (meaning t m 2027) (meaning t m 2139) (meaning t m 2307) (meaning t m 2534) (meaning t m 2657) (meaning t m 2962) (meaning t m 3097) (meaning t m 3125) (meaning t m 4236) (meaning t m 4256) (meaning t m 4330) source

theorem rule39972 (p2027 p2132 p2252 p2750 p2753 p2870 p3172 p4118 p4129 p4444 p4826 : Prop) (h : (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4129) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p4826) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4129) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory29228 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39972 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3172) (meaning t m 4118) (meaning t m 4129) (meaning t m 4444) (meaning t m 4826) source

theorem rule39977 (p2027 p2144 p2156 p2252 p2750 p3125 p3366 p3414 p3461 p3553 p5123 p5558 : Prop) (h : p2027 ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p2156) ∨ (¬ p3461) ∨ (¬ p2144) ∨ p3366 ∨ (¬ p2750) ∨ (¬ p5123) ∨ (¬ p2252) ∨ (¬ p3553) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3125) ∨ (p3366) ∨ (¬ p3414) ∨ (¬ p3461) ∨ (¬ p3553) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial39977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3125)) ∨ (meaning t m 3366) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29233 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39977 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 2252) (meaning t m 2750) (meaning t m 3125) (meaning t m 3366) (meaning t m 3414) (meaning t m 3461) (meaning t m 3553) (meaning t m 5123) (meaning t m 5558) source

theorem rule39978 (p2027 p2144 p2252 p2437 p2655 p2750 p3212 p3359 p3366 p3540 p3680 p4191 p5325 : Prop) (h : (¬ p3680) ∨ p3366 ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3212) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p3359) ∨ (¬ p2655) ∨ (¬ p5325) ∨ (¬ p3540) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3212) ∨ (¬ p3359) ∨ (p3366) ∨ (¬ p3540) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p5325) := by
  classical
  tauto

theorem initial39978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3359)) ∨ (meaning t m 3366) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5325)) := by
  have source := ElevenTheory.theory29234 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule39978 (meaning t m 2027) (meaning t m 2144) (meaning t m 2252) (meaning t m 2437) (meaning t m 2655) (meaning t m 2750) (meaning t m 3212) (meaning t m 3359) (meaning t m 3366) (meaning t m 3540) (meaning t m 3680) (meaning t m 4191) (meaning t m 5325) source

theorem rule39983 (p2027 p2144 p2220 p2252 p2579 p2655 p2750 p2753 p3016 p3146 p4256 p4348 p4438 : Prop) (h : (¬ p4438) ∨ (¬ p2753) ∨ (¬ p2144) ∨ (¬ p4348) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2655) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2220) ∨ (¬ p4256) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3146) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial39983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory29239 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39983 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2252) (meaning t m 2579) (meaning t m 2655) (meaning t m 2750) (meaning t m 2753) (meaning t m 3016) (meaning t m 3146) (meaning t m 4256) (meaning t m 4348) (meaning t m 4438) source

theorem rule39985 (p2027 p2144 p2499 p2619 p2753 p3016 p3051 p4244 p4256 p4434 p5216 : Prop) (h : (¬ p2499) ∨ (¬ p2753) ∨ (¬ p4434) ∨ (¬ p4256) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p2619) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2499) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4434) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory29241 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule39985 (meaning t m 2027) (meaning t m 2144) (meaning t m 2499) (meaning t m 2619) (meaning t m 2753) (meaning t m 3016) (meaning t m 3051) (meaning t m 4244) (meaning t m 4256) (meaning t m 4434) (meaning t m 5216) source

theorem rule39986 (p1991 p2027 p2657 p2764 p3574 p4137 p4191 : Prop) (h : (¬ p3574) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p1991) ∨ (¬ p4191) ∨ (¬ p4137) ∨ p2764) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial39986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory29242 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule39986 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2764) (meaning t m 3574) (meaning t m 4137) (meaning t m 4191) source

theorem rule39988 (p2027 p2474 p2850 p3363 p4149 p4608 p5590 : Prop) (h : (¬ p3363) ∨ (¬ p2474) ∨ (¬ p5590) ∨ (¬ p4608) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2474) ∨ (¬ p2850) ∨ (¬ p3363) ∨ (¬ p4149) ∨ (¬ p4608) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial39988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4608)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory29244 t (m.theta 0 4) (m.theta 0 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 10)
  exact rule39988 (meaning t m 2027) (meaning t m 2474) (meaning t m 2850) (meaning t m 3363) (meaning t m 4149) (meaning t m 4608) (meaning t m 5590) source

theorem rule39992 (p2027 p2252 p2750 p2963 p3093 p3922 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p2252) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3922)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial39992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory29248 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6)
  exact rule39992 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 3093) (meaning t m 3922) (meaning t m 3954) source

theorem rule39994 (p2027 p2132 p2252 p2579 p2655 p2750 p2753 p2870 p3016 p3246 p3359 p4022 p4625 : Prop) (h : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4625) ∨ (¬ p2252) ∨ (¬ p2132) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2655) ∨ (¬ p4022) ∨ (¬ p2870) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3016) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial39994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory29250 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule39994 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2579) (meaning t m 2655) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3016) (meaning t m 3246) (meaning t m 3359) (meaning t m 4022) (meaning t m 4625) source

theorem rule39996 (p2027 p2311 p2383 p2427 p3691 p4193 p4358 p4882 : Prop) (h : (¬ p4193) ∨ (¬ p3691) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4882) ∨ (¬ p2383) ∨ (¬ p2311) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2383) ∨ (¬ p2427) ∨ (¬ p3691) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial39996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory29252 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8)
  exact rule39996 (meaning t m 2027) (meaning t m 2311) (meaning t m 2383) (meaning t m 2427) (meaning t m 3691) (meaning t m 4193) (meaning t m 4358) (meaning t m 4882) source

theorem rule39997 (p2027 p2144 p2252 p2750 p2753 p2963 p3051 p3105 p3324 p4244 p4347 p4450 : Prop) (h : (¬ p2750) ∨ (¬ p4244) ∨ (¬ p2252) ∨ (¬ p2144) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4450) ∨ (¬ p4347) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p4244) ∨ (¬ p4347) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial39997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory29253 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule39997 (meaning t m 2027) (meaning t m 2144) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2963) (meaning t m 3051) (meaning t m 3105) (meaning t m 3324) (meaning t m 4244) (meaning t m 4347) (meaning t m 4450) source

theorem rule39998 (p2027 p2252 p2750 p2753 p2761 p2963 p3324 p3434 p3471 p5123 p5580 : Prop) (h : p2027 ∨ (¬ p3471) ∨ (¬ p2753) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p5580) ∨ (¬ p3434) ∨ (¬ p5123) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29254 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule39998 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2761) (meaning t m 2963) (meaning t m 3324) (meaning t m 3434) (meaning t m 3471) (meaning t m 5123) (meaning t m 5580) source

theorem rule39999 (p2027 p2249 p3038 p3292 p3707 p5284 p5363 : Prop) (h : (¬ p3038) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p5284) ∨ (¬ p5363) ∨ (¬ p3707)) : (p2027) ∨ (¬ p2249) ∨ (¬ p3038) ∨ (¬ p3292) ∨ (¬ p3707) ∨ (¬ p5284) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial39999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory29255 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 1 9) (m.theta 3 9) (m.theta 9 10)
  exact rule39999 (meaning t m 2027) (meaning t m 2249) (meaning t m 3038) (meaning t m 3292) (meaning t m 3707) (meaning t m 5284) (meaning t m 5363) source

theorem rule40000 (p2027 p2144 p2252 p2579 p2655 p2750 p2753 p3016 p3212 p3359 p3680 p4381 p4641 : Prop) (h : (¬ p4641) ∨ (¬ p2753) ∨ (¬ p3359) ∨ (¬ p3016) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p2579) ∨ (¬ p2750) ∨ (¬ p3680) ∨ (¬ p3212) ∨ (¬ p4381) ∨ (¬ p2144)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3016) ∨ (¬ p3212) ∨ (¬ p3359) ∨ (¬ p3680) ∨ (¬ p4381) ∨ (¬ p4641) := by
  classical
  tauto

theorem initial40000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4641)) := by
  have source := ElevenTheory.theory29256 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40000 (meaning t m 2027) (meaning t m 2144) (meaning t m 2252) (meaning t m 2579) (meaning t m 2655) (meaning t m 2750) (meaning t m 2753) (meaning t m 3016) (meaning t m 3212) (meaning t m 3359) (meaning t m 3680) (meaning t m 4381) (meaning t m 4641) source

theorem rule40002 (p2027 p2098 p2252 p2657 p2750 p2753 p3574 p3609 p3956 p4348 p4503 : Prop) (h : (¬ p2252) ∨ (¬ p4348) ∨ (¬ p2098) ∨ (¬ p3609) ∨ (¬ p4503) ∨ (¬ p3574) ∨ (¬ p2657) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3574) ∨ (¬ p3609) ∨ (¬ p3956) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29258 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40002 (meaning t m 2027) (meaning t m 2098) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3574) (meaning t m 3609) (meaning t m 3956) (meaning t m 4348) (meaning t m 4503) source

theorem rule40003 (p2027 p2241 p2707 p2750 p2761 p3434 p3591 p4435 p5254 : Prop) (h : (¬ p3591) ∨ (¬ p3434) ∨ (¬ p2761) ∨ (¬ p5254) ∨ (¬ p2750) ∨ (¬ p4435) ∨ (¬ p2707) ∨ (¬ p2241) ∨ p2027) : (p2027) ∨ (¬ p2241) ∨ (¬ p2707) ∨ (¬ p2750) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3591) ∨ (¬ p4435) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial40003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory29259 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40003 (meaning t m 2027) (meaning t m 2241) (meaning t m 2707) (meaning t m 2750) (meaning t m 2761) (meaning t m 3434) (meaning t m 3591) (meaning t m 4435) (meaning t m 5254) source

theorem rule40004 (p2027 p2144 p2252 p2619 p2657 p2750 p2753 p3051 p3574 p3956 p4042 p4244 p4503 : Prop) (h : p2027 ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p3574) ∨ (¬ p4503) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p2144) ∨ (¬ p3956) ∨ (¬ p3051) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2252) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3051) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29260 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule40004 (meaning t m 2027) (meaning t m 2144) (meaning t m 2252) (meaning t m 2619) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3051) (meaning t m 3574) (meaning t m 3956) (meaning t m 4042) (meaning t m 4244) (meaning t m 4503) source

theorem rule40005 (p2027 p2146 p3051 p3246 p4136 p4324 : Prop) (h : (¬ p3051) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p2146) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2146) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial40005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory29261 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule40005 (meaning t m 2027) (meaning t m 2146) (meaning t m 3051) (meaning t m 3246) (meaning t m 4136) (meaning t m 4324) source

theorem rule40006 (p1991 p2027 p2352 p2588 p2963 p2997 p3324 : Prop) (h : p2997 ∨ (¬ p1991) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2352) ∨ (¬ p2963) ∨ (¬ p3324)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial40006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory29262 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule40006 (meaning t m 1991) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2963) (meaning t m 2997) (meaning t m 3324) source

theorem rule40007 (p2027 p2252 p2534 p2657 p2750 p3599 p3670 p3950 p4256 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p2534) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3599) ∨ (¬ p3670)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3599) ∨ (¬ p3670) ∨ (¬ p3950) ∨ (¬ p4256) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial40007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory29263 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 9) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40007 (meaning t m 2027) (meaning t m 2252) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 3599) (meaning t m 3670) (meaning t m 3950) (meaning t m 4256) (meaning t m 4381) source

theorem rule40008 (p2027 p2144 p2657 p3212 p3574 p3680 p4137 p4789 p5267 p5387 : Prop) (h : (¬ p4789) ∨ (¬ p3574) ∨ (¬ p2657) ∨ (¬ p5267) ∨ (¬ p2144) ∨ (¬ p5387) ∨ (¬ p3212) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p3680)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3574) ∨ (¬ p3680) ∨ (¬ p4137) ∨ (¬ p4789) ∨ (¬ p5267) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial40008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5267)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory29264 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 9) (m.theta 3 4) (m.theta 4 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule40008 (meaning t m 2027) (meaning t m 2144) (meaning t m 2657) (meaning t m 3212) (meaning t m 3574) (meaning t m 3680) (meaning t m 4137) (meaning t m 4789) (meaning t m 5267) (meaning t m 5387) source

theorem rule40011 (p2027 p2657 p2761 p3051 p3246 p3366 p3370 p3574 p4236 p4377 p5254 p5514 : Prop) (h : (¬ p3246) ∨ (¬ p4236) ∨ (¬ p3574) ∨ (¬ p3366) ∨ (¬ p2657) ∨ (¬ p3370) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p5254) ∨ (¬ p4377) ∨ (¬ p5514)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3574) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial40011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory29267 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40011 (meaning t m 2027) (meaning t m 2657) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 3366) (meaning t m 3370) (meaning t m 3574) (meaning t m 4236) (meaning t m 4377) (meaning t m 5254) (meaning t m 5514) source

theorem rule40012 (p1988 p2027 p2388 p2761 p2797 p3051 p3246 p3370 p3953 p4228 p4315 p4377 p4435 : Prop) (h : (¬ p3246) ∨ (¬ p3953) ∨ (¬ p4435) ∨ (¬ p4377) ∨ (¬ p1988) ∨ (¬ p3370) ∨ (¬ p2761) ∨ (¬ p4228) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4315) ∨ p2388) : (¬ p1988) ∨ (p2027) ∨ (p2388) ∨ (¬ p2761) ∨ (¬ p2797) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p3953) ∨ (¬ p4228) ∨ (¬ p4315) ∨ (¬ p4377) ∨ (¬ p4435) := by
  classical
  tauto

theorem initial40012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4435)) := by
  have source := ElevenTheory.theory29268 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40012 (meaning t m 1988) (meaning t m 2027) (meaning t m 2388) (meaning t m 2761) (meaning t m 2797) (meaning t m 3051) (meaning t m 3246) (meaning t m 3370) (meaning t m 3953) (meaning t m 4228) (meaning t m 4315) (meaning t m 4377) (meaning t m 4435) source

theorem rule40013 (p2027 p2657 p3246 p3366 p3399 p3555 p3571 p3574 p4137 p4236 p4377 p4625 : Prop) (h : p2027 ∨ (¬ p3366) ∨ (¬ p2657) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4377) ∨ (¬ p4236) ∨ (¬ p3555) ∨ (¬ p3246) ∨ (¬ p3571) ∨ (¬ p4625) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2657) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial40013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory29269 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule40013 (meaning t m 2027) (meaning t m 2657) (meaning t m 3246) (meaning t m 3366) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) (meaning t m 3574) (meaning t m 4137) (meaning t m 4236) (meaning t m 4377) (meaning t m 4625) source

theorem rule40017 (p2027 p2657 p2761 p3434 p3471 p3574 p4789 p5254 p5514 : Prop) (h : (¬ p2657) ∨ (¬ p4789) ∨ (¬ p5254) ∨ (¬ p5514) ∨ (¬ p3471) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3574) ∨ (¬ p4789) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial40017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory29273 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40017 (meaning t m 2027) (meaning t m 2657) (meaning t m 2761) (meaning t m 3434) (meaning t m 3471) (meaning t m 3574) (meaning t m 4789) (meaning t m 5254) (meaning t m 5514) source

theorem rule40018 (p1976 p2027 p2202 p2440 p2528 p3083 p3324 p3365 p4195 p4348 p4503 : Prop) (h : (¬ p2440) ∨ p2202 ∨ (¬ p3365) ∨ (¬ p1976) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p3324) ∨ (¬ p2528) ∨ (¬ p3083)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29274 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40018 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2528) (meaning t m 3083) (meaning t m 3324) (meaning t m 3365) (meaning t m 4195) (meaning t m 4348) (meaning t m 4503) source

theorem rule40019 (p1976 p2027 p2202 p2440 p2528 p3324 p3365 p3641 p4195 p4343 p4348 p4503 : Prop) (h : (¬ p2440) ∨ p2202 ∨ (¬ p1976) ∨ (¬ p4343) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2528) ∨ (¬ p4195) ∨ (¬ p4503) ∨ (¬ p3324) ∨ (¬ p3641)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3641) ∨ (¬ p4195) ∨ (¬ p4343) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29275 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40019 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2528) (meaning t m 3324) (meaning t m 3365) (meaning t m 3641) (meaning t m 4195) (meaning t m 4343) (meaning t m 4348) (meaning t m 4503) source

theorem rule40021 (p2027 p2761 p3073 p3365 p3449 p4195 p4445 p4736 p5254 p5717 : Prop) (h : (¬ p4445) ∨ (¬ p3073) ∨ (¬ p5254) ∨ (¬ p3449) ∨ (¬ p4195) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p5717) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3449) ∨ (¬ p4195) ∨ (¬ p4445) ∨ (¬ p4736) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial40021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory29277 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 6 10) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40021 (meaning t m 2027) (meaning t m 2761) (meaning t m 3073) (meaning t m 3365) (meaning t m 3449) (meaning t m 4195) (meaning t m 4445) (meaning t m 4736) (meaning t m 5254) (meaning t m 5717) source

theorem rule40026 (p1976 p2027 p2528 p2630 p2657 p3498 p4236 p4340 p4364 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p2630) ∨ (¬ p4236) ∨ (¬ p2657) ∨ (¬ p4364) ∨ (¬ p2528) ∨ p3498 ∨ (¬ p4340)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p3498) ∨ (¬ p4236) ∨ (¬ p4340) ∨ (¬ p4364) := by
  classical
  tauto

theorem initial40026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) := by
  have source := ElevenTheory.theory29282 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule40026 (meaning t m 1976) (meaning t m 2027) (meaning t m 2528) (meaning t m 2630) (meaning t m 2657) (meaning t m 3498) (meaning t m 4236) (meaning t m 4340) (meaning t m 4364) source

theorem rule40031 (p1982 p2027 p2363 p2641 p2688 p3567 p3998 p4114 p5580 : Prop) (h : (¬ p4114) ∨ (¬ p1982) ∨ (¬ p3567) ∨ p2688 ∨ (¬ p2363) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p3998) ∨ (¬ p5580)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p3567) ∨ (¬ p3998) ∨ (¬ p4114) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial40031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29287 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40031 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2641) (meaning t m 2688) (meaning t m 3567) (meaning t m 3998) (meaning t m 4114) (meaning t m 5580) source

theorem rule40033 (p2573 p3346 p4422 : Prop) (h : (¬ p4422) ∨ (¬ p2573) ∨ (¬ p3346)) : (¬ p2573) ∨ (¬ p3346) ∨ (¬ p4422) := by
  classical
  tauto

theorem initial40033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4422)) := by
  have source := ElevenTheory.theory29289 (m.theta 0 4) (m.theta 4 6) (m.theta 4 9)
  exact rule40033 (meaning t m 2573) (meaning t m 3346) (meaning t m 4422) source

theorem rule40035 (p2027 p2252 p2598 p2750 p2753 p3414 p3422 p3553 p3564 p4330 p4348 : Prop) (h : (¬ p2750) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p2753) ∨ (¬ p2598) ∨ (¬ p3564) ∨ (¬ p4348) ∨ (¬ p3553) ∨ (¬ p2252) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3414) ∨ (¬ p3422) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial40035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory29291 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40035 (meaning t m 2027) (meaning t m 2252) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3414) (meaning t m 3422) (meaning t m 3553) (meaning t m 3564) (meaning t m 4330) (meaning t m 4348) source

theorem rule40036 (p2027 p2952 p3362 p3389 p3641 p3876 p3952 p3989 p4596 p4789 : Prop) (h : (¬ p3641) ∨ (¬ p4596) ∨ (¬ p2952) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p3362) ∨ (¬ p3876) ∨ (¬ p3389) ∨ (¬ p4789)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4596) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29292 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule40036 (meaning t m 2027) (meaning t m 2952) (meaning t m 3362) (meaning t m 3389) (meaning t m 3641) (meaning t m 3876) (meaning t m 3952) (meaning t m 3989) (meaning t m 4596) (meaning t m 4789) source

theorem rule40037 (p1998 p2027 p2177 p2553 p2573 p2656 p2688 p2727 : Prop) (h : (¬ p2177) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2656) ∨ (¬ p2553) ∨ p2688 ∨ (¬ p2573) ∨ (¬ p2727)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial40037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory29293 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule40037 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) source

theorem rule40041 (p2027 p2249 p2553 p2573 p2656 p2727 p2881 p3414 p3553 p4559 : Prop) (h : (¬ p2573) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p2881) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2553) ∨ (¬ p3414) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2881) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial40041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory29297 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule40041 (meaning t m 2027) (meaning t m 2249) (meaning t m 2553) (meaning t m 2573) (meaning t m 2656) (meaning t m 2727) (meaning t m 2881) (meaning t m 3414) (meaning t m 3553) (meaning t m 4559) source

theorem rule40042 (p3369 p4108 p4399 : Prop) (h : (¬ p3369) ∨ (¬ p4399) ∨ p4108) : (¬ p3369) ∨ (p4108) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial40042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3369)) ∨ (meaning t m 4108) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory29298 (m.theta 0 1) (m.theta 0 4) (m.theta 0 5)
  exact rule40042 (meaning t m 3369) (meaning t m 4108) (meaning t m 4399) source

theorem rule40047 (p1975 p2027 p2553 p2657 p2688 p2727 p3005 p3361 p3573 p4346 : Prop) (h : (¬ p2727) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p1975) ∨ (¬ p2657) ∨ (¬ p2553) ∨ p2688 ∨ (¬ p3361) ∨ (¬ p4346) ∨ (¬ p3573)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3005) ∨ (¬ p3361) ∨ (¬ p3573) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial40047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory29303 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule40047 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3005) (meaning t m 3361) (meaning t m 3573) (meaning t m 4346) source

theorem rule40048 (p1982 p2027 p2363 p2545 p2641 p2668 p4111 : Prop) (h : p2545 ∨ (¬ p4111) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial40048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory29304 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule40048 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2545) (meaning t m 2641) (meaning t m 2668) (meaning t m 4111) source

theorem rule40049 (p2027 p2166 p2241 p2750 p3369 p3371 p4120 : Prop) (h : p2027 ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p3371) ∨ (¬ p2166) ∨ (¬ p4120) ∨ (¬ p3369)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3369) ∨ (¬ p3371) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial40049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory29305 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 8)
  exact rule40049 (meaning t m 2027) (meaning t m 2166) (meaning t m 2241) (meaning t m 2750) (meaning t m 3369) (meaning t m 3371) (meaning t m 4120) source

theorem rule40050 (p1975 p2027 p2545 p2553 p3343 p3422 p5160 : Prop) (h : (¬ p3422) ∨ (¬ p1975) ∨ p2027 ∨ p2545 ∨ (¬ p3343) ∨ (¬ p2553) ∨ (¬ p5160)) : (¬ p1975) ∨ (p2027) ∨ (p2545) ∨ (¬ p2553) ∨ (¬ p3343) ∨ (¬ p3422) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial40050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory29306 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7)
  exact rule40050 (meaning t m 1975) (meaning t m 2027) (meaning t m 2545) (meaning t m 2553) (meaning t m 3343) (meaning t m 3422) (meaning t m 5160) source

theorem rule40051 (p2027 p2657 p2727 p2751 p2807 p3572 : Prop) (h : (¬ p3572) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2751) ∨ (¬ p2657) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p2807) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial40051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory29307 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule40051 (meaning t m 2027) (meaning t m 2657) (meaning t m 2727) (meaning t m 2751) (meaning t m 2807) (meaning t m 3572) source

theorem rule40052 (p1975 p2027 p2230 p2274 p2563 p2656 p2688 p2727 : Prop) (h : (¬ p1975) ∨ (¬ p2563) ∨ (¬ p2274) ∨ (¬ p2230) ∨ (¬ p2656) ∨ p2688 ∨ (¬ p2727) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial40052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory29308 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule40052 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2563) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) source

theorem rule40054 (p2027 p2191 p2573 p2656 p2727 p2751 p3564 p3692 p4282 p4315 p4330 : Prop) (h : (¬ p2573) ∨ (¬ p2727) ∨ (¬ p3692) ∨ (¬ p3564) ∨ (¬ p2751) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p4282) ∨ (¬ p4330) ∨ (¬ p2191) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4282) ∨ (¬ p4315) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial40054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory29310 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40054 (meaning t m 2027) (meaning t m 2191) (meaning t m 2573) (meaning t m 2656) (meaning t m 2727) (meaning t m 2751) (meaning t m 3564) (meaning t m 3692) (meaning t m 4282) (meaning t m 4315) (meaning t m 4330) source

theorem rule40055 (p2027 p2191 p2598 p3422 p3555 p3564 p3692 p4330 p4733 : Prop) (h : (¬ p3555) ∨ (¬ p4733) ∨ (¬ p4330) ∨ (¬ p2598) ∨ (¬ p3692) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3555) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29311 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40055 (meaning t m 2027) (meaning t m 2191) (meaning t m 2598) (meaning t m 3422) (meaning t m 3555) (meaning t m 3564) (meaning t m 3692) (meaning t m 4330) (meaning t m 4733) source

theorem rule40056 (p2027 p2598 p2952 p3276 p3333 p3497 p4789 p5123 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p4789) ∨ (¬ p3333) ∨ (¬ p3276) ∨ (¬ p5123) ∨ (¬ p3497) ∨ (¬ p2598) ∨ (¬ p2952) ∨ p2027) : (p2027) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3497) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial40056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory29312 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40056 (meaning t m 2027) (meaning t m 2598) (meaning t m 2952) (meaning t m 3276) (meaning t m 3333) (meaning t m 3497) (meaning t m 4789) (meaning t m 5123) (meaning t m 5568) source

theorem rule40057 (p1988 p2027 p2573 p2656 p2688 p2727 p3461 p3564 : Prop) (h : (¬ p2656) ∨ (¬ p2573) ∨ (¬ p2727) ∨ (¬ p1988) ∨ p2027 ∨ p2688 ∨ (¬ p3564) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3461) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial40057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory29313 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule40057 (meaning t m 1988) (meaning t m 2027) (meaning t m 2573) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3461) (meaning t m 3564) source

theorem rule40058 (p2027 p2963 p3276 p3355 p3362 p3568 p4107 p4322 p4395 p4789 : Prop) (h : p2027 ∨ (¬ p4107) ∨ (¬ p3568) ∨ (¬ p4322) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p4789) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4395)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29314 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule40058 (meaning t m 2027) (meaning t m 2963) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3568) (meaning t m 4107) (meaning t m 4322) (meaning t m 4395) (meaning t m 4789) source

theorem rule40059 (p2027 p2230 p3333 p3362 p3414 p3553 p3684 p4332 p4348 p4789 : Prop) (h : (¬ p3684) ∨ (¬ p3553) ∨ (¬ p3414) ∨ (¬ p4332) ∨ (¬ p4789) ∨ (¬ p2230) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p4348) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29315 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40059 (meaning t m 2027) (meaning t m 2230) (meaning t m 3333) (meaning t m 3362) (meaning t m 3414) (meaning t m 3553) (meaning t m 3684) (meaning t m 4332) (meaning t m 4348) (meaning t m 4789) source

theorem rule40060 (p2027 p2230 p2753 p2963 p2982 p3324 p3519 p3680 p4236 p4376 p5123 p5580 : Prop) (h : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3519) ∨ (¬ p4236) ∨ (¬ p3324) ∨ (¬ p4376) ∨ (¬ p3680) ∨ (¬ p5580) ∨ p2753 ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2230) ∨ (p2753) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial40060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2753) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29316 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40060 (meaning t m 2027) (meaning t m 2230) (meaning t m 2753) (meaning t m 2963) (meaning t m 2982) (meaning t m 3324) (meaning t m 3519) (meaning t m 3680) (meaning t m 4236) (meaning t m 4376) (meaning t m 5123) (meaning t m 5580) source

theorem rule40062 (p1975 p2027 p2230 p2299 p2563 p2766 p2881 p3365 p3872 p3877 p4118 p4419 : Prop) (h : (¬ p2563) ∨ p2766 ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3365) ∨ (¬ p4419) ∨ (¬ p4118) ∨ (¬ p3877) ∨ (¬ p2881) ∨ (¬ p2299) ∨ (¬ p3872)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2563) ∨ (p2766) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p3872) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial40062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory29318 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule40062 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2563) (meaning t m 2766) (meaning t m 2881) (meaning t m 3365) (meaning t m 3872) (meaning t m 3877) (meaning t m 4118) (meaning t m 4419) source

theorem rule40063 (p2027 p2241 p2598 p2750 p2753 p3422 p3564 p3860 p4261 p4330 : Prop) (h : (¬ p2598) ∨ (¬ p3860) ∨ (¬ p2750) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4261) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial40063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory29319 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule40063 (meaning t m 2027) (meaning t m 2241) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3422) (meaning t m 3564) (meaning t m 3860) (meaning t m 4261) (meaning t m 4330) source

theorem rule40065 (p2027 p2088 p2534 p2553 p3573 p4170 p4501 : Prop) (h : (¬ p2553) ∨ (¬ p3573) ∨ (¬ p4170) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2534) ∨ (¬ p2553) ∨ (¬ p3573) ∨ (¬ p4170) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial40065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory29321 t (m.theta 0 8) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule40065 (meaning t m 2027) (meaning t m 2088) (meaning t m 2534) (meaning t m 2553) (meaning t m 3573) (meaning t m 4170) (meaning t m 4501) source

theorem rule40068 (p2027 p3365 p3366 p3399 p3452 p4035 p4075 p4376 p4826 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p4826) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3365) ∨ (¬ p4035)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4035) ∨ (¬ p4075) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29324 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 9) (m.theta 7 10) (m.theta 9 10)
  exact rule40068 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 4035) (meaning t m 4075) (meaning t m 4376) (meaning t m 4826) (meaning t m 5284) source

theorem rule40073 (p2027 p2891 p2957 p3556 p4111 p4365 p4704 : Prop) (h : (¬ p2957) ∨ (¬ p4365) ∨ (¬ p3556) ∨ (¬ p4704) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4111)) : (p2027) ∨ (¬ p2891) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4111) ∨ (¬ p4365) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial40073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory29329 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule40073 (meaning t m 2027) (meaning t m 2891) (meaning t m 2957) (meaning t m 3556) (meaning t m 4111) (meaning t m 4365) (meaning t m 4704) source

theorem rule40075 (p2027 p2249 p3414 p3631 p3947 p4365 p4431 : Prop) (h : (¬ p4365) ∨ (¬ p2249) ∨ (¬ p3947) ∨ (¬ p4431) ∨ (¬ p3631) ∨ (¬ p3414) ∨ p2027) : (p2027) ∨ (¬ p2249) ∨ (¬ p3414) ∨ (¬ p3631) ∨ (¬ p3947) ∨ (¬ p4365) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial40075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory29331 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 3 7) (m.theta 7 9)
  exact rule40075 (meaning t m 2027) (meaning t m 2249) (meaning t m 3414) (meaning t m 3631) (meaning t m 3947) (meaning t m 4365) (meaning t m 4431) source

theorem rule40076 (p2027 p2230 p2563 p3125 p3366 p3425 p3519 p3659 p4330 p4348 p4376 : Prop) (h : (¬ p4348) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p3659) ∨ (¬ p3366) ∨ (¬ p3125) ∨ (¬ p2563) ∨ (¬ p4376) ∨ (¬ p2230) ∨ (¬ p4330)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3519) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29332 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40076 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 3125) (meaning t m 3366) (meaning t m 3425) (meaning t m 3519) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) (meaning t m 4376) source

theorem rule40078 (p2027 p2307 p2352 p2588 p3292 p3366 p3755 p3877 p4236 p4774 p4866 p5016 : Prop) (h : (¬ p3877) ∨ (¬ p5016) ∨ (¬ p2588) ∨ (¬ p4774) ∨ (¬ p4866) ∨ (¬ p2352) ∨ (¬ p3366) ∨ (¬ p2307) ∨ (¬ p4236) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p3755)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4774) ∨ (¬ p4866) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial40078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4774)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory29334 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule40078 (meaning t m 2027) (meaning t m 2307) (meaning t m 2352) (meaning t m 2588) (meaning t m 3292) (meaning t m 3366) (meaning t m 3755) (meaning t m 3877) (meaning t m 4236) (meaning t m 4774) (meaning t m 4866) (meaning t m 5016) source

theorem rule40080 (p1985 p2027 p2383 p2427 p2590 p2688 p2727 p3019 p3567 p3956 : Prop) (h : (¬ p2427) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2590) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p3019) ∨ (¬ p3567) ∨ (¬ p1985) ∨ (¬ p3956)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2427) ∨ (¬ p2590) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3019) ∨ (¬ p3567) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial40080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2590)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory29336 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8)
  exact rule40080 (meaning t m 1985) (meaning t m 2027) (meaning t m 2383) (meaning t m 2427) (meaning t m 2590) (meaning t m 2688) (meaning t m 2727) (meaning t m 3019) (meaning t m 3567) (meaning t m 3956) source

theorem rule40081 (p2027 p2104 p2230 p2427 p2881 p3256 p3366 p3519 p4041 p4340 p4376 : Prop) (h : (¬ p4041) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p4376) ∨ (¬ p2104) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3256) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4041) ∨ (¬ p4340) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29337 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule40081 (meaning t m 2027) (meaning t m 2104) (meaning t m 2230) (meaning t m 2427) (meaning t m 2881) (meaning t m 3256) (meaning t m 3366) (meaning t m 3519) (meaning t m 4041) (meaning t m 4340) (meaning t m 4376) source

theorem rule40082 (p2027 p2230 p2427 p2797 p2881 p2963 p3366 p3519 p3877 p4041 p4236 p4376 : Prop) (h : (¬ p2230) ∨ (¬ p2881) ∨ (¬ p4236) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p4041) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3877) ∨ (¬ p2963) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2797) ∨ (¬ p2881) ∨ (¬ p2963) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29338 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule40082 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2797) (meaning t m 2881) (meaning t m 2963) (meaning t m 3366) (meaning t m 3519) (meaning t m 3877) (meaning t m 4041) (meaning t m 4236) (meaning t m 4376) source

theorem rule40083 (p2027 p2295 p2750 p2753 p3276 p3355 p3362 p3549 p4037 p4245 p4322 p4397 : Prop) (h : (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4245) ∨ (¬ p4397) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2295) ∨ (¬ p3549) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3549) ∨ (¬ p4037) ∨ (¬ p4245) ∨ (¬ p4322) ∨ (¬ p4397) := by
  classical
  tauto

theorem initial40083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4397)) := by
  have source := ElevenTheory.theory29339 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule40083 (meaning t m 2027) (meaning t m 2295) (meaning t m 2750) (meaning t m 2753) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3549) (meaning t m 4037) (meaning t m 4245) (meaning t m 4322) (meaning t m 4397) source

theorem rule40089 (p2027 p2573 p2656 p2727 p2751 p3364 p3584 : Prop) (h : (¬ p3364) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p2751) ∨ (¬ p2727) ∨ (¬ p3584) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial40089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory29345 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule40089 (meaning t m 2027) (meaning t m 2573) (meaning t m 2656) (meaning t m 2727) (meaning t m 2751) (meaning t m 3364) (meaning t m 3584) source

theorem rule40091 (p2027 p2230 p2982 p3366 p3425 p3519 p3659 p3680 p4376 p5123 p5558 : Prop) (h : (¬ p3519) ∨ (¬ p3425) ∨ (¬ p5123) ∨ (¬ p3366) ∨ (¬ p3659) ∨ (¬ p4376) ∨ (¬ p2230) ∨ (¬ p5558) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p3680)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3519) ∨ (¬ p3659) ∨ (¬ p3680) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial40091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29347 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40091 (meaning t m 2027) (meaning t m 2230) (meaning t m 2982) (meaning t m 3366) (meaning t m 3425) (meaning t m 3519) (meaning t m 3659) (meaning t m 3680) (meaning t m 4376) (meaning t m 5123) (meaning t m 5558) source

theorem rule40092 (p2027 p2780 p3366 p3449 p3452 p3969 p4347 p4358 p4376 p4446 p5122 : Prop) (h : p2027 ∨ (¬ p4347) ∨ (¬ p3366) ∨ (¬ p4358) ∨ (¬ p5122) ∨ (¬ p4446) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4376) ∨ (¬ p2780) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4376) ∨ (¬ p4446) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29348 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40092 (meaning t m 2027) (meaning t m 2780) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 3969) (meaning t m 4347) (meaning t m 4358) (meaning t m 4376) (meaning t m 4446) (meaning t m 5122) source

theorem rule40094 (p2027 p2132 p2252 p2750 p2753 p2860 p3125 p3414 p3553 p4330 p4348 : Prop) (h : (¬ p2252) ∨ (¬ p4348) ∨ (¬ p4330) ∨ (¬ p3553) ∨ (¬ p3125) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2750) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial40094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory29350 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40094 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2860) (meaning t m 3125) (meaning t m 3414) (meaning t m 3553) (meaning t m 4330) (meaning t m 4348) source

theorem rule40098 (p2027 p2132 p2264 p2860 p3125 p3551 p3947 p4621 p4789 p4849 : Prop) (h : (¬ p4621) ∨ (¬ p3125) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p4849) ∨ (¬ p4789) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2264) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3551) ∨ (¬ p3947) ∨ (¬ p4621) ∨ (¬ p4789) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial40098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory29354 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40098 (meaning t m 2027) (meaning t m 2132) (meaning t m 2264) (meaning t m 2860) (meaning t m 3125) (meaning t m 3551) (meaning t m 3947) (meaning t m 4621) (meaning t m 4789) (meaning t m 4849) source

theorem rule40099 (p2027 p2264 p3201 p3874 p4383 p4653 : Prop) (h : (¬ p3201) ∨ (¬ p2264) ∨ (¬ p4653) ∨ p2027 ∨ (¬ p4383) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p4383) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial40099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory29355 t (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule40099 (meaning t m 2027) (meaning t m 2264) (meaning t m 3201) (meaning t m 3874) (meaning t m 4383) (meaning t m 4653) source

theorem rule40104 (p1997 p2027 p2611 p2860 p3362 p3389 p3582 p3876 p4110 : Prop) (h : (¬ p3362) ∨ p2611 ∨ (¬ p1997) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p2860) ∨ (¬ p4110) ∨ (¬ p3582)) : (¬ p1997) ∨ (p2027) ∨ (p2611) ∨ (¬ p2860) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3582) ∨ (¬ p3876) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial40104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory29360 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule40104 (meaning t m 1997) (meaning t m 2027) (meaning t m 2611) (meaning t m 2860) (meaning t m 3362) (meaning t m 3389) (meaning t m 3582) (meaning t m 3876) (meaning t m 4110) source

theorem rule40106 (p2027 p2230 p2427 p2753 p3609 p4129 p4261 p4419 p4436 p4963 p5560 p5600 : Prop) (h : (¬ p4261) ∨ (¬ p4419) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3609) ∨ (¬ p5600) ∨ (¬ p2427) ∨ (¬ p4129) ∨ (¬ p5560) ∨ (¬ p4963) ∨ (¬ p4436)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p4129) ∨ (¬ p4261) ∨ (¬ p4419) ∨ (¬ p4436) ∨ (¬ p4963) ∨ (¬ p5560) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial40106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 4963)) ∨ (¬ (meaning t m 5560)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory29362 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 8) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 10) (m.theta 8 9)
  exact rule40106 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2753) (meaning t m 3609) (meaning t m 4129) (meaning t m 4261) (meaning t m 4419) (meaning t m 4436) (meaning t m 4963) (meaning t m 5560) (meaning t m 5600) source

theorem rule40108 (p1998 p2027 p2177 p2553 p2765 p3125 p4137 : Prop) (h : p2765 ∨ (¬ p2177) ∨ (¬ p1998) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p4137)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial40108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory29364 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule40108 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2765) (meaning t m 3125) (meaning t m 4137) source

theorem rule40109 (p2027 p2230 p2241 p2750 p2753 p3105 p3362 p3680 p3698 p3860 p5123 p5693 : Prop) (h : (¬ p3105) ∨ (¬ p3698) ∨ (¬ p2230) ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3680) ∨ (¬ p2753) ∨ (¬ p3860) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3362) ∨ (¬ p3680) ∨ (¬ p3698) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial40109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory29365 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 4 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40109 (meaning t m 2027) (meaning t m 2230) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3105) (meaning t m 3362) (meaning t m 3680) (meaning t m 3698) (meaning t m 3860) (meaning t m 5123) (meaning t m 5693) source

theorem rule40111 (p2027 p2139 p2156 p2982 p3425 p3659 p4110 p4348 p4450 : Prop) (h : (¬ p4348) ∨ (¬ p2139) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p4450) ∨ (¬ p3425) ∨ (¬ p2982) ∨ (¬ p2156) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4110) ∨ (¬ p4348) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial40111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory29367 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40111 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2982) (meaning t m 3425) (meaning t m 3659) (meaning t m 4110) (meaning t m 4348) (meaning t m 4450) source

theorem rule40113 (p2027 p2249 p2963 p2992 p3506 p3549 p3922 p4107 p4322 p4395 p5038 : Prop) (h : (¬ p5038) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p3506) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p3549) ∨ (¬ p2963) ∨ (¬ p4107) ∨ (¬ p3922)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3506) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p5038) := by
  classical
  tauto

theorem initial40113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5038)) := by
  have source := ElevenTheory.theory29369 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 3 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule40113 (meaning t m 2027) (meaning t m 2249) (meaning t m 2963) (meaning t m 2992) (meaning t m 3506) (meaning t m 3549) (meaning t m 3922) (meaning t m 4107) (meaning t m 4322) (meaning t m 4395) (meaning t m 5038) source

theorem rule40114 (p2027 p2307 p2588 p3365 p3366 p3888 p4035 p4866 p5016 p5250 p5284 : Prop) (h : (¬ p4035) ∨ (¬ p2307) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p5250) ∨ (¬ p5016) ∨ (¬ p2588) ∨ (¬ p3888) ∨ (¬ p4866) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3888) ∨ (¬ p4035) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p5250) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5250)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29370 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 10) (m.theta 6 7) (m.theta 9 10)
  exact rule40114 (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 3365) (meaning t m 3366) (meaning t m 3888) (meaning t m 4035) (meaning t m 4866) (meaning t m 5016) (meaning t m 5250) (meaning t m 5284) source

theorem rule40119 (p2027 p2264 p2598 p3422 p3551 p3564 p3947 p4621 p4789 p4849 : Prop) (h : (¬ p4621) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4849) ∨ (¬ p3551) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4789) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p3947) ∨ (¬ p4621) ∨ (¬ p4789) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial40119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory29375 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40119 (meaning t m 2027) (meaning t m 2264) (meaning t m 2598) (meaning t m 3422) (meaning t m 3551) (meaning t m 3564) (meaning t m 3947) (meaning t m 4621) (meaning t m 4789) (meaning t m 4849) source

theorem rule40120 (p2027 p2230 p2252 p2750 p2753 p3266 p3292 p3333 p3362 p3684 p4332 p5284 : Prop) (h : p2027 ∨ (¬ p3362) ∨ (¬ p3333) ∨ (¬ p2230) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p2252) ∨ (¬ p3292) ∨ (¬ p3266) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29376 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40120 (meaning t m 2027) (meaning t m 2230) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 3266) (meaning t m 3292) (meaning t m 3333) (meaning t m 3362) (meaning t m 3684) (meaning t m 4332) (meaning t m 5284) source

theorem rule40122 (p1977 p2027 p2241 p2462 p3527 p3551 p3817 p5206 : Prop) (h : (¬ p1977) ∨ (¬ p5206) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p3527) ∨ p2462 ∨ (¬ p3817) ∨ (¬ p2241)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2462) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3817) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial40122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory29378 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 7 8) (m.theta 7 9)
  exact rule40122 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2462) (meaning t m 3527) (meaning t m 3551) (meaning t m 3817) (meaning t m 5206) source

theorem rule40125 (p2027 p2230 p2427 p3246 p3365 p3366 p3519 p3877 p3950 p4118 p4376 : Prop) (h : (¬ p3519) ∨ (¬ p4118) ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p3246) ∨ (¬ p2427) ∨ (¬ p3366) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29381 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40125 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 3246) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4376) source

theorem rule40132 (p2027 p2139 p2156 p2685 p3096 p3276 p3414 p4035 p4191 p4236 p4422 p5279 : Prop) (h : (¬ p3276) ∨ (¬ p5279) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p2156) ∨ (¬ p4191) ∨ (¬ p3096) ∨ (¬ p4422) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2685) ∨ (¬ p3096) ∨ (¬ p3276) ∨ (¬ p3414) ∨ (¬ p4035) ∨ (¬ p4191) ∨ (¬ p4236) ∨ (¬ p4422) ∨ (¬ p5279) := by
  classical
  tauto

theorem initial40132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 5279)) := by
  have source := ElevenTheory.theory29388 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule40132 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2685) (meaning t m 3096) (meaning t m 3276) (meaning t m 3414) (meaning t m 4035) (meaning t m 4191) (meaning t m 4236) (meaning t m 4422) (meaning t m 5279) source

theorem rule40137 (p4238 p4590 p4988 : Prop) (h : (¬ p4590) ∨ (¬ p4988) ∨ p4238) : (p4238) ∨ (¬ p4590) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial40137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4238) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory29393 (m.theta 0 5) (m.theta 0 7) (m.theta 0 8)
  exact rule40137 (meaning t m 4238) (meaning t m 4590) (meaning t m 4988) source

theorem rule40139 (p2005 p2027 p2230 p2964 p3346 p3422 p3684 : Prop) (h : (¬ p3346) ∨ p2964 ∨ (¬ p2005) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p2230)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (p2964) ∨ (¬ p3346) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial40139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory29395 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule40139 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2964) (meaning t m 3346) (meaning t m 3422) (meaning t m 3684) source

theorem rule40142 (p2027 p2598 p3172 p3422 p3888 p4118 p4444 p4789 p5250 : Prop) (h : (¬ p4118) ∨ (¬ p4789) ∨ (¬ p3888) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p4444) ∨ (¬ p5250)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3172) ∨ (¬ p3422) ∨ (¬ p3888) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial40142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory29398 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule40142 (meaning t m 2027) (meaning t m 2598) (meaning t m 3172) (meaning t m 3422) (meaning t m 3888) (meaning t m 4118) (meaning t m 4444) (meaning t m 4789) (meaning t m 5250) source

theorem rule40143 (p2027 p2668 p2954 p3646 p3989 p4336 : Prop) (h : (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4336) ∨ (¬ p2668) ∨ p2027) : (p2027) ∨ (¬ p2668) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial40143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory29399 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule40143 (meaning t m 2027) (meaning t m 2668) (meaning t m 2954) (meaning t m 3646) (meaning t m 3989) (meaning t m 4336) source

theorem rule40144 (p2027 p2396 p2553 p2573 p3365 p3877 p3950 p4118 p4419 : Prop) (h : (¬ p4419) ∨ (¬ p4118) ∨ (¬ p3365) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p2553) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial40144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory29400 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule40144 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3365) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4419) source

theorem rule40149 (p2027 p2230 p2870 p2963 p3246 p3324 p3362 p3698 p3950 p4347 p4789 : Prop) (h : (¬ p3950) ∨ (¬ p4347) ∨ (¬ p2963) ∨ (¬ p2870) ∨ (¬ p3362) ∨ (¬ p3246) ∨ (¬ p2230) ∨ (¬ p3698) ∨ (¬ p4789) ∨ (¬ p3324) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29405 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40149 (meaning t m 2027) (meaning t m 2230) (meaning t m 2870) (meaning t m 2963) (meaning t m 3246) (meaning t m 3324) (meaning t m 3362) (meaning t m 3698) (meaning t m 3950) (meaning t m 4347) (meaning t m 4789) source

theorem rule40150 (p2027 p2139 p2156 p3096 p3425 p3461 p3564 p3659 p5123 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p2156) ∨ (¬ p5123) ∨ (¬ p2139) ∨ (¬ p3096) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3564)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3096) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3659) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial40150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory29406 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40150 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 3096) (meaning t m 3425) (meaning t m 3461) (meaning t m 3564) (meaning t m 3659) (meaning t m 5123) (meaning t m 5558) source

theorem rule40154 (p2027 p3822 p4019 p4405 p4861 p5580 : Prop) (h : (¬ p3822) ∨ (¬ p4019) ∨ (¬ p4405) ∨ (¬ p4861) ∨ p2027 ∨ (¬ p5580)) : (p2027) ∨ (¬ p3822) ∨ (¬ p4019) ∨ (¬ p4405) ∨ (¬ p4861) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial40154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4861)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29410 t (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule40154 (meaning t m 2027) (meaning t m 3822) (meaning t m 4019) (meaning t m 4405) (meaning t m 4861) (meaning t m 5580) source

theorem rule40155 (p2027 p2264 p2427 p3880 p4132 p4362 : Prop) (h : (¬ p2427) ∨ p2027 ∨ (¬ p4362) ∨ (¬ p4132) ∨ (¬ p2264) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4362) := by
  classical
  tauto

theorem initial40155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4362)) := by
  have source := ElevenTheory.theory29411 t (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule40155 (meaning t m 2027) (meaning t m 2264) (meaning t m 2427) (meaning t m 3880) (meaning t m 4132) (meaning t m 4362) source

theorem rule40156 (p2027 p2139 p2156 p2264 p2427 p3425 p3659 p4110 p4362 : Prop) (h : (¬ p3425) ∨ (¬ p2264) ∨ (¬ p4110) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2139) ∨ (¬ p4362) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4110) ∨ (¬ p4362) := by
  classical
  tauto

theorem initial40156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4362)) := by
  have source := ElevenTheory.theory29412 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 7) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule40156 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2264) (meaning t m 2427) (meaning t m 3425) (meaning t m 3659) (meaning t m 4110) (meaning t m 4362) source

theorem rule40158 (p1977 p2027 p2241 p2264 p2355 p3548 p4366 : Prop) (h : (¬ p1977) ∨ (¬ p2241) ∨ (¬ p2264) ∨ p2027 ∨ p2355 ∨ (¬ p4366) ∨ (¬ p3548)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (p2355) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial40158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory29414 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8)
  exact rule40158 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2355) (meaning t m 3548) (meaning t m 4366) source

theorem rule40159 (p2027 p2156 p2982 p3365 p3366 p3370 p3877 p4110 p4118 p4330 p4377 p5045 : Prop) (h : (¬ p5045) ∨ (¬ p4330) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4377) ∨ (¬ p2156) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p3366) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p4110) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4377) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial40159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory29415 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9)
  exact rule40159 (meaning t m 2027) (meaning t m 2156) (meaning t m 2982) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 3877) (meaning t m 4110) (meaning t m 4118) (meaning t m 4330) (meaning t m 4377) (meaning t m 5045) source

theorem rule40160 (p2027 p2387 p2668 p2787 p3362 p3389 p3568 p3868 p4556 p5660 : Prop) (h : (¬ p4556) ∨ (¬ p3389) ∨ (¬ p2787) ∨ (¬ p2387) ∨ (¬ p3568) ∨ (¬ p2668) ∨ (¬ p5660) ∨ (¬ p3362) ∨ (¬ p3868) ∨ p2027) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3868) ∨ (¬ p4556) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial40160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory29416 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule40160 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2787) (meaning t m 3362) (meaning t m 3389) (meaning t m 3568) (meaning t m 3868) (meaning t m 4556) (meaning t m 5660) source

theorem rule40161 (p1991 p2027 p2764 p2963 p3324 p4347 p4444 : Prop) (h : (¬ p3324) ∨ (¬ p2963) ∨ p2764 ∨ p2027 ∨ (¬ p1991) ∨ (¬ p4347) ∨ (¬ p4444)) : (¬ p1991) ∨ (p2027) ∨ (p2764) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial40161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory29417 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule40161 (meaning t m 1991) (meaning t m 2027) (meaning t m 2764) (meaning t m 2963) (meaning t m 3324) (meaning t m 4347) (meaning t m 4444) source

theorem rule40164 (p2027 p2230 p2963 p3324 p3333 p3362 p3684 p4332 p4347 p4789 : Prop) (h : (¬ p4332) ∨ (¬ p2963) ∨ (¬ p4347) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p2230) ∨ (¬ p4789) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29420 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule40164 (meaning t m 2027) (meaning t m 2230) (meaning t m 2963) (meaning t m 3324) (meaning t m 3333) (meaning t m 3362) (meaning t m 3684) (meaning t m 4332) (meaning t m 4347) (meaning t m 4789) source

theorem rule40166 (p2027 p2220 p2284 p3646 p3694 p4906 : Prop) (h : (¬ p4906) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2284) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3694) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial40166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory29422 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule40166 (meaning t m 2027) (meaning t m 2220) (meaning t m 2284) (meaning t m 3646) (meaning t m 3694) (meaning t m 4906) source

theorem rule40167 (p2027 p3276 p3355 p3365 p3366 p3519 p3877 p4118 p4191 p4330 p4376 : Prop) (h : p2027 ∨ (¬ p4330) ∨ (¬ p4191) ∨ (¬ p3365) ∨ (¬ p3276) ∨ (¬ p4118) ∨ (¬ p3877) ∨ (¬ p3355) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3519)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial40167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory29423 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40167 (meaning t m 2027) (meaning t m 3276) (meaning t m 3355) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3877) (meaning t m 4118) (meaning t m 4191) (meaning t m 4330) (meaning t m 4376) source

theorem rule40170 (p2027 p2241 p2598 p2750 p2753 p3276 p3333 p3860 p5123 p5693 : Prop) (h : (¬ p3333) ∨ (¬ p3276) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2753) ∨ (¬ p3860) ∨ (¬ p2598) ∨ (¬ p5693) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial40170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory29426 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40170 (meaning t m 2027) (meaning t m 2241) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3276) (meaning t m 3333) (meaning t m 3860) (meaning t m 5123) (meaning t m 5693) source

theorem rule40171 (p1981 p2027 p2528 p2598 p2611 p3641 p4347 : Prop) (h : p2027 ∨ (¬ p2598) ∨ (¬ p2528) ∨ p2611 ∨ (¬ p4347) ∨ (¬ p3641) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3641) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial40171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory29427 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule40171 (meaning t m 1981) (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2611) (meaning t m 3641) (meaning t m 4347) source

theorem rule40178 (p2027 p2132 p2247 p2870 p2881 p3324 p4154 p4503 p4733 : Prop) (h : (¬ p3324) ∨ (¬ p4503) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p4733) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29434 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule40178 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2870) (meaning t m 2881) (meaning t m 3324) (meaning t m 4154) (meaning t m 4503) (meaning t m 4733) source

theorem rule40180 (p2027 p2780 p3366 p3449 p3555 p3969 p4347 p4358 p4377 p4446 p5122 : Prop) (h : (¬ p5122) ∨ (¬ p4347) ∨ (¬ p3969) ∨ (¬ p3555) ∨ (¬ p4377) ∨ (¬ p3449) ∨ (¬ p4446) ∨ (¬ p4358) ∨ (¬ p2780) ∨ (¬ p3366) ∨ p2027) : (p2027) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4377) ∨ (¬ p4446) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial40180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory29436 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40180 (meaning t m 2027) (meaning t m 2780) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 3969) (meaning t m 4347) (meaning t m 4358) (meaning t m 4377) (meaning t m 4446) (meaning t m 5122) source

theorem rule40181 (p2027 p2417 p2608 p2761 p3389 p3519 p3591 p3918 p4329 p4376 p5254 : Prop) (h : (¬ p2417) ∨ (¬ p5254) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p4329) ∨ (¬ p3389) ∨ (¬ p4376) ∨ (¬ p3918) ∨ (¬ p3591) ∨ (¬ p3519) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4329) ∨ (¬ p4376) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial40181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory29437 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40181 (meaning t m 2027) (meaning t m 2417) (meaning t m 2608) (meaning t m 2761) (meaning t m 3389) (meaning t m 3519) (meaning t m 3591) (meaning t m 3918) (meaning t m 4329) (meaning t m 4376) (meaning t m 5254) source

theorem rule40182 (p2741 p4262 p4436 : Prop) (h : (¬ p2741) ∨ (¬ p4262) ∨ p4436) : (¬ p2741) ∨ (¬ p4262) ∨ (p4436) := by
  classical
  tauto

theorem initial40182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 4262)) ∨ (meaning t m 4436) := by
  have source := ElevenTheory.theory29438 (m.theta 1 2) (m.theta 1 3) (m.theta 1 8)
  exact rule40182 (meaning t m 2741) (meaning t m 4262) (meaning t m 4436) source

theorem rule40184 (p2027 p2307 p2584 p2588 p3266 p3519 p3564 p4330 p4376 p4379 p5387 : Prop) (h : (¬ p3519) ∨ (¬ p4379) ∨ (¬ p2307) ∨ (¬ p5387) ∨ (¬ p2588) ∨ (¬ p4376) ∨ (¬ p3266) ∨ (¬ p2584) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3266) ∨ (¬ p3519) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4376) ∨ (¬ p4379) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial40184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory29440 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40184 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 3266) (meaning t m 3519) (meaning t m 3564) (meaning t m 4330) (meaning t m 4376) (meaning t m 4379) (meaning t m 5387) source

theorem rule40188 (p2027 p2249 p2952 p3027 p3256 p3989 p4044 p4173 p4282 p4348 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p3989) ∨ (¬ p2249) ∨ (¬ p3027) ∨ (¬ p2952) ∨ (¬ p4282) ∨ (¬ p4173) ∨ (¬ p4044) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3256)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2952) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p3989) ∨ (¬ p4044) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial40188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory29444 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40188 (meaning t m 2027) (meaning t m 2249) (meaning t m 2952) (meaning t m 3027) (meaning t m 3256) (meaning t m 3989) (meaning t m 4044) (meaning t m 4173) (meaning t m 4282) (meaning t m 4348) (meaning t m 4503) source

theorem rule40189 (p2027 p2166 p3684 p3948 p4031 p4120 p5217 : Prop) (h : (¬ p5217) ∨ (¬ p4031) ∨ (¬ p3948) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p4120) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3684) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial40189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory29445 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8)
  exact rule40189 (meaning t m 2027) (meaning t m 2166) (meaning t m 3684) (meaning t m 3948) (meaning t m 4031) (meaning t m 4120) (meaning t m 5217) source

theorem rule40190 (p2027 p2132 p2247 p2619 p3146 p4037 p4154 p4604 p4733 : Prop) (h : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p4604) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p4037) ∨ (¬ p2247) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29446 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40190 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2619) (meaning t m 3146) (meaning t m 4037) (meaning t m 4154) (meaning t m 4604) (meaning t m 4733) source

theorem rule40191 (p1987 p2027 p2177 p2641 p2997 p3031 p3548 p4195 : Prop) (h : p2997 ∨ (¬ p1987) ∨ (¬ p3031) ∨ (¬ p4195) ∨ (¬ p3548) ∨ (¬ p2177) ∨ (¬ p2641) ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2641) ∨ (p2997) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial40191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory29447 t (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule40191 (meaning t m 1987) (meaning t m 2027) (meaning t m 2177) (meaning t m 2641) (meaning t m 2997) (meaning t m 3031) (meaning t m 3548) (meaning t m 4195) source

theorem rule40193 (p2027 p2191 p2192 p3737 p4506 p5586 : Prop) (h : (¬ p5586) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p4506) ∨ (¬ p3737)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p3737) ∨ (¬ p4506) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial40193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory29449 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 8)
  exact rule40193 (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 3737) (meaning t m 4506) (meaning t m 5586) source

theorem rule40195 (p2027 p2785 p3319 p3486 p3946 p4185 p4338 p4555 : Prop) (h : (¬ p3946) ∨ (¬ p3319) ∨ (¬ p4555) ∨ (¬ p2785) ∨ p2027 ∨ (¬ p4185) ∨ (¬ p3486) ∨ (¬ p4338)) : (p2027) ∨ (¬ p2785) ∨ (¬ p3319) ∨ (¬ p3486) ∨ (¬ p3946) ∨ (¬ p4185) ∨ (¬ p4338) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial40195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory29451 t (m.theta 0 6) (m.theta 1 5) (m.theta 1 6) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule40195 (meaning t m 2027) (meaning t m 2785) (meaning t m 3319) (meaning t m 3486) (meaning t m 3946) (meaning t m 4185) (meaning t m 4338) (meaning t m 4555) source

theorem rule40201 (p3483 p3564 p4390 : Prop) (h : (¬ p3564) ∨ (¬ p4390) ∨ p3483) : (p3483) ∨ (¬ p3564) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial40201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3483) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory29457 (m.theta 2 6) (m.theta 4 6) (m.theta 6 9)
  exact rule40201 (meaning t m 3483) (meaning t m 3564) (meaning t m 4390) source

theorem rule40205 (p2027 p2928 p3073 p3695 p4340 p4359 p4644 p4688 : Prop) (h : (¬ p2928) ∨ (¬ p3695) ∨ (¬ p4359) ∨ (¬ p4644) ∨ (¬ p4340) ∨ (¬ p4688) ∨ p2027 ∨ (¬ p3073)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3073) ∨ (¬ p3695) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4644) ∨ (¬ p4688) := by
  classical
  tauto

theorem initial40205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4644)) ∨ (¬ (meaning t m 4688)) := by
  have source := ElevenTheory.theory29461 t (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 4 7) (m.theta 8 9)
  exact rule40205 (meaning t m 2027) (meaning t m 2928) (meaning t m 3073) (meaning t m 3695) (meaning t m 4340) (meaning t m 4359) (meaning t m 4644) (meaning t m 4688) source

theorem rule40206 (p2027 p2437 p2655 p2946 p3540 p4704 : Prop) (h : (¬ p2655) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p4704) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p3540) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial40206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory29462 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule40206 (meaning t m 2027) (meaning t m 2437) (meaning t m 2655) (meaning t m 2946) (meaning t m 3540) (meaning t m 4704) source

theorem rule40207 (p1975 p2027 p2553 p2633 p3941 p3956 p5580 : Prop) (h : p2633 ∨ (¬ p2553) ∨ (¬ p1975) ∨ (¬ p3941) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p5580)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2633) ∨ (¬ p3941) ∨ (¬ p3956) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial40207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29463 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule40207 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2633) (meaning t m 3941) (meaning t m 3956) (meaning t m 5580) source

theorem rule40209 (p2027 p2191 p2352 p2598 p2891 p3369 p3422 p3556 p4134 p4733 : Prop) (h : (¬ p2352) ∨ (¬ p3422) ∨ (¬ p2191) ∨ (¬ p4134) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3556) ∨ (¬ p3369) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3422) ∨ (¬ p3556) ∨ (¬ p4134) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29465 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule40209 (meaning t m 2027) (meaning t m 2191) (meaning t m 2352) (meaning t m 2598) (meaning t m 2891) (meaning t m 3369) (meaning t m 3422) (meaning t m 3556) (meaning t m 4134) (meaning t m 4733) source

theorem rule40211 (p1997 p2027 p2764 p2891 p4235 p4363 p4381 p4382 : Prop) (h : (¬ p4382) ∨ (¬ p4381) ∨ p2764 ∨ (¬ p4363) ∨ (¬ p1997) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p4235)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p2891) ∨ (¬ p4235) ∨ (¬ p4363) ∨ (¬ p4381) ∨ (¬ p4382) := by
  classical
  tauto

theorem initial40211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4382)) := by
  have source := ElevenTheory.theory29467 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40211 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 2891) (meaning t m 4235) (meaning t m 4363) (meaning t m 4381) (meaning t m 4382) source

theorem rule40213 (p2027 p2230 p2247 p2373 p3848 p3969 p5119 p5190 p5284 : Prop) (h : (¬ p5190) ∨ (¬ p3848) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3969) ∨ (¬ p2247) ∨ (¬ p5284) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2373) ∨ (¬ p3848) ∨ (¬ p3969) ∨ (¬ p5119) ∨ (¬ p5190) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial40213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory29469 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40213 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2373) (meaning t m 3848) (meaning t m 3969) (meaning t m 5119) (meaning t m 5190) (meaning t m 5284) source

theorem rule40214 (p2027 p3361 p3585 p3631 p3687 p3821 p4749 p4849 : Prop) (h : (¬ p3687) ∨ (¬ p3821) ∨ (¬ p3361) ∨ (¬ p4849) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p4749)) : (p2027) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p4749) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial40214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory29470 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 7 9)
  exact rule40214 (meaning t m 2027) (meaning t m 3361) (meaning t m 3585) (meaning t m 3631) (meaning t m 3687) (meaning t m 3821) (meaning t m 4749) (meaning t m 4849) source

theorem rule40215 (p2027 p2132 p2247 p2274 p2860 p3324 p4154 p4501 p4733 : Prop) (h : (¬ p2247) ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p4501) ∨ (¬ p2860) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p2860) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4501) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29471 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule40215 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2274) (meaning t m 2860) (meaning t m 3324) (meaning t m 4154) (meaning t m 4501) (meaning t m 4733) source

theorem rule40218 (p1985 p2027 p2707 p2842 p3434 p3585 p3690 : Prop) (h : p2027 ∨ (¬ p3434) ∨ p2842 ∨ (¬ p1985) ∨ (¬ p3690) ∨ (¬ p3585) ∨ (¬ p2707)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2707) ∨ (p2842) ∨ (¬ p3434) ∨ (¬ p3585) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial40218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory29474 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule40218 (meaning t m 1985) (meaning t m 2027) (meaning t m 2707) (meaning t m 2842) (meaning t m 3434) (meaning t m 3585) (meaning t m 3690) source

theorem rule40221 (p2027 p2528 p2850 p4340 p4608 p5368 : Prop) (h : p2027 ∨ (¬ p4608) ∨ (¬ p5368) ∨ (¬ p2528) ∨ (¬ p2850) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2850) ∨ (¬ p4340) ∨ (¬ p4608) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial40221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4608)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory29477 t (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule40221 (meaning t m 2027) (meaning t m 2528) (meaning t m 2850) (meaning t m 4340) (meaning t m 4608) (meaning t m 5368) source

theorem rule40222 (p2027 p2249 p2727 p2901 p2950 p3413 p3556 : Prop) (h : (¬ p2950) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p2727) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2727) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3413) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial40222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory29478 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule40222 (meaning t m 2027) (meaning t m 2249) (meaning t m 2727) (meaning t m 2901) (meaning t m 2950) (meaning t m 3413) (meaning t m 3556) source

theorem rule40223 (p2027 p2727 p2751 p2901 p3413 p4244 p4392 : Prop) (h : (¬ p2727) ∨ (¬ p3413) ∨ p2027 ∨ (¬ p4392) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p4244) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial40223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory29479 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule40223 (meaning t m 2027) (meaning t m 2727) (meaning t m 2751) (meaning t m 2901) (meaning t m 3413) (meaning t m 4244) (meaning t m 4392) source

theorem rule40226 (p2027 p2190 p2284 p2534 p3146 p4607 p4705 : Prop) (h : (¬ p4607) ∨ (¬ p3146) ∨ (¬ p2534) ∨ (¬ p4705) ∨ (¬ p2190) ∨ p2027 ∨ (¬ p2284)) : (p2027) ∨ (¬ p2190) ∨ (¬ p2284) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial40226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory29482 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule40226 (meaning t m 2027) (meaning t m 2190) (meaning t m 2284) (meaning t m 2534) (meaning t m 3146) (meaning t m 4607) (meaning t m 4705) source

theorem rule40228 (p3276 p3767 p4264 : Prop) (h : (¬ p4264) ∨ (¬ p3276) ∨ p3767) : (¬ p3276) ∨ (p3767) ∨ (¬ p4264) := by
  classical
  tauto

theorem initial40228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3276)) ∨ (meaning t m 3767) ∨ (¬ (meaning t m 4264)) := by
  have source := ElevenTheory.theory29484 (m.theta 0 9) (m.theta 4 9) (m.theta 9 10)
  exact rule40228 (meaning t m 3276) (meaning t m 3767) (meaning t m 4264) source

theorem rule40229 (p2027 p2247 p2573 p2996 p3461 p3564 p4391 p4831 p5190 : Prop) (h : (¬ p3564) ∨ (¬ p5190) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4831) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p4391)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2573) ∨ (¬ p2996) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4391) ∨ (¬ p4831) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial40229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory29485 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule40229 (meaning t m 2027) (meaning t m 2247) (meaning t m 2573) (meaning t m 2996) (meaning t m 3461) (meaning t m 3564) (meaning t m 4391) (meaning t m 4831) (meaning t m 5190) source

theorem rule40235 (p1984 p2027 p2191 p2459 p2633 p3555 p3692 : Prop) (h : p2633 ∨ (¬ p2459) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p2191)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3555) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial40235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory29491 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40235 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2459) (meaning t m 2633) (meaning t m 3555) (meaning t m 3692) source

theorem rule40238 (p2027 p2166 p2459 p3949 p4363 p4902 : Prop) (h : (¬ p2459) ∨ (¬ p3949) ∨ p2027 ∨ (¬ p4902) ∨ (¬ p2166) ∨ (¬ p4363)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2459) ∨ (¬ p3949) ∨ (¬ p4363) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29494 t (m.theta 1 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40238 (meaning t m 2027) (meaning t m 2166) (meaning t m 2459) (meaning t m 3949) (meaning t m 4363) (meaning t m 4902) source

theorem rule40239 (p2027 p2363 p2598 p2911 p3201 p3369 p3692 p4120 p4503 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p4120) ∨ (¬ p3369) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4503) ∨ (¬ p3201) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3369) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29495 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40239 (meaning t m 2027) (meaning t m 2363) (meaning t m 2598) (meaning t m 2911) (meaning t m 3201) (meaning t m 3369) (meaning t m 3692) (meaning t m 4120) (meaning t m 4503) (meaning t m 4733) source

theorem rule40248 (p2027 p2156 p2656 p2685 p3758 p4392 p4399 p4652 : Prop) (h : (¬ p4392) ∨ (¬ p4652) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2156) ∨ (¬ p2656) ∨ (¬ p4399) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2656) ∨ (¬ p2685) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4399) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial40248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory29504 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6)
  exact rule40248 (meaning t m 2027) (meaning t m 2156) (meaning t m 2656) (meaning t m 2685) (meaning t m 3758) (meaning t m 4392) (meaning t m 4399) (meaning t m 4652) source

theorem rule40252 (p2027 p2352 p2459 p2598 p3422 p3860 p4133 p4261 p4733 : Prop) (h : (¬ p2352) ∨ (¬ p4133) ∨ (¬ p4733) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3860) ∨ (¬ p4133) ∨ (¬ p4261) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial40252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory29508 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40252 (meaning t m 2027) (meaning t m 2352) (meaning t m 2459) (meaning t m 2598) (meaning t m 3422) (meaning t m 3860) (meaning t m 4133) (meaning t m 4261) (meaning t m 4733) source

theorem rule40253 (p3685 p4357 p4364 : Prop) (h : (¬ p4357) ∨ (¬ p3685) ∨ p4364) : (¬ p3685) ∨ (¬ p4357) ∨ (p4364) := by
  classical
  tauto

theorem initial40253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4357)) ∨ (meaning t m 4364) := by
  have source := ElevenTheory.theory29509 (m.theta 2 3) (m.theta 2 7) (m.theta 2 8)
  exact rule40253 (meaning t m 3685) (meaning t m 4357) (meaning t m 4364) source

theorem rule40254 (p2027 p2156 p2245 p2619 p3027 p3414 p3758 p4043 p4360 p4521 : Prop) (h : (¬ p3414) ∨ (¬ p4521) ∨ (¬ p2245) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2156) ∨ (¬ p4043) ∨ (¬ p4360) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2245) ∨ (¬ p2619) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p3758) ∨ (¬ p4043) ∨ (¬ p4360) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial40254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4043)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory29510 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8)
  exact rule40254 (meaning t m 2027) (meaning t m 2156) (meaning t m 2245) (meaning t m 2619) (meaning t m 3027) (meaning t m 3414) (meaning t m 3758) (meaning t m 4043) (meaning t m 4360) (meaning t m 4521) source

theorem rule40258 (p2027 p3073 p3857 p3961 p4173 p4283 p4496 p4558 : Prop) (h : (¬ p4496) ∨ (¬ p4283) ∨ (¬ p3857) ∨ p2027 ∨ (¬ p3073) ∨ (¬ p3961) ∨ (¬ p4558) ∨ (¬ p4173)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4173) ∨ (¬ p4283) ∨ (¬ p4496) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial40258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory29514 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule40258 (meaning t m 2027) (meaning t m 3073) (meaning t m 3857) (meaning t m 3961) (meaning t m 4173) (meaning t m 4283) (meaning t m 4496) (meaning t m 4558) source

theorem rule40261 (p2027 p2230 p2249 p2373 p2459 p2656 p2727 p3037 p3414 p3544 p4261 p4902 : Prop) (h : (¬ p2656) ∨ (¬ p2230) ∨ (¬ p3037) ∨ (¬ p2249) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p4902) ∨ (¬ p2459) ∨ (¬ p3414) ∨ (¬ p3544) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2249) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3037) ∨ (¬ p3414) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29517 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 7) (m.theta 1 8) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40261 (meaning t m 2027) (meaning t m 2230) (meaning t m 2249) (meaning t m 2373) (meaning t m 2459) (meaning t m 2656) (meaning t m 2727) (meaning t m 3037) (meaning t m 3414) (meaning t m 3544) (meaning t m 4261) (meaning t m 4902) source

theorem rule40262 (p1998 p2027 p2177 p2202 p2553 p2573 p3238 p3519 : Prop) (h : (¬ p2553) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3238) ∨ p2202 ∨ (¬ p3519) ∨ (¬ p1998) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3238) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial40262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory29518 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule40262 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2553) (meaning t m 2573) (meaning t m 3238) (meaning t m 3519) source

theorem rule40266 (p1986 p2027 p2573 p2764 p3193 p3519 p3584 p4022 p4191 : Prop) (h : (¬ p4022) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p3584) ∨ (¬ p2573) ∨ (¬ p1986) ∨ (¬ p4191) ∨ (¬ p3193) ∨ p2764) : (¬ p1986) ∨ (p2027) ∨ (¬ p2573) ∨ (p2764) ∨ (¬ p3193) ∨ (¬ p3519) ∨ (¬ p3584) ∨ (¬ p4022) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial40266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory29522 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule40266 (meaning t m 1986) (meaning t m 2027) (meaning t m 2573) (meaning t m 2764) (meaning t m 3193) (meaning t m 3519) (meaning t m 3584) (meaning t m 4022) (meaning t m 4191) source

theorem rule40267 (p2027 p2573 p2751 p2951 p2992 p3364 p3584 p3904 : Prop) (h : (¬ p3364) ∨ (¬ p2951) ∨ p2027 ∨ (¬ p2751) ∨ (¬ p2992) ∨ (¬ p3904) ∨ (¬ p2573) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial40267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory29523 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6)
  exact rule40267 (meaning t m 2027) (meaning t m 2573) (meaning t m 2751) (meaning t m 2951) (meaning t m 2992) (meaning t m 3364) (meaning t m 3584) (meaning t m 3904) source

end SunPrize.SMT
