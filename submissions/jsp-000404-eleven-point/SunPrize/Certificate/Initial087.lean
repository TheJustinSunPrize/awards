import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory071
import SunPrize.Certificate.Theory072
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule40674 (p2027 p2295 p2313 p2373 p2598 p2787 p2850 p3324 p4433 : Prop) (h : (¬ p2373) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2787) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p4433) ∨ (¬ p3324) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2598) ∨ (¬ p2787) ∨ (¬ p2850) ∨ (¬ p3324) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial40674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory29930 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule40674 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2373) (meaning t m 2598) (meaning t m 2787) (meaning t m 2850) (meaning t m 3324) (meaning t m 4433) source

theorem rule40676 (p1990 p2027 p2156 p2177 p2997 p3553 p3556 p4333 : Prop) (h : (¬ p3553) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2156) ∨ (¬ p1990) ∨ (¬ p4333) ∨ p2997 ∨ (¬ p2177)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3553) ∨ (¬ p3556) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial40676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory29932 t (m.theta 0 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule40676 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2997) (meaning t m 3553) (meaning t m 3556) (meaning t m 4333) source

theorem rule40678 (p2027 p2598 p2952 p3641 p4149 p4208 p4322 p4789 p5119 : Prop) (h : (¬ p4208) ∨ (¬ p5119) ∨ (¬ p4322) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4149) ∨ (¬ p4789) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29934 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule40678 (meaning t m 2027) (meaning t m 2598) (meaning t m 2952) (meaning t m 3641) (meaning t m 4149) (meaning t m 4208) (meaning t m 4322) (meaning t m 4789) (meaning t m 5119) source

theorem rule40679 (p1977 p2027 p2241 p2633 p3452 p3644 p3742 p4116 : Prop) (h : (¬ p1977) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4116) ∨ p2633 ∨ (¬ p3742)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2633) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial40679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory29935 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule40679 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2633) (meaning t m 3452) (meaning t m 3644) (meaning t m 3742) (meaning t m 4116) source

theorem rule40682 (p2027 p2598 p3414 p3422 p3888 p3947 p4381 p4789 p5250 : Prop) (h : (¬ p3888) ∨ (¬ p3414) ∨ (¬ p5250) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p3422) ∨ (¬ p2598) ∨ (¬ p4789) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3414) ∨ (¬ p3422) ∨ (¬ p3888) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial40682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory29938 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40682 (meaning t m 2027) (meaning t m 2598) (meaning t m 3414) (meaning t m 3422) (meaning t m 3888) (meaning t m 3947) (meaning t m 4381) (meaning t m 4789) (meaning t m 5250) source

theorem rule40683 (p1977 p2027 p2241 p2459 p2633 p3544 p4261 p4366 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p1977) ∨ (¬ p4366) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p4261) ∨ (¬ p3544)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial40683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory29939 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40683 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2633) (meaning t m 3544) (meaning t m 4261) (meaning t m 4366) source

theorem rule40687 (p2027 p2252 p2750 p2963 p3073 p3324 p3449 p3954 p5118 p5580 : Prop) (h : (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3449) ∨ (¬ p3073) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3954) ∨ (¬ p3324) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3073) ∨ (¬ p3324) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial40687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory29943 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40687 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 3073) (meaning t m 3324) (meaning t m 3449) (meaning t m 3954) (meaning t m 5118) (meaning t m 5580) source

theorem rule40688 (p2027 p2252 p2750 p2901 p2950 p3073 p3449 p3556 p3954 p4208 p5059 : Prop) (h : (¬ p3073) ∨ p2027 ∨ (¬ p5059) ∨ (¬ p3449) ∨ (¬ p4208) ∨ (¬ p3954) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p2950)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3556) ∨ (¬ p3954) ∨ (¬ p4208) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial40688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory29944 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule40688 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2901) (meaning t m 2950) (meaning t m 3073) (meaning t m 3449) (meaning t m 3556) (meaning t m 3954) (meaning t m 4208) (meaning t m 5059) source

theorem rule40693 (p2027 p2241 p2470 p2750 p2753 p3333 p3362 p3817 p3874 p4366 p4638 : Prop) (h : (¬ p3874) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p3362) ∨ (¬ p4366) ∨ (¬ p2241) ∨ (¬ p3817) ∨ p2027 ∨ (¬ p4638) ∨ (¬ p2470) ∨ (¬ p3333)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2470) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3817) ∨ (¬ p3874) ∨ (¬ p4366) ∨ (¬ p4638) := by
  classical
  tauto

theorem initial40693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4638)) := by
  have source := ElevenTheory.theory29949 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 9)
  exact rule40693 (meaning t m 2027) (meaning t m 2241) (meaning t m 2470) (meaning t m 2750) (meaning t m 2753) (meaning t m 3333) (meaning t m 3362) (meaning t m 3817) (meaning t m 3874) (meaning t m 4366) (meaning t m 4638) source

theorem rule40701 (p2027 p2774 p2819 p2952 p3979 p4208 p4322 p4789 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p4322) ∨ (¬ p4208) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p2774) ∨ (¬ p4789) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3979) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory29957 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40701 (meaning t m 2027) (meaning t m 2774) (meaning t m 2819) (meaning t m 2952) (meaning t m 3979) (meaning t m 4208) (meaning t m 4322) (meaning t m 4789) (meaning t m 5119) source

theorem rule40703 (p1975 p2027 p2187 p2553 p2765 p3573 p3998 p4170 p4286 : Prop) (h : (¬ p1975) ∨ (¬ p3573) ∨ (¬ p4170) ∨ p2027 ∨ (¬ p4286) ∨ (¬ p3998) ∨ p2765 ∨ (¬ p2553) ∨ (¬ p2187)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2553) ∨ (p2765) ∨ (¬ p3573) ∨ (¬ p3998) ∨ (¬ p4170) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial40703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory29959 t (m.theta 0 8) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule40703 (meaning t m 1975) (meaning t m 2027) (meaning t m 2187) (meaning t m 2553) (meaning t m 2765) (meaning t m 3573) (meaning t m 3998) (meaning t m 4170) (meaning t m 4286) source

theorem rule40705 (p2027 p2252 p2373 p2459 p2598 p2750 p2753 p2850 p3172 p4118 p4902 : Prop) (h : (¬ p4118) ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p2750) ∨ (¬ p4902) ∨ (¬ p2459) ∨ (¬ p2753) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory29961 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40705 (meaning t m 2027) (meaning t m 2252) (meaning t m 2373) (meaning t m 2459) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 2850) (meaning t m 3172) (meaning t m 4118) (meaning t m 4902) source

theorem rule40706 (p2027 p2952 p3276 p3355 p3362 p3744 p3952 p4444 p4604 p4789 : Prop) (h : (¬ p3276) ∨ (¬ p3952) ∨ (¬ p3362) ∨ (¬ p2952) ∨ (¬ p4604) ∨ (¬ p4444) ∨ (¬ p4789) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p3355)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29962 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40706 (meaning t m 2027) (meaning t m 2952) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3744) (meaning t m 3952) (meaning t m 4444) (meaning t m 4604) (meaning t m 4789) source

theorem rule40709 (p2027 p2241 p2363 p2750 p2753 p2774 p2819 p3817 p4366 p4669 : Prop) (h : (¬ p2819) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2753) ∨ (¬ p4669) ∨ (¬ p2750) ∨ (¬ p3817) ∨ (¬ p2774) ∨ (¬ p4366) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory29965 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40709 (meaning t m 2027) (meaning t m 2241) (meaning t m 2363) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) source

theorem rule40711 (p2027 p2470 p2753 p2761 p3204 p3333 p3362 p3874 p3946 p4191 p4638 p4870 : Prop) (h : p2027 ∨ (¬ p3946) ∨ (¬ p2761) ∨ (¬ p4191) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p3204) ∨ (¬ p2470) ∨ (¬ p4638) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3204) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3874) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4638) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial40711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory29967 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40711 (meaning t m 2027) (meaning t m 2470) (meaning t m 2753) (meaning t m 2761) (meaning t m 3204) (meaning t m 3333) (meaning t m 3362) (meaning t m 3874) (meaning t m 3946) (meaning t m 4191) (meaning t m 4638) (meaning t m 4870) source

theorem rule40715 (p2027 p2132 p2295 p2313 p2619 p2753 p3146 p3204 p4037 p4604 p4870 : Prop) (h : (¬ p3146) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p4604) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p3204) ∨ (¬ p4037) ∨ (¬ p2295) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3204) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial40715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory29971 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule40715 (meaning t m 2027) (meaning t m 2132) (meaning t m 2295) (meaning t m 2313) (meaning t m 2619) (meaning t m 2753) (meaning t m 3146) (meaning t m 3204) (meaning t m 4037) (meaning t m 4604) (meaning t m 4870) source

theorem rule40719 (p2027 p2573 p2952 p3362 p3570 p3584 p3641 p4320 p4420 p4789 : Prop) (h : (¬ p3570) ∨ (¬ p4420) ∨ (¬ p3641) ∨ (¬ p2573) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p4789) ∨ (¬ p2952) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4320) ∨ (¬ p4420) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory29975 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule40719 (meaning t m 2027) (meaning t m 2573) (meaning t m 2952) (meaning t m 3362) (meaning t m 3570) (meaning t m 3584) (meaning t m 3641) (meaning t m 4320) (meaning t m 4420) (meaning t m 4789) source

theorem rule40722 (p2027 p2295 p2312 p3324 p3516 p4138 p4668 : Prop) (h : (¬ p2312) ∨ (¬ p3516) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p3324) ∨ (¬ p3516) ∨ (¬ p4138) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial40722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory29978 t (m.theta 0 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule40722 (meaning t m 2027) (meaning t m 2295) (meaning t m 2312) (meaning t m 3324) (meaning t m 3516) (meaning t m 4138) (meaning t m 4668) source

theorem rule40723 (p1975 p2027 p2187 p2553 p2765 p3573 p3979 p4286 : Prop) (h : (¬ p1975) ∨ (¬ p3573) ∨ (¬ p2553) ∨ (¬ p4286) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p3979) ∨ p2765) : (¬ p1975) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2553) ∨ (p2765) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial40723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory29979 t (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule40723 (meaning t m 1975) (meaning t m 2027) (meaning t m 2187) (meaning t m 2553) (meaning t m 2765) (meaning t m 3573) (meaning t m 3979) (meaning t m 4286) source

theorem rule40726 (p2027 p2098 p2241 p2750 p2753 p3591 p3609 p3692 p3923 p4433 : Prop) (h : (¬ p4433) ∨ (¬ p2753) ∨ (¬ p3609) ∨ (¬ p2750) ∨ (¬ p3923) ∨ (¬ p2098) ∨ (¬ p3591) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2241)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3923) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial40726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory29982 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule40726 (meaning t m 2027) (meaning t m 2098) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3591) (meaning t m 3609) (meaning t m 3692) (meaning t m 3923) (meaning t m 4433) source

theorem rule40728 (p2027 p2241 p2528 p2598 p2750 p2753 p3591 p3641 p4026 p4604 : Prop) (h : (¬ p2753) ∨ (¬ p4026) ∨ (¬ p2528) ∨ (¬ p2241) ∨ (¬ p3641) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3591) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p4026) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial40728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory29984 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule40728 (meaning t m 2027) (meaning t m 2241) (meaning t m 2528) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3591) (meaning t m 3641) (meaning t m 4026) (meaning t m 4604) source

theorem rule40729 (p2027 p2132 p2241 p2750 p2753 p3105 p3680 p4366 p4442 p4831 : Prop) (h : (¬ p4366) ∨ (¬ p3105) ∨ (¬ p2132) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p4831) ∨ (¬ p4442)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial40729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory29985 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule40729 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3105) (meaning t m 3680) (meaning t m 4366) (meaning t m 4442) (meaning t m 4831) source

theorem rule40730 (p2027 p2145 p2284 p2528 p2598 p3641 p3646 p4033 p4208 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p2284) ∨ (¬ p2145) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p3641) ∨ (¬ p4033) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p2528)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial40730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory29986 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9)
  exact rule40730 (meaning t m 2027) (meaning t m 2145) (meaning t m 2284) (meaning t m 2528) (meaning t m 2598) (meaning t m 3641) (meaning t m 3646) (meaning t m 4033) (meaning t m 4208) (meaning t m 4604) source

theorem rule40731 (p2027 p2417 p3644 p4403 p4443 p5118 p5590 : Prop) (h : (¬ p4403) ∨ (¬ p4443) ∨ (¬ p2417) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p4403) ∨ (¬ p4443) ∨ (¬ p5118) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial40731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory29987 t (m.theta 0 8) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule40731 (meaning t m 2027) (meaning t m 2417) (meaning t m 3644) (meaning t m 4403) (meaning t m 4443) (meaning t m 5118) (meaning t m 5590) source

theorem rule40734 (p1990 p2027 p2633 p3032 p3097 p3553 p3631 p4107 : Prop) (h : (¬ p3097) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p3553) ∨ p2633 ∨ (¬ p1990) ∨ (¬ p3032) ∨ (¬ p3631)) : (¬ p1990) ∨ (p2027) ∨ (p2633) ∨ (¬ p3032) ∨ (¬ p3097) ∨ (¬ p3553) ∨ (¬ p3631) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial40734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory29990 t (m.theta 1 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule40734 (meaning t m 1990) (meaning t m 2027) (meaning t m 2633) (meaning t m 3032) (meaning t m 3097) (meaning t m 3553) (meaning t m 3631) (meaning t m 4107) source

theorem rule40738 (p2027 p2230 p2252 p2459 p2750 p3172 p3519 p3541 p3641 p3684 p4118 p4420 : Prop) (h : (¬ p4118) ∨ (¬ p3641) ∨ (¬ p4420) ∨ (¬ p2459) ∨ (¬ p3684) ∨ (¬ p3172) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4118) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial40738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory29994 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40738 (meaning t m 2027) (meaning t m 2230) (meaning t m 2252) (meaning t m 2459) (meaning t m 2750) (meaning t m 3172) (meaning t m 3519) (meaning t m 3541) (meaning t m 3641) (meaning t m 3684) (meaning t m 4118) (meaning t m 4420) source

theorem rule40739 (p2027 p2230 p2241 p2750 p3324 p3519 p3541 p3591 p3641 p3684 p4319 p4596 : Prop) (h : (¬ p3519) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2750) ∨ (¬ p4596) ∨ (¬ p2241) ∨ (¬ p4319) ∨ (¬ p2230) ∨ (¬ p3541)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p3519) ∨ (¬ p3541) ∨ (¬ p3591) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4319) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial40739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory29995 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8)
  exact rule40739 (meaning t m 2027) (meaning t m 2230) (meaning t m 2241) (meaning t m 2750) (meaning t m 3324) (meaning t m 3519) (meaning t m 3541) (meaning t m 3591) (meaning t m 3641) (meaning t m 3684) (meaning t m 4319) (meaning t m 4596) source

theorem rule40742 (p2027 p2230 p2373 p2476 p4434 : Prop) (h : (¬ p2373) ∨ (¬ p2230) ∨ (¬ p4434) ∨ p2027 ∨ (¬ p2476)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2476) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial40742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory29998 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule40742 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2476) (meaning t m 4434) source

theorem rule40744 (p1977 p2027 p2241 p2633 p3548 p3631 p3821 p5206 : Prop) (h : p2027 ∨ (¬ p1977) ∨ (¬ p2241) ∨ (¬ p3548) ∨ p2633 ∨ (¬ p5206) ∨ (¬ p3631) ∨ (¬ p3821)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2633) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial40744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory30000 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 7 8) (m.theta 7 9)
  exact rule40744 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2633) (meaning t m 3548) (meaning t m 3631) (meaning t m 3821) (meaning t m 5206) source

theorem rule40745 (p2027 p2210 p2373 p3551 p4210 p4902 p5206 : Prop) (h : (¬ p2210) ∨ (¬ p4902) ∨ (¬ p4210) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2373) ∨ (¬ p5206)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3551) ∨ (¬ p4210) ∨ (¬ p4902) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial40745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory30001 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule40745 (meaning t m 2027) (meaning t m 2210) (meaning t m 2373) (meaning t m 3551) (meaning t m 4210) (meaning t m 4902) (meaning t m 5206) source

theorem rule40746 (p2027 p3516 p3551 p3692 p4443 p4902 : Prop) (h : (¬ p4902) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p3551) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory30002 t (m.theta 0 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40746 (meaning t m 2027) (meaning t m 3516) (meaning t m 3551) (meaning t m 3692) (meaning t m 4443) (meaning t m 4902) source

theorem rule40747 (p2027 p2252 p2504 p2750 p3093 p3414 p3888 p3947 p3954 p4381 p5250 : Prop) (h : (¬ p4381) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p5250) ∨ (¬ p3414) ∨ (¬ p3093) ∨ (¬ p3947) ∨ (¬ p3888) ∨ (¬ p3954) ∨ (¬ p2504) ∨ p2027) : (p2027) ∨ (¬ p2252) ∨ (¬ p2504) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3414) ∨ (¬ p3888) ∨ (¬ p3947) ∨ (¬ p3954) ∨ (¬ p4381) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial40747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory30003 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule40747 (meaning t m 2027) (meaning t m 2252) (meaning t m 2504) (meaning t m 2750) (meaning t m 3093) (meaning t m 3414) (meaning t m 3888) (meaning t m 3947) (meaning t m 3954) (meaning t m 4381) (meaning t m 5250) source

theorem rule40748 (p2027 p2166 p2210 p2252 p2459 p2750 p3172 p3954 p4118 p4902 : Prop) (h : (¬ p3954) ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p4118) ∨ (¬ p4902) ∨ (¬ p3172) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3954) ∨ (¬ p4118) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial40748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory30004 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule40748 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2252) (meaning t m 2459) (meaning t m 2750) (meaning t m 3172) (meaning t m 3954) (meaning t m 4118) (meaning t m 4902) source

theorem rule40750 (p2027 p2098 p2963 p3266 p3568 p3609 p4260 p4789 p4831 : Prop) (h : (¬ p4831) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p2963) ∨ (¬ p3609) ∨ (¬ p3266) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p3568) ∨ (¬ p3609) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial40750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory30006 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 8) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule40750 (meaning t m 2027) (meaning t m 2098) (meaning t m 2963) (meaning t m 3266) (meaning t m 3568) (meaning t m 3609) (meaning t m 4260) (meaning t m 4789) (meaning t m 4831) source

theorem rule40751 (p2027 p2753 p3097 p3619 p3645 p3646 p3670 p4107 p4444 p4669 p4877 : Prop) (h : (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3645) ∨ (¬ p3619) ∨ p2027 ∨ (¬ p3670) ∨ (¬ p4444) ∨ (¬ p3646) ∨ (¬ p4877) ∨ (¬ p4107) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3619) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial40751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory30007 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40751 (meaning t m 2027) (meaning t m 2753) (meaning t m 3097) (meaning t m 3619) (meaning t m 3645) (meaning t m 3646) (meaning t m 3670) (meaning t m 4107) (meaning t m 4444) (meaning t m 4669) (meaning t m 4877) source

theorem rule40752 (p2027 p2470 p2963 p3333 p3362 p3568 p3874 p4107 p4638 p4789 : Prop) (h : (¬ p4107) ∨ (¬ p3874) ∨ (¬ p2470) ∨ (¬ p4638) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p3362) ∨ (¬ p3333) ∨ (¬ p4789) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2963) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3568) ∨ (¬ p3874) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory30008 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule40752 (meaning t m 2027) (meaning t m 2470) (meaning t m 2963) (meaning t m 3333) (meaning t m 3362) (meaning t m 3568) (meaning t m 3874) (meaning t m 4107) (meaning t m 4638) (meaning t m 4789) source

theorem rule40753 (p1982 p2027 p2633 p2761 p3548 p3631 p4444 : Prop) (h : (¬ p3631) ∨ (¬ p1982) ∨ p2633 ∨ (¬ p4444) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3548)) : (¬ p1982) ∨ (p2027) ∨ (p2633) ∨ (¬ p2761) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial40753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory30009 t (m.theta 1 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40753 (meaning t m 1982) (meaning t m 2027) (meaning t m 2633) (meaning t m 2761) (meaning t m 3548) (meaning t m 3631) (meaning t m 4444) source

theorem rule40757 (p2027 p2761 p3516 p4322 p4402 p4990 : Prop) (h : (¬ p4990) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4402) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4990) := by
  classical
  tauto

theorem initial40757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4990)) := by
  have source := ElevenTheory.theory30013 t (m.theta 0 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule40757 (meaning t m 2027) (meaning t m 2761) (meaning t m 3516) (meaning t m 4322) (meaning t m 4402) (meaning t m 4990) source

theorem rule40758 (p1978 p2027 p2284 p2633 p3570 p3646 p4320 : Prop) (h : p2027 ∨ (¬ p1978) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p2284) ∨ (¬ p3570) ∨ p2633) : (¬ p1978) ∨ (p2027) ∨ (¬ p2284) ∨ (p2633) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial40758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory30014 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule40758 (meaning t m 1978) (meaning t m 2027) (meaning t m 2284) (meaning t m 2633) (meaning t m 3570) (meaning t m 3646) (meaning t m 4320) source

theorem rule40760 (p4009 p4181 p5074 : Prop) (h : (¬ p4181) ∨ (¬ p5074) ∨ p4009) : (p4009) ∨ (¬ p4181) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial40760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4009) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory30016 (m.theta 1 8) (m.theta 3 8) (m.theta 8 10)
  exact rule40760 (meaning t m 4009) (meaning t m 4181) (meaning t m 5074) source

theorem rule40762 (p2027 p2145 p2284 p2459 p2717 p3471 p3646 p4208 p5059 : Prop) (h : (¬ p3646) ∨ (¬ p5059) ∨ (¬ p4208) ∨ (¬ p2284) ∨ (¬ p3471) ∨ (¬ p2717) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2145)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial40762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory30018 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40762 (meaning t m 2027) (meaning t m 2145) (meaning t m 2284) (meaning t m 2459) (meaning t m 2717) (meaning t m 3471) (meaning t m 3646) (meaning t m 4208) (meaning t m 5059) source

theorem rule40763 (p2027 p3292 p3333 p3362 p3389 p3461 p3876 p4789 p5284 p5322 : Prop) (h : (¬ p3389) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p3362) ∨ (¬ p3333) ∨ (¬ p5322) ∨ (¬ p4789) ∨ (¬ p3292) ∨ (¬ p3461)) : (p2027) ∨ (¬ p3292) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3461) ∨ (¬ p3876) ∨ (¬ p4789) ∨ (¬ p5284) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial40763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory30019 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 9) (m.theta 4 7) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule40763 (meaning t m 2027) (meaning t m 3292) (meaning t m 3333) (meaning t m 3362) (meaning t m 3389) (meaning t m 3461) (meaning t m 3876) (meaning t m 4789) (meaning t m 5284) (meaning t m 5322) source

theorem rule40764 (p2027 p2717 p2963 p3471 p3941 p4037 p4191 p4789 p5119 : Prop) (h : (¬ p4191) ∨ (¬ p4037) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p5119) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2963) ∨ (¬ p3471) ∨ (¬ p3941) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial40764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory30020 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule40764 (meaning t m 2027) (meaning t m 2717) (meaning t m 2963) (meaning t m 3471) (meaning t m 3941) (meaning t m 4037) (meaning t m 4191) (meaning t m 4789) (meaning t m 5119) source

theorem rule40766 (p2027 p2241 p2573 p2750 p2753 p3333 p3362 p3548 p3584 p4366 p4451 p4668 : Prop) (h : p2027 ∨ (¬ p3584) ∨ (¬ p2573) ∨ (¬ p3548) ∨ (¬ p3333) ∨ (¬ p4451) ∨ (¬ p4668) ∨ (¬ p3362) ∨ (¬ p4366) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2573) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3584) ∨ (¬ p4366) ∨ (¬ p4451) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial40766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory30022 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 7 8) (m.theta 7 9)
  exact rule40766 (meaning t m 2027) (meaning t m 2241) (meaning t m 2573) (meaning t m 2750) (meaning t m 2753) (meaning t m 3333) (meaning t m 3362) (meaning t m 3548) (meaning t m 3584) (meaning t m 4366) (meaning t m 4451) (meaning t m 4668) source

theorem rule40767 (p2027 p2241 p2363 p2750 p2753 p2774 p2819 p3555 p4363 p5059 : Prop) (h : (¬ p2774) ∨ (¬ p2753) ∨ (¬ p2750) ∨ (¬ p2363) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2819)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial40767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory30023 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule40767 (meaning t m 2027) (meaning t m 2241) (meaning t m 2363) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3555) (meaning t m 4363) (meaning t m 5059) source

theorem rule40768 (p2027 p2241 p2750 p2753 p3276 p3355 p3362 p3817 p4366 p4444 p4669 : Prop) (h : (¬ p3355) ∨ (¬ p3276) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p4444) ∨ (¬ p2753) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3362)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory30024 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40768 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 3276) (meaning t m 3355) (meaning t m 3362) (meaning t m 3817) (meaning t m 4366) (meaning t m 4444) (meaning t m 4669) source

theorem rule40769 (p2027 p3707 p3923 p4025 p4191 p4501 p5153 : Prop) (h : (¬ p5153) ∨ (¬ p4501) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p3707) ∨ (¬ p4025) ∨ (¬ p3923)) : (p2027) ∨ (¬ p3707) ∨ (¬ p3923) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4501) ∨ (¬ p5153) := by
  classical
  tauto

theorem initial40769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 5153)) := by
  have source := ElevenTheory.theory30025 t (m.theta 1 6) (m.theta 1 9) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule40769 (meaning t m 2027) (meaning t m 3707) (meaning t m 3923) (meaning t m 4025) (meaning t m 4191) (meaning t m 4501) (meaning t m 5153) source

theorem rule40774 (p2027 p2241 p2476 p2518 p2750 p3541 p4108 : Prop) (h : (¬ p2750) ∨ (¬ p2476) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3541) ∨ (¬ p4108)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3541) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial40774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory30030 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 8)
  exact rule40774 (meaning t m 2027) (meaning t m 2241) (meaning t m 2476) (meaning t m 2518) (meaning t m 2750) (meaning t m 3541) (meaning t m 4108) source

theorem rule40776 (p2027 p2363 p2774 p2819 p2952 p3690 p4320 p4669 p4789 : Prop) (h : (¬ p4789) ∨ (¬ p3690) ∨ (¬ p2819) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p2774) ∨ (¬ p4669) ∨ (¬ p4320) ∨ p2027) : (p2027) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4669) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory30032 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40776 (meaning t m 2027) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 2952) (meaning t m 3690) (meaning t m 4320) (meaning t m 4669) (meaning t m 4789) source

theorem rule40777 (p2027 p2363 p2753 p2774 p2819 p2901 p3556 p3645 p4208 p4877 p5059 : Prop) (h : (¬ p2901) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2774) ∨ (¬ p4208) ∨ (¬ p5059) ∨ (¬ p2819) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p4877) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4208) ∨ (¬ p4877) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial40777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory30033 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule40777 (meaning t m 2027) (meaning t m 2363) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 2901) (meaning t m 3556) (meaning t m 3645) (meaning t m 4208) (meaning t m 4877) (meaning t m 5059) source

theorem rule40781 (p2027 p2598 p2952 p3276 p3333 p4320 p4789 p4831 p5660 : Prop) (h : (¬ p3276) ∨ (¬ p4789) ∨ (¬ p2952) ∨ (¬ p2598) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p5660) ∨ (¬ p4320) ∨ (¬ p3333)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4320) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial40781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory30037 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule40781 (meaning t m 2027) (meaning t m 2598) (meaning t m 2952) (meaning t m 3276) (meaning t m 3333) (meaning t m 4320) (meaning t m 4789) (meaning t m 4831) (meaning t m 5660) source

theorem rule40782 (p2027 p2598 p2963 p3276 p3333 p3568 p4260 p4789 p4831 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4260) ∨ (¬ p3568) ∨ (¬ p4789) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p4831)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3568) ∨ (¬ p4260) ∨ (¬ p4789) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial40782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory30038 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule40782 (meaning t m 2027) (meaning t m 2598) (meaning t m 2963) (meaning t m 3276) (meaning t m 3333) (meaning t m 3568) (meaning t m 4260) (meaning t m 4789) (meaning t m 4831) source

theorem rule40783 (p3073 p3609 p5315 : Prop) (h : (¬ p3609) ∨ (¬ p5315) ∨ p3073) : (p3073) ∨ (¬ p3609) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial40783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3073) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory30039 (m.theta 1 8) (m.theta 2 8) (m.theta 8 9)
  exact rule40783 (meaning t m 3073) (meaning t m 3609) (meaning t m 5315) source

theorem rule40784 (p3609 p4261 p5315 : Prop) (h : (¬ p3609) ∨ (¬ p5315) ∨ (¬ p4261)) : (¬ p3609) ∨ (¬ p4261) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial40784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory30040 (m.theta 1 8) (m.theta 2 8) (m.theta 8 9)
  exact rule40784 (meaning t m 3609) (meaning t m 4261) (meaning t m 5315) source

theorem rule40787 (p2007 p2027 p2114 p2534 p3449 p3609 p3954 p5315 : Prop) (h : (¬ p5315) ∨ p2114 ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2534) ∨ (¬ p3609) ∨ (¬ p3449) ∨ (¬ p2007)) : (¬ p2007) ∨ (p2027) ∨ (p2114) ∨ (¬ p2534) ∨ (¬ p3449) ∨ (¬ p3609) ∨ (¬ p3954) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial40787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory30043 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule40787 (meaning t m 2007) (meaning t m 2027) (meaning t m 2114) (meaning t m 2534) (meaning t m 3449) (meaning t m 3609) (meaning t m 3954) (meaning t m 5315) source

theorem rule40788 (p2027 p2284 p2417 p2598 p2950 p3201 p3646 p3951 p4208 p4789 : Prop) (h : (¬ p3646) ∨ (¬ p3951) ∨ (¬ p2284) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p2417) ∨ (¬ p2950) ∨ (¬ p4789) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2950) ∨ (¬ p3201) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial40788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory30044 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9)
  exact rule40788 (meaning t m 2027) (meaning t m 2284) (meaning t m 2417) (meaning t m 2598) (meaning t m 2950) (meaning t m 3201) (meaning t m 3646) (meaning t m 3951) (meaning t m 4208) (meaning t m 4789) source

theorem rule40790 (p2027 p2241 p2528 p2598 p2750 p2753 p3641 p3860 p5118 p5693 : Prop) (h : (¬ p2753) ∨ (¬ p2598) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p5118) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial40790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory30046 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule40790 (meaning t m 2027) (meaning t m 2241) (meaning t m 2528) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3641) (meaning t m 3860) (meaning t m 5118) (meaning t m 5693) source

theorem rule40791 (p1982 p2027 p2169 p3323 p3324 p3461 p4444 : Prop) (h : p2027 ∨ (¬ p3324) ∨ p2169 ∨ (¬ p3461) ∨ (¬ p4444) ∨ (¬ p1982) ∨ (¬ p3323)) : (¬ p1982) ∨ (p2027) ∨ (p2169) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3461) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial40791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory30047 t (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule40791 (meaning t m 1982) (meaning t m 2027) (meaning t m 2169) (meaning t m 3323) (meaning t m 3324) (meaning t m 3461) (meaning t m 4444) source

theorem rule40792 (p2027 p2252 p2417 p2750 p2933 p2952 p3399 p3570 p3954 p4320 p4668 : Prop) (h : (¬ p2933) ∨ (¬ p2417) ∨ (¬ p3399) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3570) ∨ (¬ p2252) ∨ (¬ p4668) ∨ (¬ p2952) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2417) ∨ (¬ p2750) ∨ (¬ p2933) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3954) ∨ (¬ p4320) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial40792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory30048 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule40792 (meaning t m 2027) (meaning t m 2252) (meaning t m 2417) (meaning t m 2750) (meaning t m 2933) (meaning t m 2952) (meaning t m 3399) (meaning t m 3570) (meaning t m 3954) (meaning t m 4320) (meaning t m 4668) source

theorem rule40794 (p1977 p2027 p2169 p2241 p3452 p3574 p3956 p4116 : Prop) (h : (¬ p3452) ∨ (¬ p2241) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p1977) ∨ p2169 ∨ (¬ p3574) ∨ (¬ p3956)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2241) ∨ (¬ p3452) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial40794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory30050 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule40794 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2241) (meaning t m 3452) (meaning t m 3574) (meaning t m 3956) (meaning t m 4116) source

theorem rule40795 (p2499 p3574 p4116 : Prop) (h : (¬ p3574) ∨ (¬ p4116) ∨ p2499) : (p2499) ∨ (¬ p3574) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial40795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2499) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory30051 (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule40795 (meaning t m 2499) (meaning t m 3574) (meaning t m 4116) source

theorem rule40799 (p2027 p2241 p2459 p2717 p2750 p2753 p3471 p3555 p4363 p5059 : Prop) (h : (¬ p3471) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2241) ∨ (¬ p3555) ∨ (¬ p5059) ∨ (¬ p2459) ∨ (¬ p4363) ∨ (¬ p2750) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial40799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory30055 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule40799 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3555) (meaning t m 4363) (meaning t m 5059) source

theorem rule40800 (p2027 p2132 p2241 p2619 p2750 p2753 p3032 p3146 p3947 p4366 p4669 : Prop) (h : (¬ p3146) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2132) ∨ (¬ p4669) ∨ (¬ p2750) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2619) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3032) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory30056 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40800 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2619) (meaning t m 2750) (meaning t m 2753) (meaning t m 3032) (meaning t m 3146) (meaning t m 3947) (meaning t m 4366) (meaning t m 4669) source

theorem rule40803 (p1977 p2027 p2241 p2764 p3193 p3452 p4425 : Prop) (h : (¬ p3452) ∨ p2764 ∨ (¬ p4425) ∨ (¬ p2241) ∨ (¬ p1977) ∨ (¬ p3193) ∨ p2027) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2764) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial40803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory30059 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 9) (m.theta 9 10)
  exact rule40803 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2764) (meaning t m 3193) (meaning t m 3452) (meaning t m 4425) source

theorem rule40804 (p2027 p2241 p2363 p2750 p2753 p2774 p2819 p3032 p3947 p4366 p4669 : Prop) (h : (¬ p2750) ∨ (¬ p2363) ∨ (¬ p2753) ∨ (¬ p2819) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4669) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3032) ∨ (¬ p3947) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial40804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory30060 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule40804 (meaning t m 2027) (meaning t m 2241) (meaning t m 2363) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3032) (meaning t m 3947) (meaning t m 4366) (meaning t m 4669) source

theorem rule40806 (p2027 p3193 p3229 p3452 p3830 : Prop) (h : p2027 ∨ (¬ p3229) ∨ (¬ p3193) ∨ (¬ p3830) ∨ (¬ p3452)) : (p2027) ∨ (¬ p3193) ∨ (¬ p3229) ∨ (¬ p3452) ∨ (¬ p3830) := by
  classical
  tauto

theorem initial40806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3229)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3830)) := by
  have source := ElevenTheory.theory30062 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 4 9)
  exact rule40806 (meaning t m 2027) (meaning t m 3193) (meaning t m 3229) (meaning t m 3452) (meaning t m 3830) source

theorem rule40808 (p2819 p3641 p4157 p5220 : Prop) (h : (¬ p4157) ∨ (¬ p3641) ∨ (¬ p5220) ∨ p2819) : (p2819) ∨ (¬ p3641) ∨ (¬ p4157) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial40808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2819) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory30064 (m.theta 2 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 8)
  exact rule40808 (meaning t m 2819) (meaning t m 3641) (meaning t m 4157) (meaning t m 5220) source

end SunPrize.SMT
