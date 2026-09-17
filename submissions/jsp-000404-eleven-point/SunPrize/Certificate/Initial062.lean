import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory046
import SunPrize.Certificate.Theory047
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule26809 (p1975 p2027 p2122 p2148 p2156 p3737 p4329 : Prop) (h : (¬ p2156) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p4329) ∨ (¬ p2122) ∨ p2148 ∨ (¬ p3737)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p3737) ∨ (¬ p4329) := by
  classical
  tauto

theorem initial26809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4329)) := by
  have source := ElevenTheory.theory16065 t (m.theta 0 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7)
  exact rule26809 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2148) (meaning t m 2156) (meaning t m 3737) (meaning t m 4329) source

theorem rule26810 (p2027 p2331 p2589 p3323 p3461 p3880 p4117 p4729 p5123 p5568 : Prop) (h : (¬ p5123) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p3880) ∨ (¬ p4729) ∨ (¬ p2589) ∨ (¬ p2331) ∨ (¬ p3461) ∨ (¬ p4117) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p4729) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial26810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory16066 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule26810 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 3323) (meaning t m 3461) (meaning t m 3880) (meaning t m 4117) (meaning t m 4729) (meaning t m 5123) (meaning t m 5568) source

theorem rule26811 (p1978 p2027 p2274 p2373 p2588 p2590 p2765 p4120 : Prop) (h : (¬ p2373) ∨ p2765 ∨ p2027 ∨ (¬ p4120) ∨ (¬ p1978) ∨ (¬ p2588) ∨ (¬ p2274) ∨ (¬ p2590)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (p2765) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial26811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory16067 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule26811 (meaning t m 1978) (meaning t m 2027) (meaning t m 2274) (meaning t m 2373) (meaning t m 2588) (meaning t m 2590) (meaning t m 2765) (meaning t m 4120) source

theorem rule26813 (p2027 p2352 p2573 p3540 p3921 p4405 : Prop) (h : p2027 ∨ (¬ p3921) ∨ (¬ p2352) ∨ (¬ p4405) ∨ (¬ p2573) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial26813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory16069 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule26813 (meaning t m 2027) (meaning t m 2352) (meaning t m 2573) (meaning t m 3540) (meaning t m 3921) (meaning t m 4405) source

theorem rule26814 (p4184 p5131 p5175 p5284 : Prop) (h : (¬ p5131) ∨ (¬ p5284) ∨ (¬ p5175) ∨ (¬ p4184)) : (¬ p4184) ∨ (¬ p5131) ∨ (¬ p5175) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial26814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4184)) ∨ (¬ (meaning t m 5131)) ∨ (¬ (meaning t m 5175)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory16070 (m.theta 3 9) (m.theta 4 10) (m.theta 4 9) (m.theta 9 10)
  exact rule26814 (meaning t m 4184) (meaning t m 5131) (meaning t m 5175) (meaning t m 5284) source

theorem rule26815 (p2027 p2528 p2598 p2743 p2963 p3361 p3641 p4037 p4604 p4737 : Prop) (h : (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p2743) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p4737) ∨ (¬ p2528) ∨ (¬ p4604) ∨ p2027) : (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3641) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial26815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory16071 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule26815 (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 3641) (meaning t m 4037) (meaning t m 4604) (meaning t m 4737) source

theorem rule26816 (p2027 p2737 p2928 p3201 p4257 p4749 : Prop) (h : (¬ p2737) ∨ (¬ p4749) ∨ p2027 ∨ (¬ p4257) ∨ (¬ p3201) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4257) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial26816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory16072 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7)
  exact rule26816 (meaning t m 2027) (meaning t m 2737) (meaning t m 2928) (meaning t m 3201) (meaning t m 4257) (meaning t m 4749) source

theorem rule26817 (p2027 p2383 p2584 p2590 p2656 p3742 p3956 p4644 : Prop) (h : (¬ p2656) ∨ (¬ p2584) ∨ (¬ p2590) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4644)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2590) ∨ (¬ p2656) ∨ (¬ p3742) ∨ (¬ p3956) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial26817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory16073 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule26817 (meaning t m 2027) (meaning t m 2383) (meaning t m 2584) (meaning t m 2590) (meaning t m 2656) (meaning t m 3742) (meaning t m 3956) (meaning t m 4644) source

theorem rule26818 (p1987 p2027 p2098 p2737 p2842 p3055 p4242 : Prop) (h : p2842 ∨ (¬ p2737) ∨ (¬ p3055) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p4242) ∨ (¬ p2098)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2737) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial26818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory16074 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8)
  exact rule26818 (meaning t m 1987) (meaning t m 2027) (meaning t m 2098) (meaning t m 2737) (meaning t m 2842) (meaning t m 3055) (meaning t m 4242) source

theorem rule26822 (p3556 p3645 p4243 p4244 : Prop) (h : (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4243) ∨ p4244) : (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4243) ∨ (p4244) := by
  classical
  tauto

theorem initial26822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4243)) ∨ (meaning t m 4244) := by
  have source := ElevenTheory.theory16078 (m.theta 0 5) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule26822 (meaning t m 3556) (meaning t m 3645) (meaning t m 4243) (meaning t m 4244) source

theorem rule26825 (p2027 p2166 p3051 p4120 p4235 p4632 : Prop) (h : (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4632) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4235) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial26825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory16081 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule26825 (meaning t m 2027) (meaning t m 2166) (meaning t m 3051) (meaning t m 4120) (meaning t m 4235) (meaning t m 4632) source

theorem rule26828 (p1990 p2027 p2299 p2470 p2542 p2563 p2633 p3549 p3591 p4256 p5190 : Prop) (h : p2633 ∨ (¬ p1990) ∨ (¬ p4256) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p3591) ∨ (¬ p3549) ∨ (¬ p5190) ∨ (¬ p2299) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4256) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial26828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory16084 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule26828 (meaning t m 1990) (meaning t m 2027) (meaning t m 2299) (meaning t m 2470) (meaning t m 2542) (meaning t m 2563) (meaning t m 2633) (meaning t m 3549) (meaning t m 3591) (meaning t m 4256) (meaning t m 5190) source

theorem rule26829 (p1990 p2027 p2459 p2563 p2633 p3692 p4119 p4241 p4320 : Prop) (h : (¬ p1990) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4241) ∨ p2633 ∨ (¬ p2563) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3692)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4241) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial26829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory16085 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26829 (meaning t m 1990) (meaning t m 2027) (meaning t m 2459) (meaning t m 2563) (meaning t m 2633) (meaning t m 3692) (meaning t m 4119) (meaning t m 4241) (meaning t m 4320) source

theorem rule26835 (p2027 p2651 p2761 p3422 p3564 p3572 p3773 p4155 p4343 p4621 p4790 p5294 : Prop) (h : (¬ p5294) ∨ (¬ p3564) ∨ (¬ p3572) ∨ (¬ p4621) ∨ (¬ p2651) ∨ (¬ p3773) ∨ (¬ p3422) ∨ (¬ p4790) ∨ (¬ p4343) ∨ p2027 ∨ (¬ p4155) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2761) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3572) ∨ (¬ p3773) ∨ (¬ p4155) ∨ (¬ p4343) ∨ (¬ p4621) ∨ (¬ p4790) ∨ (¬ p5294) := by
  classical
  tauto

theorem initial26835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5294)) := by
  have source := ElevenTheory.theory16091 t (m.theta 0 3) (m.theta 0 7) (m.theta 0 9) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule26835 (meaning t m 2027) (meaning t m 2651) (meaning t m 2761) (meaning t m 3422) (meaning t m 3564) (meaning t m 3572) (meaning t m 3773) (meaning t m 4155) (meaning t m 4343) (meaning t m 4621) (meaning t m 4790) (meaning t m 5294) source

theorem rule26847 (p1988 p2027 p2462 p2651 p3276 p3343 p3572 p3791 p4107 p4391 p4790 : Prop) (h : p2462 ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p4790) ∨ (¬ p3276) ∨ (¬ p3572) ∨ (¬ p1988) ∨ (¬ p2651) ∨ (¬ p3791) ∨ (¬ p4391)) : (¬ p1988) ∨ (p2027) ∨ (p2462) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3572) ∨ (¬ p3791) ∨ (¬ p4107) ∨ (¬ p4391) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial26847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory16103 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule26847 (meaning t m 1988) (meaning t m 2027) (meaning t m 2462) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 3572) (meaning t m 3791) (meaning t m 4107) (meaning t m 4391) (meaning t m 4790) source

theorem rule26850 (p2027 p2396 p2553 p2573 p3365 p3366 p3519 p3553 p3572 p4376 p4668 : Prop) (h : (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3572) ∨ (¬ p3365) ∨ (¬ p3519) ∨ (¬ p4668) ∨ (¬ p2573) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4376) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial26850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory16106 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26850 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3553) (meaning t m 3572) (meaning t m 4376) (meaning t m 4668) source

theorem rule26852 (p2470 p2509 p3519 : Prop) (h : (¬ p2470) ∨ (¬ p3519) ∨ (¬ p2509)) : (¬ p2470) ∨ (¬ p2509) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial26852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory16108 (m.theta 0 4) (m.theta 1 4) (m.theta 4 8)
  exact rule26852 (meaning t m 2470) (meaning t m 2509) (meaning t m 3519) source

theorem rule26853 (p3645 p4539 p4632 : Prop) (h : (¬ p3645) ∨ (¬ p4539) ∨ p4632) : (¬ p3645) ∨ (¬ p4539) ∨ (p4632) := by
  classical
  tauto

theorem initial26853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4539)) ∨ (meaning t m 4632) := by
  have source := ElevenTheory.theory16109 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5)
  exact rule26853 (meaning t m 3645) (meaning t m 4539) (meaning t m 4632) source

theorem rule26860 (p1992 p2027 p2437 p2545 p2696 p2743 p3540 p3905 : Prop) (h : (¬ p1992) ∨ p2545 ∨ (¬ p2743) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3540) ∨ (¬ p2437)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3540) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial26860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory16116 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule26860 (meaning t m 1992) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2696) (meaning t m 2743) (meaning t m 3540) (meaning t m 3905) source

theorem rule26861 (p2027 p2210 p2252 p2440 p2657 p2750 p2972 p3954 p4110 p5046 : Prop) (h : (¬ p4110) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p5046) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p2750) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2972) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial26861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory16117 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule26861 (meaning t m 2027) (meaning t m 2210) (meaning t m 2252) (meaning t m 2440) (meaning t m 2657) (meaning t m 2750) (meaning t m 2972) (meaning t m 3954) (meaning t m 4110) (meaning t m 5046) source

theorem rule26862 (p1998 p2027 p2528 p3008 p3083 p3574 p4348 : Prop) (h : (¬ p3083) ∨ (¬ p1998) ∨ (¬ p3574) ∨ p3008 ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2528)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2528) ∨ (p3008) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial26862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory16118 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26862 (meaning t m 1998) (meaning t m 2027) (meaning t m 2528) (meaning t m 3008) (meaning t m 3083) (meaning t m 3574) (meaning t m 4348) source

theorem rule26865 (p2027 p2307 p2786 p2952 p3483 p3497 p3692 p3822 p4330 p4789 : Prop) (h : (¬ p3822) ∨ (¬ p4330) ∨ (¬ p3483) ∨ (¬ p2307) ∨ (¬ p2952) ∨ (¬ p2786) ∨ (¬ p3497) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p3692)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p4330) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial26865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory16121 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule26865 (meaning t m 2027) (meaning t m 2307) (meaning t m 2786) (meaning t m 2952) (meaning t m 3483) (meaning t m 3497) (meaning t m 3692) (meaning t m 3822) (meaning t m 4330) (meaning t m 4789) source

theorem rule26866 (p2027 p2307 p2534 p2657 p2786 p3483 p3822 p4256 p4330 p4789 : Prop) (h : (¬ p4330) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p2657) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2786) ∨ (¬ p4789)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2786) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4256) ∨ (¬ p4330) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial26866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory16122 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule26866 (meaning t m 2027) (meaning t m 2307) (meaning t m 2534) (meaning t m 2657) (meaning t m 2786) (meaning t m 3483) (meaning t m 3822) (meaning t m 4256) (meaning t m 4330) (meaning t m 4789) source

theorem rule26869 (p2027 p2952 p3055 p3276 p3361 p3497 p3619 p4749 p5123 p5164 p5568 : Prop) (h : (¬ p3361) ∨ (¬ p5123) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p5164) ∨ (¬ p3276) ∨ (¬ p2952) ∨ (¬ p5568) ∨ (¬ p3619) ∨ (¬ p3055) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial26869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5164)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory16125 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26869 (meaning t m 2027) (meaning t m 2952) (meaning t m 3055) (meaning t m 3276) (meaning t m 3361) (meaning t m 3497) (meaning t m 3619) (meaning t m 4749) (meaning t m 5123) (meaning t m 5164) (meaning t m 5568) source

theorem rule26870 (p2027 p3055 p3276 p3361 p3414 p3553 p3619 p4749 p5123 p5164 p5558 : Prop) (h : (¬ p3619) ∨ (¬ p5164) ∨ (¬ p5123) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3361) ∨ (¬ p4749) ∨ (¬ p3276) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p5558)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3276) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3619) ∨ (¬ p4749) ∨ (¬ p5123) ∨ (¬ p5164) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial26870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5164)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory16126 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26870 (meaning t m 2027) (meaning t m 3055) (meaning t m 3276) (meaning t m 3361) (meaning t m 3414) (meaning t m 3553) (meaning t m 3619) (meaning t m 4749) (meaning t m 5123) (meaning t m 5164) (meaning t m 5558) source

theorem rule26872 (p2027 p2132 p2437 p2619 p3146 p3359 p3540 p4697 p4729 : Prop) (h : (¬ p4729) ∨ (¬ p2619) ∨ (¬ p2132) ∨ (¬ p2437) ∨ (¬ p3540) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3359)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2437) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3359) ∨ (¬ p3540) ∨ (¬ p4697) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial26872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory16128 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule26872 (meaning t m 2027) (meaning t m 2132) (meaning t m 2437) (meaning t m 2619) (meaning t m 3146) (meaning t m 3359) (meaning t m 3540) (meaning t m 4697) (meaning t m 4729) source

theorem rule26873 (p2027 p2144 p2220 p2579 p2655 p3105 p3461 p3579 p3581 p3694 p4397 p4429 p4789 p5284 : Prop) (h : (¬ p4429) ∨ (¬ p4397) ∨ (¬ p5284) ∨ (¬ p3581) ∨ (¬ p3694) ∨ (¬ p2579) ∨ (¬ p3461) ∨ (¬ p3579) ∨ (¬ p2144) ∨ (¬ p4789) ∨ (¬ p2655) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p3105)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p3105) ∨ (¬ p3461) ∨ (¬ p3579) ∨ (¬ p3581) ∨ (¬ p3694) ∨ (¬ p4397) ∨ (¬ p4429) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial26873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory16129 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 5) (m.theta 3 7) (m.theta 3 9) (m.theta 4 6) (m.theta 4 7) (m.theta 5 8) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule26873 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2579) (meaning t m 2655) (meaning t m 3105) (meaning t m 3461) (meaning t m 3579) (meaning t m 3581) (meaning t m 3694) (meaning t m 4397) (meaning t m 4429) (meaning t m 4789) (meaning t m 5284) source

theorem rule26874 (p2027 p2088 p2122 p4078 p4170 p4340 p4501 : Prop) (h : (¬ p4078) ∨ (¬ p2122) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p4501)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2122) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial26874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory16130 t (m.theta 0 8) (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule26874 (meaning t m 2027) (meaning t m 2088) (meaning t m 2122) (meaning t m 4078) (meaning t m 4170) (meaning t m 4340) (meaning t m 4501) source

theorem rule26875 (p2027 p2589 p2598 p3237 p3333 p3589 p5193 : Prop) (h : (¬ p3589) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3333) ∨ (¬ p5193) ∨ (¬ p3237) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2598) ∨ (¬ p3237) ∨ (¬ p3333) ∨ (¬ p3589) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial26875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory16131 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9)
  exact rule26875 (meaning t m 2027) (meaning t m 2589) (meaning t m 2598) (meaning t m 3237) (meaning t m 3333) (meaning t m 3589) (meaning t m 5193) source

theorem rule26876 (p2027 p2088 p2187 p4078 p4170 p4340 p4889 : Prop) (h : (¬ p4889) ∨ (¬ p4078) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p4170) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2187) ∨ (¬ p4078) ∨ (¬ p4170) ∨ (¬ p4340) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial26876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory16132 t (m.theta 0 8) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule26876 (meaning t m 2027) (meaning t m 2088) (meaning t m 2187) (meaning t m 4078) (meaning t m 4170) (meaning t m 4340) (meaning t m 4889) source

theorem rule26879 (p2027 p2656 p3389 p3868 p4256 p4383 p5564 : Prop) (h : (¬ p4256) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p5564) ∨ (¬ p4383) ∨ (¬ p3389) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2656) ∨ (¬ p3389) ∨ (¬ p3868) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial26879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory16135 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 10) (m.theta 7 8)
  exact rule26879 (meaning t m 2027) (meaning t m 2656) (meaning t m 3389) (meaning t m 3868) (meaning t m 4256) (meaning t m 4383) (meaning t m 5564) source

theorem rule26881 (p2002 p2027 p2187 p2307 p2387 p2765 p3822 : Prop) (h : (¬ p2002) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2307) ∨ (¬ p2187) ∨ p2765) : (¬ p2002) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (p2765) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial26881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory16137 t (m.theta 0 6) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26881 (meaning t m 2002) (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2387) (meaning t m 2765) (meaning t m 3822) source

theorem rule26882 (p3093 p3449 p4317 : Prop) (h : (¬ p3093) ∨ (¬ p4317) ∨ p3449) : (¬ p3093) ∨ (p3449) ∨ (¬ p4317) := by
  classical
  tauto

theorem initial26882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3093)) ∨ (meaning t m 3449) ∨ (¬ (meaning t m 4317)) := by
  have source := ElevenTheory.theory16138 (m.theta 0 1) (m.theta 1 6) (m.theta 1 8)
  exact rule26882 (meaning t m 3093) (meaning t m 3449) (meaning t m 4317) source

theorem rule26883 (p1985 p2027 p2230 p2427 p2545 p2579 p3016 : Prop) (h : (¬ p1985) ∨ p2545 ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2427)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial26883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory16139 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule26883 (meaning t m 1985) (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2545) (meaning t m 2579) (meaning t m 3016) source

theorem rule26884 (p2027 p2104 p2373 p2406 p2459 p3379 p4340 p4736 p4902 : Prop) (h : (¬ p2373) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4736) ∨ (¬ p2104) ∨ (¬ p4902) ∨ (¬ p4340) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory16140 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26884 (meaning t m 2027) (meaning t m 2104) (meaning t m 2373) (meaning t m 2406) (meaning t m 2459) (meaning t m 3379) (meaning t m 4340) (meaning t m 4736) (meaning t m 4902) source

theorem rule26885 (p2027 p2191 p2563 p2619 p4210 p4244 p4555 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4555) ∨ (¬ p4244) ∨ (¬ p2619) ∨ (¬ p4210) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2619) ∨ (¬ p4210) ∨ (¬ p4244) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial26885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory16141 t (m.theta 1 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule26885 (meaning t m 2027) (meaning t m 2191) (meaning t m 2563) (meaning t m 2619) (meaning t m 4210) (meaning t m 4244) (meaning t m 4555) source

theorem rule26889 (p2027 p2132 p2619 p3146 p3414 p3553 p4789 p5118 p5558 : Prop) (h : p2027 ∨ (¬ p3146) ∨ (¬ p2132) ∨ (¬ p4789) ∨ (¬ p2619) ∨ (¬ p3553) ∨ (¬ p3414) ∨ (¬ p5118) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4789) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial26889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory16145 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26889 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 3146) (meaning t m 3414) (meaning t m 3553) (meaning t m 4789) (meaning t m 5118) (meaning t m 5558) source

theorem rule26890 (p3324 p3325 p3568 : Prop) (h : (¬ p3324) ∨ (¬ p3325) ∨ p3568) : (¬ p3324) ∨ (¬ p3325) ∨ (p3568) := by
  classical
  tauto

theorem initial26890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3325)) ∨ (meaning t m 3568) := by
  have source := ElevenTheory.theory16146 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26890 (meaning t m 3324) (meaning t m 3325) (meaning t m 3568) source

theorem rule26892 (p2504 p3958 p4514 : Prop) (h : (¬ p2504) ∨ (¬ p3958) ∨ p4514) : (¬ p2504) ∨ (¬ p3958) ∨ (p4514) := by
  classical
  tauto

theorem initial26892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3958)) ∨ (meaning t m 4514) := by
  have source := ElevenTheory.theory16148 t (m.theta 1 6) (m.theta 4 6) (m.theta 5 6)
  exact rule26892 (meaning t m 2504) (meaning t m 3958) (meaning t m 4514) source

theorem rule26893 (p2027 p2264 p2696 p2742 p3027 p3363 p3540 p3585 p4278 p4666 p4737 : Prop) (h : (¬ p3363) ∨ (¬ p3027) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2264) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial26893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory16149 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26893 (meaning t m 2027) (meaning t m 2264) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 4278) (meaning t m 4666) (meaning t m 4737) source

theorem rule26895 (p1990 p2027 p2611 p2839 p2860 p3471 p3588 : Prop) (h : p2611 ∨ (¬ p3471) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2860) ∨ (¬ p3588)) : (¬ p1990) ∨ (p2027) ∨ (p2611) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial26895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory16151 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6)
  exact rule26895 (meaning t m 1990) (meaning t m 2027) (meaning t m 2611) (meaning t m 2839) (meaning t m 2860) (meaning t m 3471) (meaning t m 3588) source

theorem rule26896 (p1975 p2027 p2765 p3051 p3246 p3370 p4107 p4173 : Prop) (h : (¬ p4107) ∨ (¬ p3246) ∨ (¬ p3370) ∨ p2027 ∨ p2765 ∨ (¬ p3051) ∨ (¬ p4173) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (p2765) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3370) ∨ (¬ p4107) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial26896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory16152 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule26896 (meaning t m 1975) (meaning t m 2027) (meaning t m 2765) (meaning t m 3051) (meaning t m 3246) (meaning t m 3370) (meaning t m 4107) (meaning t m 4173) source

theorem rule26898 (p2027 p2307 p2534 p2589 p2668 p3146 p3347 p3568 p4134 p4257 p4607 p4866 p5016 : Prop) (h : (¬ p4607) ∨ p2027 ∨ (¬ p4866) ∨ (¬ p2534) ∨ (¬ p2307) ∨ (¬ p3347) ∨ (¬ p4257) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p3146) ∨ (¬ p3568) ∨ (¬ p4134) ∨ (¬ p5016)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p3146) ∨ (¬ p3347) ∨ (¬ p3568) ∨ (¬ p4134) ∨ (¬ p4257) ∨ (¬ p4607) ∨ (¬ p4866) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial26898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory16154 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule26898 (meaning t m 2027) (meaning t m 2307) (meaning t m 2534) (meaning t m 2589) (meaning t m 2668) (meaning t m 3146) (meaning t m 3347) (meaning t m 3568) (meaning t m 4134) (meaning t m 4257) (meaning t m 4607) (meaning t m 4866) (meaning t m 5016) source

theorem rule26900 (p2027 p2247 p2744 p3055 p3093 p3309 p3366 p3584 p3956 p4501 : Prop) (h : (¬ p3366) ∨ (¬ p3309) ∨ (¬ p4501) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3584) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial26900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory16156 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule26900 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3055) (meaning t m 3093) (meaning t m 3309) (meaning t m 3366) (meaning t m 3584) (meaning t m 3956) (meaning t m 4501) source

theorem rule26901 (p2027 p2440 p3016 p4031 p4120 p4203 p4507 : Prop) (h : (¬ p4031) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p4120) ∨ (¬ p4203) ∨ (¬ p4507)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4203) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial26901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory16157 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule26901 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 4031) (meaning t m 4120) (meaning t m 4203) (meaning t m 4507) source

theorem rule26903 (p2027 p2363 p2534 p2819 p3573 p5225 : Prop) (h : (¬ p5225) ∨ (¬ p2819) ∨ (¬ p2534) ∨ (¬ p3573) ∨ p2027 ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2819) ∨ (¬ p3573) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial26903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory16159 t (m.theta 2 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26903 (meaning t m 2027) (meaning t m 2363) (meaning t m 2534) (meaning t m 2819) (meaning t m 3573) (meaning t m 5225) source

theorem rule26904 (p2651 p3286 p5176 : Prop) (h : (¬ p5176) ∨ (¬ p2651) ∨ p3286) : (¬ p2651) ∨ (p3286) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial26904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (meaning t m 3286) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory16160 (m.theta 0 3) (m.theta 3 4) (m.theta 3 9)
  exact rule26904 (meaning t m 2651) (meaning t m 3286) (meaning t m 5176) source

theorem rule26907 (p2027 p2230 p2246 p2440 p2608 p2663 p2744 p3083 p3591 p3923 p4596 : Prop) (h : (¬ p3083) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p2440) ∨ (¬ p4596) ∨ (¬ p2246) ∨ (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2744)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial26907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory16163 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8)
  exact rule26907 (meaning t m 2027) (meaning t m 2230) (meaning t m 2246) (meaning t m 2440) (meaning t m 2608) (meaning t m 2663) (meaning t m 2744) (meaning t m 3083) (meaning t m 3591) (meaning t m 3923) (meaning t m 4596) source

theorem rule26909 (p2027 p2088 p3591 p4238 p4261 p4371 p4521 : Prop) (h : (¬ p3591) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p4238) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3591) ∨ (¬ p4238) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial26909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory16165 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 8) (m.theta 1 6) (m.theta 1 8) (m.theta 8 9)
  exact rule26909 (meaning t m 2027) (meaning t m 2088) (meaning t m 3591) (meaning t m 4238) (meaning t m 4261) (meaning t m 4371) (meaning t m 4521) source

theorem rule26911 (p2027 p2248 p3166 p3256 p3588 p3659 p3692 p3954 p4902 : Prop) (h : p2027 ∨ (¬ p3954) ∨ (¬ p3588) ∨ (¬ p3256) ∨ (¬ p2248) ∨ (¬ p3659) ∨ (¬ p3166) ∨ (¬ p3692) ∨ (¬ p4902)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory16167 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26911 (meaning t m 2027) (meaning t m 2248) (meaning t m 3166) (meaning t m 3256) (meaning t m 3588) (meaning t m 3659) (meaning t m 3692) (meaning t m 3954) (meaning t m 4902) source

theorem rule26913 (p1990 p2027 p2563 p2622 p2630 p2657 p2946 p4241 : Prop) (h : (¬ p2657) ∨ (¬ p2630) ∨ (¬ p4241) ∨ p2622 ∨ p2027 ∨ (¬ p2563) ∨ (¬ p1990) ∨ (¬ p2946)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial26913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory16169 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule26913 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2946) (meaning t m 4241) source

theorem rule26917 (p2668 p3156 p4336 p4506 : Prop) (h : (¬ p2668) ∨ (¬ p4336) ∨ (¬ p4506) ∨ p3156) : (¬ p2668) ∨ (p3156) ∨ (¬ p4336) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial26917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (meaning t m 3156) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory16173 (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8)
  exact rule26917 (meaning t m 2668) (meaning t m 3156) (meaning t m 4336) (meaning t m 4506) source

theorem rule26921 (p1982 p2027 p2148 p2156 p2373 p3146 p4110 : Prop) (h : (¬ p4110) ∨ p2148 ∨ (¬ p2373) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial26921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory16177 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule26921 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2373) (meaning t m 3146) (meaning t m 4110) source

theorem rule26922 (p2027 p2104 p2230 p2459 p2563 p3125 p3322 p4133 p4340 p4419 : Prop) (h : (¬ p2563) ∨ (¬ p2104) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3125) ∨ (¬ p4419) ∨ (¬ p2459) ∨ (¬ p3322) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3322) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial26922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory16178 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26922 (meaning t m 2027) (meaning t m 2104) (meaning t m 2230) (meaning t m 2459) (meaning t m 2563) (meaning t m 3125) (meaning t m 3322) (meaning t m 4133) (meaning t m 4340) (meaning t m 4419) source

theorem rule26923 (p2027 p2685 p3093 p3309 p3366 p3414 p3452 p3877 p4236 p4376 p4501 p4769 : Prop) (h : (¬ p4769) ∨ (¬ p3877) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4501) ∨ (¬ p3452) ∨ (¬ p3366) ∨ (¬ p2685) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4501) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial26923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory16179 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule26923 (meaning t m 2027) (meaning t m 2685) (meaning t m 3093) (meaning t m 3309) (meaning t m 3366) (meaning t m 3414) (meaning t m 3452) (meaning t m 3877) (meaning t m 4236) (meaning t m 4376) (meaning t m 4501) (meaning t m 4769) source

theorem rule26933 (p2470 p2518 p3519 : Prop) (h : (¬ p3519) ∨ (¬ p2470) ∨ p2518) : (¬ p2470) ∨ (p2518) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial26933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (meaning t m 2518) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory16189 (m.theta 0 4) (m.theta 1 4) (m.theta 4 8)
  exact rule26933 (meaning t m 2470) (meaning t m 2518) (meaning t m 3519) source

theorem rule26935 (p2685 p2995 p3136 : Prop) (h : (¬ p3136) ∨ (¬ p2995) ∨ p2685) : (p2685) ∨ (¬ p2995) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial26935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2685) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory16191 (m.theta 2 3) (m.theta 3 5) (m.theta 3 7)
  exact rule26935 (meaning t m 2685) (meaning t m 2995) (meaning t m 3136) source

theorem rule26936 (p2027 p2499 p2922 p3956 p4501 p4710 : Prop) (h : (¬ p4710) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2499) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3956) ∨ (¬ p4501) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial26936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory16192 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule26936 (meaning t m 2027) (meaning t m 2499) (meaning t m 2922) (meaning t m 3956) (meaning t m 4501) (meaning t m 4710) source

theorem rule26937 (p1982 p2027 p2166 p2202 p2363 p2563 p4173 p4441 : Prop) (h : p2027 ∨ (¬ p4441) ∨ (¬ p1982) ∨ (¬ p4173) ∨ (¬ p2363) ∨ (¬ p2166) ∨ p2202 ∨ (¬ p2563)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2166) ∨ (p2202) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial26937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory16193 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26937 (meaning t m 1982) (meaning t m 2027) (meaning t m 2166) (meaning t m 2202) (meaning t m 2363) (meaning t m 2563) (meaning t m 4173) (meaning t m 4441) source

theorem rule26943 (p2027 p2363 p3055 p3063 p3093 p3876 p4278 p4669 p4736 : Prop) (h : (¬ p4278) ∨ (¬ p4736) ∨ (¬ p3063) ∨ (¬ p4669) ∨ (¬ p3093) ∨ (¬ p3055) ∨ (¬ p2363) ∨ (¬ p3876) ∨ p2027) : (p2027) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial26943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory16199 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26943 (meaning t m 2027) (meaning t m 2363) (meaning t m 3055) (meaning t m 3063) (meaning t m 3093) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) (meaning t m 4736) source

theorem rule26952 (p2027 p2459 p2717 p3692 p4119 p4898 : Prop) (h : p2027 ∨ (¬ p4898) ∨ (¬ p4119) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2717) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial26952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory16208 t (m.theta 2 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26952 (meaning t m 2027) (meaning t m 2459) (meaning t m 2717) (meaning t m 3692) (meaning t m 4119) (meaning t m 4898) source

theorem rule26953 (p2588 p4025 p4137 : Prop) (h : (¬ p4025) ∨ (¬ p2588) ∨ p4137) : (¬ p2588) ∨ (¬ p4025) ∨ (p4137) := by
  classical
  tauto

theorem initial26953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4025)) ∨ (meaning t m 4137) := by
  have source := ElevenTheory.theory16209 (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule26953 (meaning t m 2588) (meaning t m 4025) (meaning t m 4137) source

theorem rule26954 (p2588 p3744 p4025 p4203 : Prop) (h : (¬ p4203) ∨ (¬ p4025) ∨ (¬ p2588) ∨ p3744) : (¬ p2588) ∨ (p3744) ∨ (¬ p4025) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial26954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2588)) ∨ (meaning t m 3744) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory16210 (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule26954 (meaning t m 2588) (meaning t m 3744) (meaning t m 4025) (meaning t m 4203) source

theorem rule26955 (p2027 p3055 p3366 p3631 p3687 p3821 p3959 p4357 p4749 : Prop) (h : p2027 ∨ (¬ p3959) ∨ (¬ p4749) ∨ (¬ p3055) ∨ (¬ p4357) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p3687) ∨ (¬ p3366)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4357) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial26955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory16211 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9)
  exact rule26955 (meaning t m 2027) (meaning t m 3055) (meaning t m 3366) (meaning t m 3631) (meaning t m 3687) (meaning t m 3821) (meaning t m 3959) (meaning t m 4357) (meaning t m 4749) source

theorem rule26956 (p4337 p4401 p4560 : Prop) (h : (¬ p4337) ∨ (¬ p4560) ∨ p4401) : (¬ p4337) ∨ (p4401) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial26956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4337)) ∨ (meaning t m 4401) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory16212 t (m.theta 2 6) (m.theta 3 6) (m.theta 5 6)
  exact rule26956 (meaning t m 4337) (meaning t m 4401) (meaning t m 4560) source

theorem rule26957 (p4443 p4604 p4625 : Prop) (h : (¬ p4604) ∨ (¬ p4443) ∨ p4625) : (¬ p4443) ∨ (¬ p4604) ∨ (p4625) := by
  classical
  tauto

theorem initial26957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4604)) ∨ (meaning t m 4625) := by
  have source := ElevenTheory.theory16213 t (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule26957 (meaning t m 4443) (meaning t m 4604) (meaning t m 4625) source

theorem rule26960 (p2027 p2246 p2264 p2459 p2608 p2663 p2744 p3389 p3740 p3834 p4351 p5118 p5693 : Prop) (h : (¬ p2663) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p2459) ∨ (¬ p3740) ∨ (¬ p3834) ∨ (¬ p2744) ∨ (¬ p4351) ∨ (¬ p3389) ∨ (¬ p5118) ∨ (¬ p2264) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3389) ∨ (¬ p3740) ∨ (¬ p3834) ∨ (¬ p4351) ∨ (¬ p5118) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial26960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory16216 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 1 9) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26960 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2459) (meaning t m 2608) (meaning t m 2663) (meaning t m 2744) (meaning t m 3389) (meaning t m 3740) (meaning t m 3834) (meaning t m 4351) (meaning t m 5118) (meaning t m 5693) source

theorem rule26963 (p1982 p2027 p2765 p3105 p3680 p3758 p4444 : Prop) (h : (¬ p3680) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p3758) ∨ p2765 ∨ (¬ p3105)) : (¬ p1982) ∨ (p2027) ∨ (p2765) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial26963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory16219 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26963 (meaning t m 1982) (meaning t m 2027) (meaning t m 2765) (meaning t m 3105) (meaning t m 3680) (meaning t m 3758) (meaning t m 4444) source

theorem rule26964 (p2027 p3426 p3434 p4107 p4358 p4501 : Prop) (h : (¬ p4358) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p4107) ∨ (¬ p3426) ∨ (¬ p3434)) : (p2027) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p4107) ∨ (¬ p4358) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial26964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory16220 t (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule26964 (meaning t m 2027) (meaning t m 3426) (meaning t m 3434) (meaning t m 4107) (meaning t m 4358) (meaning t m 4501) source

theorem rule26965 (p1997 p2027 p2459 p2534 p2542 p2633 p4256 : Prop) (h : (¬ p2542) ∨ (¬ p4256) ∨ p2633 ∨ (¬ p1997) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2534)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2542) ∨ (p2633) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial26965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory16221 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26965 (meaning t m 1997) (meaning t m 2027) (meaning t m 2459) (meaning t m 2534) (meaning t m 2542) (meaning t m 2633) (meaning t m 4256) source

theorem rule26966 (p2027 p2122 p2246 p2313 p2744 p3286 p3506 p3645 p3917 p4198 p4444 p4604 p4874 : Prop) (h : (¬ p4444) ∨ (¬ p3645) ∨ (¬ p4874) ∨ (¬ p4198) ∨ (¬ p3506) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p2246) ∨ (¬ p2122) ∨ (¬ p4604) ∨ (¬ p2744) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3917) ∨ (¬ p4198) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial26966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory16222 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 3 9) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26966 (meaning t m 2027) (meaning t m 2122) (meaning t m 2246) (meaning t m 2313) (meaning t m 2744) (meaning t m 3286) (meaning t m 3506) (meaning t m 3645) (meaning t m 3917) (meaning t m 4198) (meaning t m 4444) (meaning t m 4604) (meaning t m 4874) source

theorem rule26967 (p1983 p2027 p2417 p3578 p3644 p3969 p5558 : Prop) (h : (¬ p3644) ∨ (¬ p3969) ∨ p2027 ∨ p3578 ∨ (¬ p2417) ∨ (¬ p1983) ∨ (¬ p5558)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (p3578) ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial26967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory16223 t (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule26967 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 3578) (meaning t m 3644) (meaning t m 3969) (meaning t m 5558) source

theorem rule26968 (p1994 p2027 p2406 p2440 p2633 p3347 p3540 p3644 : Prop) (h : (¬ p3347) ∨ (¬ p2406) ∨ (¬ p3644) ∨ (¬ p2440) ∨ (¬ p1994) ∨ p2633 ∨ p2027 ∨ (¬ p3540)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2633) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial26968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory16224 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule26968 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2633) (meaning t m 3347) (meaning t m 3540) (meaning t m 3644) source

theorem rule26970 (p2027 p2797 p3567 p4173 p4315 p4356 p4957 : Prop) (h : (¬ p4173) ∨ (¬ p3567) ∨ (¬ p4315) ∨ (¬ p4957) ∨ (¬ p2797) ∨ (¬ p4356) ∨ p2027) : (p2027) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4173) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial26970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory16226 t (m.theta 0 6) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule26970 (meaning t m 2027) (meaning t m 2797) (meaning t m 3567) (meaning t m 4173) (meaning t m 4315) (meaning t m 4356) (meaning t m 4957) source

theorem rule26972 (p2027 p2156 p2891 p3556 p3952 p4960 : Prop) (h : (¬ p3556) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4960) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3952) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial26972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory16228 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule26972 (meaning t m 2027) (meaning t m 2156) (meaning t m 2891) (meaning t m 3556) (meaning t m 3952) (meaning t m 4960) source

theorem rule26978 (p2027 p2140 p2829 p3583 p3646 p4185 : Prop) (h : p2027 ∨ (¬ p4185) ∨ (¬ p2140) ∨ (¬ p3583) ∨ (¬ p2829) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2140) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial26978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory16234 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6)
  exact rule26978 (meaning t m 2027) (meaning t m 2140) (meaning t m 2829) (meaning t m 3583) (meaning t m 3646) (meaning t m 4185) source

theorem rule26980 (p1982 p2027 p2169 p3461 p3483 p4358 p4444 : Prop) (h : (¬ p1982) ∨ p2027 ∨ p2169 ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p4444) ∨ (¬ p3461)) : (¬ p1982) ∨ (p2027) ∨ (p2169) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial26980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory16236 t (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26980 (meaning t m 1982) (meaning t m 2027) (meaning t m 2169) (meaning t m 3461) (meaning t m 3483) (meaning t m 4358) (meaning t m 4444) source

theorem rule26981 (p2027 p2459 p3438 p3449 p3834 p4832 : Prop) (h : p2027 ∨ (¬ p4832) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p2459) ∨ (¬ p3438)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4832) := by
  classical
  tauto

theorem initial26981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4832)) := by
  have source := ElevenTheory.theory16237 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26981 (meaning t m 2027) (meaning t m 2459) (meaning t m 3438) (meaning t m 3449) (meaning t m 3834) (meaning t m 4832) source

theorem rule26982 (p2027 p2132 p2192 p2780 p4428 p4878 : Prop) (h : (¬ p2192) ∨ (¬ p4428) ∨ (¬ p2132) ∨ (¬ p4878) ∨ p2027 ∨ (¬ p2780)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2780) ∨ (¬ p4428) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial26982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory16238 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6)
  exact rule26982 (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2780) (meaning t m 4428) (meaning t m 4878) source

theorem rule26983 (p2027 p2122 p2248 p2542 p2563 p2651 p3549 p3591 p4401 : Prop) (h : (¬ p2248) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p2122) ∨ (¬ p2542) ∨ (¬ p4401) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2248) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial26983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory16239 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule26983 (meaning t m 2027) (meaning t m 2122) (meaning t m 2248) (meaning t m 2542) (meaning t m 2563) (meaning t m 2651) (meaning t m 3549) (meaning t m 3591) (meaning t m 4401) source

theorem rule26984 (p2027 p2248 p3286 p3506 p3555 p3744 p4173 p4381 p4625 : Prop) (h : (¬ p4381) ∨ (¬ p4173) ∨ (¬ p3744) ∨ (¬ p4625) ∨ (¬ p3506) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3555) ∨ (¬ p3286)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4381) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial26984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory16240 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule26984 (meaning t m 2027) (meaning t m 2248) (meaning t m 3286) (meaning t m 3506) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4381) (meaning t m 4625) source

theorem rule26987 (p2027 p2156 p2406 p3952 p4109 p4700 p4814 : Prop) (h : p2027 ∨ (¬ p2156) ∨ (¬ p4700) ∨ (¬ p2406) ∨ (¬ p3952) ∨ (¬ p4814) ∨ (¬ p4109)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2406) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4700) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial26987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory16243 t (m.theta 0 5) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule26987 (meaning t m 2027) (meaning t m 2156) (meaning t m 2406) (meaning t m 3952) (meaning t m 4109) (meaning t m 4700) (meaning t m 4814) source

theorem rule26988 (p1994 p2027 p2622 p2743 p3367 p3422 p3574 : Prop) (h : (¬ p1994) ∨ p2622 ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3422) ∨ (¬ p3367)) : (¬ p1994) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial26988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory16244 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule26988 (meaning t m 1994) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3422) (meaning t m 3574) source

theorem rule26989 (p1994 p2027 p2573 p2764 p3346 p3574 p4425 : Prop) (h : p2764 ∨ (¬ p4425) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2573) ∨ (¬ p3346) ∨ (¬ p3574)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2573) ∨ (p2764) ∨ (¬ p3346) ∨ (¬ p3574) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial26989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory16245 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule26989 (meaning t m 1994) (meaning t m 2027) (meaning t m 2573) (meaning t m 2764) (meaning t m 3346) (meaning t m 3574) (meaning t m 4425) source

theorem rule26990 (p2138 p3055 p3582 : Prop) (h : (¬ p2138) ∨ (¬ p3582) ∨ p3055) : (¬ p2138) ∨ (p3055) ∨ (¬ p3582) := by
  classical
  tauto

theorem initial26990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (meaning t m 3055) ∨ (¬ (meaning t m 3582)) := by
  have source := ElevenTheory.theory16246 (m.theta 0 2) (m.theta 2 4) (m.theta 2 5)
  exact rule26990 (meaning t m 2138) (meaning t m 3055) (meaning t m 3582) source

theorem rule26993 (p2027 p2132 p2753 p2870 p3246 p3379 p3860 p3950 p4261 p5216 : Prop) (h : (¬ p3246) ∨ (¬ p2870) ∨ (¬ p3860) ∨ (¬ p5216) ∨ (¬ p3379) ∨ (¬ p4261) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial26993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory16249 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule26993 (meaning t m 2027) (meaning t m 2132) (meaning t m 2753) (meaning t m 2870) (meaning t m 3246) (meaning t m 3379) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 5216) source

theorem rule26994 (p1988 p2027 p2323 p2807 p3506 p3572 p3755 : Prop) (h : p2323 ∨ (¬ p3506) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p1988) ∨ (¬ p2807)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3572) ∨ (¬ p3755) := by
  classical
  tauto

theorem initial26994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3755)) := by
  have source := ElevenTheory.theory16250 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 9 10)
  exact rule26994 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2807) (meaning t m 3506) (meaning t m 3572) (meaning t m 3755) source

theorem rule26995 (p4118 p4348 p4548 : Prop) (h : (¬ p4548) ∨ (¬ p4348) ∨ p4118) : (p4118) ∨ (¬ p4348) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial26995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4118) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory16251 (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26995 (meaning t m 4118) (meaning t m 4348) (meaning t m 4548) source

theorem rule26997 (p2027 p2579 p2696 p3115 p3136 p3956 p4347 p4450 p4729 : Prop) (h : (¬ p4729) ∨ (¬ p2579) ∨ (¬ p3136) ∨ (¬ p4347) ∨ (¬ p2696) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4450) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4450) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial26997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory16253 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule26997 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 3115) (meaning t m 3136) (meaning t m 3956) (meaning t m 4347) (meaning t m 4450) (meaning t m 4729) source

theorem rule26999 (p4210 p4363 p4948 : Prop) (h : (¬ p4363) ∨ (¬ p4210) ∨ p4948) : (¬ p4210) ∨ (¬ p4363) ∨ (p4948) := by
  classical
  tauto

theorem initial26999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4363)) ∨ (meaning t m 4948) := by
  have source := ElevenTheory.theory16255 (m.theta 1 5) (m.theta 4 5) (m.theta 5 9)
  exact rule26999 (meaning t m 4210) (meaning t m 4363) (meaning t m 4948) source

theorem rule27000 (p2027 p3178 p3877 p3998 p4790 p5600 : Prop) (h : (¬ p3178) ∨ (¬ p3877) ∨ (¬ p5600) ∨ (¬ p3998) ∨ (¬ p4790) ∨ p2027) : (p2027) ∨ (¬ p3178) ∨ (¬ p3877) ∨ (¬ p3998) ∨ (¬ p4790) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial27000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory16256 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 3) (m.theta 3 8) (m.theta 8 10)
  exact rule27000 (meaning t m 2027) (meaning t m 3178) (meaning t m 3877) (meaning t m 3998) (meaning t m 4790) (meaning t m 5600) source

theorem rule27003 (p3696 p4592 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p3696) ∨ p4592) : (¬ p3696) ∨ (p4592) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial27003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3696)) ∨ (meaning t m 4592) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory16259 t (m.theta 0 8) (m.theta 5 8) (m.theta 7 8)
  exact rule27003 (meaning t m 3696) (meaning t m 4592) (meaning t m 4905) source

theorem rule27004 (p2027 p2437 p2651 p3364 p3876 p4790 : Prop) (h : (¬ p2437) ∨ (¬ p3364) ∨ p2027 ∨ (¬ p4790) ∨ (¬ p2651) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3876) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial27004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory16260 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule27004 (meaning t m 2027) (meaning t m 2437) (meaning t m 2651) (meaning t m 3364) (meaning t m 3876) (meaning t m 4790) source

theorem rule27005 (p2027 p2579 p2744 p3212 p3347 p3370 p3422 p3680 p4257 p4365 p4381 p4641 p5160 : Prop) (h : (¬ p3212) ∨ (¬ p4365) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3347) ∨ (¬ p5160) ∨ (¬ p2744) ∨ (¬ p4641) ∨ (¬ p4381) ∨ (¬ p4257) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3212) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3680) ∨ (¬ p4257) ∨ (¬ p4365) ∨ (¬ p4381) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial27005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory16261 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule27005 (meaning t m 2027) (meaning t m 2579) (meaning t m 2744) (meaning t m 3212) (meaning t m 3347) (meaning t m 3370) (meaning t m 3422) (meaning t m 3680) (meaning t m 4257) (meaning t m 4365) (meaning t m 4381) (meaning t m 4641) (meaning t m 5160) source

theorem rule27011 (p2253 p2331 p3093 p4319 : Prop) (h : (¬ p4319) ∨ (¬ p2331) ∨ (¬ p2253) ∨ p3093) : (¬ p2253) ∨ (¬ p2331) ∨ (p3093) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial27011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 3093) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory16267 (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 6)
  exact rule27011 (meaning t m 2253) (meaning t m 2331) (meaning t m 3093) (meaning t m 4319) source

theorem rule27012 (p1977 p2027 p2299 p2396 p2633 p2996 p3577 p4155 p4324 : Prop) (h : (¬ p4324) ∨ (¬ p1977) ∨ (¬ p4155) ∨ p2633 ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3577) ∨ (¬ p2996)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3577) ∨ (¬ p4155) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial27012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory16268 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27012 (meaning t m 1977) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 2996) (meaning t m 3577) (meaning t m 4155) (meaning t m 4324) source

theorem rule27019 (p2027 p2313 p2505 p2608 p3309 p4376 p5015 : Prop) (h : (¬ p2608) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p5015) ∨ (¬ p3309) ∨ (¬ p2505)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2505) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4376) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial27019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory16275 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7)
  exact rule27019 (meaning t m 2027) (meaning t m 2313) (meaning t m 2505) (meaning t m 2608) (meaning t m 3309) (meaning t m 4376) (meaning t m 5015) source

theorem rule27020 (p1987 p2027 p2662 p2810 p2881 p2938 p3540 p3644 : Prop) (h : (¬ p3644) ∨ p2938 ∨ (¬ p1987) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2881)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3540) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial27020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory16276 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule27020 (meaning t m 1987) (meaning t m 2027) (meaning t m 2662) (meaning t m 2810) (meaning t m 2881) (meaning t m 2938) (meaning t m 3540) (meaning t m 3644) source

theorem rule27022 (p2027 p2331 p2727 p2810 p4154 p4790 : Prop) (h : (¬ p2727) ∨ (¬ p4790) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4154) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p4154) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial27022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory16278 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule27022 (meaning t m 2027) (meaning t m 2331) (meaning t m 2727) (meaning t m 2810) (meaning t m 4154) (meaning t m 4790) source

theorem rule27024 (p3660 p3872 p4203 p4235 : Prop) (h : (¬ p3660) ∨ (¬ p4203) ∨ (¬ p3872) ∨ (¬ p4235)) : (¬ p3660) ∨ (¬ p3872) ∨ (¬ p4203) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial27024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory16280 (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule27024 (meaning t m 3660) (meaning t m 3872) (meaning t m 4203) (meaning t m 4235) source

theorem rule27026 (p2027 p2741 p2839 p2870 p3848 p4040 p4204 p5043 : Prop) (h : (¬ p4040) ∨ (¬ p4204) ∨ (¬ p2870) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p5043) ∨ (¬ p2839) ∨ (¬ p3848)) : (p2027) ∨ (¬ p2741) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3848) ∨ (¬ p4040) ∨ (¬ p4204) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial27026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory16282 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 9) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule27026 (meaning t m 2027) (meaning t m 2741) (meaning t m 2839) (meaning t m 2870) (meaning t m 3848) (meaning t m 4040) (meaning t m 4204) (meaning t m 5043) source

theorem rule27027 (p1996 p2027 p2499 p2922 p3008 p3516 p3575 p3947 : Prop) (h : (¬ p2499) ∨ p3008 ∨ (¬ p2922) ∨ (¬ p1996) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (p3008) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial27027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory16283 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule27027 (meaning t m 1996) (meaning t m 2027) (meaning t m 2499) (meaning t m 2922) (meaning t m 3008) (meaning t m 3516) (meaning t m 3575) (meaning t m 3947) source

theorem rule27028 (p2027 p3146 p3166 p3292 p3438 p3853 p5063 : Prop) (h : (¬ p3438) ∨ (¬ p3146) ∨ (¬ p3853) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5063) ∨ p2027) : (p2027) ∨ (¬ p3146) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p3438) ∨ (¬ p3853) ∨ (¬ p5063) := by
  classical
  tauto

theorem initial27028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 5063)) := by
  have source := ElevenTheory.theory16284 t (m.theta 0 3) (m.theta 1 9) (m.theta 3 8) (m.theta 3 9) (m.theta 5 8) (m.theta 8 9)
  exact rule27028 (meaning t m 2027) (meaning t m 3146) (meaning t m 3166) (meaning t m 3292) (meaning t m 3438) (meaning t m 3853) (meaning t m 5063) source

theorem rule27029 (p1994 p2027 p2630 p2766 p3551 p3572 p4155 p4348 : Prop) (h : (¬ p2630) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p4348) ∨ (¬ p4155) ∨ p2766 ∨ (¬ p3551)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2766) ∨ (¬ p3551) ∨ (¬ p3572) ∨ (¬ p4155) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial27029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory16285 t (m.theta 0 7) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule27029 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2766) (meaning t m 3551) (meaning t m 3572) (meaning t m 4155) (meaning t m 4348) source

theorem rule27030 (p2027 p2132 p2860 p3737 p3817 p4366 p4381 p4733 p5250 : Prop) (h : p2027 ∨ (¬ p5250) ∨ (¬ p3737) ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p2860) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3737) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) ∨ (¬ p4733) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial27030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory16286 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule27030 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3737) (meaning t m 3817) (meaning t m 4366) (meaning t m 4381) (meaning t m 4733) (meaning t m 5250) source

theorem rule27032 (p2027 p2248 p2331 p2928 p3005 p3452 p3644 p4195 p4550 : Prop) (h : (¬ p3644) ∨ (¬ p4195) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p4550) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2928) ∨ (¬ p3005) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4195) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial27032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory16288 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule27032 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2928) (meaning t m 3005) (meaning t m 3452) (meaning t m 3644) (meaning t m 4195) (meaning t m 4550) source

theorem rule27034 (p2027 p2476 p2901 p2946 p3905 p4129 p4340 p4444 p4786 p4826 p5373 : Prop) (h : (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4826) ∨ (¬ p4786) ∨ (¬ p3905) ∨ (¬ p4129) ∨ (¬ p2476) ∨ (¬ p5373) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3905) ∨ (¬ p4129) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4786) ∨ (¬ p4826) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial27034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory16290 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 8) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule27034 (meaning t m 2027) (meaning t m 2476) (meaning t m 2901) (meaning t m 2946) (meaning t m 3905) (meaning t m 4129) (meaning t m 4340) (meaning t m 4444) (meaning t m 4786) (meaning t m 4826) (meaning t m 5373) source

theorem rule27036 (p3877 p4035 p4349 : Prop) (h : (¬ p4349) ∨ (¬ p3877) ∨ p4035) : (¬ p3877) ∨ (p4035) ∨ (¬ p4349) := by
  classical
  tauto

theorem initial27036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3877)) ∨ (meaning t m 4035) ∨ (¬ (meaning t m 4349)) := by
  have source := ElevenTheory.theory16292 (m.theta 2 3) (m.theta 3 8) (m.theta 3 9)
  exact rule27036 (meaning t m 3877) (meaning t m 4035) (meaning t m 4349) source

theorem rule27038 (p2027 p2245 p2363 p2657 p2774 p2819 p2928 p3487 p4278 p4669 p4733 : Prop) (h : (¬ p2657) ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p2245) ∨ (¬ p4733) ∨ (¬ p2819) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2928) ∨ (¬ p3487) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial27038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory16294 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27038 (meaning t m 2027) (meaning t m 2245) (meaning t m 2363) (meaning t m 2657) (meaning t m 2774) (meaning t m 2819) (meaning t m 2928) (meaning t m 3487) (meaning t m 4278) (meaning t m 4669) (meaning t m 4733) source

theorem rule27039 (p1991 p2938 p3414 p4280 : Prop) (h : (¬ p3414) ∨ p2938 ∨ (¬ p1991) ∨ p4280) : (¬ p1991) ∨ (p2938) ∨ (¬ p3414) ∨ (p4280) := by
  classical
  tauto

theorem initial27039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3414)) ∨ (meaning t m 4280) := by
  have source := ElevenTheory.theory16295 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 7)
  exact rule27039 (meaning t m 1991) (meaning t m 2938) (meaning t m 3414) (meaning t m 4280) source

theorem rule27040 (p2027 p2299 p2319 p2341 p2748 p2779 p2829 p3365 p3662 p4320 p4559 p4734 : Prop) (h : p2027 ∨ (¬ p4559) ∨ (¬ p3365) ∨ (¬ p4320) ∨ (¬ p2829) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p4734) ∨ (¬ p3662) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2319)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p4320) ∨ (¬ p4559) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial27040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory16296 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27040 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2748) (meaning t m 2779) (meaning t m 2829) (meaning t m 3365) (meaning t m 3662) (meaning t m 4320) (meaning t m 4559) (meaning t m 4734) source

theorem rule27044 (p2027 p2245 p2299 p2657 p2727 p2881 p2996 p3051 p4361 p4521 : Prop) (h : (¬ p2996) ∨ (¬ p4521) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p4361) ∨ (¬ p2881) ∨ (¬ p2299) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2299) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3051) ∨ (¬ p4361) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial27044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory16300 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27044 (meaning t m 2027) (meaning t m 2245) (meaning t m 2299) (meaning t m 2657) (meaning t m 2727) (meaning t m 2881) (meaning t m 2996) (meaning t m 3051) (meaning t m 4361) (meaning t m 4521) source

theorem rule27045 (p2027 p2901 p3946 p3952 p4140 p4356 p4620 : Prop) (h : (¬ p3946) ∨ (¬ p2901) ∨ (¬ p4140) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p4356) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3946) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4356) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial27045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory16301 t (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule27045 (meaning t m 2027) (meaning t m 2901) (meaning t m 3946) (meaning t m 3952) (meaning t m 4140) (meaning t m 4356) (meaning t m 4620) source

theorem rule27046 (p3949 p4330 p4368 : Prop) (h : (¬ p3949) ∨ (¬ p4330) ∨ p4368) : (¬ p3949) ∨ (¬ p4330) ∨ (p4368) := by
  classical
  tauto

theorem initial27046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4330)) ∨ (meaning t m 4368) := by
  have source := ElevenTheory.theory16302 t (m.theta 5 9) (m.theta 6 9) (m.theta 8 9)
  exact rule27046 (meaning t m 3949) (meaning t m 4330) (meaning t m 4368) source

theorem rule27047 (p2476 p2662 p4256 : Prop) (h : (¬ p2476) ∨ (¬ p2662) ∨ p4256) : (¬ p2476) ∨ (¬ p2662) ∨ (p4256) := by
  classical
  tauto

theorem initial27047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 4256) := by
  have source := ElevenTheory.theory16303 (m.theta 0 4) (m.theta 3 4) (m.theta 4 8)
  exact rule27047 (meaning t m 2476) (meaning t m 2662) (meaning t m 4256) source

theorem rule27048 (p2027 p2534 p2657 p3366 p3399 p3555 p3631 p3950 p4236 p4256 p4377 : Prop) (h : (¬ p4236) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p4256) ∨ (¬ p2657) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial27048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory16304 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27048 (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 3366) (meaning t m 3399) (meaning t m 3555) (meaning t m 3631) (meaning t m 3950) (meaning t m 4236) (meaning t m 4256) (meaning t m 4377) source

theorem rule27049 (p2027 p2307 p3717 p3743 p3822 p4193 p5449 : Prop) (h : (¬ p3743) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p4193) ∨ (¬ p3822) ∨ (¬ p3717) ∨ (¬ p5449)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3717) ∨ (¬ p3743) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p5449) := by
  classical
  tauto

theorem initial27049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3717)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 5449)) := by
  have source := ElevenTheory.theory16305 t (m.theta 0 6) (m.theta 2 5) (m.theta 2 6) (m.theta 5 10) (m.theta 5 6) (m.theta 6 7)
  exact rule27049 (meaning t m 2027) (meaning t m 2307) (meaning t m 3717) (meaning t m 3743) (meaning t m 3822) (meaning t m 4193) (meaning t m 5449) source

theorem rule27051 (p2027 p2406 p2589 p2928 p3201 p4727 : Prop) (h : (¬ p2589) ∨ (¬ p4727) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p2406) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial27051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory16307 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule27051 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2928) (meaning t m 3201) (meaning t m 4727) source

theorem rule27053 (p2027 p2177 p2254 p2657 p3093 p3309 p3683 p3876 p4278 p4666 : Prop) (h : (¬ p3309) ∨ (¬ p3093) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3683) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial27053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory16309 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27053 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2657) (meaning t m 3093) (meaning t m 3309) (meaning t m 3683) (meaning t m 3876) (meaning t m 4278) (meaning t m 4666) source

theorem rule27055 (p2657 p3292 p5170 : Prop) (h : (¬ p2657) ∨ (¬ p5170) ∨ p3292) : (¬ p2657) ∨ (p3292) ∨ (¬ p5170) := by
  classical
  tauto

theorem initial27055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (meaning t m 3292) ∨ (¬ (meaning t m 5170)) := by
  have source := ElevenTheory.theory16311 (m.theta 0 3) (m.theta 3 4) (m.theta 3 9)
  exact rule27055 (meaning t m 2657) (meaning t m 3292) (meaning t m 5170) source

theorem rule27056 (p2001 p2027 p2156 p2252 p2462 p2619 p2657 p2750 p3125 p3370 p3371 p3742 p3917 p4193 p4278 : Prop) (h : (¬ p2001) ∨ (¬ p4278) ∨ (¬ p3370) ∨ (¬ p2619) ∨ p2462 ∨ (¬ p2657) ∨ (¬ p2252) ∨ (¬ p3371) ∨ (¬ p2750) ∨ (¬ p3742) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4193) ∨ (¬ p3125) ∨ (¬ p3917)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (p2462) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3125) ∨ (¬ p3370) ∨ (¬ p3371) ∨ (¬ p3742) ∨ (¬ p3917) ∨ (¬ p4193) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial27056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory16312 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 9) (m.theta 7 9)
  exact rule27056 (meaning t m 2001) (meaning t m 2027) (meaning t m 2156) (meaning t m 2252) (meaning t m 2462) (meaning t m 2619) (meaning t m 2657) (meaning t m 2750) (meaning t m 3125) (meaning t m 3370) (meaning t m 3371) (meaning t m 3742) (meaning t m 3917) (meaning t m 4193) (meaning t m 4278) source

theorem rule27064 (p2027 p2230 p2427 p2608 p3519 p3834 p4029 p4129 p4376 p4826 p5387 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p3834) ∨ (¬ p3519) ∨ (¬ p4029) ∨ (¬ p5387) ∨ (¬ p2427) ∨ (¬ p4826) ∨ (¬ p4129) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3834) ∨ (¬ p4029) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial27064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4029)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory16320 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule27064 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2608) (meaning t m 3519) (meaning t m 3834) (meaning t m 4029) (meaning t m 4129) (meaning t m 4376) (meaning t m 4826) (meaning t m 5387) source

theorem rule27065 (p2027 p2963 p3324 p3366 p3399 p3452 p3631 p3950 p4236 p4347 p4376 : Prop) (h : (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4236) ∨ (¬ p3452) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2963) ∨ (¬ p4376) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial27065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory16321 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27065 (meaning t m 2027) (meaning t m 2963) (meaning t m 3324) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3631) (meaning t m 3950) (meaning t m 4236) (meaning t m 4347) (meaning t m 4376) source

theorem rule27066 (p1991 p2027 p2313 p2766 p3941 p3955 p3983 p4348 p5580 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p1991) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p5580) ∨ (¬ p3983)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p3983) ∨ (¬ p4348) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial27066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory16322 t (m.theta 0 3) (m.theta 0 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27066 (meaning t m 1991) (meaning t m 2027) (meaning t m 2313) (meaning t m 2766) (meaning t m 3941) (meaning t m 3955) (meaning t m 3983) (meaning t m 4348) (meaning t m 5580) source

theorem rule27069 (p2027 p2230 p2427 p2753 p3365 p3519 p3877 p4129 p4376 p5560 p5600 : Prop) (h : (¬ p4129) ∨ (¬ p3365) ∨ (¬ p5560) ∨ (¬ p2230) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3519) ∨ p2753 ∨ (¬ p3877) ∨ (¬ p5600)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (p2753) ∨ (¬ p3365) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4129) ∨ (¬ p4376) ∨ (¬ p5560) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial27069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2753) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5560)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory16325 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 10)
  exact rule27069 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2753) (meaning t m 3365) (meaning t m 3519) (meaning t m 3877) (meaning t m 4129) (meaning t m 4376) (meaning t m 5560) (meaning t m 5600) source

theorem rule27070 (p3333 p3358 p3641 : Prop) (h : (¬ p3358) ∨ (¬ p3641) ∨ p3333) : (p3333) ∨ (¬ p3358) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial27070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3333) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory16326 (m.theta 2 4) (m.theta 4 8) (m.theta 4 9)
  exact rule27070 (meaning t m 3333) (meaning t m 3358) (meaning t m 3641) source

theorem rule27071 (p2027 p2307 p2387 p2668 p3097 p4560 : Prop) (h : p2027 ∨ (¬ p2387) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p4560) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial27071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory16327 t (m.theta 0 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule27071 (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2668) (meaning t m 3097) (meaning t m 4560) source

theorem rule27073 (p2027 p2143 p2751 p2901 p2992 p3556 p4392 : Prop) (h : (¬ p2143) ∨ (¬ p4392) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2751) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3556) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial27073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory16329 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule27073 (meaning t m 2027) (meaning t m 2143) (meaning t m 2751) (meaning t m 2901) (meaning t m 2992) (meaning t m 3556) (meaning t m 4392) source

theorem rule27074 (p2027 p2751 p2901 p2992 p4244 p4392 : Prop) (h : (¬ p2992) ∨ p2027 ∨ (¬ p2751) ∨ (¬ p4392) ∨ (¬ p2901) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4244) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial27074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory16330 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule27074 (meaning t m 2027) (meaning t m 2751) (meaning t m 2901) (meaning t m 2992) (meaning t m 4244) (meaning t m 4392) source

theorem rule27078 (p3877 p4237 p4315 : Prop) (h : (¬ p4237) ∨ (¬ p3877) ∨ p4315) : (¬ p3877) ∨ (¬ p4237) ∨ (p4315) := by
  classical
  tauto

theorem initial27078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4237)) ∨ (meaning t m 4315) := by
  have source := ElevenTheory.theory16334 (m.theta 2 3) (m.theta 3 5) (m.theta 3 8)
  exact rule27078 (meaning t m 3877) (meaning t m 4237) (meaning t m 4315) source

theorem rule27080 (p2027 p2146 p2341 p3570 p4244 p4988 : Prop) (h : (¬ p3570) ∨ (¬ p2146) ∨ p2027 ∨ (¬ p4988) ∨ (¬ p2341) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial27080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory16336 t (m.theta 0 5) (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule27080 (meaning t m 2027) (meaning t m 2146) (meaning t m 2341) (meaning t m 3570) (meaning t m 4244) (meaning t m 4988) source

theorem rule27082 (p3662 p4111 p4700 : Prop) (h : (¬ p4700) ∨ (¬ p4111) ∨ p3662) : (p3662) ∨ (¬ p4111) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial27082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3662) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory16338 (m.theta 1 3) (m.theta 3 4) (m.theta 3 5)
  exact rule27082 (meaning t m 3662) (meaning t m 4111) (meaning t m 4700) source

theorem rule27085 (p1986 p2027 p2611 p2696 p2741 p3136 p3367 p3662 : Prop) (h : (¬ p2741) ∨ (¬ p3367) ∨ (¬ p1986) ∨ (¬ p3662) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3136) ∨ p2611) : (¬ p1986) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p3136) ∨ (¬ p3367) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial27085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory16341 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule27085 (meaning t m 1986) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2741) (meaning t m 3136) (meaning t m 3367) (meaning t m 3662) source

theorem rule27087 (p2630 p2727 p2748 : Prop) (h : (¬ p2748) ∨ (¬ p2630) ∨ p2727) : (¬ p2630) ∨ (p2727) ∨ (¬ p2748) := by
  classical
  tauto

theorem initial27087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (meaning t m 2727) ∨ (¬ (meaning t m 2748)) := by
  have source := ElevenTheory.theory16343 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule27087 (meaning t m 2630) (meaning t m 2727) (meaning t m 2748) source

theorem rule27089 (p2027 p2341 p3570 p3575 p3741 p4320 p4702 : Prop) (h : (¬ p3575) ∨ (¬ p3741) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4702)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial27089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory16345 t (m.theta 0 7) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule27089 (meaning t m 2027) (meaning t m 2341) (meaning t m 3570) (meaning t m 3575) (meaning t m 3741) (meaning t m 4320) (meaning t m 4702) source

theorem rule27092 (p1977 p2027 p2331 p2938 p2952 p4154 p4320 : Prop) (h : (¬ p2952) ∨ (¬ p1977) ∨ (¬ p4154) ∨ p2938 ∨ (¬ p4320) ∨ p2027 ∨ (¬ p2331)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2938) ∨ (¬ p2952) ∨ (¬ p4154) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial27092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory16348 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule27092 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2938) (meaning t m 2952) (meaning t m 4154) (meaning t m 4320) source

theorem rule27093 (p1987 p2598 p2699 p3589 p4749 : Prop) (h : p2699 ∨ (¬ p1987) ∨ (¬ p3589) ∨ (¬ p2598) ∨ p4749) : (¬ p1987) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p3589) ∨ (p4749) := by
  classical
  tauto

theorem initial27093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3589)) ∨ (meaning t m 4749) := by
  have source := ElevenTheory.theory16349 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 3) (m.theta 2 4)
  exact rule27093 (meaning t m 1987) (meaning t m 2598) (meaning t m 2699) (meaning t m 3589) (meaning t m 4749) source

theorem rule27097 (p2027 p2177 p2254 p2598 p2707 p3414 p3553 p3585 p3589 p4473 : Prop) (h : (¬ p4473) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2707) ∨ (¬ p2598) ∨ (¬ p3589) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial27097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory16353 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27097 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2598) (meaning t m 2707) (meaning t m 3414) (meaning t m 3553) (meaning t m 3585) (meaning t m 3589) (meaning t m 4473) source

theorem rule27100 (p2005 p2027 p2611 p2727 p2946 p3016 p3662 p4117 : Prop) (h : p2611 ∨ (¬ p4117) ∨ (¬ p2946) ∨ (¬ p2727) ∨ (¬ p3662) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (p2611) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial27100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory16356 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule27100 (meaning t m 2005) (meaning t m 2027) (meaning t m 2611) (meaning t m 2727) (meaning t m 2946) (meaning t m 3016) (meaning t m 3662) (meaning t m 4117) source

theorem rule27101 (p1975 p2027 p2230 p2493 p2553 p2766 p3238 p3365 p3877 p4079 p4118 p4736 : Prop) (h : (¬ p2553) ∨ (¬ p1975) ∨ p2766 ∨ (¬ p2493) ∨ (¬ p4118) ∨ (¬ p3365) ∨ (¬ p4736) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p4079) ∨ (¬ p2230) ∨ (¬ p3238)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (p2766) ∨ (¬ p3238) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4079) ∨ (¬ p4118) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial27101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory16357 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 8 9)
  exact rule27101 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2493) (meaning t m 2553) (meaning t m 2766) (meaning t m 3238) (meaning t m 3365) (meaning t m 3877) (meaning t m 4079) (meaning t m 4118) (meaning t m 4736) source

theorem rule27103 (p2005 p2027 p2493 p3193 p3767 p3783 p4425 : Prop) (h : (¬ p2005) ∨ (¬ p2493) ∨ (¬ p4425) ∨ p2027 ∨ p3783 ∨ (¬ p3193) ∨ (¬ p3767)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p3193) ∨ (¬ p3767) ∨ (p3783) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial27103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3767)) ∨ (meaning t m 3783) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory16359 t (m.theta 0 9) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule27103 (meaning t m 2005) (meaning t m 2027) (meaning t m 2493) (meaning t m 3193) (meaning t m 3767) (meaning t m 3783) (meaning t m 4425) source

theorem rule27107 (p2156 p2901 p2951 p3872 : Prop) (h : (¬ p2156) ∨ (¬ p3872) ∨ (¬ p2951) ∨ p2901) : (¬ p2156) ∨ (p2901) ∨ (¬ p2951) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial27107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (meaning t m 2901) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory16363 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule27107 (meaning t m 2156) (meaning t m 2901) (meaning t m 2951) (meaning t m 3872) source

theorem rule27115 (p2005 p2027 p2114 p2588 p3093 p3309 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p3093) ∨ p2114 ∨ (¬ p2005) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p3309)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial27115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory16371 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule27115 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2588) (meaning t m 3093) (meaning t m 3309) (meaning t m 3954) source

theorem rule27120 (p2744 p4365 p4377 : Prop) (h : (¬ p4365) ∨ (¬ p2744) ∨ p4377) : (¬ p2744) ∨ (¬ p4365) ∨ (p4377) := by
  classical
  tauto

theorem initial27120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4365)) ∨ (meaning t m 4377) := by
  have source := ElevenTheory.theory16376 t (m.theta 1 2) (m.theta 1 3) (m.theta 1 5)
  exact rule27120 (meaning t m 2744) (meaning t m 4365) (meaning t m 4377) source

theorem rule27121 (p2027 p2383 p2584 p3584 p3956 p4730 : Prop) (h : (¬ p2584) ∨ (¬ p4730) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p2383) ∨ p2027) : (p2027) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial27121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory16377 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule27121 (meaning t m 2027) (meaning t m 2383) (meaning t m 2584) (meaning t m 3584) (meaning t m 3956) (meaning t m 4730) source

theorem rule27122 (p2383 p2470 p2584 p4432 : Prop) (h : (¬ p2383) ∨ (¬ p4432) ∨ (¬ p2584) ∨ p2470) : (¬ p2383) ∨ (p2470) ∨ (¬ p2584) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial27122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (meaning t m 2470) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory16378 (m.theta 0 4) (m.theta 0 6) (m.theta 4 8) (m.theta 6 8)
  exact rule27122 (meaning t m 2383) (meaning t m 2470) (meaning t m 2584) (meaning t m 4432) source

theorem rule27129 (p2005 p2284 p2388 p3958 : Prop) (h : p2388 ∨ (¬ p2005) ∨ p3958 ∨ (¬ p2284)) : (¬ p2005) ∨ (¬ p2284) ∨ (p2388) ∨ (p3958) := by
  classical
  tauto

theorem initial27129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (meaning t m 3958) := by
  have source := ElevenTheory.theory16385 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6)
  exact rule27129 (meaning t m 2005) (meaning t m 2284) (meaning t m 2388) (meaning t m 3958) source

theorem rule27130 (p2518 p3238 p4607 : Prop) (h : (¬ p4607) ∨ (¬ p3238) ∨ (¬ p2518)) : (¬ p2518) ∨ (¬ p3238) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial27130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory16386 (m.theta 1 4) (m.theta 4 5) (m.theta 4 8)
  exact rule27130 (meaning t m 2518) (meaning t m 3238) (meaning t m 4607) source

theorem rule27131 (p2027 p2138 p2241 p2641 p2668 p3097 p3758 p4405 p4736 : Prop) (h : (¬ p3758) ∨ (¬ p3097) ∨ (¬ p4405) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p2641) ∨ (¬ p2138) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p3758) ∨ (¬ p4405) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial27131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory16387 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule27131 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2641) (meaning t m 2668) (meaning t m 3097) (meaning t m 3758) (meaning t m 4405) (meaning t m 4736) source

theorem rule27135 (p1987 p2027 p2114 p2241 p2992 p3954 p4315 : Prop) (h : (¬ p4315) ∨ (¬ p1987) ∨ p2027 ∨ p2114 ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3954)) : (¬ p1987) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial27135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory16391 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule27135 (meaning t m 1987) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2992) (meaning t m 3954) (meaning t m 4315) source

theorem rule27139 (p2027 p3238 p3434 p3452 p3471 p4107 p4235 p4559 p4733 : Prop) (h : (¬ p4107) ∨ (¬ p3238) ∨ (¬ p3471) ∨ (¬ p4733) ∨ (¬ p4559) ∨ (¬ p3434) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3452)) : (p2027) ∨ (¬ p3238) ∨ (¬ p3434) ∨ (¬ p3452) ∨ (¬ p3471) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial27139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory16395 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule27139 (meaning t m 2027) (meaning t m 3238) (meaning t m 3434) (meaning t m 3452) (meaning t m 3471) (meaning t m 4107) (meaning t m 4235) (meaning t m 4559) (meaning t m 4733) source

theorem rule27148 (p3879 p3952 p4110 : Prop) (h : (¬ p3879) ∨ (¬ p4110) ∨ p3952) : (¬ p3879) ∨ (p3952) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial27148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3879)) ∨ (meaning t m 3952) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory16404 (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule27148 (meaning t m 3879) (meaning t m 3952) (meaning t m 4110) source

theorem rule27149 (p1988 p2027 p2156 p2699 p2972 p3461 p4172 p4173 p5045 : Prop) (h : p2027 ∨ (¬ p3461) ∨ p2699 ∨ (¬ p1988) ∨ (¬ p2156) ∨ (¬ p2972) ∨ (¬ p4173) ∨ (¬ p4172) ∨ (¬ p5045)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2156) ∨ (p2699) ∨ (¬ p2972) ∨ (¬ p3461) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial27149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory16405 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule27149 (meaning t m 1988) (meaning t m 2027) (meaning t m 2156) (meaning t m 2699) (meaning t m 2972) (meaning t m 3461) (meaning t m 4172) (meaning t m 4173) (meaning t m 5045) source

theorem rule27151 (p2027 p2651 p3016 p3364 p3584 p4790 : Prop) (h : (¬ p4790) ∨ (¬ p3584) ∨ (¬ p3364) ∨ (¬ p3016) ∨ (¬ p2651) ∨ p2027) : (p2027) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial27151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory16407 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule27151 (meaning t m 2027) (meaning t m 2651) (meaning t m 3016) (meaning t m 3364) (meaning t m 3584) (meaning t m 4790) source

theorem rule27157 (p1976 p2027 p2765 p2911 p3425 p3659 p3741 p4110 : Prop) (h : (¬ p1976) ∨ (¬ p3425) ∨ p2765 ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3741) ∨ (¬ p3659) ∨ (¬ p2911)) : (¬ p1976) ∨ (p2027) ∨ (p2765) ∨ (¬ p2911) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3741) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial27157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory16413 t (m.theta 0 2) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 7 8)
  exact rule27157 (meaning t m 1976) (meaning t m 2027) (meaning t m 2765) (meaning t m 2911) (meaning t m 3425) (meaning t m 3659) (meaning t m 3741) (meaning t m 4110) source

theorem rule27158 (p2027 p2255 p2352 p2459 p2493 p2651 p2996 p3857 p3961 p4116 p4133 p4155 : Prop) (h : (¬ p3961) ∨ (¬ p2255) ∨ (¬ p2996) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4155) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p4133) ∨ (¬ p2651) ∨ (¬ p3857) ∨ (¬ p4116)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p2651) ∨ (¬ p2996) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4116) ∨ (¬ p4133) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial27158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory16414 t (m.theta 0 3) (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27158 (meaning t m 2027) (meaning t m 2255) (meaning t m 2352) (meaning t m 2459) (meaning t m 2493) (meaning t m 2651) (meaning t m 2996) (meaning t m 3857) (meaning t m 3961) (meaning t m 4116) (meaning t m 4133) (meaning t m 4155) source

theorem rule27159 (p2493 p2922 p3920 : Prop) (h : (¬ p2493) ∨ (¬ p3920) ∨ p2922) : (¬ p2493) ∨ (p2922) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial27159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (meaning t m 2922) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory16415 (m.theta 1 4) (m.theta 4 6) (m.theta 4 7)
  exact rule27159 (meaning t m 2493) (meaning t m 2922) (meaning t m 3920) source

theorem rule27160 (p2027 p2493 p2553 p4116 p4256 p4432 p4501 : Prop) (h : (¬ p4432) ∨ (¬ p4116) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p2553) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p4116) ∨ (¬ p4256) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial27160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory16416 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule27160 (meaning t m 2027) (meaning t m 2493) (meaning t m 2553) (meaning t m 4116) (meaning t m 4256) (meaning t m 4432) (meaning t m 4501) source

theorem rule27163 (p3551 p3657 p3690 p4283 : Prop) (h : (¬ p4283) ∨ (¬ p3657) ∨ (¬ p3551) ∨ p3690) : (¬ p3551) ∨ (¬ p3657) ∨ (p3690) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial27163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 3690) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory16419 (m.theta 0 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27163 (meaning t m 3551) (meaning t m 3657) (meaning t m 3690) (meaning t m 4283) source

theorem rule27167 (p2027 p2166 p2255 p2667 p2946 p3412 p3946 p3969 p4154 p4191 p5119 : Prop) (h : (¬ p2667) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p5119) ∨ (¬ p3969) ∨ (¬ p4154) ∨ (¬ p2255) ∨ (¬ p3412) ∨ (¬ p4191) ∨ (¬ p3946)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3412) ∨ (¬ p3946) ∨ (¬ p3969) ∨ (¬ p4154) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial27167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory16423 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule27167 (meaning t m 2027) (meaning t m 2166) (meaning t m 2255) (meaning t m 2667) (meaning t m 2946) (meaning t m 3412) (meaning t m 3946) (meaning t m 3969) (meaning t m 4154) (meaning t m 4191) (meaning t m 5119) source

theorem rule27170 (p2027 p2870 p2992 p2996 p3691 p4155 p5053 : Prop) (h : (¬ p3691) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4155) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p5053)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3691) ∨ (¬ p4155) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial27170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory16426 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule27170 (meaning t m 2027) (meaning t m 2870) (meaning t m 2992) (meaning t m 2996) (meaning t m 3691) (meaning t m 4155) (meaning t m 5053) source

theorem rule27173 (p2027 p2459 p3189 p3848 p4550 p5107 : Prop) (h : (¬ p3189) ∨ p2027 ∨ (¬ p4550) ∨ (¬ p2459) ∨ (¬ p5107) ∨ (¬ p3848)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3189) ∨ (¬ p3848) ∨ (¬ p4550) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial27173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory16429 t (m.theta 1 3) (m.theta 3 8) (m.theta 3 9) (m.theta 7 8) (m.theta 8 9)
  exact rule27173 (meaning t m 2027) (meaning t m 2459) (meaning t m 3189) (meaning t m 3848) (meaning t m 4550) (meaning t m 5107) source

theorem rule27175 (p1980 p2331 p2622 p4787 : Prop) (h : (¬ p2331) ∨ p2622 ∨ (¬ p1980) ∨ p4787) : (¬ p1980) ∨ (¬ p2331) ∨ (p2622) ∨ (p4787) := by
  classical
  tauto

theorem initial27175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2622) ∨ (meaning t m 4787) := by
  have source := ElevenTheory.theory16431 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6)
  exact rule27175 (meaning t m 1980) (meaning t m 2331) (meaning t m 2622) (meaning t m 4787) source

theorem rule27176 (p1988 p2027 p2230 p2622 p2630 p2982 p3519 p3680 p4116 : Prop) (h : (¬ p3519) ∨ (¬ p2982) ∨ (¬ p2630) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p4116) ∨ (¬ p2230) ∨ p2622 ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2982) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial27176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory16432 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule27176 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2622) (meaning t m 2630) (meaning t m 2982) (meaning t m 3519) (meaning t m 3680) (meaning t m 4116) source

theorem rule27178 (p2000 p2027 p2589 p2633 p2850 p3644 p3876 : Prop) (h : p2027 ∨ (¬ p2850) ∨ (¬ p2589) ∨ (¬ p2000) ∨ (¬ p3644) ∨ (¬ p3876) ∨ p2633) : (¬ p2000) ∨ (p2027) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p2850) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial27178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory16434 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule27178 (meaning t m 2000) (meaning t m 2027) (meaning t m 2589) (meaning t m 2633) (meaning t m 2850) (meaning t m 3644) (meaning t m 3876) source

theorem rule27179 (p2027 p2553 p2774 p3425 p4471 p5222 : Prop) (h : (¬ p5222) ∨ (¬ p4471) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial27179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory16435 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7)
  exact rule27179 (meaning t m 2027) (meaning t m 2553) (meaning t m 2774) (meaning t m 3425) (meaning t m 4471) (meaning t m 5222) source

theorem rule27182 (p2027 p2187 p2363 p3857 p4197 p4486 : Prop) (h : p2027 ∨ (¬ p4486) ∨ (¬ p4197) ∨ (¬ p3857) ∨ (¬ p2187) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial27182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory16438 t (m.theta 0 6) (m.theta 0 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule27182 (meaning t m 2027) (meaning t m 2187) (meaning t m 2363) (meaning t m 3857) (meaning t m 4197) (meaning t m 4486) source

theorem rule27184 (p1991 p2027 p2202 p2657 p3422 p3574 p3684 : Prop) (h : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p3574) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p2657)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2657) ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial27184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory16440 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule27184 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2657) (meaning t m 3422) (meaning t m 3574) (meaning t m 3684) source

theorem rule27187 (p1982 p2027 p2274 p2363 p2668 p2765 p3568 : Prop) (h : (¬ p2668) ∨ p2765 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2274) ∨ (¬ p2363) ∨ (¬ p3568)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (p2765) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial27187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory16443 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule27187 (meaning t m 1982) (meaning t m 2027) (meaning t m 2274) (meaning t m 2363) (meaning t m 2668) (meaning t m 2765) (meaning t m 3568) source

theorem rule27188 (p2027 p2264 p2751 p3027 p3364 p3659 p3686 : Prop) (h : (¬ p3659) ∨ (¬ p3364) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3686) ∨ p2027 ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3364) ∨ (¬ p3659) ∨ (¬ p3686) := by
  classical
  tauto

theorem initial27188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) := by
  have source := ElevenTheory.theory16444 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule27188 (meaning t m 2027) (meaning t m 2264) (meaning t m 2751) (meaning t m 3027) (meaning t m 3364) (meaning t m 3659) (meaning t m 3686) source

theorem rule27194 (p2187 p3125 p3990 : Prop) (h : (¬ p3990) ∨ (¬ p2187) ∨ p3125) : (¬ p2187) ∨ (p3125) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial27194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (meaning t m 3125) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory16450 (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule27194 (meaning t m 2187) (meaning t m 3125) (meaning t m 3990) source

theorem rule27203 (p1990 p2027 p2138 p2284 p2696 p3136 p3474 : Prop) (h : (¬ p2696) ∨ p3474 ∨ (¬ p2284) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p3136)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (p3474) := by
  classical
  tauto

theorem initial27203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (meaning t m 3474) := by
  have source := ElevenTheory.theory16459 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule27203 (meaning t m 1990) (meaning t m 2027) (meaning t m 2138) (meaning t m 2284) (meaning t m 2696) (meaning t m 3136) (meaning t m 3474) source

theorem rule27210 (p3570 p3872 p3989 p4138 : Prop) (h : (¬ p4138) ∨ (¬ p3989) ∨ (¬ p3872) ∨ p3570) : (p3570) ∨ (¬ p3872) ∨ (¬ p3989) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial27210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3570) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory16466 (m.theta 5 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule27210 (meaning t m 3570) (meaning t m 3872) (meaning t m 3989) (meaning t m 4138) source

theorem rule27211 (p1996 p2027 p2622 p3365 p3434 p3471 p3947 : Prop) (h : (¬ p1996) ∨ p2622 ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3947) ∨ (¬ p3434)) : (¬ p1996) ∨ (p2027) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial27211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory16467 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 9)
  exact rule27211 (meaning t m 1996) (meaning t m 2027) (meaning t m 2622) (meaning t m 3365) (meaning t m 3434) (meaning t m 3471) (meaning t m 3947) source

theorem rule27212 (p2027 p2396 p2553 p3956 p4138 p4668 : Prop) (h : (¬ p4668) ∨ p2027 ∨ (¬ p4138) ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial27212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory16468 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule27212 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 3956) (meaning t m 4138) (meaning t m 4668) source

theorem rule27215 (p3212 p3646 p4205 : Prop) (h : (¬ p4205) ∨ (¬ p3646) ∨ (¬ p3212)) : (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4205) := by
  classical
  tauto

theorem initial27215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4205)) := by
  have source := ElevenTheory.theory16471 (m.theta 0 5) (m.theta 5 6) (m.theta 5 9)
  exact rule27215 (meaning t m 3212) (meaning t m 3646) (meaning t m 4205) source

theorem rule27216 (p3952 p4205 p4208 : Prop) (h : (¬ p4205) ∨ (¬ p3952) ∨ p4208) : (¬ p3952) ∨ (¬ p4205) ∨ (p4208) := by
  classical
  tauto

theorem initial27216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4205)) ∨ (meaning t m 4208) := by
  have source := ElevenTheory.theory16472 (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule27216 (meaning t m 3952) (meaning t m 4205) (meaning t m 4208) source

theorem rule27220 (p2027 p2542 p2589 p2655 p2807 p4652 : Prop) (h : (¬ p2807) ∨ (¬ p4652) ∨ (¬ p2655) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial27220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory16476 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule27220 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2807) (meaning t m 4652) source

theorem rule27224 (p2027 p2252 p2476 p2534 p2655 p2750 p3063 p3093 p3146 p3954 p4134 : Prop) (h : (¬ p3146) ∨ (¬ p3093) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4134) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3954) ∨ (¬ p4134) := by
  classical
  tauto

theorem initial27224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4134)) := by
  have source := ElevenTheory.theory16480 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule27224 (meaning t m 2027) (meaning t m 2252) (meaning t m 2476) (meaning t m 2534) (meaning t m 2655) (meaning t m 2750) (meaning t m 3063) (meaning t m 3093) (meaning t m 3146) (meaning t m 3954) (meaning t m 4134) source

theorem rule27225 (p1981 p2027 p2114 p2187 p2192 p2210 p3954 : Prop) (h : (¬ p1981) ∨ p2114 ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2187) ∨ (¬ p2192)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial27225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory16481 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6) (m.theta 6 8)
  exact rule27225 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 3954) source

theorem rule27228 (p1986 p2027 p2589 p2765 p3389 p3876 p4110 : Prop) (h : (¬ p3389) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2589) ∨ p2765 ∨ (¬ p1986) ∨ (¬ p3876)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2589) ∨ (p2765) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial27228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory16484 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule27228 (meaning t m 1986) (meaning t m 2027) (meaning t m 2589) (meaning t m 2765) (meaning t m 3389) (meaning t m 3876) (meaning t m 4110) source

theorem rule27229 (p4697 p4947 p5059 : Prop) (h : (¬ p4947) ∨ (¬ p5059) ∨ p4697) : (p4697) ∨ (¬ p4947) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial27229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4697) ∨ (¬ (meaning t m 4947)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory16485 t (m.theta 4 9) (m.theta 5 9) (m.theta 8 9)
  exact rule27229 (meaning t m 4697) (meaning t m 4947) (meaning t m 5059) source

theorem rule27235 (p2027 p2352 p3399 p3631 p3923 p3954 p4137 p4625 p4870 : Prop) (h : (¬ p3631) ∨ (¬ p2352) ∨ (¬ p4137) ∨ (¬ p3399) ∨ (¬ p4870) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p3954) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial27235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory16491 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule27235 (meaning t m 2027) (meaning t m 2352) (meaning t m 3399) (meaning t m 3631) (meaning t m 3923) (meaning t m 3954) (meaning t m 4137) (meaning t m 4625) (meaning t m 4870) source

theorem rule27236 (p3379 p3555 p3948 : Prop) (h : (¬ p3948) ∨ (¬ p3379) ∨ (¬ p3555)) : (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3948) := by
  classical
  tauto

theorem initial27236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3948)) := by
  have source := ElevenTheory.theory16492 (m.theta 0 1) (m.theta 1 4) (m.theta 1 5)
  exact rule27236 (meaning t m 3379) (meaning t m 3555) (meaning t m 3948) source

theorem rule27239 (p2027 p2518 p2743 p3541 p3874 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p2518) ∨ (¬ p3874) ∨ (¬ p3541) ∨ p2027 ∨ (¬ p2743)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2743) ∨ (¬ p3541) ∨ (¬ p3874) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial27239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory16495 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 8)
  exact rule27239 (meaning t m 2027) (meaning t m 2518) (meaning t m 2743) (meaning t m 3541) (meaning t m 3874) (meaning t m 4752) source

theorem rule27240 (p2027 p2248 p2881 p2901 p2928 p2946 p3452 p4278 p4666 : Prop) (h : (¬ p3452) ∨ (¬ p4278) ∨ (¬ p2928) ∨ (¬ p2901) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p2881) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial27240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory16496 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27240 (meaning t m 2027) (meaning t m 2248) (meaning t m 2881) (meaning t m 2901) (meaning t m 2928) (meaning t m 2946) (meaning t m 3452) (meaning t m 4278) (meaning t m 4666) source

theorem rule27243 (p2027 p3083 p3570 p3742 p4404 p4647 : Prop) (h : (¬ p4404) ∨ (¬ p4647) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3083)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4404) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial27243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory16499 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule27243 (meaning t m 2027) (meaning t m 3083) (meaning t m 3570) (meaning t m 3742) (meaning t m 4404) (meaning t m 4647) source

theorem rule27244 (p2027 p2573 p3222 p3238 p3346 p4717 : Prop) (h : (¬ p3222) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2573) ∨ (¬ p4717) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial27244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory16500 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule27244 (meaning t m 2027) (meaning t m 2573) (meaning t m 3222) (meaning t m 3238) (meaning t m 3346) (meaning t m 4717) source

theorem rule27245 (p2027 p2563 p3343 p3952 p4700 p4953 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4953) ∨ (¬ p3343) ∨ (¬ p4700) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3343) ∨ (¬ p3952) ∨ (¬ p4700) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial27245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory16501 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule27245 (meaning t m 2027) (meaning t m 2563) (meaning t m 3343) (meaning t m 3952) (meaning t m 4700) (meaning t m 4953) source

theorem rule27246 (p2027 p2563 p3222 p4173 p4202 p4953 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4202) ∨ (¬ p3222) ∨ (¬ p4953) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3222) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial27246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory16502 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule27246 (meaning t m 2027) (meaning t m 2563) (meaning t m 3222) (meaning t m 4173) (meaning t m 4202) (meaning t m 4953) source

theorem rule27247 (p1990 p2027 p2860 p2964 p3276 p4322 p4385 : Prop) (h : p2964 ∨ (¬ p4322) ∨ (¬ p3276) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p4385)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2860) ∨ (p2964) ∨ (¬ p3276) ∨ (¬ p4322) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial27247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory16503 t (m.theta 2 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule27247 (meaning t m 1990) (meaning t m 2027) (meaning t m 2860) (meaning t m 2964) (meaning t m 3276) (meaning t m 4322) (meaning t m 4385) source

theorem rule27249 (p2498 p4319 p4389 : Prop) (h : (¬ p4319) ∨ (¬ p4389) ∨ p2498) : (p2498) ∨ (¬ p4319) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial27249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2498) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory16505 (m.theta 1 6) (m.theta 3 6) (m.theta 4 6)
  exact rule27249 (meaning t m 2498) (meaning t m 4319) (meaning t m 4389) source

theorem rule27252 (p1983 p2027 p2202 p2563 p3051 p3246 p3646 : Prop) (h : (¬ p1983) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p2563) ∨ p2202 ∨ (¬ p3646)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial27252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory16508 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule27252 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 3051) (meaning t m 3246) (meaning t m 3646) source

theorem rule27253 (p1983 p2027 p2202 p2396 p2440 p3055 p3471 p4343 p4475 : Prop) (h : (¬ p2396) ∨ (¬ p1983) ∨ (¬ p4475) ∨ p2027 ∨ (¬ p3055) ∨ p2202 ∨ (¬ p4343) ∨ (¬ p2440) ∨ (¬ p3471)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2396) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p4343) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial27253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory16509 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 6 7) (m.theta 7 9)
  exact rule27253 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2396) (meaning t m 2440) (meaning t m 3055) (meaning t m 3471) (meaning t m 4343) (meaning t m 4475) source

theorem rule27255 (p1982 p2027 p2202 p2459 p2911 p2922 p3238 : Prop) (h : (¬ p1982) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p2911) ∨ p2202 ∨ (¬ p2922) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial27255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory16511 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule27255 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2459) (meaning t m 2911) (meaning t m 2922) (meaning t m 3238) source

theorem rule27256 (p1984 p2027 p2177 p2247 p2996 p2997 p3553 : Prop) (h : p2027 ∨ (¬ p3553) ∨ (¬ p1984) ∨ p2997 ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p2177)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (p2997) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial27256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory16512 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27256 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2996) (meaning t m 2997) (meaning t m 3553) source

theorem rule27258 (p1983 p2027 p2274 p2396 p2542 p2545 p2563 : Prop) (h : p2545 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2396) ∨ (¬ p2563) ∨ (¬ p2274)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial27258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory16514 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule27258 (meaning t m 1983) (meaning t m 2027) (meaning t m 2274) (meaning t m 2396) (meaning t m 2542) (meaning t m 2545) (meaning t m 2563) source

theorem rule27261 (p4203 p4560 p4976 : Prop) (h : (¬ p4203) ∨ (¬ p4560) ∨ p4976) : (¬ p4203) ∨ (¬ p4560) ∨ (p4976) := by
  classical
  tauto

theorem initial27261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4560)) ∨ (meaning t m 4976) := by
  have source := ElevenTheory.theory16517 t (m.theta 3 6) (m.theta 4 6) (m.theta 5 6)
  exact rule27261 (meaning t m 4203) (meaning t m 4560) (meaning t m 4976) source

theorem rule27265 (p2027 p2220 p2249 p2656 p2727 p2963 p3922 p3923 p3969 p4347 p4399 p5122 : Prop) (h : (¬ p2963) ∨ (¬ p4399) ∨ (¬ p3922) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3969) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4347) ∨ (¬ p2249) ∨ (¬ p3923) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4399) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial27265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory16521 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27265 (meaning t m 2027) (meaning t m 2220) (meaning t m 2249) (meaning t m 2656) (meaning t m 2727) (meaning t m 2963) (meaning t m 3922) (meaning t m 3923) (meaning t m 3969) (meaning t m 4347) (meaning t m 4399) (meaning t m 5122) source

theorem rule27266 (p1978 p2027 p2192 p2633 p3486 p3570 p3646 : Prop) (h : (¬ p3486) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p1978) ∨ (¬ p2192) ∨ (¬ p3570) ∨ p2633) : (¬ p1978) ∨ (p2027) ∨ (¬ p2192) ∨ (p2633) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial27266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory16522 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule27266 (meaning t m 1978) (meaning t m 2027) (meaning t m 2192) (meaning t m 2633) (meaning t m 3486) (meaning t m 3570) (meaning t m 3646) source

end SunPrize.SMT
