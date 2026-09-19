import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory057
import SunPrize.Certificate.Theory058
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule32699 (p2027 p3063 p3093 p3365 p3366 p3452 p3553 p3572 p4133 p4376 : Prop) (h : (¬ p3452) ∨ (¬ p3093) ∨ (¬ p4133) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4376) ∨ (¬ p3553) ∨ (¬ p3063) ∨ (¬ p3572)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial32699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory21955 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8)
  exact rule32699 (meaning t m 2027) (meaning t m 3063) (meaning t m 3093) (meaning t m 3365) (meaning t m 3366) (meaning t m 3452) (meaning t m 3553) (meaning t m 3572) (meaning t m 4133) (meaning t m 4376) source

theorem rule32701 (p2027 p2247 p2352 p2573 p3848 p3979 p5119 p5190 p5284 : Prop) (h : (¬ p2352) ∨ (¬ p5190) ∨ (¬ p2247) ∨ (¬ p2573) ∨ (¬ p3979) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p5284) ∨ (¬ p3848)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3848) ∨ (¬ p3979) ∨ (¬ p5119) ∨ (¬ p5190) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial32701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory21957 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule32701 (meaning t m 2027) (meaning t m 2247) (meaning t m 2352) (meaning t m 2573) (meaning t m 3848) (meaning t m 3979) (meaning t m 5119) (meaning t m 5190) (meaning t m 5284) source

theorem rule32703 (p1984 p2027 p2202 p3609 p3684 p3860 p4261 p4354 : Prop) (h : p2202 ∨ (¬ p4261) ∨ (¬ p3860) ∨ (¬ p3684) ∨ (¬ p1984) ∨ (¬ p3609) ∨ (¬ p4354) ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p3609) ∨ (¬ p3684) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4354) := by
  classical
  tauto

theorem initial32703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4354)) := by
  have source := ElevenTheory.theory21959 t (m.theta 0 1) (m.theta 1 8) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 8 9)
  exact rule32703 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 3609) (meaning t m 3684) (meaning t m 3860) (meaning t m 4261) (meaning t m 4354) source

theorem rule32706 (p2027 p2810 p3609 p4118 p4426 p4861 p5011 : Prop) (h : (¬ p3609) ∨ (¬ p4861) ∨ (¬ p2810) ∨ (¬ p4426) ∨ p2027 ∨ (¬ p5011) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4426) ∨ (¬ p4861) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial32706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4861)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory21962 t (m.theta 2 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule32706 (meaning t m 2027) (meaning t m 2810) (meaning t m 3609) (meaning t m 4118) (meaning t m 4426) (meaning t m 4861) (meaning t m 5011) source

theorem rule32707 (p2006 p2027 p2132 p2881 p2938 p3425 p3659 : Prop) (h : (¬ p3425) ∨ p2027 ∨ p2938 ∨ (¬ p3659) ∨ (¬ p2881) ∨ (¬ p2132) ∨ (¬ p2006)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial32707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory21963 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule32707 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2881) (meaning t m 2938) (meaning t m 3425) (meaning t m 3659) source

theorem rule32710 (p2027 p2192 p2928 p2957 p3646 p3948 p4241 p4644 : Prop) (h : (¬ p2957) ∨ (¬ p4241) ∨ (¬ p3646) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3948) ∨ (¬ p4644)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2928) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3948) ∨ (¬ p4241) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial32710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory21966 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule32710 (meaning t m 2027) (meaning t m 2192) (meaning t m 2928) (meaning t m 2957) (meaning t m 3646) (meaning t m 3948) (meaning t m 4241) (meaning t m 4644) source

theorem rule32723 (p2307 p3324 p3325 p3567 : Prop) (h : (¬ p3324) ∨ (¬ p2307) ∨ (¬ p3567) ∨ (¬ p3325)) : (¬ p2307) ∨ (¬ p3324) ∨ (¬ p3325) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial32723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory21979 (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule32723 (meaning t m 2307) (meaning t m 3324) (meaning t m 3325) (meaning t m 3567) source

theorem rule32728 (p2007 p2027 p2699 p3222 p3379 p3641 p5160 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p3379) ∨ (¬ p5160) ∨ (¬ p3222) ∨ (¬ p3641) ∨ (¬ p2007)) : (¬ p2007) ∨ (p2027) ∨ (p2699) ∨ (¬ p3222) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial32728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory21984 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9)
  exact rule32728 (meaning t m 2007) (meaning t m 2027) (meaning t m 2699) (meaning t m 3222) (meaning t m 3379) (meaning t m 3641) (meaning t m 5160) source

theorem rule32737 (p1983 p2027 p2114 p2449 p2707 p2717 p3553 : Prop) (h : (¬ p2449) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2707) ∨ (¬ p1983) ∨ (¬ p2717) ∨ p2114) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2449) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial32737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory21993 t (m.theta 1 2) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32737 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2449) (meaning t m 2707) (meaning t m 2717) (meaning t m 3553) source

theorem rule32738 (p3204 p3917 p3946 p4024 : Prop) (h : (¬ p3946) ∨ (¬ p4024) ∨ (¬ p3204) ∨ p3917) : (¬ p3204) ∨ (p3917) ∨ (¬ p3946) ∨ (¬ p4024) := by
  classical
  tauto

theorem initial32738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3204)) ∨ (meaning t m 3917) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4024)) := by
  have source := ElevenTheory.theory21994 (m.theta 0 6) (m.theta 1 6) (m.theta 2 6) (m.theta 6 9)
  exact rule32738 (meaning t m 3204) (meaning t m 3917) (meaning t m 3946) (meaning t m 4024) source

theorem rule32742 (p1990 p2027 p2202 p2352 p2440 p2493 p3989 p4116 : Prop) (h : (¬ p1990) ∨ p2027 ∨ (¬ p4116) ∨ (¬ p2352) ∨ (¬ p2440) ∨ p2202 ∨ (¬ p2493) ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2352) ∨ (¬ p2440) ∨ (¬ p2493) ∨ (¬ p3989) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial32742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory21998 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule32742 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2352) (meaning t m 2440) (meaning t m 2493) (meaning t m 3989) (meaning t m 4116) source

theorem rule32744 (p4193 p4313 p4426 : Prop) (h : p4313 ∨ (¬ p4193) ∨ (¬ p4426)) : (¬ p4193) ∨ (p4313) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial32744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4193)) ∨ (meaning t m 4313) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory22000 (m.theta 2 3) (m.theta 2 5) (m.theta 2 6)
  exact rule32744 (meaning t m 4193) (meaning t m 4313) (meaning t m 4426) source

theorem rule32746 (p2027 p2829 p3055 p3366 p3684 p4390 p4717 : Prop) (h : (¬ p3366) ∨ (¬ p4390) ∨ (¬ p3055) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p4390) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial32746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory22002 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule32746 (meaning t m 2027) (meaning t m 2829) (meaning t m 3055) (meaning t m 3366) (meaning t m 3684) (meaning t m 4390) (meaning t m 4717) source

theorem rule32748 (p2027 p2177 p2437 p2630 p2696 p3548 p4276 p4366 p4733 : Prop) (h : (¬ p2630) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p2696) ∨ (¬ p2437) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3548) ∨ (¬ p4276) ∨ (¬ p4366) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial32748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory22004 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule32748 (meaning t m 2027) (meaning t m 2177) (meaning t m 2437) (meaning t m 2630) (meaning t m 2696) (meaning t m 3548) (meaning t m 4276) (meaning t m 4366) (meaning t m 4733) source

theorem rule32758 (p2027 p2166 p3371 p3585 p3694 p4392 p4749 : Prop) (h : (¬ p3694) ∨ (¬ p3585) ∨ (¬ p4392) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p3694) ∨ (¬ p4392) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial32758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory22014 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 8)
  exact rule32758 (meaning t m 2027) (meaning t m 2166) (meaning t m 3371) (meaning t m 3585) (meaning t m 3694) (meaning t m 4392) (meaning t m 4749) source

theorem rule32760 (p2027 p2145 p2598 p3276 p3333 p3556 p3570 p5123 p5558 : Prop) (h : (¬ p3556) ∨ (¬ p5123) ∨ (¬ p2598) ∨ (¬ p2145) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3333) ∨ (¬ p5558) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2598) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory22016 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule32760 (meaning t m 2027) (meaning t m 2145) (meaning t m 2598) (meaning t m 3276) (meaning t m 3333) (meaning t m 3556) (meaning t m 3570) (meaning t m 5123) (meaning t m 5558) source

theorem rule32761 (p2027 p2254 p2518 p2528 p3379 p3414 p3553 p5118 p5558 : Prop) (h : (¬ p3379) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p5118) ∨ (¬ p2254) ∨ (¬ p3553) ∨ (¬ p3414) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial32761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory22017 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule32761 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2528) (meaning t m 3379) (meaning t m 3414) (meaning t m 3553) (meaning t m 5118) (meaning t m 5558) source

theorem rule32762 (p3537 p3688 p4078 : Prop) (h : (¬ p3688) ∨ (¬ p4078) ∨ (¬ p3537)) : (¬ p3537) ∨ (¬ p3688) ∨ (¬ p4078) := by
  classical
  tauto

theorem initial32762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4078)) := by
  have source := ElevenTheory.theory22018 (m.theta 1 2) (m.theta 2 6) (m.theta 2 8)
  exact rule32762 (meaning t m 3537) (meaning t m 3688) (meaning t m 4078) source

theorem rule32770 (p2774 p3589 p3591 p3918 : Prop) (h : (¬ p3589) ∨ (¬ p3591) ∨ (¬ p2774) ∨ (¬ p3918)) : (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial32770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory22026 (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 6)
  exact rule32770 (meaning t m 2774) (meaning t m 3589) (meaning t m 3591) (meaning t m 3918) source

theorem rule32771 (p2027 p2573 p3365 p3461 p3564 p3572 p4391 p4419 p4831 : Prop) (h : (¬ p2573) ∨ (¬ p4391) ∨ (¬ p3572) ∨ (¬ p4831) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3564) ∨ (¬ p4419)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3572) ∨ (¬ p4391) ∨ (¬ p4419) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial32771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory22027 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule32771 (meaning t m 2027) (meaning t m 2573) (meaning t m 3365) (meaning t m 3461) (meaning t m 3564) (meaning t m 3572) (meaning t m 4391) (meaning t m 4419) (meaning t m 4831) source

theorem rule32773 (p1992 p2027 p2202 p2440 p2655 p2743 p3343 p3346 p3361 : Prop) (h : (¬ p1992) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p2440) ∨ p2202) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2655) ∨ (¬ p2743) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial32773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory22029 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule32773 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2655) (meaning t m 2743) (meaning t m 3343) (meaning t m 3346) (meaning t m 3361) source

theorem rule32776 (p2753 p4233 p4379 p5352 : Prop) (h : (¬ p2753) ∨ (¬ p4379) ∨ (¬ p4233) ∨ (¬ p5352)) : (¬ p2753) ∨ (¬ p4233) ∨ (¬ p4379) ∨ (¬ p5352) := by
  classical
  tauto

theorem initial32776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 4233)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5352)) := by
  have source := ElevenTheory.theory22032 (m.theta 0 2) (m.theta 0 9) (m.theta 1 2) (m.theta 2 9)
  exact rule32776 (meaning t m 2753) (meaning t m 4233) (meaning t m 4379) (meaning t m 5352) source

theorem rule32777 (p2027 p2246 p2608 p2744 p2958 p3212 p3506 p3860 p4040 p4191 p4261 p4330 : Prop) (h : (¬ p4261) ∨ (¬ p2608) ∨ (¬ p3860) ∨ (¬ p2246) ∨ (¬ p4330) ∨ (¬ p2744) ∨ (¬ p3506) ∨ (¬ p4040) ∨ p2027 ∨ (¬ p3212) ∨ (¬ p2958) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3506) ∨ (¬ p3860) ∨ (¬ p4040) ∨ (¬ p4191) ∨ (¬ p4261) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial32777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory22033 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 9) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule32777 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2958) (meaning t m 3212) (meaning t m 3506) (meaning t m 3860) (meaning t m 4040) (meaning t m 4191) (meaning t m 4261) (meaning t m 4330) source

theorem rule32779 (p2027 p2685 p3063 p3093 p3366 p3414 p3452 p3877 p4236 p4376 p4774 : Prop) (h : (¬ p2685) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p3093) ∨ (¬ p3063) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4774) ∨ (¬ p3414) ∨ (¬ p4236) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial32779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory22035 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 8)
  exact rule32779 (meaning t m 2027) (meaning t m 2685) (meaning t m 3063) (meaning t m 3093) (meaning t m 3366) (meaning t m 3414) (meaning t m 3452) (meaning t m 3877) (meaning t m 4236) (meaning t m 4376) (meaning t m 4774) source

theorem rule32780 (p2027 p2264 p2307 p2387 p4138 p4361 : Prop) (h : (¬ p4138) ∨ (¬ p4361) ∨ (¬ p2307) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p4138) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial32780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory22036 t (m.theta 0 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule32780 (meaning t m 2027) (meaning t m 2264) (meaning t m 2307) (meaning t m 2387) (meaning t m 4138) (meaning t m 4361) source

theorem rule32783 (p2027 p2651 p2780 p3083 p3917 p4149 p4191 p4786 p5119 : Prop) (h : (¬ p4191) ∨ (¬ p3917) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p4149) ∨ (¬ p4786) ∨ (¬ p2651) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3083) ∨ (¬ p3917) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4786) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial32783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory22039 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule32783 (meaning t m 2027) (meaning t m 2651) (meaning t m 2780) (meaning t m 3083) (meaning t m 3917) (meaning t m 4149) (meaning t m 4191) (meaning t m 4786) (meaning t m 5119) source

theorem rule32784 (p1976 p2027 p2753 p2938 p3662 p3842 p4320 p4379 p5454 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p4320) ∨ p2938 ∨ (¬ p3842) ∨ (¬ p5454) ∨ (¬ p4379) ∨ (¬ p2753) ∨ (¬ p3662)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2753) ∨ (p2938) ∨ (¬ p3662) ∨ (¬ p3842) ∨ (¬ p4320) ∨ (¬ p4379) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial32784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory22040 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 9) (m.theta 3 5) (m.theta 3 9) (m.theta 5 7)
  exact rule32784 (meaning t m 1976) (meaning t m 2027) (meaning t m 2753) (meaning t m 2938) (meaning t m 3662) (meaning t m 3842) (meaning t m 4320) (meaning t m 4379) (meaning t m 5454) source

theorem rule32787 (p1999 p2027 p2323 p2797 p3166 p3323 p3877 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3877) ∨ (¬ p3323) ∨ (¬ p1999)) : (¬ p1999) ∨ (p2027) ∨ (p2323) ∨ (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3323) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial32787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory22043 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 9)
  exact rule32787 (meaning t m 1999) (meaning t m 2027) (meaning t m 2323) (meaning t m 2797) (meaning t m 3166) (meaning t m 3323) (meaning t m 3877) source

theorem rule32794 (p2027 p2132 p2860 p3540 p3737 p4278 p4381 p4729 p5250 : Prop) (h : (¬ p4278) ∨ (¬ p3737) ∨ (¬ p4729) ∨ (¬ p3540) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p5250) ∨ (¬ p2860) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3540) ∨ (¬ p3737) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial32794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory22050 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule32794 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 3540) (meaning t m 3737) (meaning t m 4278) (meaning t m 4381) (meaning t m 4729) (meaning t m 5250) source

theorem rule32795 (p3662 p4154 p4336 : Prop) (h : (¬ p4336) ∨ (¬ p4154) ∨ p3662) : (p3662) ∨ (¬ p4154) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial32795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3662) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory22051 (m.theta 1 3) (m.theta 3 5) (m.theta 3 6)
  exact rule32795 (meaning t m 3662) (meaning t m 4154) (meaning t m 4336) source

theorem rule32801 (p1990 p2027 p2254 p2563 p2598 p2766 p2839 p3414 p3553 p3585 p3589 p3695 p4348 : Prop) (h : p2027 ∨ (¬ p3553) ∨ (¬ p3695) ∨ (¬ p1990) ∨ (¬ p3589) ∨ p2766 ∨ (¬ p2254) ∨ (¬ p4348) ∨ (¬ p3414) ∨ (¬ p2563) ∨ (¬ p3585) ∨ (¬ p2839) ∨ (¬ p2598)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2254) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p2839) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3695) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial32801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory22057 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 7 8) (m.theta 8 9)
  exact rule32801 (meaning t m 1990) (meaning t m 2027) (meaning t m 2254) (meaning t m 2563) (meaning t m 2598) (meaning t m 2766) (meaning t m 2839) (meaning t m 3414) (meaning t m 3553) (meaning t m 3585) (meaning t m 3589) (meaning t m 3695) (meaning t m 4348) source

theorem rule32803 (p2027 p2578 p3051 p3422 p4198 p4320 p4700 p4753 : Prop) (h : (¬ p4198) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p3422) ∨ (¬ p3051) ∨ (¬ p4753) ∨ (¬ p2578) ∨ (¬ p4700)) : (p2027) ∨ (¬ p2578) ∨ (¬ p3051) ∨ (¬ p3422) ∨ (¬ p4198) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial32803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory22059 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7)
  exact rule32803 (meaning t m 2027) (meaning t m 2578) (meaning t m 3051) (meaning t m 3422) (meaning t m 4198) (meaning t m 4320) (meaning t m 4700) (meaning t m 4753) source

theorem rule32806 (p2027 p2482 p2589 p3989 p4110 p4614 : Prop) (h : (¬ p3989) ∨ (¬ p4110) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4614) ∨ (¬ p2482)) : (p2027) ∨ (¬ p2482) ∨ (¬ p2589) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4614) := by
  classical
  tauto

theorem initial32806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4614)) := by
  have source := ElevenTheory.theory22062 t (m.theta 0 4) (m.theta 0 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule32806 (meaning t m 2027) (meaning t m 2482) (meaning t m 2589) (meaning t m 3989) (meaning t m 4110) (meaning t m 4614) source

theorem rule32808 (p2027 p2088 p2104 p3178 p4117 p4118 p4969 : Prop) (h : (¬ p2104) ∨ (¬ p4118) ∨ (¬ p3178) ∨ (¬ p4969) ∨ p2027 ∨ (¬ p4117) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2104) ∨ (¬ p3178) ∨ (¬ p4117) ∨ (¬ p4118) ∨ (¬ p4969) := by
  classical
  tauto

theorem initial32808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3178)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4969)) := by
  have source := ElevenTheory.theory22064 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 8) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule32808 (meaning t m 2027) (meaning t m 2088) (meaning t m 2104) (meaning t m 3178) (meaning t m 4117) (meaning t m 4118) (meaning t m 4969) source

theorem rule32809 (p2027 p2707 p2748 p3324 p3365 p3609 p4154 p4348 p4503 p4734 p4805 : Prop) (h : (¬ p2707) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p4805) ∨ (¬ p2748) ∨ (¬ p4503) ∨ (¬ p3365) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2748) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p3609) ∨ (¬ p4154) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p4734) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial32809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory22065 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule32809 (meaning t m 2027) (meaning t m 2707) (meaning t m 2748) (meaning t m 3324) (meaning t m 3365) (meaning t m 3609) (meaning t m 4154) (meaning t m 4348) (meaning t m 4503) (meaning t m 4734) (meaning t m 4805) source

theorem rule32810 (p2027 p3399 p3645 p3646 p3744 p3954 p4075 p4191 p4826 p4877 : Prop) (h : (¬ p4075) ∨ (¬ p3399) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p3954) ∨ (¬ p4877) ∨ (¬ p3645) ∨ (¬ p3744) ∨ (¬ p4191)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3954) ∨ (¬ p4075) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial32810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory22066 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule32810 (meaning t m 2027) (meaning t m 3399) (meaning t m 3645) (meaning t m 3646) (meaning t m 3744) (meaning t m 3954) (meaning t m 4075) (meaning t m 4191) (meaning t m 4826) (meaning t m 4877) source

theorem rule32812 (p2027 p2245 p2749 p2952 p2992 p3379 p5216 : Prop) (h : (¬ p2245) ∨ (¬ p2992) ∨ (¬ p3379) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2749) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3379) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory22068 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5)
  exact rule32812 (meaning t m 2027) (meaning t m 2245) (meaning t m 2749) (meaning t m 2952) (meaning t m 2992) (meaning t m 3379) (meaning t m 5216) source

theorem rule32813 (p1984 p2027 p2202 p2264 p2440 p3548 p3580 p3591 p4105 : Prop) (h : (¬ p3548) ∨ (¬ p3591) ∨ (¬ p4105) ∨ (¬ p2264) ∨ (¬ p3580) ∨ p2202 ∨ (¬ p2440) ∨ p2027 ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2264) ∨ (¬ p2440) ∨ (¬ p3548) ∨ (¬ p3580) ∨ (¬ p3591) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial32813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory22069 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 7 8)
  exact rule32813 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2264) (meaning t m 2440) (meaning t m 3548) (meaning t m 3580) (meaning t m 3591) (meaning t m 4105) source

theorem rule32814 (p2136 p2778 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p2136) ∨ p2778) : (¬ p2136) ∨ (p2778) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial32814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2136)) ∨ (meaning t m 2778) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory22070 (m.theta 0 2) (m.theta 0 5) (m.theta 0 6)
  exact rule32814 (meaning t m 2136) (meaning t m 2778) (meaning t m 4198) source

theorem rule32817 (p2027 p2295 p3246 p4037 p4396 p4559 : Prop) (h : (¬ p3246) ∨ p2027 ∨ (¬ p4559) ∨ (¬ p2295) ∨ (¬ p4396) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3246) ∨ (¬ p4037) ∨ (¬ p4396) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial32817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory22073 t (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule32817 (meaning t m 2027) (meaning t m 2295) (meaning t m 3246) (meaning t m 4037) (meaning t m 4396) (meaning t m 4559) source

theorem rule32824 (p2027 p2230 p2247 p2563 p3125 p4118 p4330 p4360 p5190 : Prop) (h : (¬ p4360) ∨ (¬ p4118) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p5190) ∨ (¬ p4330) ∨ (¬ p2563) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial32824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory22080 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule32824 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2563) (meaning t m 3125) (meaning t m 4118) (meaning t m 4330) (meaning t m 4360) (meaning t m 5190) source

theorem rule32828 (p2027 p2589 p3166 p3690 p3755 p3877 p4117 p4235 p4658 p4729 : Prop) (h : (¬ p4658) ∨ (¬ p4235) ∨ (¬ p2589) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p4729) ∨ (¬ p3166) ∨ (¬ p3755) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3166) ∨ (¬ p3690) ∨ (¬ p3755) ∨ (¬ p3877) ∨ (¬ p4117) ∨ (¬ p4235) ∨ (¬ p4658) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial32828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4658)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory22084 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule32828 (meaning t m 2027) (meaning t m 2589) (meaning t m 3166) (meaning t m 3690) (meaning t m 3755) (meaning t m 3877) (meaning t m 4117) (meaning t m 4235) (meaning t m 4658) (meaning t m 4729) source

theorem rule32831 (p1990 p2027 p2252 p2284 p2622 p2630 p2657 p2992 : Prop) (h : (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2284) ∨ p2622 ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2252)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2284) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial32831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory22087 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule32831 (meaning t m 1990) (meaning t m 2027) (meaning t m 2252) (meaning t m 2284) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2992) source

theorem rule32834 (p1987 p2027 p2299 p2633 p2696 p2780 p3822 : Prop) (h : (¬ p2299) ∨ (¬ p3822) ∨ (¬ p2780) ∨ (¬ p1987) ∨ p2027 ∨ p2633 ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2696) ∨ (¬ p2780) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial32834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory22090 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule32834 (meaning t m 1987) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2696) (meaning t m 2780) (meaning t m 3822) source

theorem rule32835 (p2027 p2441 p2534 p3146 p3156 p4186 p4705 : Prop) (h : (¬ p4186) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p4705) ∨ (¬ p2441) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4186) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial32835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory22091 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule32835 (meaning t m 2027) (meaning t m 2441) (meaning t m 2534) (meaning t m 3146) (meaning t m 3156) (meaning t m 4186) (meaning t m 4705) source

theorem rule32836 (p2027 p2441 p2563 p3434 p4169 p4278 p4555 : Prop) (h : (¬ p3434) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p4555) ∨ (¬ p2441) ∨ (¬ p4169) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (¬ p3434) ∨ (¬ p4169) ∨ (¬ p4278) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial32836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory22092 t (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule32836 (meaning t m 2027) (meaning t m 2441) (meaning t m 2563) (meaning t m 3434) (meaning t m 4169) (meaning t m 4278) (meaning t m 4555) source

theorem rule32838 (p2027 p2187 p2284 p2608 p2744 p2992 p3548 p4133 p4366 : Prop) (h : (¬ p2992) ∨ (¬ p4366) ∨ (¬ p2608) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p2744) ∨ (¬ p3548) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2992) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial32838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory22094 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule32838 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2608) (meaning t m 2744) (meaning t m 2992) (meaning t m 3548) (meaning t m 4133) (meaning t m 4366) source

theorem rule32839 (p2027 p2459 p2657 p2881 p3051 p3366 p3370 p3584 p3683 p4137 p4236 p4377 p4604 : Prop) (h : (¬ p3370) ∨ (¬ p2657) ∨ (¬ p4604) ∨ (¬ p3683) ∨ (¬ p4236) ∨ (¬ p3051) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p4377) ∨ (¬ p2881) ∨ (¬ p3584) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2657) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4137) ∨ (¬ p4236) ∨ (¬ p4377) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial32839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory22095 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule32839 (meaning t m 2027) (meaning t m 2459) (meaning t m 2657) (meaning t m 2881) (meaning t m 3051) (meaning t m 3366) (meaning t m 3370) (meaning t m 3584) (meaning t m 3683) (meaning t m 4137) (meaning t m 4236) (meaning t m 4377) (meaning t m 4604) source

theorem rule32847 (p2027 p3105 p3952 p3958 p4137 p4316 p4388 p5152 : Prop) (h : (¬ p3958) ∨ (¬ p4316) ∨ (¬ p5152) ∨ (¬ p4388) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3105)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3952) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p4316) ∨ (¬ p4388) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial32847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4388)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory22103 t (m.theta 1 9) (m.theta 2 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule32847 (meaning t m 2027) (meaning t m 3105) (meaning t m 3952) (meaning t m 3958) (meaning t m 4137) (meaning t m 4316) (meaning t m 4388) (meaning t m 5152) source

theorem rule32848 (p2518 p3083 p3487 : Prop) (h : (¬ p3487) ∨ (¬ p3083) ∨ p2518) : (p2518) ∨ (¬ p3083) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial32848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2518) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory22104 (m.theta 1 4) (m.theta 3 4) (m.theta 4 8)
  exact rule32848 (meaning t m 2518) (meaning t m 3083) (meaning t m 3487) source

theorem rule32850 (p2005 p2027 p3016 p3623 p3742 p4075 p5503 : Prop) (h : (¬ p5503) ∨ (¬ p3016) ∨ (¬ p2005) ∨ p2027 ∨ (¬ p4075) ∨ (¬ p3742) ∨ p3623) : (¬ p2005) ∨ (p2027) ∨ (¬ p3016) ∨ (p3623) ∨ (¬ p3742) ∨ (¬ p4075) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial32850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory22106 t (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 10)
  exact rule32850 (meaning t m 2005) (meaning t m 2027) (meaning t m 3016) (meaning t m 3623) (meaning t m 3742) (meaning t m 4075) (meaning t m 5503) source

theorem rule32851 (p2027 p2145 p2563 p2807 p3506 p3646 p3951 p4117 p4381 p4661 p4948 : Prop) (h : (¬ p2563) ∨ (¬ p2145) ∨ (¬ p3951) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4948) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p4661) ∨ (¬ p2807) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3951) ∨ (¬ p4117) ∨ (¬ p4381) ∨ (¬ p4661) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial32851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4661)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory22107 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule32851 (meaning t m 2027) (meaning t m 2145) (meaning t m 2563) (meaning t m 2807) (meaning t m 3506) (meaning t m 3646) (meaning t m 3951) (meaning t m 4117) (meaning t m 4381) (meaning t m 4661) (meaning t m 4948) source

theorem rule32859 (p2933 p3547 p4710 : Prop) (h : (¬ p4710) ∨ (¬ p2933) ∨ p3547) : (¬ p2933) ∨ (p3547) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial32859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2933)) ∨ (meaning t m 3547) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory22115 (m.theta 1 7) (m.theta 4 7) (m.theta 6 7)
  exact rule32859 (meaning t m 2933) (meaning t m 3547) (meaning t m 4710) source

theorem rule32861 (p2027 p2230 p2518 p2531 p3238 p3324 p3365 p4079 p4195 p4433 p4736 : Prop) (h : (¬ p3365) ∨ (¬ p4195) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p3324) ∨ (¬ p2531) ∨ (¬ p4079) ∨ (¬ p4433) ∨ (¬ p2230) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3238) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4079) ∨ (¬ p4195) ∨ (¬ p4433) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial32861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory22117 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8)
  exact rule32861 (meaning t m 2027) (meaning t m 2230) (meaning t m 2518) (meaning t m 2531) (meaning t m 3238) (meaning t m 3324) (meaning t m 3365) (meaning t m 4079) (meaning t m 4195) (meaning t m 4433) (meaning t m 4736) source

theorem rule32864 (p1977 p2997 p3097 p3957 p4756 : Prop) (h : (¬ p3097) ∨ p2997 ∨ (¬ p1977) ∨ (¬ p3957) ∨ p4756) : (¬ p1977) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3957) ∨ (p4756) := by
  classical
  tauto

theorem initial32864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3957)) ∨ (meaning t m 4756) := by
  have source := ElevenTheory.theory22120 t (m.theta 1 3) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule32864 (meaning t m 1977) (meaning t m 2997) (meaning t m 3097) (meaning t m 3957) (meaning t m 4756) source

theorem rule32872 (p1978 p2027 p2997 p3063 p3549 p3646 p3989 : Prop) (h : (¬ p3549) ∨ p2997 ∨ (¬ p3646) ∨ (¬ p1978) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3063)) : (¬ p1978) ∨ (p2027) ∨ (p2997) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3646) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial32872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory22128 t (m.theta 0 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule32872 (meaning t m 1978) (meaning t m 2027) (meaning t m 2997) (meaning t m 3063) (meaning t m 3549) (meaning t m 3646) (meaning t m 3989) source

theorem rule32875 (p2027 p2307 p2589 p2655 p2819 p3146 p3822 p4118 p4134 p4346 p4580 p4607 : Prop) (h : (¬ p2819) ∨ (¬ p2589) ∨ (¬ p4134) ∨ (¬ p4118) ∨ (¬ p4580) ∨ (¬ p2307) ∨ (¬ p2655) ∨ (¬ p3146) ∨ (¬ p4607) ∨ (¬ p3822) ∨ (¬ p4346) ∨ p2027) : (p2027) ∨ (¬ p2307) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2819) ∨ (¬ p3146) ∨ (¬ p3822) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p4346) ∨ (¬ p4580) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial32875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4580)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory22131 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 2 6) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule32875 (meaning t m 2027) (meaning t m 2307) (meaning t m 2589) (meaning t m 2655) (meaning t m 2819) (meaning t m 3146) (meaning t m 3822) (meaning t m 4118) (meaning t m 4134) (meaning t m 4346) (meaning t m 4580) (meaning t m 4607) source

theorem rule32878 (p1994 p2027 p2406 p2440 p2633 p3347 p3540 p3570 p4001 : Prop) (h : (¬ p1994) ∨ (¬ p2440) ∨ (¬ p3540) ∨ (¬ p4001) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p2406) ∨ p2633) : (¬ p1994) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2633) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial32878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory22134 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule32878 (meaning t m 1994) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2633) (meaning t m 3347) (meaning t m 3540) (meaning t m 3570) (meaning t m 4001) source

theorem rule32881 (p2027 p2641 p2656 p3212 p3368 p4363 p4399 p4975 : Prop) (h : (¬ p4399) ∨ (¬ p2656) ∨ (¬ p3368) ∨ (¬ p4363) ∨ p2027 ∨ (¬ p4975) ∨ (¬ p3212) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3212) ∨ (¬ p3368) ∨ (¬ p4363) ∨ (¬ p4399) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial32881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory22137 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 9)
  exact rule32881 (meaning t m 2027) (meaning t m 2641) (meaning t m 2656) (meaning t m 3212) (meaning t m 3368) (meaning t m 4363) (meaning t m 4399) (meaning t m 4975) source

theorem rule32882 (p2010 p2027 p2264 p2545 p3027 p3644 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p3027) ∨ (¬ p2010) ∨ p2545 ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2264)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2264) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p3644) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial32882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory22138 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule32882 (meaning t m 2010) (meaning t m 2027) (meaning t m 2264) (meaning t m 2545) (meaning t m 3027) (meaning t m 3644) (meaning t m 4111) source

theorem rule32886 (p1997 p2027 p2619 p2839 p3437 p3588 p3880 : Prop) (h : (¬ p3588) ∨ (¬ p1997) ∨ (¬ p3880) ∨ (¬ p2839) ∨ p3437 ∨ p2027 ∨ (¬ p2619)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (p3437) ∨ (¬ p3588) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial32886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory22142 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8)
  exact rule32886 (meaning t m 1997) (meaning t m 2027) (meaning t m 2619) (meaning t m 2839) (meaning t m 3437) (meaning t m 3588) (meaning t m 3880) source

theorem rule32888 (p2027 p2254 p2518 p2528 p3292 p3379 p3461 p4604 p5284 : Prop) (h : (¬ p3379) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p2254) ∨ (¬ p3292) ∨ (¬ p4604) ∨ (¬ p3461) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3292) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial32888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory22144 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule32888 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 2528) (meaning t m 3292) (meaning t m 3379) (meaning t m 3461) (meaning t m 4604) (meaning t m 5284) source

theorem rule32892 (p2027 p2717 p3399 p3576 p3834 p4666 p5358 : Prop) (h : (¬ p3399) ∨ (¬ p2717) ∨ (¬ p3576) ∨ p2027 ∨ (¬ p3834) ∨ (¬ p4666) ∨ (¬ p5358)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3834) ∨ (¬ p4666) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial32892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory22148 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32892 (meaning t m 2027) (meaning t m 2717) (meaning t m 3399) (meaning t m 3576) (meaning t m 3834) (meaning t m 4666) (meaning t m 5358) source

theorem rule32895 (p1984 p2027 p2651 p2688 p2952 p2992 p3016 p3585 p3684 p3954 p4717 : Prop) (h : (¬ p2992) ∨ p2688 ∨ (¬ p3954) ∨ (¬ p4717) ∨ (¬ p3016) ∨ (¬ p2651) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3585) ∨ (¬ p3684)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2651) ∨ (p2688) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial32895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory22151 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6)
  exact rule32895 (meaning t m 1984) (meaning t m 2027) (meaning t m 2651) (meaning t m 2688) (meaning t m 2952) (meaning t m 2992) (meaning t m 3016) (meaning t m 3585) (meaning t m 3684) (meaning t m 3954) (meaning t m 4717) source

theorem rule32899 (p2027 p2230 p2528 p3688 p3692 p3954 p4355 p4358 p4433 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p2230) ∨ (¬ p3688) ∨ (¬ p4355) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4433) ∨ (¬ p2528) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2528) ∨ (¬ p3688) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4355) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial32899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory22155 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule32899 (meaning t m 2027) (meaning t m 2230) (meaning t m 2528) (meaning t m 3688) (meaning t m 3692) (meaning t m 3954) (meaning t m 4355) (meaning t m 4358) (meaning t m 4433) (meaning t m 5190) source

theorem rule32901 (p1976 p2027 p2764 p2810 p3359 p3365 p4425 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p4425) ∨ (¬ p3365) ∨ (¬ p3359) ∨ p2764) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial32901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory22157 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 9 10)
  exact rule32901 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 2810) (meaning t m 3359) (meaning t m 3365) (meaning t m 4425) source

theorem rule32906 (p2027 p2264 p2685 p2696 p2753 p3379 p3591 p3923 p4503 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3591) ∨ (¬ p2264) ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p2685) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4503) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial32906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory22162 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8)
  exact rule32906 (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3379) (meaning t m 3591) (meaning t m 3923) (meaning t m 4503) (meaning t m 5216) source

theorem rule32908 (p1983 p2027 p2598 p2611 p2707 p3434 p3585 : Prop) (h : p2027 ∨ (¬ p2707) ∨ (¬ p1983) ∨ p2611 ∨ (¬ p3434) ∨ (¬ p3585) ∨ (¬ p2598)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial32908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory22164 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 9)
  exact rule32908 (meaning t m 1983) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 2707) (meaning t m 3434) (meaning t m 3585) source

theorem rule32909 (p2027 p2745 p2860 p3662 p3952 p4313 : Prop) (h : (¬ p3662) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4313) ∨ (¬ p2860) ∨ (¬ p2745)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2860) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial32909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory22165 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule32909 (meaning t m 2027) (meaning t m 2745) (meaning t m 2860) (meaning t m 3662) (meaning t m 3952) (meaning t m 4313) source

theorem rule32910 (p1994 p2027 p2323 p2331 p2922 p3742 p4154 p4281 : Prop) (h : (¬ p2331) ∨ (¬ p3742) ∨ p2027 ∨ p2323 ∨ (¬ p1994) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p2922)) : (¬ p1994) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4154) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial32910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory22166 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7)
  exact rule32910 (meaning t m 1994) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2922) (meaning t m 3742) (meaning t m 4154) (meaning t m 4281) source

theorem rule32914 (p1990 p2027 p2156 p2622 p2901 p3136 p3556 : Prop) (h : p2622 ∨ (¬ p3556) ∨ (¬ p2901) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3136)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (p2622) ∨ (¬ p2901) ∨ (¬ p3136) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial32914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory22170 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule32914 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2622) (meaning t m 2901) (meaning t m 3136) (meaning t m 3556) source

theorem rule32916 (p2027 p2284 p2598 p2707 p3585 p3589 p3646 p4320 p4524 p4895 : Prop) (h : (¬ p3589) ∨ (¬ p2284) ∨ (¬ p4895) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p2707) ∨ (¬ p4320) ∨ (¬ p3646) ∨ (¬ p4524)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4524) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial32916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory22172 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule32916 (meaning t m 2027) (meaning t m 2284) (meaning t m 2598) (meaning t m 2707) (meaning t m 3585) (meaning t m 3589) (meaning t m 3646) (meaning t m 4320) (meaning t m 4524) (meaning t m 4895) source

theorem rule32917 (p1992 p2027 p2220 p2765 p2951 p3583 p3694 p3952 : Prop) (h : (¬ p1992) ∨ p2765 ∨ (¬ p3952) ∨ (¬ p2951) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p3694)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2220) ∨ (p2765) ∨ (¬ p2951) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial32917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory22173 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule32917 (meaning t m 1992) (meaning t m 2027) (meaning t m 2220) (meaning t m 2765) (meaning t m 2951) (meaning t m 3583) (meaning t m 3694) (meaning t m 3952) source

theorem rule32924 (p1986 p2027 p2622 p2774 p3365 p3367 p3688 : Prop) (h : (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3688) ∨ p2622) : (¬ p1986) ∨ (p2027) ∨ (p2622) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial32924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory22180 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6)
  exact rule32924 (meaning t m 1986) (meaning t m 2027) (meaning t m 2622) (meaning t m 2774) (meaning t m 3365) (meaning t m 3367) (meaning t m 3688) source

theorem rule32925 (p2027 p2542 p2589 p2608 p2707 p2717 p3693 p4256 p4905 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2542) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p2589) ∨ (¬ p3693) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4905) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial32925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory22181 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule32925 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 3693) (meaning t m 4256) (meaning t m 4905) (meaning t m 5193) source

theorem rule32929 (p2417 p2911 p3657 : Prop) (h : (¬ p3657) ∨ (¬ p2417) ∨ p2911) : (¬ p2417) ∨ (p2911) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial32929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (meaning t m 2911) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory22185 (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32929 (meaning t m 2417) (meaning t m 2911) (meaning t m 3657) source

theorem rule32931 (p1987 p2027 p2387 p2737 p2766 p2785 p3688 p4347 : Prop) (h : (¬ p2387) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2785) ∨ (¬ p1987) ∨ p2766 ∨ (¬ p2737) ∨ (¬ p3688)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2737) ∨ (p2766) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial32931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory22187 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule32931 (meaning t m 1987) (meaning t m 2027) (meaning t m 2387) (meaning t m 2737) (meaning t m 2766) (meaning t m 2785) (meaning t m 3688) (meaning t m 4347) source

theorem rule32932 (p2027 p2499 p2934 p3527 p3551 p4031 p4715 p4984 : Prop) (h : (¬ p3551) ∨ (¬ p4984) ∨ (¬ p2499) ∨ (¬ p4715) ∨ (¬ p2934) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p4031)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4031) ∨ (¬ p4715) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial32932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory22188 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 8)
  exact rule32932 (meaning t m 2027) (meaning t m 2499) (meaning t m 2934) (meaning t m 3527) (meaning t m 3551) (meaning t m 4031) (meaning t m 4715) (meaning t m 4984) source

theorem rule32933 (p2027 p2810 p3365 p3399 p3631 p3742 p4107 p4712 p4736 : Prop) (h : (¬ p2810) ∨ (¬ p3631) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p4107) ∨ (¬ p4736) ∨ (¬ p3365) ∨ (¬ p4712)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3742) ∨ (¬ p4107) ∨ (¬ p4712) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial32933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory22189 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule32933 (meaning t m 2027) (meaning t m 2810) (meaning t m 3365) (meaning t m 3399) (meaning t m 3631) (meaning t m 3742) (meaning t m 4107) (meaning t m 4712) (meaning t m 4736) source

theorem rule32934 (p2027 p2088 p2534 p3156 p3696 p4607 p4705 : Prop) (h : (¬ p3696) ∨ (¬ p2534) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p2088) ∨ (¬ p4607)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2534) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4607) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial32934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory22190 t (m.theta 0 8) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule32934 (meaning t m 2027) (meaning t m 2088) (meaning t m 2534) (meaning t m 3156) (meaning t m 3696) (meaning t m 4607) (meaning t m 4705) source

theorem rule32935 (p2027 p2104 p2598 p2811 p2946 p3115 p3680 p4752 p5123 p5612 : Prop) (h : (¬ p4752) ∨ (¬ p2811) ∨ p2027 ∨ (¬ p5123) ∨ (¬ p2104) ∨ (¬ p5612) ∨ (¬ p2598) ∨ (¬ p3115) ∨ (¬ p2946) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2598) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4752) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial32935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory22191 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 5) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule32935 (meaning t m 2027) (meaning t m 2104) (meaning t m 2598) (meaning t m 2811) (meaning t m 2946) (meaning t m 3115) (meaning t m 3680) (meaning t m 4752) (meaning t m 5123) (meaning t m 5612) source

theorem rule32937 (p1981 p2027 p2114 p2122 p2187 p2829 p3097 : Prop) (h : (¬ p3097) ∨ (¬ p1981) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2187) ∨ p2114 ∨ (¬ p2122)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2187) ∨ (¬ p2829) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial32937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory22193 t (m.theta 1 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule32937 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2122) (meaning t m 2187) (meaning t m 2829) (meaning t m 3097) source

theorem rule32942 (p1997 p2027 p2247 p2504 p2542 p2688 p3449 p3574 p4371 : Prop) (h : p2027 ∨ (¬ p3449) ∨ (¬ p2247) ∨ (¬ p4371) ∨ p2688 ∨ (¬ p3574) ∨ (¬ p2542) ∨ (¬ p2504) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2504) ∨ (¬ p2542) ∨ (p2688) ∨ (¬ p3449) ∨ (¬ p3574) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial32942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory22198 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 1 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule32942 (meaning t m 1997) (meaning t m 2027) (meaning t m 2247) (meaning t m 2504) (meaning t m 2542) (meaning t m 2688) (meaning t m 3449) (meaning t m 3574) (meaning t m 4371) source

theorem rule32944 (p1975 p2027 p2553 p2699 p3093 p3319 p4137 : Prop) (h : (¬ p3093) ∨ p2027 ∨ p2699 ∨ (¬ p3319) ∨ (¬ p1975) ∨ (¬ p2553) ∨ (¬ p4137)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial32944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory22200 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule32944 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 4137) source

theorem rule32945 (p2839 p3599 p5025 : Prop) (h : (¬ p3599) ∨ (¬ p5025) ∨ p2839) : (p2839) ∨ (¬ p3599) ∨ (¬ p5025) := by
  classical
  tauto

theorem initial32945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2839) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 5025)) := by
  have source := ElevenTheory.theory22201 (m.theta 1 2) (m.theta 2 5) (m.theta 2 9)
  exact rule32945 (meaning t m 2839) (meaning t m 3599) (meaning t m 5025) source

theorem rule32946 (p2027 p2774 p2952 p3461 p3483 p4320 p4789 p4831 p5660 : Prop) (h : (¬ p2952) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p5660) ∨ (¬ p2774) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p3461) ∨ (¬ p3483)) : (p2027) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4320) ∨ (¬ p4789) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial32946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory22202 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule32946 (meaning t m 2027) (meaning t m 2774) (meaning t m 2952) (meaning t m 3461) (meaning t m 3483) (meaning t m 4320) (meaning t m 4789) (meaning t m 4831) (meaning t m 5660) source

theorem rule32947 (p4425 p5164 p5387 : Prop) (h : (¬ p5387) ∨ (¬ p5164) ∨ p4425) : (p4425) ∨ (¬ p5164) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial32947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4425) ∨ (¬ (meaning t m 5164)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory22203 (m.theta 2 9) (m.theta 4 9) (m.theta 9 10)
  exact rule32947 (meaning t m 4425) (meaning t m 5164) (meaning t m 5387) source

theorem rule32948 (p2011 p2027 p2192 p2210 p2699 p2982 p4110 : Prop) (h : (¬ p2982) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2011) ∨ (¬ p2192) ∨ (¬ p2210) ∨ p2699) : (¬ p2011) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2982) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial32948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory22204 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule32948 (meaning t m 2011) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2699) (meaning t m 2982) (meaning t m 4110) source

theorem rule32950 (p2027 p3365 p3366 p3449 p3452 p4035 p4181 p4376 p5119 p5284 : Prop) (h : (¬ p4181) ∨ (¬ p3366) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3365) ∨ (¬ p5119) ∨ (¬ p5284) ∨ (¬ p4376) ∨ (¬ p4035)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4035) ∨ (¬ p4181) ∨ (¬ p4376) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial32950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory22206 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 2 3) (m.theta 3 9) (m.theta 8 10) (m.theta 9 10)
  exact rule32950 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 4035) (meaning t m 4181) (meaning t m 4376) (meaning t m 5119) (meaning t m 5284) source

theorem rule32952 (p2027 p2470 p2531 p2951 p2963 p3136 p3146 p3324 p3904 p4787 p5118 p5580 : Prop) (h : (¬ p5118) ∨ (¬ p3904) ∨ p2027 ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p2531) ∨ (¬ p3146) ∨ (¬ p2470) ∨ (¬ p4787) ∨ (¬ p5580) ∨ (¬ p2963) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2951) ∨ (¬ p2963) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p3904) ∨ (¬ p4787) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial32952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory22208 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule32952 (meaning t m 2027) (meaning t m 2470) (meaning t m 2531) (meaning t m 2951) (meaning t m 2963) (meaning t m 3136) (meaning t m 3146) (meaning t m 3324) (meaning t m 3904) (meaning t m 4787) (meaning t m 5118) (meaning t m 5580) source

theorem rule32955 (p2027 p2459 p2741 p2911 p3136 p3389 p3519 p3662 p4035 p4376 p5113 : Prop) (h : (¬ p3389) ∨ (¬ p2741) ∨ (¬ p3662) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p3136) ∨ (¬ p2911) ∨ (¬ p5113)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2741) ∨ (¬ p2911) ∨ (¬ p3136) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3662) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial32955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory22211 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule32955 (meaning t m 2027) (meaning t m 2459) (meaning t m 2741) (meaning t m 2911) (meaning t m 3136) (meaning t m 3389) (meaning t m 3519) (meaning t m 3662) (meaning t m 4035) (meaning t m 4376) (meaning t m 5113) source

theorem rule32956 (p1994 p2027 p2630 p2633 p3568 p3945 p4107 p4195 : Prop) (h : (¬ p1994) ∨ p2027 ∨ p2633 ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p2630) ∨ (¬ p3568) ∨ (¬ p4195)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2633) ∨ (¬ p3568) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial32956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory22212 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule32956 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2633) (meaning t m 3568) (meaning t m 3945) (meaning t m 4107) (meaning t m 4195) source

theorem rule32958 (p2000 p2589 p2873 p4632 : Prop) (h : p2873 ∨ (¬ p2000) ∨ (¬ p2589) ∨ p4632) : (¬ p2000) ∨ (¬ p2589) ∨ (p2873) ∨ (p4632) := by
  classical
  tauto

theorem initial32958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2873) ∨ (meaning t m 4632) := by
  have source := ElevenTheory.theory22214 t (m.theta 0 4) (m.theta 1 5) (m.theta 4 5)
  exact rule32958 (meaning t m 2000) (meaning t m 2589) (meaning t m 2873) (meaning t m 4632) source

theorem rule32960 (p2027 p2210 p3156 p3591 p3957 p4282 p4509 : Prop) (h : (¬ p3957) ∨ (¬ p4282) ∨ (¬ p3156) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p4509) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4282) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial32960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory22216 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule32960 (meaning t m 2027) (meaning t m 2210) (meaning t m 3156) (meaning t m 3591) (meaning t m 3957) (meaning t m 4282) (meaning t m 4509) source

theorem rule32964 (p2005 p2027 p2088 p2233 p2482 p2493 p2509 p2534 : Prop) (h : (¬ p2088) ∨ p2027 ∨ p2233 ∨ (¬ p2534) ∨ (¬ p2509) ∨ (¬ p2005) ∨ (¬ p2482) ∨ (¬ p2493)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2088) ∨ (p2233) ∨ (¬ p2482) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2534) := by
  classical
  tauto

theorem initial32964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) := by
  have source := ElevenTheory.theory22220 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule32964 (meaning t m 2005) (meaning t m 2027) (meaning t m 2088) (meaning t m 2233) (meaning t m 2482) (meaning t m 2493) (meaning t m 2509) (meaning t m 2534) source

theorem rule32965 (p2027 p2255 p2584 p2663 p3654 p4037 p4154 : Prop) (h : (¬ p2663) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p2584) ∨ (¬ p3654) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2584) ∨ (¬ p2663) ∨ (¬ p3654) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial32965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory22221 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9)
  exact rule32965 (meaning t m 2027) (meaning t m 2255) (meaning t m 2584) (meaning t m 2663) (meaning t m 3654) (meaning t m 4037) (meaning t m 4154) source

theorem rule32966 (p2027 p2459 p3461 p4045 p4171 p4420 p4425 : Prop) (h : (¬ p4420) ∨ (¬ p4425) ∨ (¬ p3461) ∨ (¬ p4045) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p4171)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3461) ∨ (¬ p4045) ∨ (¬ p4171) ∨ (¬ p4420) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial32966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory22222 t (m.theta 4 8) (m.theta 4 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule32966 (meaning t m 2027) (meaning t m 2459) (meaning t m 3461) (meaning t m 4045) (meaning t m 4171) (meaning t m 4420) (meaning t m 4425) source

theorem rule32967 (p2027 p2459 p3266 p4045 p4420 p4425 : Prop) (h : (¬ p2459) ∨ (¬ p4425) ∨ (¬ p4045) ∨ (¬ p4420) ∨ p2027 ∨ (¬ p3266)) : (p2027) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4045) ∨ (¬ p4420) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial32967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory22223 t (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule32967 (meaning t m 2027) (meaning t m 2459) (meaning t m 3266) (meaning t m 4045) (meaning t m 4420) (meaning t m 4425) source

theorem rule32969 (p2027 p2312 p2553 p3516 p3689 p4324 p5222 : Prop) (h : (¬ p5222) ∨ p2027 ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p4324) ∨ (¬ p2553) ∨ (¬ p3689)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2553) ∨ (¬ p3516) ∨ (¬ p3689) ∨ (¬ p4324) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial32969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory22225 t (m.theta 0 7) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule32969 (meaning t m 2027) (meaning t m 2312) (meaning t m 2553) (meaning t m 3516) (meaning t m 3689) (meaning t m 4324) (meaning t m 5222) source

theorem rule32972 (p1984 p2027 p2911 p2914 p3486 p3555 p3570 : Prop) (h : (¬ p1984) ∨ (¬ p3555) ∨ p2914 ∨ p2027 ∨ (¬ p2911) ∨ (¬ p3486) ∨ (¬ p3570)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial32972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory22228 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule32972 (meaning t m 1984) (meaning t m 2027) (meaning t m 2911) (meaning t m 2914) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) source

theorem rule32973 (p1986 p2027 p2138 p2166 p2598 p2688 p3694 p4365 : Prop) (h : p2027 ∨ (¬ p2166) ∨ (¬ p1986) ∨ (¬ p2138) ∨ (¬ p4365) ∨ (¬ p2598) ∨ (¬ p3694) ∨ p2688) : (¬ p1986) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2166) ∨ (¬ p2598) ∨ (p2688) ∨ (¬ p3694) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial32973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory22229 t (m.theta 0 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 8)
  exact rule32973 (meaning t m 1986) (meaning t m 2027) (meaning t m 2138) (meaning t m 2166) (meaning t m 2598) (meaning t m 2688) (meaning t m 3694) (meaning t m 4365) source

theorem rule32975 (p2685 p3877 p4044 : Prop) (h : (¬ p4044) ∨ (¬ p2685) ∨ (¬ p3877)) : (¬ p2685) ∨ (¬ p3877) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial32975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory22231 (m.theta 2 3) (m.theta 3 7) (m.theta 3 8)
  exact rule32975 (meaning t m 2685) (meaning t m 3877) (meaning t m 4044) source

theorem rule32980 (p2027 p2248 p2651 p3276 p3343 p3591 p3923 p5123 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p3923) ∨ (¬ p2248) ∨ (¬ p3343) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p5123) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial32980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory22236 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule32980 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 3591) (meaning t m 3923) (meaning t m 5123) (meaning t m 5580) source

theorem rule32981 (p1990 p2027 p2144 p2192 p2622 p3051 p3365 p3486 : Prop) (h : p2027 ∨ p2622 ∨ (¬ p3365) ∨ (¬ p3051) ∨ (¬ p2144) ∨ (¬ p3486) ∨ (¬ p2192) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2144) ∨ (¬ p2192) ∨ (p2622) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial32981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory22237 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 5 6) (m.theta 5 7)
  exact rule32981 (meaning t m 1990) (meaning t m 2027) (meaning t m 2144) (meaning t m 2192) (meaning t m 2622) (meaning t m 3051) (meaning t m 3365) (meaning t m 3486) source

theorem rule32984 (p2027 p2254 p2299 p2952 p3136 p3399 p3527 p3572 p4361 : Prop) (h : (¬ p2299) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p3136) ∨ (¬ p3399) ∨ (¬ p2952) ∨ (¬ p2254) ∨ (¬ p4361) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2299) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3572) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial32984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory22240 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule32984 (meaning t m 2027) (meaning t m 2254) (meaning t m 2299) (meaning t m 2952) (meaning t m 3136) (meaning t m 3399) (meaning t m 3527) (meaning t m 3572) (meaning t m 4361) source

theorem rule32986 (p1990 p2027 p2307 p2764 p3097 p3946 p4191 : Prop) (h : (¬ p1990) ∨ (¬ p3097) ∨ (¬ p3946) ∨ (¬ p2307) ∨ p2027 ∨ p2764 ∨ (¬ p4191)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (p2764) ∨ (¬ p3097) ∨ (¬ p3946) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial32986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory22242 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule32986 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2764) (meaning t m 3097) (meaning t m 3946) (meaning t m 4191) source

theorem rule32992 (p2027 p2145 p2588 p2696 p3506 p3646 p3755 p4203 p4260 p4831 : Prop) (h : (¬ p2696) ∨ (¬ p3755) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p3506) ∨ (¬ p2145) ∨ (¬ p4831) ∨ (¬ p3646) ∨ (¬ p4203) ∨ (¬ p4260)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4203) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial32992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory22248 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule32992 (meaning t m 2027) (meaning t m 2145) (meaning t m 2588) (meaning t m 2696) (meaning t m 3506) (meaning t m 3646) (meaning t m 3755) (meaning t m 4203) (meaning t m 4260) (meaning t m 4831) source

theorem rule32996 (p2025 p2027 p2997 p3461 p3483 p3822 p4321 : Prop) (h : (¬ p3483) ∨ (¬ p2025) ∨ p2027 ∨ (¬ p3822) ∨ p2997 ∨ (¬ p4321) ∨ (¬ p3461)) : (¬ p2025) ∨ (p2027) ∨ (p2997) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial32996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2025)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory22252 t (m.theta 1 9) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule32996 (meaning t m 2025) (meaning t m 2027) (meaning t m 2997) (meaning t m 3461) (meaning t m 3483) (meaning t m 3822) (meaning t m 4321) source

theorem rule32998 (p2027 p2417 p2696 p2761 p2780 p3389 p3759 p4329 p4749 p5254 : Prop) (h : (¬ p3389) ∨ (¬ p4329) ∨ (¬ p5254) ∨ (¬ p2696) ∨ (¬ p3759) ∨ (¬ p4749) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2417) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2696) ∨ (¬ p2761) ∨ (¬ p2780) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4329) ∨ (¬ p4749) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial32998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4329)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory22254 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule32998 (meaning t m 2027) (meaning t m 2417) (meaning t m 2696) (meaning t m 2761) (meaning t m 2780) (meaning t m 3389) (meaning t m 3759) (meaning t m 4329) (meaning t m 4749) (meaning t m 5254) source

theorem rule33001 (p2027 p2252 p2542 p2589 p2655 p2750 p2819 p3654 p3917 p4256 p4384 p4869 p5016 : Prop) (h : (¬ p2750) ∨ (¬ p2252) ∨ (¬ p2589) ∨ (¬ p4869) ∨ (¬ p5016) ∨ (¬ p2542) ∨ (¬ p3654) ∨ (¬ p4384) ∨ (¬ p2655) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p3917) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p4869) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial33001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory22257 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9)
  exact rule33001 (meaning t m 2027) (meaning t m 2252) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2750) (meaning t m 2819) (meaning t m 3654) (meaning t m 3917) (meaning t m 4256) (meaning t m 4384) (meaning t m 4869) (meaning t m 5016) source

theorem rule33006 (p1991 p2027 p2630 p2657 p2764 p4035 p5284 : Prop) (h : (¬ p1991) ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p4035) ∨ p2764 ∨ p2027 ∨ (¬ p5284)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2764) ∨ (¬ p4035) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial33006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory22262 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule33006 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2764) (meaning t m 4035) (meaning t m 5284) source

theorem rule33012 (p2001 p2027 p2873 p3256 p3692 p4044 p4075 p4391 p4431 : Prop) (h : p2027 ∨ (¬ p4391) ∨ (¬ p4431) ∨ p2873 ∨ (¬ p3692) ∨ (¬ p4075) ∨ (¬ p2001) ∨ (¬ p3256) ∨ (¬ p4044)) : (¬ p2001) ∨ (p2027) ∨ (p2873) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4044) ∨ (¬ p4075) ∨ (¬ p4391) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial33012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory22268 t (m.theta 1 5) (m.theta 1 7) (m.theta 3 7) (m.theta 3 8) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9)
  exact rule33012 (meaning t m 2001) (meaning t m 2027) (meaning t m 2873) (meaning t m 3256) (meaning t m 3692) (meaning t m 4044) (meaning t m 4075) (meaning t m 4391) (meaning t m 4431) source

theorem rule33014 (p2027 p2761 p3692 p3945 p4444 p4902 : Prop) (h : (¬ p3945) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p2761) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3692) ∨ (¬ p3945) ∨ (¬ p4444) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial33014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory22270 t (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule33014 (meaning t m 2027) (meaning t m 2761) (meaning t m 3692) (meaning t m 3945) (meaning t m 4444) (meaning t m 4902) source

theorem rule33016 (p2027 p2166 p3097 p4173 p4405 p4441 : Prop) (h : p2027 ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4441) ∨ (¬ p3097) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3097) ∨ (¬ p4173) ∨ (¬ p4405) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial33016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory22272 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule33016 (meaning t m 2027) (meaning t m 2166) (meaning t m 3097) (meaning t m 4173) (meaning t m 4405) (meaning t m 4441) source

theorem rule33040 (p4288 p4967 p5315 : Prop) (h : (¬ p4967) ∨ (¬ p5315) ∨ p4288) : (p4288) ∨ (¬ p4967) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial33040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4288) ∨ (¬ (meaning t m 4967)) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory22296 (m.theta 1 8) (m.theta 2 8) (m.theta 3 8)
  exact rule33040 (meaning t m 4288) (meaning t m 4967) (meaning t m 5315) source

theorem rule33042 (p1998 p2027 p2274 p2396 p2765 p2911 p4278 : Prop) (h : (¬ p2274) ∨ p2765 ∨ (¬ p1998) ∨ (¬ p2911) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4278)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (p2765) ∨ (¬ p2911) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial33042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory22298 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33042 (meaning t m 1998) (meaning t m 2027) (meaning t m 2274) (meaning t m 2396) (meaning t m 2765) (meaning t m 2911) (meaning t m 4278) source

theorem rule33044 (p1982 p2027 p2114 p2737 p3136 p3146 p3156 : Prop) (h : (¬ p2737) ∨ (¬ p3136) ∨ p2027 ∨ p2114 ∨ (¬ p1982) ∨ (¬ p3156) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p3136) ∨ (¬ p3146) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial33044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory22300 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule33044 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 3136) (meaning t m 3146) (meaning t m 3156) source

theorem rule33051 (p2027 p3343 p3690 p3742 p4647 p5182 p5299 : Prop) (h : (¬ p5182) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3343) ∨ (¬ p5299) ∨ (¬ p4647) ∨ (¬ p3690)) : (p2027) ∨ (¬ p3343) ∨ (¬ p3690) ∨ (¬ p3742) ∨ (¬ p4647) ∨ (¬ p5182) ∨ (¬ p5299) := by
  classical
  tauto

theorem initial33051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5182)) ∨ (¬ (meaning t m 5299)) := by
  have source := ElevenTheory.theory22307 t (m.theta 0 9) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule33051 (meaning t m 2027) (meaning t m 3343) (meaning t m 3690) (meaning t m 3742) (meaning t m 4647) (meaning t m 5182) (meaning t m 5299) source

theorem rule33053 (p2027 p2307 p2630 p2951 p2962 p3822 p4701 p4841 : Prop) (h : (¬ p2951) ∨ (¬ p2630) ∨ (¬ p3822) ∨ (¬ p2307) ∨ (¬ p4701) ∨ (¬ p4841) ∨ p2027 ∨ (¬ p2962)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p3822) ∨ (¬ p4701) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial33053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4701)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory22309 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 7)
  exact rule33053 (meaning t m 2027) (meaning t m 2307) (meaning t m 2630) (meaning t m 2951) (meaning t m 2962) (meaning t m 3822) (meaning t m 4701) (meaning t m 4841) source

theorem rule33054 (p3554 p4105 p4512 : Prop) (h : (¬ p4105) ∨ (¬ p4512) ∨ p3554) : (p3554) ∨ (¬ p4105) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial33054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3554) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory22310 (m.theta 1 5) (m.theta 1 6) (m.theta 1 7)
  exact rule33054 (meaning t m 3554) (meaning t m 4105) (meaning t m 4512) source

theorem rule33055 (p2027 p2952 p3136 p3364 p3367 p4236 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p3136) ∨ (¬ p2952) ∨ (¬ p4236) ∨ (¬ p3364) ∨ (¬ p3367) ∨ p2027) : (p2027) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3367) ∨ (¬ p4236) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory22311 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule33055 (meaning t m 2027) (meaning t m 2952) (meaning t m 3136) (meaning t m 3364) (meaning t m 3367) (meaning t m 4236) (meaning t m 4734) source

theorem rule33056 (p2027 p2553 p2573 p2881 p3367 p3425 p3548 p3576 p3759 p4559 p4734 : Prop) (h : p2027 ∨ (¬ p2553) ∨ (¬ p2881) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3425) ∨ (¬ p4734) ∨ (¬ p3576) ∨ (¬ p3548) ∨ (¬ p4559)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2881) ∨ (¬ p3367) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3759) ∨ (¬ p4559) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory22312 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule33056 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2881) (meaning t m 3367) (meaning t m 3425) (meaning t m 3548) (meaning t m 3576) (meaning t m 3759) (meaning t m 4559) (meaning t m 4734) source

theorem rule33057 (p2027 p2187 p2230 p2563 p2743 p3877 p3954 p4774 p5190 : Prop) (h : (¬ p4774) ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p5190) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2743) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4774) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial33057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4774)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory22313 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule33057 (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 2743) (meaning t m 3877) (meaning t m 3954) (meaning t m 4774) (meaning t m 5190) source

theorem rule33062 (p2027 p2210 p2299 p2313 p2972 p3204 p3954 p4348 p4450 p4870 : Prop) (h : (¬ p2210) ∨ (¬ p2972) ∨ (¬ p2299) ∨ (¬ p4870) ∨ (¬ p4450) ∨ (¬ p3204) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2972) ∨ (¬ p3204) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial33062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory22318 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule33062 (meaning t m 2027) (meaning t m 2210) (meaning t m 2299) (meaning t m 2313) (meaning t m 2972) (meaning t m 3204) (meaning t m 3954) (meaning t m 4348) (meaning t m 4450) (meaning t m 4870) source

theorem rule33065 (p2005 p2027 p2997 p3324 p3325 p3506 p4137 p4191 p4421 : Prop) (h : (¬ p3506) ∨ p2997 ∨ (¬ p3325) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2005) ∨ (¬ p3324) ∨ (¬ p4421) ∨ (¬ p4191)) : (¬ p2005) ∨ (p2027) ∨ (p2997) ∨ (¬ p3324) ∨ (¬ p3325) ∨ (¬ p3506) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4421) := by
  classical
  tauto

theorem initial33065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4421)) := by
  have source := ElevenTheory.theory22321 t (m.theta 3 6) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule33065 (meaning t m 2005) (meaning t m 2027) (meaning t m 2997) (meaning t m 3324) (meaning t m 3325) (meaning t m 3506) (meaning t m 4137) (meaning t m 4191) (meaning t m 4421) source

theorem rule33067 (p2027 p2780 p3471 p3917 p4475 p4620 : Prop) (h : (¬ p4620) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p4475) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3917) ∨ (¬ p4475) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial33067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory22323 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 9)
  exact rule33067 (meaning t m 2027) (meaning t m 2780) (meaning t m 3471) (meaning t m 3917) (meaning t m 4475) (meaning t m 4620) source

theorem rule33071 (p1982 p2027 p2122 p2169 p2246 p2313 p2470 p2663 p2744 p2778 p3146 p3366 p4149 p4358 p5568 : Prop) (h : (¬ p2470) ∨ (¬ p4149) ∨ (¬ p3366) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p4358) ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2778) ∨ (¬ p2313) ∨ p2169 ∨ (¬ p3146) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p5568)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2122) ∨ (p2169) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p4149) ∨ (¬ p4358) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial33071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory22327 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule33071 (meaning t m 1982) (meaning t m 2027) (meaning t m 2122) (meaning t m 2169) (meaning t m 2246) (meaning t m 2313) (meaning t m 2470) (meaning t m 2663) (meaning t m 2744) (meaning t m 2778) (meaning t m 3146) (meaning t m 3366) (meaning t m 4149) (meaning t m 4358) (meaning t m 5568) source

theorem rule33074 (p2027 p2573 p3461 p3564 p3588 p3954 p4423 p4831 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p4831) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3954) ∨ (¬ p3461) ∨ (¬ p3588) ∨ (¬ p4423)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4423) ∨ (¬ p4831) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial33074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory22330 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule33074 (meaning t m 2027) (meaning t m 2573) (meaning t m 3461) (meaning t m 3564) (meaning t m 3588) (meaning t m 3954) (meaning t m 4423) (meaning t m 4831) (meaning t m 5190) source

theorem rule33078 (p2707 p2839 p4136 : Prop) (h : (¬ p4136) ∨ (¬ p2707) ∨ p2839) : (¬ p2707) ∨ (p2839) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial33078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (meaning t m 2839) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory22334 (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule33078 (meaning t m 2707) (meaning t m 2839) (meaning t m 4136) source

theorem rule33092 (p2027 p2331 p2437 p2655 p3540 p4975 : Prop) (h : (¬ p2437) ∨ (¬ p4975) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p3540) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial33092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory22348 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 7)
  exact rule33092 (meaning t m 2027) (meaning t m 2331) (meaning t m 2437) (meaning t m 2655) (meaning t m 3540) (meaning t m 4975) source

theorem rule33093 (p1984 p2027 p2247 p2553 p3008 p3568 p4154 : Prop) (h : (¬ p4154) ∨ (¬ p3568) ∨ (¬ p1984) ∨ (¬ p2247) ∨ p2027 ∨ p3008 ∨ (¬ p2553)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial33093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory22349 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule33093 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2553) (meaning t m 3008) (meaning t m 3568) (meaning t m 4154) source

theorem rule33099 (p2027 p2220 p2509 p2608 p3146 p3370 p3452 p4348 p4377 p4438 : Prop) (h : (¬ p2509) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3452) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4377) ∨ (¬ p2608) ∨ (¬ p3370)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4348) ∨ (¬ p4377) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial33099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory22355 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33099 (meaning t m 2027) (meaning t m 2220) (meaning t m 2509) (meaning t m 2608) (meaning t m 3146) (meaning t m 3370) (meaning t m 3452) (meaning t m 4348) (meaning t m 4377) (meaning t m 4438) source

theorem rule33100 (p2027 p2210 p2579 p2891 p3246 p3950 p3956 p4347 p5193 : Prop) (h : (¬ p2891) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p5193) ∨ (¬ p3246) ∨ (¬ p2210) ∨ (¬ p3950) ∨ (¬ p4347) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial33100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory22356 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule33100 (meaning t m 2027) (meaning t m 2210) (meaning t m 2579) (meaning t m 2891) (meaning t m 3246) (meaning t m 3950) (meaning t m 3956) (meaning t m 4347) (meaning t m 5193) source

theorem rule33105 (p2027 p2132 p2192 p2743 p3172 p3361 p3737 p4418 p4737 p5582 p5600 : Prop) (h : (¬ p2192) ∨ (¬ p3361) ∨ (¬ p4418) ∨ (¬ p5600) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p3737) ∨ (¬ p3172) ∨ (¬ p4737) ∨ (¬ p5582) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (¬ p2743) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p3737) ∨ (¬ p4418) ∨ (¬ p4737) ∨ (¬ p5582) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial33105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5582)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory22361 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 10) (m.theta 8 10)
  exact rule33105 (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2743) (meaning t m 3172) (meaning t m 3361) (meaning t m 3737) (meaning t m 4418) (meaning t m 4737) (meaning t m 5582) (meaning t m 5600) source

theorem rule33108 (p2027 p2608 p3537 p3556 p3947 p4019 p4333 p4381 p4524 p5119 : Prop) (h : (¬ p4019) ∨ (¬ p4524) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p2608) ∨ (¬ p4333) ∨ (¬ p3556) ∨ (¬ p5119) ∨ (¬ p3947) ∨ (¬ p3537)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3556) ∨ (¬ p3947) ∨ (¬ p4019) ∨ (¬ p4333) ∨ (¬ p4381) ∨ (¬ p4524) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial33108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory22364 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 8) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule33108 (meaning t m 2027) (meaning t m 2608) (meaning t m 3537) (meaning t m 3556) (meaning t m 3947) (meaning t m 4019) (meaning t m 4333) (meaning t m 4381) (meaning t m 4524) (meaning t m 5119) source

theorem rule33109 (p2027 p2299 p2319 p2341 p2396 p2608 p3555 p3951 p4363 p4866 p5016 : Prop) (h : (¬ p4363) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3555) ∨ (¬ p2608) ∨ (¬ p5016) ∨ (¬ p2319) ∨ (¬ p2396) ∨ (¬ p4866) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p3951) ∨ (¬ p4363) ∨ (¬ p4866) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial33109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory22365 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33109 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2396) (meaning t m 2608) (meaning t m 3555) (meaning t m 3951) (meaning t m 4363) (meaning t m 4866) (meaning t m 5016) source

theorem rule33110 (p2027 p2247 p2299 p2744 p2780 p3037 p3366 p3399 p3822 p3931 p5564 : Prop) (h : (¬ p5564) ∨ (¬ p3931) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p2780) ∨ (¬ p3399) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3822) ∨ (¬ p3931) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial33110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory22366 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule33110 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2744) (meaning t m 2780) (meaning t m 3037) (meaning t m 3366) (meaning t m 3399) (meaning t m 3822) (meaning t m 3931) (meaning t m 5564) source

theorem rule33114 (p1997 p2027 p2542 p2573 p2964 p3346 p3574 : Prop) (h : (¬ p1997) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3574) ∨ p2964 ∨ (¬ p3346)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (p2964) ∨ (¬ p3346) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial33114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory22370 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule33114 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2573) (meaning t m 2964) (meaning t m 3346) (meaning t m 3574) source

theorem rule33116 (p1982 p2027 p2156 p2187 p2363 p2406 p2409 p4109 : Prop) (h : (¬ p1982) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p2363) ∨ p2409 ∨ (¬ p2156) ∨ (¬ p2187)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial33116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory22372 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule33116 (meaning t m 1982) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2406) (meaning t m 2409) (meaning t m 4109) source

theorem rule33117 (p1988 p2027 p2202 p2363 p2383 p2563 p3266 p3743 : Prop) (h : p2202 ∨ (¬ p1988) ∨ (¬ p3743) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p3266) ∨ (¬ p2363) ∨ (¬ p2383)) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3266) ∨ (¬ p3743) := by
  classical
  tauto

theorem initial33117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3743)) := by
  have source := ElevenTheory.theory22373 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule33117 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2363) (meaning t m 2383) (meaning t m 2563) (meaning t m 3266) (meaning t m 3743) source

theorem rule33119 (p2027 p3097 p3680 p4191 p4334 p4624 : Prop) (h : (¬ p4334) ∨ (¬ p4191) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p3680)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p4334) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial33119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory22375 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule33119 (meaning t m 2027) (meaning t m 3097) (meaning t m 3680) (meaning t m 4191) (meaning t m 4334) (meaning t m 4624) source

theorem rule33126 (p2027 p2743 p3379 p3954 p4030 p4752 : Prop) (h : (¬ p4030) ∨ (¬ p3954) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial33126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory22382 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4)
  exact rule33126 (meaning t m 2027) (meaning t m 2743) (meaning t m 3379) (meaning t m 3954) (meaning t m 4030) (meaning t m 4752) source

theorem rule33132 (p1976 p2027 p2136 p2459 p2633 p3646 p3989 p4347 : Prop) (h : (¬ p2459) ∨ (¬ p1976) ∨ p2633 ∨ p2027 ∨ (¬ p2136) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p3989)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2136) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial33132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory22388 t (m.theta 0 2) (m.theta 0 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33132 (meaning t m 1976) (meaning t m 2027) (meaning t m 2136) (meaning t m 2459) (meaning t m 2633) (meaning t m 3646) (meaning t m 3989) (meaning t m 4347) source

theorem rule33133 (p2027 p2331 p2668 p2737 p2811 p3055 p3238 p3880 p4030 p4134 p4734 : Prop) (h : (¬ p3055) ∨ (¬ p3880) ∨ (¬ p4734) ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4030) ∨ (¬ p4134) ∨ (¬ p3238) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p4030) ∨ (¬ p4134) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial33133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory22389 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8)
  exact rule33133 (meaning t m 2027) (meaning t m 2331) (meaning t m 2668) (meaning t m 2737) (meaning t m 2811) (meaning t m 3055) (meaning t m 3238) (meaning t m 3880) (meaning t m 4030) (meaning t m 4134) (meaning t m 4734) source

theorem rule33143 (p1998 p2027 p2177 p2499 p2842 p2922 p3422 p4710 : Prop) (h : (¬ p4710) ∨ (¬ p1998) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3422) ∨ p2842 ∨ (¬ p2922) ∨ (¬ p2499)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2499) ∨ (p2842) ∨ (¬ p2922) ∨ (¬ p3422) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial33143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory22399 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule33143 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2499) (meaning t m 2842) (meaning t m 2922) (meaning t m 3422) (meaning t m 4710) source

theorem rule33144 (p3951 p4443 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p4443) ∨ p3951) : (p3951) ∨ (¬ p4443) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial33144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3951) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory22400 t (m.theta 5 9) (m.theta 7 9) (m.theta 8 9)
  exact rule33144 (meaning t m 3951) (meaning t m 4443) (meaning t m 5059) source

theorem rule33146 (p2027 p2177 p2427 p2598 p2850 p3548 p4366 p4556 p4733 : Prop) (h : (¬ p3548) ∨ (¬ p2598) ∨ (¬ p4366) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4556) ∨ (¬ p4733) ∨ (¬ p2850) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4556) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial33146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory22402 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule33146 (meaning t m 2027) (meaning t m 2177) (meaning t m 2427) (meaning t m 2598) (meaning t m 2850) (meaning t m 3548) (meaning t m 4366) (meaning t m 4556) (meaning t m 4733) source

theorem rule33149 (p2027 p2589 p2696 p3506 p3755 p4235 p4729 p4831 p5660 : Prop) (h : (¬ p2589) ∨ (¬ p4235) ∨ (¬ p4831) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3755) ∨ (¬ p3506) ∨ (¬ p4729) ∨ (¬ p5660)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial33149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory22405 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule33149 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 3506) (meaning t m 3755) (meaning t m 4235) (meaning t m 4729) (meaning t m 4831) (meaning t m 5660) source

theorem rule33150 (p1988 p2027 p2233 p2499 p2573 p3222 p3276 : Prop) (h : (¬ p3276) ∨ p2233 ∨ (¬ p2499) ∨ (¬ p3222) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2233) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3222) ∨ (¬ p3276) := by
  classical
  tauto

theorem initial33150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) := by
  have source := ElevenTheory.theory22406 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule33150 (meaning t m 1988) (meaning t m 2027) (meaning t m 2233) (meaning t m 2499) (meaning t m 2573) (meaning t m 3222) (meaning t m 3276) source

theorem rule33155 (p2027 p2383 p2497 p2922 p2962 p3923 p4109 p4646 : Prop) (h : (¬ p3923) ∨ (¬ p2962) ∨ (¬ p4109) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p2497) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2497) ∨ (¬ p2922) ∨ (¬ p2962) ∨ (¬ p3923) ∨ (¬ p4109) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial33155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory22411 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 7) (m.theta 6 8)
  exact rule33155 (meaning t m 2027) (meaning t m 2383) (meaning t m 2497) (meaning t m 2922) (meaning t m 2962) (meaning t m 3923) (meaning t m 4109) (meaning t m 4646) source

theorem rule33157 (p2027 p3549 p3591 p3830 p4624 p5152 : Prop) (h : (¬ p3549) ∨ (¬ p5152) ∨ (¬ p4624) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p3830)) : (p2027) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4624) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial33157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4624)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory22413 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 6 7) (m.theta 6 9)
  exact rule33157 (meaning t m 2027) (meaning t m 3549) (meaning t m 3591) (meaning t m 3830) (meaning t m 4624) (meaning t m 5152) source

theorem rule33159 (p3115 p4385 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p4385) ∨ (¬ p3115)) : (¬ p3115) ∨ (¬ p4385) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial33159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory22415 (m.theta 2 5) (m.theta 3 5) (m.theta 5 9)
  exact rule33159 (meaning t m 3115) (meaning t m 4385) (meaning t m 5051) source

theorem rule33164 (p2027 p2659 p3346 p3506 p4425 p5176 : Prop) (h : (¬ p5176) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p3346) ∨ (¬ p2659) ∨ p2027) : (p2027) ∨ (¬ p2659) ∨ (¬ p3346) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial33164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory22420 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule33164 (meaning t m 2027) (meaning t m 2659) (meaning t m 3346) (meaning t m 3506) (meaning t m 4425) (meaning t m 5176) source

theorem rule33165 (p2027 p2122 p2177 p2528 p2774 p3860 p4261 p4438 p4733 : Prop) (h : (¬ p4438) ∨ (¬ p2177) ∨ (¬ p4733) ∨ (¬ p3860) ∨ (¬ p2122) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2528) ∨ (¬ p2774) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial33165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory22421 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule33165 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2528) (meaning t m 2774) (meaning t m 3860) (meaning t m 4261) (meaning t m 4438) (meaning t m 4733) source

theorem rule33166 (p2331 p2651 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2651) ∨ p2331) : (p2331) ∨ (¬ p2651) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial33166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2331) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory22422 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule33166 (meaning t m 2331) (meaning t m 2651) (meaning t m 3019) source

theorem rule33173 (p1988 p2027 p2622 p2707 p2743 p2761 p3434 : Prop) (h : (¬ p2743) ∨ p2622 ∨ (¬ p3434) ∨ (¬ p2761) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2707)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2761) ∨ (¬ p3434) := by
  classical
  tauto

theorem initial33173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) := by
  have source := ElevenTheory.theory22429 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule33173 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 2761) (meaning t m 3434) source

theorem rule33177 (p2027 p2579 p3016 p3399 p3631 p3690 p3742 p4647 p5193 : Prop) (h : (¬ p4647) ∨ (¬ p3631) ∨ (¬ p3742) ∨ (¬ p2579) ∨ (¬ p3690) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p3742) ∨ (¬ p4647) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial33177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory22433 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule33177 (meaning t m 2027) (meaning t m 2579) (meaning t m 3016) (meaning t m 3399) (meaning t m 3631) (meaning t m 3690) (meaning t m 3742) (meaning t m 4647) (meaning t m 5193) source

theorem rule33180 (p2027 p2274 p2313 p2696 p2787 p3005 p3256 p3744 p4604 : Prop) (h : (¬ p2313) ∨ (¬ p3005) ∨ (¬ p2787) ∨ (¬ p3256) ∨ (¬ p2696) ∨ (¬ p4604) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3744)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial33180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory22436 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule33180 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2696) (meaning t m 2787) (meaning t m 3005) (meaning t m 3256) (meaning t m 3744) (meaning t m 4604) source

theorem rule33185 (p2027 p3555 p3830 p4387 p4632 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p4632) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p4387) ∨ (¬ p3830)) : (p2027) ∨ (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4387) ∨ (¬ p4632) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial33185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4632)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory22441 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 4 5) (m.theta 5 9)
  exact rule33185 (meaning t m 2027) (meaning t m 3555) (meaning t m 3830) (meaning t m 4387) (meaning t m 4632) (meaning t m 4948) source

theorem rule33188 (p2274 p3125 p4025 : Prop) (h : (¬ p3125) ∨ (¬ p4025) ∨ p2274) : (p2274) ∨ (¬ p3125) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial33188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2274) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory22444 (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule33188 (meaning t m 2274) (meaning t m 3125) (meaning t m 4025) source

theorem rule33190 (p2027 p2139 p2156 p2187 p2363 p3055 p3876 p4278 p4669 : Prop) (h : (¬ p2156) ∨ (¬ p4669) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2187) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial33190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory22446 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule33190 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3055) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) source

theorem rule33191 (p2027 p2630 p2745 p3193 p3343 p3402 : Prop) (h : (¬ p3402) ∨ (¬ p3343) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3193) ∨ p2027) : (p2027) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial33191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory22447 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9)
  exact rule33191 (meaning t m 2027) (meaning t m 2630) (meaning t m 2745) (meaning t m 3193) (meaning t m 3343) (meaning t m 3402) source

theorem rule33192 (p2027 p2246 p2331 p2363 p2608 p2668 p2744 p4324 p4366 p4424 p4669 : Prop) (h : (¬ p2363) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p2668) ∨ (¬ p4324) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial33192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory22448 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule33192 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2363) (meaning t m 2608) (meaning t m 2668) (meaning t m 2744) (meaning t m 4324) (meaning t m 4366) (meaning t m 4424) (meaning t m 4669) source

theorem rule33193 (p1982 p2027 p2459 p2765 p2911 p3292 p3389 p3755 p3952 p4236 p4315 p4419 : Prop) (h : (¬ p3755) ∨ (¬ p4419) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p1982) ∨ (¬ p3292) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2459) ∨ p2765 ∨ (¬ p3952) ∨ (¬ p4315)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2765) ∨ (¬ p2911) ∨ (¬ p3292) ∨ (¬ p3389) ∨ (¬ p3755) ∨ (¬ p3952) ∨ (¬ p4236) ∨ (¬ p4315) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial33193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory22449 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 7) (m.theta 5 6) (m.theta 7 8) (m.theta 8 9)
  exact rule33193 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2765) (meaning t m 2911) (meaning t m 3292) (meaning t m 3389) (meaning t m 3755) (meaning t m 3952) (meaning t m 4236) (meaning t m 4315) (meaning t m 4419) source

theorem rule33198 (p1987 p2027 p2651 p2764 p2810 p3292 p5284 : Prop) (h : (¬ p1987) ∨ (¬ p2810) ∨ (¬ p2651) ∨ (¬ p3292) ∨ p2027 ∨ p2764 ∨ (¬ p5284)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p2810) ∨ (¬ p3292) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial33198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory22454 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule33198 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 2810) (meaning t m 3292) (meaning t m 5284) source

theorem rule33203 (p2027 p2743 p3222 p3541 p4752 p5160 : Prop) (h : (¬ p3541) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3222) ∨ (¬ p5160) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3222) ∨ (¬ p3541) ∨ (¬ p4752) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial33203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory22459 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 9)
  exact rule33203 (meaning t m 2027) (meaning t m 2743) (meaning t m 3222) (meaning t m 3541) (meaning t m 4752) (meaning t m 5160) source

theorem rule33205 (p2027 p2962 p3556 p3654 p3690 p4621 : Prop) (h : (¬ p4621) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3654) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3654) ∨ (¬ p3690) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial33205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory22461 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule33205 (meaning t m 2027) (meaning t m 2962) (meaning t m 3556) (meaning t m 3654) (meaning t m 3690) (meaning t m 4621) source

theorem rule33206 (p1992 p2027 p2143 p2462 p3097 p3583 p3646 p4107 : Prop) (h : (¬ p3646) ∨ (¬ p3097) ∨ p2462 ∨ p2027 ∨ (¬ p4107) ∨ (¬ p3583) ∨ (¬ p1992) ∨ (¬ p2143)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2462) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial33206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory22462 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule33206 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2462) (meaning t m 3097) (meaning t m 3583) (meaning t m 3646) (meaning t m 4107) source

theorem rule33209 (p2027 p2248 p2499 p2946 p3005 p3452 p3956 p4311 p4315 p4433 : Prop) (h : (¬ p4311) ∨ (¬ p3005) ∨ (¬ p4433) ∨ (¬ p3452) ∨ (¬ p2499) ∨ (¬ p4315) ∨ (¬ p3956) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p2946)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4311) ∨ (¬ p4315) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial33209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory22465 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8)
  exact rule33209 (meaning t m 2027) (meaning t m 2248) (meaning t m 2499) (meaning t m 2946) (meaning t m 3005) (meaning t m 3452) (meaning t m 3956) (meaning t m 4311) (meaning t m 4315) (meaning t m 4433) source

theorem rule33210 (p1983 p2027 p2688 p2807 p2952 p2992 p3246 p4333 : Prop) (h : (¬ p4333) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p1983) ∨ (¬ p2952) ∨ p2688 ∨ (¬ p2807) ∨ (¬ p2992)) : (¬ p1983) ∨ (p2027) ∨ (p2688) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3246) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial33210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory22466 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule33210 (meaning t m 1983) (meaning t m 2027) (meaning t m 2688) (meaning t m 2807) (meaning t m 2952) (meaning t m 2992) (meaning t m 3246) (meaning t m 4333) source

theorem rule33211 (p1982 p2027 p2323 p2470 p2663 p3146 p4149 p5568 : Prop) (h : (¬ p2663) ∨ (¬ p2470) ∨ p2323 ∨ (¬ p1982) ∨ (¬ p5568) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p3146) ∨ (¬ p4149) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial33211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory22467 t (m.theta 0 3) (m.theta 0 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule33211 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2470) (meaning t m 2663) (meaning t m 3146) (meaning t m 4149) (meaning t m 5568) source

theorem rule33218 (p2027 p2608 p3537 p3540 p3644 p3969 p4188 p4348 p5122 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p3537) ∨ (¬ p3540) ∨ (¬ p3969) ∨ (¬ p4188) ∨ (¬ p5122) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p4188) ∨ (¬ p4348) ∨ (¬ p5122) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial33218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory22474 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule33218 (meaning t m 2027) (meaning t m 2608) (meaning t m 3537) (meaning t m 3540) (meaning t m 3644) (meaning t m 3969) (meaning t m 4188) (meaning t m 4348) (meaning t m 5122) (meaning t m 5193) source

theorem rule33221 (p2027 p3037 p3399 p3542 p3860 p3931 p5564 : Prop) (h : (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3037) ∨ p2027 ∨ (¬ p5564) ∨ (¬ p3860) ∨ (¬ p3931)) : (p2027) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p3931) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial33221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory22477 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 3 7) (m.theta 7 10) (m.theta 7 8)
  exact rule33221 (meaning t m 2027) (meaning t m 3037) (meaning t m 3399) (meaning t m 3542) (meaning t m 3860) (meaning t m 3931) (meaning t m 5564) source

theorem rule33225 (p1981 p2027 p2254 p2608 p2764 p3414 p3537 p3609 p3947 p4347 p4381 : Prop) (h : (¬ p3414) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3609) ∨ (¬ p1981) ∨ (¬ p4381) ∨ (¬ p3947) ∨ (¬ p2254) ∨ p2764 ∨ (¬ p3537)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (p2764) ∨ (¬ p3414) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3947) ∨ (¬ p4347) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial33225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory22481 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule33225 (meaning t m 1981) (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2764) (meaning t m 3414) (meaning t m 3537) (meaning t m 3609) (meaning t m 3947) (meaning t m 4347) (meaning t m 4381) source

theorem rule33228 (p2027 p3222 p3276 p3365 p3366 p3572 p3947 p4376 p4444 p4669 : Prop) (h : (¬ p4444) ∨ (¬ p3276) ∨ (¬ p4669) ∨ (¬ p3947) ∨ (¬ p3572) ∨ (¬ p3222) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4376)) : (p2027) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial33228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory22484 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule33228 (meaning t m 2027) (meaning t m 3222) (meaning t m 3276) (meaning t m 3365) (meaning t m 3366) (meaning t m 3572) (meaning t m 3947) (meaning t m 4376) (meaning t m 4444) (meaning t m 4669) source

theorem rule33230 (p1995 p2027 p2633 p2928 p3553 p3931 p5503 : Prop) (h : (¬ p3553) ∨ (¬ p1995) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p5503) ∨ (¬ p3931) ∨ p2633) : (¬ p1995) ∨ (p2027) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3553) ∨ (¬ p3931) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial33230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory22486 t (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 10) (m.theta 7 8)
  exact rule33230 (meaning t m 1995) (meaning t m 2027) (meaning t m 2633) (meaning t m 2928) (meaning t m 3553) (meaning t m 3931) (meaning t m 5503) source

theorem rule33231 (p1982 p2027 p2177 p2230 p2252 p2373 p2741 p2797 p2963 p2997 p3146 p3519 p3877 p4376 p4548 : Prop) (h : p2997 ∨ (¬ p2177) ∨ (¬ p4548) ∨ (¬ p3146) ∨ (¬ p1982) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p2373) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2797) ∨ (¬ p2230) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p3877)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2230) ∨ (¬ p2252) ∨ (¬ p2373) ∨ (¬ p2741) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3146) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4376) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial33231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory22487 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule33231 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2230) (meaning t m 2252) (meaning t m 2373) (meaning t m 2741) (meaning t m 2797) (meaning t m 2963) (meaning t m 2997) (meaning t m 3146) (meaning t m 3519) (meaning t m 3877) (meaning t m 4376) (meaning t m 4548) source

theorem rule33233 (p2027 p2352 p2573 p3366 p3425 p3519 p3979 p4324 p4376 p4381 p5119 : Prop) (h : (¬ p2352) ∨ (¬ p3979) ∨ (¬ p3425) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p5119) ∨ (¬ p4381) ∨ (¬ p3519) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3519) ∨ (¬ p3979) ∨ (¬ p4324) ∨ (¬ p4376) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial33233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory22489 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule33233 (meaning t m 2027) (meaning t m 2352) (meaning t m 2573) (meaning t m 3366) (meaning t m 3425) (meaning t m 3519) (meaning t m 3979) (meaning t m 4324) (meaning t m 4376) (meaning t m 4381) (meaning t m 5119) source

theorem rule33236 (p2098 p2470 p3905 p5373 : Prop) (h : (¬ p5373) ∨ (¬ p3905) ∨ (¬ p2098) ∨ p2470) : (¬ p2098) ∨ (p2470) ∨ (¬ p3905) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial33236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (meaning t m 2470) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory22492 (m.theta 0 2) (m.theta 0 4) (m.theta 2 8) (m.theta 4 8)
  exact rule33236 (meaning t m 2098) (meaning t m 2470) (meaning t m 3905) (meaning t m 5373) source

theorem rule33238 (p2027 p2246 p2534 p2744 p3055 p3286 p3366 p3506 p3874 p3950 p4381 : Prop) (h : (¬ p2534) ∨ (¬ p4381) ∨ (¬ p3366) ∨ (¬ p3286) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p3055) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3286) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial33238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory22494 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 9) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule33238 (meaning t m 2027) (meaning t m 2246) (meaning t m 2534) (meaning t m 2744) (meaning t m 3055) (meaning t m 3286) (meaning t m 3366) (meaning t m 3506) (meaning t m 3874) (meaning t m 3950) (meaning t m 4381) source

theorem rule33242 (p1976 p2027 p2202 p3346 p3584 p3660 p3670 p3905 p4425 p5165 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p3905) ∨ p2202 ∨ (¬ p5165) ∨ (¬ p3660) ∨ (¬ p3584) ∨ (¬ p3346) ∨ (¬ p3670) ∨ (¬ p4425)) : (¬ p1976) ∨ (p2027) ∨ (p2202) ∨ (¬ p3346) ∨ (¬ p3584) ∨ (¬ p3660) ∨ (¬ p3670) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5165) := by
  classical
  tauto

theorem initial33242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5165)) := by
  have source := ElevenTheory.theory22498 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 9) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule33242 (meaning t m 1976) (meaning t m 2027) (meaning t m 2202) (meaning t m 3346) (meaning t m 3584) (meaning t m 3660) (meaning t m 3670) (meaning t m 3905) (meaning t m 4425) (meaning t m 5165) source

theorem rule33243 (p2027 p3483 p3857 p3858 p4345 p4358 p4995 : Prop) (h : (¬ p3858) ∨ (¬ p4995) ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p3857) ∨ (¬ p4345) ∨ p2027) : (p2027) ∨ (¬ p3483) ∨ (¬ p3857) ∨ (¬ p3858) ∨ (¬ p4345) ∨ (¬ p4358) ∨ (¬ p4995) := by
  classical
  tauto

theorem initial33243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3858)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4995)) := by
  have source := ElevenTheory.theory22499 t (m.theta 0 8) (m.theta 1 8) (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule33243 (meaning t m 2027) (meaning t m 3483) (meaning t m 3857) (meaning t m 3858) (meaning t m 4345) (meaning t m 4358) (meaning t m 4995) source

theorem rule33250 (p1976 p2027 p2528 p2579 p3422 p3498 p3905 p4340 p5368 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p2528) ∨ p3498 ∨ (¬ p4340) ∨ (¬ p5368) ∨ (¬ p3905) ∨ (¬ p3422) ∨ (¬ p2579)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (p3498) ∨ (¬ p3905) ∨ (¬ p4340) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial33250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3422)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory22506 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule33250 (meaning t m 1976) (meaning t m 2027) (meaning t m 2528) (meaning t m 2579) (meaning t m 3422) (meaning t m 3498) (meaning t m 3905) (meaning t m 4340) (meaning t m 5368) source

theorem rule33253 (p2143 p3556 p4385 p4402 : Prop) (h : (¬ p4402) ∨ (¬ p3556) ∨ (¬ p2143) ∨ p4385) : (¬ p2143) ∨ (¬ p3556) ∨ (p4385) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial33253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 3556)) ∨ (meaning t m 4385) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory22509 (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9)
  exact rule33253 (meaning t m 2143) (meaning t m 3556) (meaning t m 4385) (meaning t m 4402) source

theorem rule33259 (p1991 p2027 p2633 p3005 p3172 p3553 p3572 : Prop) (h : (¬ p1991) ∨ (¬ p3172) ∨ (¬ p3005) ∨ (¬ p3553) ∨ p2633 ∨ (¬ p3572) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial33259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory22515 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule33259 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 3005) (meaning t m 3172) (meaning t m 3553) (meaning t m 3572) source

theorem rule33265 (p1990 p2027 p2284 p2688 p3136 p3189 p3877 : Prop) (h : (¬ p1990) ∨ p2688 ∨ (¬ p3877) ∨ (¬ p3189) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3136)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (p2688) ∨ (¬ p3136) ∨ (¬ p3189) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial33265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory22521 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6)
  exact rule33265 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2688) (meaning t m 3136) (meaning t m 3189) (meaning t m 3877) source

theorem rule33266 (p2027 p2122 p2177 p2245 p2657 p2727 p2774 p4360 p4437 p4438 p4733 : Prop) (h : (¬ p2657) ∨ (¬ p4437) ∨ (¬ p4733) ∨ (¬ p4360) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2122) ∨ (¬ p4438) ∨ (¬ p2177) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2774) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4438) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial33266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory22522 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule33266 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2245) (meaning t m 2657) (meaning t m 2727) (meaning t m 2774) (meaning t m 4360) (meaning t m 4437) (meaning t m 4438) (meaning t m 4733) source

theorem rule33268 (p3016 p3584 p3683 : Prop) (h : (¬ p3683) ∨ (¬ p3584) ∨ (¬ p3016)) : (¬ p3016) ∨ (¬ p3584) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial33268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory22524 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule33268 (meaning t m 3016) (meaning t m 3584) (meaning t m 3683) source

theorem rule33272 (p2027 p2156 p2960 p3125 p4037 p4153 : Prop) (h : (¬ p3125) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4153) ∨ (¬ p2960)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2960) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial33272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory22528 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule33272 (meaning t m 2027) (meaning t m 2156) (meaning t m 2960) (meaning t m 3125) (meaning t m 4037) (meaning t m 4153) source

theorem rule33274 (p2027 p2312 p2341 p3125 p3570 p4204 p4624 : Prop) (h : (¬ p3570) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p3125) ∨ (¬ p2312) ∨ (¬ p4204) ∨ (¬ p4624)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3125) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial33274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory22530 t (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule33274 (meaning t m 2027) (meaning t m 2312) (meaning t m 2341) (meaning t m 3125) (meaning t m 3570) (meaning t m 4204) (meaning t m 4624) source

theorem rule33275 (p1991 p2027 p2952 p2992 p2997 p3097 p3745 p4154 : Prop) (h : (¬ p3097) ∨ (¬ p2952) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p2992) ∨ p2997 ∨ (¬ p1991) ∨ (¬ p4154)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3745) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial33275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory22531 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule33275 (meaning t m 1991) (meaning t m 2027) (meaning t m 2952) (meaning t m 2992) (meaning t m 2997) (meaning t m 3097) (meaning t m 3745) (meaning t m 4154) source

theorem rule33277 (p2027 p2241 p2459 p2476 p2534 p2992 p3156 p4902 p5193 : Prop) (h : (¬ p2534) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p4902) ∨ (¬ p5193) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p2241) ∨ p2027) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4902) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial33277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory22533 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule33277 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 2992) (meaning t m 3156) (meaning t m 4902) (meaning t m 5193) source

theorem rule33279 (p1992 p2027 p2608 p2633 p3452 p3590 p3644 p3876 : Prop) (h : (¬ p3876) ∨ (¬ p3590) ∨ (¬ p3452) ∨ (¬ p3644) ∨ p2633 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2633) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial33279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory22535 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule33279 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2633) (meaning t m 3452) (meaning t m 3590) (meaning t m 3644) (meaning t m 3876) source

theorem rule33280 (p2137 p4032 p4385 : Prop) (h : (¬ p4385) ∨ (¬ p2137) ∨ p4032) : (¬ p2137) ∨ (p4032) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial33280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2137)) ∨ (meaning t m 4032) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory22536 (m.theta 0 5) (m.theta 2 5) (m.theta 5 9)
  exact rule33280 (meaning t m 2137) (meaning t m 4032) (meaning t m 4385) source

theorem rule33283 (p2027 p2383 p2584 p2656 p2992 p3923 p4245 p4704 : Prop) (h : (¬ p2584) ∨ (¬ p2992) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p4245) ∨ (¬ p3923) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3923) ∨ (¬ p4245) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial33283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory22539 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 8)
  exact rule33283 (meaning t m 2027) (meaning t m 2383) (meaning t m 2584) (meaning t m 2656) (meaning t m 2992) (meaning t m 3923) (meaning t m 4245) (meaning t m 4704) source

theorem rule33292 (p2015 p2027 p2388 p2901 p3093 p3486 p3555 : Prop) (h : (¬ p2015) ∨ p2027 ∨ (¬ p2901) ∨ p2388 ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3486)) : (¬ p2015) ∨ (p2027) ∨ (p2388) ∨ (¬ p2901) ∨ (¬ p3093) ∨ (¬ p3486) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial33292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory22548 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 7)
  exact rule33292 (meaning t m 2015) (meaning t m 2027) (meaning t m 2388) (meaning t m 2901) (meaning t m 3093) (meaning t m 3486) (meaning t m 3555) source

theorem rule33296 (p2027 p2449 p2589 p2685 p2696 p3692 p3880 p3950 p4729 : Prop) (h : (¬ p3692) ∨ (¬ p4729) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3950) ∨ (¬ p3880) ∨ (¬ p2685) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial33296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory22552 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule33296 (meaning t m 2027) (meaning t m 2449) (meaning t m 2589) (meaning t m 2685) (meaning t m 2696) (meaning t m 3692) (meaning t m 3880) (meaning t m 3950) (meaning t m 4729) source

theorem rule33298 (p1997 p2027 p2230 p2579 p2688 p2727 p3016 : Prop) (h : p2688 ∨ (¬ p3016) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2230) ∨ (¬ p2727)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial33298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory22554 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule33298 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2579) (meaning t m 2688) (meaning t m 2727) (meaning t m 3016) source

theorem rule33299 (p2027 p2177 p2246 p2295 p2331 p2608 p2744 p3817 p4366 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p2177) ∨ (¬ p2331) ∨ (¬ p2295) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p3817)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2246) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial33299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory22555 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule33299 (meaning t m 2027) (meaning t m 2177) (meaning t m 2246) (meaning t m 2295) (meaning t m 2331) (meaning t m 2608) (meaning t m 2744) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) source

theorem rule33316 (p2027 p2284 p3051 p3646 p4235 p4705 : Prop) (h : (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p4705) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial33316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory22572 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule33316 (meaning t m 2027) (meaning t m 2284) (meaning t m 3051) (meaning t m 3646) (meaning t m 4235) (meaning t m 4705) source

end SunPrize.SMT
