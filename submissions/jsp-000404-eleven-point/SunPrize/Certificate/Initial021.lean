import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory010
import SunPrize.Certificate.Theory011
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule11307 (p2027 p2252 p2750 p2952 p3449 p3497 p3692 p3954 p4181 p5122 : Prop) (h : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3497) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4181) ∨ (¬ p3449) ∨ (¬ p5122) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3449) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial11307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory2819 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule11307 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3449) (meaning t m 3497) (meaning t m 3692) (meaning t m 3954) (meaning t m 4181) (meaning t m 5122) source

theorem rule11308 (p2027 p2241 p2750 p3073 p3857 p4416 p5316 : Prop) (h : (¬ p4416) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p3073) ∨ (¬ p5316) ∨ (¬ p2750) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4416) ∨ (¬ p5316) := by
  classical
  tauto

theorem initial11308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 5316)) := by
  have source := ElevenTheory.theory2820 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 8 9)
  exact rule11308 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 3073) (meaning t m 3857) (meaning t m 4416) (meaning t m 5316) source

theorem rule11309 (p2027 p3449 p3591 p4318 p4358 p4871 : Prop) (h : (¬ p4871) ∨ (¬ p4318) ∨ (¬ p3449) ∨ (¬ p4358) ∨ (¬ p3591) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p4318) ∨ (¬ p4358) ∨ (¬ p4871) := by
  classical
  tauto

theorem initial11309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4871)) := by
  have source := ElevenTheory.theory2821 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 2 6) (m.theta 6 8)
  exact rule11309 (meaning t m 2027) (meaning t m 3449) (meaning t m 3591) (meaning t m 4318) (meaning t m 4358) (meaning t m 4871) source

theorem rule11310 (p2027 p2241 p2750 p2780 p2829 p3873 : Prop) (h : (¬ p2780) ∨ (¬ p3873) ∨ (¬ p2241) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2829)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial11310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory2822 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6)
  exact rule11310 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2780) (meaning t m 2829) (meaning t m 3873) source

theorem rule11311 (p2027 p2383 p2786 p3292 p3483 p3680 p4358 p4368 p4789 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p2786) ∨ (¬ p3483) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p2383) ∨ (¬ p4368) ∨ (¬ p4789) ∨ (¬ p3680) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3292) ∨ (¬ p3483) ∨ (¬ p3680) ∨ (¬ p4358) ∨ (¬ p4368) ∨ (¬ p4789) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11311 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2823 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 9) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule11311 (meaning t m 2027) (meaning t m 2383) (meaning t m 2786) (meaning t m 3292) (meaning t m 3483) (meaning t m 3680) (meaning t m 4358) (meaning t m 4368) (meaning t m 4789) (meaning t m 5284) source

theorem rule11312 (p2027 p2241 p2717 p2750 p2753 p3471 p3834 p3941 p4321 p5119 : Prop) (h : p2027 ∨ (¬ p5119) ∨ (¬ p3471) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3834) ∨ (¬ p2750) ∨ (¬ p4321) ∨ (¬ p2241) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2717) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3834) ∨ (¬ p3941) ∨ (¬ p4321) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2824 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11312 (meaning t m 2027) (meaning t m 2241) (meaning t m 2717) (meaning t m 2750) (meaning t m 2753) (meaning t m 3471) (meaning t m 3834) (meaning t m 3941) (meaning t m 4321) (meaning t m 5119) source

theorem rule11313 (p2027 p2252 p2383 p2440 p2657 p2750 p2753 p2786 p3483 p4358 p4368 p4948 : Prop) (h : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p4368) ∨ (¬ p2252) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p2750) ∨ (¬ p2383) ∨ (¬ p4948) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3483)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p3483) ∨ (¬ p4358) ∨ (¬ p4368) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory2825 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9)
  exact rule11313 (meaning t m 2027) (meaning t m 2252) (meaning t m 2383) (meaning t m 2440) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2786) (meaning t m 3483) (meaning t m 4358) (meaning t m 4368) (meaning t m 4948) source

theorem rule11314 (p2027 p2373 p4110 p4358 p4441 p4889 : Prop) (h : (¬ p4889) ∨ (¬ p4110) ∨ (¬ p4358) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4441)) : (p2027) ∨ (¬ p2373) ∨ (¬ p4110) ∨ (¬ p4358) ∨ (¬ p4441) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial11314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory2826 t (m.theta 2 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule11314 (meaning t m 2027) (meaning t m 2373) (meaning t m 4110) (meaning t m 4358) (meaning t m 4441) (meaning t m 4889) source

theorem rule11315 (p2027 p2901 p3879 p3880 p4129 p4132 p5564 : Prop) (h : (¬ p2901) ∨ (¬ p4132) ∨ p2027 ∨ (¬ p5564) ∨ (¬ p4129) ∨ (¬ p3880) ∨ (¬ p3879)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3879) ∨ (¬ p3880) ∨ (¬ p4129) ∨ (¬ p4132) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2827 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8)
  exact rule11315 (meaning t m 2027) (meaning t m 2901) (meaning t m 3879) (meaning t m 3880) (meaning t m 4129) (meaning t m 4132) (meaning t m 5564) source

theorem rule11316 (p2027 p2608 p2737 p3591 p3918 p4842 : Prop) (h : (¬ p2737) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3918) ∨ (¬ p4842) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2828 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6)
  exact rule11316 (meaning t m 2027) (meaning t m 2608) (meaning t m 2737) (meaning t m 3591) (meaning t m 3918) (meaning t m 4842) source

theorem rule11319 (p2027 p2440 p2657 p2807 p3579 p4646 : Prop) (h : p2027 ∨ (¬ p4646) ∨ (¬ p2807) ∨ (¬ p2657) ∨ (¬ p2440) ∨ (¬ p3579)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial11319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2831 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule11319 (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2807) (meaning t m 3579) (meaning t m 4646) source

theorem rule11320 (p2027 p2318 p2911 p3551 p3822 p3920 p5222 : Prop) (h : p2027 ∨ (¬ p3822) ∨ (¬ p3551) ∨ (¬ p5222) ∨ (¬ p2911) ∨ (¬ p2318) ∨ (¬ p3920)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p3822) ∨ (¬ p3920) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial11320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory2832 t (m.theta 0 7) (m.theta 2 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule11320 (meaning t m 2027) (meaning t m 2318) (meaning t m 2911) (meaning t m 3551) (meaning t m 3822) (meaning t m 3920) (meaning t m 5222) source

theorem rule11321 (p2027 p2132 p2901 p3425 p4169 p4906 : Prop) (h : (¬ p4169) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p2901) ∨ (¬ p2132) ∨ (¬ p4906)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2901) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial11321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2833 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7)
  exact rule11321 (meaning t m 2027) (meaning t m 2132) (meaning t m 2901) (meaning t m 3425) (meaning t m 4169) (meaning t m 4906) source

theorem rule11322 (p2027 p2264 p2318 p3551 p4037 p4156 p4620 : Prop) (h : (¬ p4156) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p4620) ∨ (¬ p2318) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2318) ∨ (¬ p3551) ∨ (¬ p4037) ∨ (¬ p4156) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial11322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory2834 t (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule11322 (meaning t m 2027) (meaning t m 2264) (meaning t m 2318) (meaning t m 3551) (meaning t m 4037) (meaning t m 4156) (meaning t m 4620) source

theorem rule11323 (p2027 p2387 p2668 p3758 p4336 p4356 p4906 : Prop) (h : (¬ p4336) ∨ (¬ p3758) ∨ (¬ p4906) ∨ (¬ p4356) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p3758) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial11323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2835 t (m.theta 0 6) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule11323 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 3758) (meaning t m 4336) (meaning t m 4356) (meaning t m 4906) source

theorem rule11325 (p2027 p2241 p2750 p3527 p3551 p4452 p4869 p5206 : Prop) (h : (¬ p5206) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3527) ∨ (¬ p4452) ∨ (¬ p3551) ∨ (¬ p4869)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4452) ∨ (¬ p4869) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial11325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory2837 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 1 7) (m.theta 7 8)
  exact rule11325 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 3527) (meaning t m 3551) (meaning t m 4452) (meaning t m 4869) (meaning t m 5206) source

theorem rule11326 (p2027 p2252 p2750 p2753 p2774 p2819 p3414 p3947 p3979 p4381 p5119 : Prop) (h : (¬ p2252) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p5119) ∨ (¬ p2774) ∨ (¬ p2753) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4381) ∨ (¬ p2819) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p3979) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2838 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11326 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3414) (meaning t m 3947) (meaning t m 3979) (meaning t m 4381) (meaning t m 5119) source

theorem rule11327 (p2027 p2542 p3379 p3555 p4034 p4811 : Prop) (h : (¬ p3379) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4811)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial11327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2839 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5)
  exact rule11327 (meaning t m 2027) (meaning t m 2542) (meaning t m 3379) (meaning t m 3555) (meaning t m 4034) (meaning t m 4811) source

theorem rule11328 (p2027 p2132 p2619 p3414 p3947 p3969 p4381 p4789 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p3947) ∨ (¬ p4789) ∨ (¬ p3414) ∨ (¬ p2619) ∨ (¬ p4381) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p2132)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p3969) ∨ (¬ p4381) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2840 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11328 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 3414) (meaning t m 3947) (meaning t m 3969) (meaning t m 4381) (meaning t m 4789) (meaning t m 5119) source

theorem rule11331 (p2027 p2383 p2962 p3989 p4173 p4525 : Prop) (h : p2027 ∨ (¬ p2962) ∨ (¬ p3989) ∨ (¬ p4525) ∨ (¬ p4173) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4525) := by
  classical
  tauto

theorem initial11331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4525)) := by
  have source := ElevenTheory.theory2843 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 5) (m.theta 5 6) (m.theta 6 8)
  exact rule11331 (meaning t m 2027) (meaning t m 2383) (meaning t m 2962) (meaning t m 3989) (meaning t m 4173) (meaning t m 4525) source

theorem rule11332 (p2027 p2187 p2829 p4242 p4857 p4889 : Prop) (h : (¬ p4857) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2187) ∨ (¬ p4242) ∨ (¬ p4889)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2829) ∨ (¬ p4242) ∨ (¬ p4857) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial11332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4857)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory2844 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8)
  exact rule11332 (meaning t m 2027) (meaning t m 2187) (meaning t m 2829) (meaning t m 4242) (meaning t m 4857) (meaning t m 4889) source

theorem rule11333 (p2027 p2780 p3516 p3819 p4324 p4357 p4842 : Prop) (h : (¬ p2780) ∨ (¬ p3819) ∨ p2027 ∨ (¬ p4357) ∨ (¬ p3516) ∨ (¬ p4324) ∨ (¬ p4842)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3516) ∨ (¬ p3819) ∨ (¬ p4324) ∨ (¬ p4357) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2845 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 2 6) (m.theta 2 7) (m.theta 7 9)
  exact rule11333 (meaning t m 2027) (meaning t m 2780) (meaning t m 3516) (meaning t m 3819) (meaning t m 4324) (meaning t m 4357) (meaning t m 4842) source

theorem rule11334 (p2027 p2307 p2737 p2779 p3549 p3953 p4842 : Prop) (h : (¬ p2737) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4842) ∨ (¬ p3953) ∨ (¬ p2779) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2779) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2846 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule11334 (meaning t m 2027) (meaning t m 2307) (meaning t m 2737) (meaning t m 2779) (meaning t m 3549) (meaning t m 3953) (meaning t m 4842) source

theorem rule11335 (p2027 p2122 p2177 p2252 p2657 p2750 p2753 p2774 p3742 p4278 p4666 : Prop) (h : (¬ p2252) ∨ (¬ p2657) ∨ (¬ p3742) ∨ (¬ p2177) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory2847 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11335 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3742) (meaning t m 4278) (meaning t m 4666) source

theorem rule11336 (p3266 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3266)) : (¬ p3266) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial11336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory2848 (m.theta 8 9) (m.theta 9 10)
  exact rule11336 (meaning t m 3266) (meaning t m 4444) source

theorem rule11337 (p2027 p2532 p3115 p3497 p4340 p4742 : Prop) (h : (¬ p4742) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4340) ∨ (¬ p4742) := by
  classical
  tauto

theorem initial11337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4742)) := by
  have source := ElevenTheory.theory2849 t (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule11337 (meaning t m 2027) (meaning t m 2532) (meaning t m 3115) (meaning t m 3497) (meaning t m 4340) (meaning t m 4742) source

theorem rule11339 (p2027 p2954 p3146 p3156 p3697 p3857 : Prop) (h : p2027 ∨ (¬ p3857) ∨ (¬ p3697) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p2954)) : (p2027) ∨ (¬ p2954) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3697) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial11339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory2851 t (m.theta 0 5) (m.theta 0 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule11339 (meaning t m 2027) (meaning t m 2954) (meaning t m 3146) (meaning t m 3156) (meaning t m 3697) (meaning t m 3857) source

theorem rule11340 (p2027 p2252 p2745 p3005 p3170 p3256 p3857 : Prop) (h : (¬ p2745) ∨ (¬ p3170) ∨ (¬ p3005) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2745) ∨ (¬ p3005) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial11340 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory2852 t (m.theta 0 3) (m.theta 0 8) (m.theta 1 3) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9)
  exact rule11340 (meaning t m 2027) (meaning t m 2252) (meaning t m 2745) (meaning t m 3005) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) source

theorem rule11344 (p2027 p3680 p3821 p4192 p4381 p4986 : Prop) (h : p2027 ∨ (¬ p3821) ∨ (¬ p4986) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p3680)) : (p2027) ∨ (¬ p3680) ∨ (¬ p3821) ∨ (¬ p4192) ∨ (¬ p4381) ∨ (¬ p4986) := by
  classical
  tauto

theorem initial11344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4986)) := by
  have source := ElevenTheory.theory2856 t (m.theta 0 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule11344 (meaning t m 2027) (meaning t m 3680) (meaning t m 3821) (meaning t m 4192) (meaning t m 4381) (meaning t m 4986) source

theorem rule11345 (p2027 p3051 p3646 p4140 p4393 p5472 : Prop) (h : (¬ p5472) ∨ (¬ p3646) ∨ (¬ p3051) ∨ (¬ p4140) ∨ p2027 ∨ (¬ p4393)) : (p2027) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140) ∨ (¬ p4393) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial11345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory2857 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10) (m.theta 6 7)
  exact rule11345 (meaning t m 2027) (meaning t m 3051) (meaning t m 3646) (meaning t m 4140) (meaning t m 4393) (meaning t m 5472) source

theorem rule11346 (p2027 p2098 p2780 p3989 p4401 p4417 p4967 : Prop) (h : (¬ p4401) ∨ p2027 ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p4417) ∨ (¬ p3989) ∨ (¬ p4967)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3989) ∨ (¬ p4401) ∨ (¬ p4417) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial11346 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory2858 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule11346 (meaning t m 2027) (meaning t m 2098) (meaning t m 2780) (meaning t m 3989) (meaning t m 4401) (meaning t m 4417) (meaning t m 4967) source

theorem rule11349 (p3661 p3919 p4386 : Prop) (h : (¬ p4386) ∨ p3661 ∨ (¬ p3919)) : (p3661) ∨ (¬ p3919) ∨ (¬ p4386) := by
  classical
  tauto

theorem initial11349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3661) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4386)) := by
  have source := ElevenTheory.theory2861 (m.theta 3 5) (m.theta 3 7) (m.theta 3 8)
  exact rule11349 (meaning t m 3661) (meaning t m 3919) (meaning t m 4386) source

theorem rule11350 (p2027 p2166 p3609 p3949 p4363 p4746 : Prop) (h : (¬ p4746) ∨ (¬ p3949) ∨ (¬ p3609) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4363)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3609) ∨ (¬ p3949) ∨ (¬ p4363) ∨ (¬ p4746) := by
  classical
  tauto

theorem initial11350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4746)) := by
  have source := ElevenTheory.theory2862 t (m.theta 1 5) (m.theta 2 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule11350 (meaning t m 2027) (meaning t m 2166) (meaning t m 3609) (meaning t m 3949) (meaning t m 4363) (meaning t m 4746) source

theorem rule11351 (p2027 p2295 p2313 p2608 p2839 p3105 p4037 p4397 p5021 : Prop) (h : (¬ p2608) ∨ (¬ p2295) ∨ (¬ p4397) ∨ (¬ p2839) ∨ (¬ p4037) ∨ (¬ p5021) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3105)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p4037) ∨ (¬ p4397) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial11351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory2863 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule11351 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 4037) (meaning t m 4397) (meaning t m 5021) source

theorem rule11352 (p2027 p2449 p2685 p2745 p3031 p3817 : Prop) (h : (¬ p3031) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p2745) ∨ (¬ p2685) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3031) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial11352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory2864 t (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9)
  exact rule11352 (meaning t m 2027) (meaning t m 2449) (meaning t m 2685) (meaning t m 2745) (meaning t m 3031) (meaning t m 3817) source

theorem rule11353 (p2027 p2668 p3093 p3860 p4757 p4993 : Prop) (h : (¬ p3860) ∨ p2027 ∨ (¬ p4993) ∨ (¬ p4757) ∨ (¬ p3093) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4757) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial11353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4757)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory2865 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8)
  exact rule11353 (meaning t m 2027) (meaning t m 2668) (meaning t m 3093) (meaning t m 3860) (meaning t m 4757) (meaning t m 4993) source

theorem rule11354 (p2027 p2685 p3877 p3931 p4548 p5564 : Prop) (h : (¬ p4548) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p5564) ∨ (¬ p3877) ∨ (¬ p3931)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3877) ∨ (¬ p3931) ∨ (¬ p4548) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2866 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 10) (m.theta 7 8)
  exact rule11354 (meaning t m 2027) (meaning t m 2685) (meaning t m 3877) (meaning t m 3931) (meaning t m 4548) (meaning t m 5564) source

theorem rule11355 (p2027 p2470 p2528 p3365 p3366 p3519 p3553 p3572 p4133 p4347 p4376 : Prop) (h : p2027 ∨ (¬ p3366) ∨ (¬ p3553) ∨ (¬ p2470) ∨ (¬ p3572) ∨ (¬ p3365) ∨ (¬ p4133) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p4347) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11355 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2867 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11355 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3553) (meaning t m 3572) (meaning t m 4133) (meaning t m 4347) (meaning t m 4376) source

theorem rule11358 (p2027 p2252 p2352 p2363 p2573 p2741 p2952 p3136 p3519 p4035 p4376 p5113 : Prop) (h : (¬ p5113) ∨ (¬ p2252) ∨ (¬ p2573) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p2741) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2741) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial11358 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory2870 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule11358 (meaning t m 2027) (meaning t m 2252) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2741) (meaning t m 2952) (meaning t m 3136) (meaning t m 3519) (meaning t m 4035) (meaning t m 4376) (meaning t m 5113) source

theorem rule11359 (p2027 p2962 p3556 p3654 p3744 p4555 : Prop) (h : (¬ p2962) ∨ (¬ p3654) ∨ (¬ p4555) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3744)) : (p2027) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2871 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule11359 (meaning t m 2027) (meaning t m 2962) (meaning t m 3556) (meaning t m 3654) (meaning t m 3744) (meaning t m 4555) source

theorem rule11360 (p2027 p2406 p2589 p2742 p2774 p3905 p4281 p4845 : Prop) (h : (¬ p2406) ∨ (¬ p3905) ∨ (¬ p2742) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4845) ∨ (¬ p2774) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2742) ∨ (¬ p2774) ∨ (¬ p3905) ∨ (¬ p4281) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory2872 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 6) (m.theta 4 5)
  exact rule11360 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2742) (meaning t m 2774) (meaning t m 3905) (meaning t m 4281) (meaning t m 4845) source

theorem rule11362 (p2027 p2383 p2737 p2779 p3923 p3953 p4842 : Prop) (h : (¬ p4842) ∨ (¬ p2779) ∨ (¬ p2383) ∨ (¬ p3953) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2737) ∨ (¬ p2779) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2874 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule11362 (meaning t m 2027) (meaning t m 2383) (meaning t m 2737) (meaning t m 2779) (meaning t m 3923) (meaning t m 3953) (meaning t m 4842) source

theorem rule11363 (p2027 p2928 p3055 p3471 p3658 p5214 : Prop) (h : p2027 ∨ (¬ p3471) ∨ (¬ p3658) ∨ (¬ p2928) ∨ (¬ p5214) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3658) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial11363 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2875 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule11363 (meaning t m 2027) (meaning t m 2928) (meaning t m 3055) (meaning t m 3471) (meaning t m 3658) (meaning t m 5214) source

theorem rule11364 (p2027 p2780 p3097 p3471 p4401 p4475 : Prop) (h : (¬ p4401) ∨ p2027 ∨ (¬ p4475) ∨ (¬ p3471) ∨ (¬ p2780) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3097) ∨ (¬ p3471) ∨ (¬ p4401) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial11364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory2876 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7)
  exact rule11364 (meaning t m 2027) (meaning t m 2780) (meaning t m 3097) (meaning t m 3471) (meaning t m 4401) (meaning t m 4475) source

theorem rule11365 (p2027 p2264 p2459 p3692 p4119 p4362 : Prop) (h : (¬ p2459) ∨ (¬ p4119) ∨ (¬ p3692) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p4362)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4362) := by
  classical
  tauto

theorem initial11365 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4362)) := by
  have source := ElevenTheory.theory2877 t (m.theta 3 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11365 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 3692) (meaning t m 4119) (meaning t m 4362) source

theorem rule11367 (p2027 p3684 p4019 p4186 p4286 p4354 p4646 : Prop) (h : (¬ p4354) ∨ (¬ p4019) ∨ (¬ p3684) ∨ (¬ p4186) ∨ p2027 ∨ (¬ p4286) ∨ (¬ p4646)) : (p2027) ∨ (¬ p3684) ∨ (¬ p4019) ∨ (¬ p4186) ∨ (¬ p4286) ∨ (¬ p4354) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial11367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4354)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2879 t (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 8 10)
  exact rule11367 (meaning t m 2027) (meaning t m 3684) (meaning t m 4019) (meaning t m 4186) (meaning t m 4286) (meaning t m 4354) (meaning t m 4646) source

theorem rule11368 (p2027 p2098 p2138 p2191 p4188 p4875 : Prop) (h : (¬ p2138) ∨ (¬ p4875) ∨ (¬ p2191) ∨ (¬ p4188) ∨ (¬ p2098) ∨ p2027) : (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2191) ∨ (¬ p4188) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial11368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory2880 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8)
  exact rule11368 (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 2191) (meaning t m 4188) (meaning t m 4875) source

theorem rule11370 (p2027 p2510 p2528 p3422 p3878 p4118 p4753 : Prop) (h : p2027 ∨ (¬ p4753) ∨ (¬ p4118) ∨ (¬ p3878) ∨ (¬ p3422) ∨ (¬ p2510) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p3422) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2882 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule11370 (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 3422) (meaning t m 3878) (meaning t m 4118) (meaning t m 4753) source

theorem rule11371 (p2027 p2122 p2230 p2313 p2440 p2778 p3083 p4358 p4419 p4596 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p4596) ∨ (¬ p4358) ∨ (¬ p2230) ∨ (¬ p4419) ∨ (¬ p2778) ∨ (¬ p2440) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2313) ∨ (¬ p2440) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p4358) ∨ (¬ p4419) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial11371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory2883 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule11371 (meaning t m 2027) (meaning t m 2122) (meaning t m 2230) (meaning t m 2313) (meaning t m 2440) (meaning t m 2778) (meaning t m 3083) (meaning t m 4358) (meaning t m 4419) (meaning t m 4596) source

theorem rule11372 (p2027 p2230 p2313 p2440 p2459 p2778 p3083 p3955 p4347 p4419 p4420 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p4420) ∨ (¬ p2230) ∨ (¬ p4419) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p2440) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2313) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4419) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial11372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory2884 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11372 (meaning t m 2027) (meaning t m 2230) (meaning t m 2313) (meaning t m 2440) (meaning t m 2459) (meaning t m 2778) (meaning t m 3083) (meaning t m 3955) (meaning t m 4347) (meaning t m 4419) (meaning t m 4420) source

theorem rule11373 (p2027 p2122 p2313 p2778 p3166 p3256 p3692 p3917 p3990 p4433 p4786 : Prop) (h : (¬ p2313) ∨ (¬ p3166) ∨ (¬ p4786) ∨ (¬ p2778) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3990) ∨ (¬ p2122) ∨ (¬ p4433) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2778) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3917) ∨ (¬ p3990) ∨ (¬ p4433) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial11373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory2885 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule11373 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2778) (meaning t m 3166) (meaning t m 3256) (meaning t m 3692) (meaning t m 3917) (meaning t m 3990) (meaning t m 4433) (meaning t m 4786) source

theorem rule11374 (p2027 p2307 p2534 p3055 p3323 p3366 p3568 p3874 p3950 p4623 p4866 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p4866) ∨ (¬ p3366) ∨ (¬ p4623) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p3323) ∨ (¬ p3055) ∨ (¬ p2534) ∨ (¬ p3874) ∨ (¬ p3568) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3568) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4623) ∨ (¬ p4866) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial11374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory2886 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule11374 (meaning t m 2027) (meaning t m 2307) (meaning t m 2534) (meaning t m 3055) (meaning t m 3323) (meaning t m 3366) (meaning t m 3568) (meaning t m 3874) (meaning t m 3950) (meaning t m 4623) (meaning t m 4866) (meaning t m 5016) source

theorem rule11377 (p2027 p2331 p2589 p2668 p3905 p3979 p4322 p4786 p4948 p5119 : Prop) (h : (¬ p2668) ∨ (¬ p2589) ∨ (¬ p3979) ∨ (¬ p4948) ∨ (¬ p3905) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p2331) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p3905) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4786) ∨ (¬ p4948) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2889 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11377 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 2668) (meaning t m 3905) (meaning t m 3979) (meaning t m 4322) (meaning t m 4786) (meaning t m 4948) (meaning t m 5119) source

theorem rule11379 (p2027 p2138 p2307 p3323 p3366 p3568 p3692 p3694 p3950 p4623 p4866 p5016 : Prop) (h : (¬ p2138) ∨ (¬ p4623) ∨ (¬ p3366) ∨ (¬ p4866) ∨ (¬ p2307) ∨ (¬ p3950) ∨ (¬ p5016) ∨ (¬ p3323) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3568) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) ∨ (¬ p4623) ∨ (¬ p4866) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial11379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory2891 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule11379 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 3323) (meaning t m 3366) (meaning t m 3568) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) (meaning t m 4623) (meaning t m 4866) (meaning t m 5016) source

theorem rule11380 (p2027 p3333 p3876 p3947 p4327 p5182 p5299 : Prop) (h : (¬ p5299) ∨ (¬ p5182) ∨ (¬ p3333) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p3876) ∨ (¬ p4327)) : (p2027) ∨ (¬ p3333) ∨ (¬ p3876) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p5182) ∨ (¬ p5299) := by
  classical
  tauto

theorem initial11380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 5182)) ∨ (¬ (meaning t m 5299)) := by
  have source := ElevenTheory.theory2892 t (m.theta 0 9) (m.theta 2 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule11380 (meaning t m 2027) (meaning t m 3333) (meaning t m 3876) (meaning t m 3947) (meaning t m 4327) (meaning t m 5182) (meaning t m 5299) source

theorem rule11381 (p2027 p2341 p2449 p3055 p3553 p3584 p4137 p4625 p5257 : Prop) (h : (¬ p5257) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4625) ∨ (¬ p2449) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2449) ∨ (¬ p3055) ∨ (¬ p3553) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5257) := by
  classical
  tauto

theorem initial11381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5257)) := by
  have source := ElevenTheory.theory2893 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule11381 (meaning t m 2027) (meaning t m 2341) (meaning t m 2449) (meaning t m 3055) (meaning t m 3553) (meaning t m 3584) (meaning t m 4137) (meaning t m 4625) (meaning t m 5257) source

theorem rule11382 (p2027 p2307 p2589 p2668 p2781 p2850 p3568 p3874 p3905 p4384 : Prop) (h : (¬ p2668) ∨ p2027 ∨ (¬ p3905) ∨ (¬ p2781) ∨ (¬ p3874) ∨ (¬ p2589) ∨ (¬ p3568) ∨ (¬ p2307) ∨ (¬ p4384) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p2781) ∨ (¬ p2850) ∨ (¬ p3568) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial11382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory2894 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule11382 (meaning t m 2027) (meaning t m 2307) (meaning t m 2589) (meaning t m 2668) (meaning t m 2781) (meaning t m 2850) (meaning t m 3568) (meaning t m 3874) (meaning t m 3905) (meaning t m 4384) source

theorem rule11383 (p2027 p3227 p3333 p3584 p4037 p4973 p5152 : Prop) (h : (¬ p3333) ∨ (¬ p5152) ∨ (¬ p3227) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p4973) ∨ (¬ p4037)) : (p2027) ∨ (¬ p3227) ∨ (¬ p3333) ∨ (¬ p3584) ∨ (¬ p4037) ∨ (¬ p4973) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial11383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4973)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory2895 t (m.theta 1 9) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule11383 (meaning t m 2027) (meaning t m 3227) (meaning t m 3333) (meaning t m 3584) (meaning t m 4037) (meaning t m 4973) (meaning t m 5152) source

theorem rule11384 (p2027 p2307 p2781 p3323 p3346 p3568 p3680 p3905 p4368 p4425 : Prop) (h : (¬ p3905) ∨ (¬ p3680) ∨ (¬ p3346) ∨ (¬ p2781) ∨ (¬ p4425) ∨ (¬ p3323) ∨ (¬ p2307) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p4368)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p3568) ∨ (¬ p3680) ∨ (¬ p3905) ∨ (¬ p4368) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial11384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory2896 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 3 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule11384 (meaning t m 2027) (meaning t m 2307) (meaning t m 2781) (meaning t m 3323) (meaning t m 3346) (meaning t m 3568) (meaning t m 3680) (meaning t m 3905) (meaning t m 4368) (meaning t m 4425) source

theorem rule11385 (p2027 p2156 p2166 p3952 p4120 p4960 : Prop) (h : (¬ p2156) ∨ (¬ p2166) ∨ (¬ p4960) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4120)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p3952) ∨ (¬ p4120) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial11385 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory2897 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule11385 (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 3952) (meaning t m 4120) (meaning t m 4960) source

theorem rule11387 (p2027 p2156 p2190 p2958 p3055 p3146 p3644 p3876 p4133 p4347 p4786 : Prop) (h : (¬ p3876) ∨ (¬ p4786) ∨ (¬ p3644) ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p4133)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2958) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial11387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory2899 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11387 (meaning t m 2027) (meaning t m 2156) (meaning t m 2190) (meaning t m 2958) (meaning t m 3055) (meaning t m 3146) (meaning t m 3644) (meaning t m 3876) (meaning t m 4133) (meaning t m 4347) (meaning t m 4786) source

theorem rule11388 (p2027 p3449 p3497 p3555 p4418 p4446 p5053 : Prop) (h : (¬ p3449) ∨ (¬ p4418) ∨ (¬ p3497) ∨ (¬ p5053) ∨ (¬ p3555) ∨ (¬ p4446) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (¬ p4418) ∨ (¬ p4446) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial11388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory2900 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule11388 (meaning t m 2027) (meaning t m 3449) (meaning t m 3497) (meaning t m 3555) (meaning t m 4418) (meaning t m 4446) (meaning t m 5053) source

theorem rule11389 (p2027 p2284 p2946 p3125 p3425 p3659 p4330 p4348 p4786 : Prop) (h : (¬ p3659) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p4786) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p4348) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial11389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory2901 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11389 (meaning t m 2027) (meaning t m 2284) (meaning t m 2946) (meaning t m 3125) (meaning t m 3425) (meaning t m 3659) (meaning t m 4330) (meaning t m 4348) (meaning t m 4786) source

theorem rule11390 (p2027 p2187 p2284 p2459 p2946 p3425 p3685 p4133 p4340 p4786 : Prop) (h : p2027 ∨ (¬ p4133) ∨ (¬ p4786) ∨ (¬ p3425) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p2459) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2459) ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p3685) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial11390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory2902 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11390 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2459) (meaning t m 2946) (meaning t m 3425) (meaning t m 3685) (meaning t m 4133) (meaning t m 4340) (meaning t m 4786) source

theorem rule11391 (p2027 p2187 p2284 p2946 p3201 p3540 p3874 p3905 p4384 p4786 : Prop) (h : (¬ p2284) ∨ (¬ p2187) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p4786) ∨ (¬ p4384) ∨ (¬ p3540) ∨ (¬ p2946) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4384) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial11391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory2903 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule11391 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2946) (meaning t m 3201) (meaning t m 3540) (meaning t m 3874) (meaning t m 3905) (meaning t m 4384) (meaning t m 4786) source

theorem rule11393 (p2027 p2481 p2819 p3016 p4170 p4256 p5225 : Prop) (h : (¬ p2481) ∨ (¬ p2819) ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p5225) ∨ (¬ p4170) ∨ p2027) : (p2027) ∨ (¬ p2481) ∨ (¬ p2819) ∨ (¬ p3016) ∨ (¬ p4170) ∨ (¬ p4256) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial11393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory2905 t (m.theta 0 8) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule11393 (meaning t m 2027) (meaning t m 2481) (meaning t m 2819) (meaning t m 3016) (meaning t m 4170) (meaning t m 4256) (meaning t m 5225) source

theorem rule11394 (p2027 p3073 p3177 p3570 p3857 p4189 p4378 p4914 : Prop) (h : p2027 ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p4914) ∨ (¬ p4378) ∨ (¬ p3570) ∨ (¬ p3073) ∨ (¬ p4189)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3177) ∨ (¬ p3570) ∨ (¬ p3857) ∨ (¬ p4189) ∨ (¬ p4378) ∨ (¬ p4914) := by
  classical
  tauto

theorem initial11394 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4914)) := by
  have source := ElevenTheory.theory2906 t (m.theta 0 8) (m.theta 1 7) (m.theta 1 8) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11394 (meaning t m 2027) (meaning t m 3073) (meaning t m 3177) (meaning t m 3570) (meaning t m 3857) (meaning t m 4189) (meaning t m 4378) (meaning t m 4914) source

theorem rule11395 (p2027 p2230 p2284 p3125 p3879 p3954 p4242 p4330 p4340 p5190 : Prop) (h : p2027 ∨ (¬ p3125) ∨ (¬ p4242) ∨ (¬ p4330) ∨ (¬ p5190) ∨ (¬ p3954) ∨ (¬ p4340) ∨ (¬ p2284) ∨ (¬ p2230) ∨ (¬ p3879)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p3879) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4330) ∨ (¬ p4340) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2907 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule11395 (meaning t m 2027) (meaning t m 2230) (meaning t m 2284) (meaning t m 3125) (meaning t m 3879) (meaning t m 3954) (meaning t m 4242) (meaning t m 4330) (meaning t m 4340) (meaning t m 5190) source

theorem rule11396 (p2027 p3426 p3434 p3742 p3821 p4279 p4375 p4753 : Prop) (h : (¬ p4279) ∨ (¬ p3426) ∨ (¬ p4753) ∨ (¬ p4375) ∨ (¬ p3434) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p3821)) : (p2027) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3742) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4375) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11396 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2908 t (m.theta 0 7) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule11396 (meaning t m 2027) (meaning t m 3426) (meaning t m 3434) (meaning t m 3742) (meaning t m 3821) (meaning t m 4279) (meaning t m 4375) (meaning t m 4753) source

theorem rule11397 (p2027 p2386 p2387 p2819 p3574 p4375 p4753 : Prop) (h : (¬ p4753) ∨ (¬ p4375) ∨ (¬ p2819) ∨ (¬ p3574) ∨ (¬ p2386) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11397 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2909 t (m.theta 0 6) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule11397 (meaning t m 2027) (meaning t m 2386) (meaning t m 2387) (meaning t m 2819) (meaning t m 3574) (meaning t m 4375) (meaning t m 4753) source

theorem rule11398 (p2027 p2459 p2573 p3083 p3574 p3860 p4261 p4420 p5190 : Prop) (h : (¬ p2573) ∨ (¬ p4261) ∨ (¬ p3574) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p4420) ∨ (¬ p3083) ∨ (¬ p2459) ∨ (¬ p5190)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4420) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2910 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11398 (meaning t m 2027) (meaning t m 2459) (meaning t m 2573) (meaning t m 3083) (meaning t m 3574) (meaning t m 3860) (meaning t m 4261) (meaning t m 4420) (meaning t m 5190) source

theorem rule11399 (p2027 p2284 p2946 p3425 p3737 p4324 p4381 p4786 p5250 : Prop) (h : (¬ p4381) ∨ (¬ p2284) ∨ (¬ p4786) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p5250) ∨ (¬ p3737) ∨ (¬ p4324)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p3737) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4786) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial11399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory2911 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule11399 (meaning t m 2027) (meaning t m 2284) (meaning t m 2946) (meaning t m 3425) (meaning t m 3737) (meaning t m 4324) (meaning t m 4381) (meaning t m 4786) (meaning t m 5250) source

theorem rule11400 (p2027 p2230 p2284 p3125 p3548 p3879 p4330 p4348 p4366 p5190 : Prop) (h : (¬ p4366) ∨ (¬ p4348) ∨ (¬ p4330) ∨ (¬ p5190) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3879) ∨ (¬ p2230) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p3125) ∨ (¬ p3548) ∨ (¬ p3879) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2912 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11400 (meaning t m 2027) (meaning t m 2230) (meaning t m 2284) (meaning t m 3125) (meaning t m 3548) (meaning t m 3879) (meaning t m 4330) (meaning t m 4348) (meaning t m 4366) (meaning t m 5190) source

theorem rule11402 (p2027 p2230 p2437 p2440 p3434 p3817 p3954 p4400 p5087 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p3954) ∨ (¬ p3817) ∨ (¬ p5087) ∨ (¬ p3434) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2437) ∨ (¬ p2230) ∨ (¬ p4400)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3434) ∨ (¬ p3817) ∨ (¬ p3954) ∨ (¬ p4400) ∨ (¬ p5087) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 5087)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2914 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule11402 (meaning t m 2027) (meaning t m 2230) (meaning t m 2437) (meaning t m 2440) (meaning t m 3434) (meaning t m 3817) (meaning t m 3954) (meaning t m 4400) (meaning t m 5087) (meaning t m 5190) source

theorem rule11403 (p2027 p2528 p2651 p2761 p2778 p3083 p3946 p4669 p4786 p5269 p5387 : Prop) (h : (¬ p3083) ∨ (¬ p2778) ∨ (¬ p2651) ∨ (¬ p4786) ∨ (¬ p2528) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p3946) ∨ (¬ p5387) ∨ (¬ p5269)) : (p2027) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2761) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3946) ∨ (¬ p4669) ∨ (¬ p4786) ∨ (¬ p5269) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial11403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5269)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory2915 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 9) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule11403 (meaning t m 2027) (meaning t m 2528) (meaning t m 2651) (meaning t m 2761) (meaning t m 2778) (meaning t m 3083) (meaning t m 3946) (meaning t m 4669) (meaning t m 4786) (meaning t m 5269) (meaning t m 5387) source

theorem rule11404 (p2027 p2230 p2299 p2313 p2440 p2778 p3343 p3366 p3519 p4332 p4348 p4376 : Prop) (h : (¬ p2299) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p3343) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2440) ∨ (¬ p3366) ∨ (¬ p2778) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2440) ∨ (¬ p2778) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2916 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11404 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2313) (meaning t m 2440) (meaning t m 2778) (meaning t m 3343) (meaning t m 3366) (meaning t m 3519) (meaning t m 4332) (meaning t m 4348) (meaning t m 4376) source

theorem rule11406 (p2027 p2386 p3483 p3574 p3946 p4375 p4753 : Prop) (h : (¬ p4753) ∨ (¬ p3946) ∨ (¬ p3483) ∨ (¬ p4375) ∨ p2027 ∨ (¬ p2386) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2386) ∨ (¬ p3483) ∨ (¬ p3574) ∨ (¬ p3946) ∨ (¬ p4375) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2918 t (m.theta 0 6) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9)
  exact rule11406 (meaning t m 2027) (meaning t m 2386) (meaning t m 3483) (meaning t m 3574) (meaning t m 3946) (meaning t m 4375) (meaning t m 4753) source

theorem rule11410 (p2027 p2313 p2743 p2785 p3309 p4845 p4869 : Prop) (h : (¬ p2785) ∨ (¬ p2313) ∨ (¬ p4869) ∨ (¬ p3309) ∨ (¬ p4845) ∨ (¬ p2743) ∨ p2027) : (p2027) ∨ (¬ p2313) ∨ (¬ p2743) ∨ (¬ p2785) ∨ (¬ p3309) ∨ (¬ p4845) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial11410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4845)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory2922 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule11410 (meaning t m 2027) (meaning t m 2313) (meaning t m 2743) (meaning t m 2785) (meaning t m 3309) (meaning t m 4845) (meaning t m 4869) source

theorem rule11411 (p2136 p3369 p3873 : Prop) (h : (¬ p2136) ∨ p3369 ∨ (¬ p3873)) : (¬ p2136) ∨ (p3369) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial11411 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2136)) ∨ (meaning t m 3369) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory2923 (m.theta 0 1) (m.theta 0 2) (m.theta 0 5)
  exact rule11411 (meaning t m 2136) (meaning t m 3369) (meaning t m 3873) source

theorem rule11412 (p2027 p2139 p2156 p2668 p3055 p3745 p3979 p4425 p5119 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p4425) ∨ (¬ p3979) ∨ (¬ p2156) ∨ (¬ p2668) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p3055) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3745) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial11412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2924 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11412 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2668) (meaning t m 3055) (meaning t m 3745) (meaning t m 3979) (meaning t m 4425) (meaning t m 5119) (meaning t m 5160) source

theorem rule11415 (p2027 p2745 p2951 p3051 p3136 p3368 p3486 : Prop) (h : p2027 ∨ (¬ p3051) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3368) ∨ (¬ p3136) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) ∨ (¬ p3368) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial11415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory2927 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7)
  exact rule11415 (meaning t m 2027) (meaning t m 2745) (meaning t m 2951) (meaning t m 3051) (meaning t m 3136) (meaning t m 3368) (meaning t m 3486) source

theorem rule11417 (p2027 p2630 p3343 p3879 p4315 p4953 : Prop) (h : (¬ p3343) ∨ (¬ p2630) ∨ (¬ p4315) ∨ (¬ p3879) ∨ (¬ p4953) ∨ p2027) : (p2027) ∨ (¬ p2630) ∨ (¬ p3343) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial11417 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory2929 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9)
  exact rule11417 (meaning t m 2027) (meaning t m 2630) (meaning t m 3343) (meaning t m 3879) (meaning t m 4315) (meaning t m 4953) source

theorem rule11418 (p2027 p2387 p2668 p2807 p3019 p3983 p4652 : Prop) (h : (¬ p3019) ∨ (¬ p2387) ∨ (¬ p4652) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p3983)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2807) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2930 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 6 8)
  exact rule11418 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 2807) (meaning t m 3019) (meaning t m 3983) (meaning t m 4652) source

theorem rule11420 (p2685 p3572 : Prop) (h : (¬ p3572) ∨ (¬ p2685)) : (¬ p2685) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial11420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory2932 (m.theta 2 3) (m.theta 3 7)
  exact rule11420 (meaning t m 2685) (meaning t m 3572) source

theorem rule11421 (p2027 p2230 p2373 p2685 p2741 p2996 p3146 p3519 p4035 p4376 p5113 : Prop) (h : (¬ p2685) ∨ (¬ p3519) ∨ (¬ p5113) ∨ (¬ p3146) ∨ (¬ p2373) ∨ (¬ p4376) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2741) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2685) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial11421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory2933 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule11421 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 2685) (meaning t m 2741) (meaning t m 2996) (meaning t m 3146) (meaning t m 3519) (meaning t m 4035) (meaning t m 4376) (meaning t m 5113) source

theorem rule11422 (p2027 p2230 p2373 p3425 p3969 p4324 p4381 p4419 p5119 : Prop) (h : (¬ p3425) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p5119) ∨ (¬ p2230) ∨ (¬ p4419) ∨ (¬ p2373) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4419) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2934 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11422 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3425) (meaning t m 3969) (meaning t m 4324) (meaning t m 4381) (meaning t m 4419) (meaning t m 5119) source

theorem rule11423 (p2027 p2230 p2563 p2685 p3125 p3414 p4035 p4236 p4419 p5279 : Prop) (h : (¬ p4236) ∨ (¬ p2685) ∨ (¬ p3414) ∨ p2027 ∨ (¬ p5279) ∨ (¬ p4035) ∨ (¬ p2230) ∨ (¬ p4419) ∨ (¬ p2563) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2685) ∨ (¬ p3125) ∨ (¬ p3414) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p5279) := by
  classical
  tauto

theorem initial11423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5279)) := by
  have source := ElevenTheory.theory2935 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule11423 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 2685) (meaning t m 3125) (meaning t m 3414) (meaning t m 4035) (meaning t m 4236) (meaning t m 4419) (meaning t m 5279) source

theorem rule11424 (p2027 p2307 p3549 p3555 p3953 p4377 p5020 : Prop) (h : (¬ p3953) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p3549) ∨ (¬ p5020) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3555) ∨ (¬ p3953) ∨ (¬ p4377) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial11424 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory2936 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 6 7)
  exact rule11424 (meaning t m 2027) (meaning t m 2307) (meaning t m 3549) (meaning t m 3555) (meaning t m 3953) (meaning t m 4377) (meaning t m 5020) source

theorem rule11425 (p2027 p3073 p3365 p3366 p3449 p3555 p4037 p4195 p4377 p4604 : Prop) (h : (¬ p3449) ∨ (¬ p3073) ∨ (¬ p3555) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p4604)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial11425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory2937 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9)
  exact rule11425 (meaning t m 2027) (meaning t m 3073) (meaning t m 3365) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 4037) (meaning t m 4195) (meaning t m 4377) (meaning t m 4604) source

theorem rule11426 (p2027 p2252 p2741 p3073 p3292 p3449 p3452 p3461 p4376 p4604 p5284 : Prop) (h : (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p3461) ∨ (¬ p3452) ∨ (¬ p2252) ∨ (¬ p5284) ∨ (¬ p4376) ∨ (¬ p2741)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p3073) ∨ (¬ p3292) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p3461) ∨ (¬ p4376) ∨ (¬ p4604) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2938 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 8) (m.theta 3 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule11426 (meaning t m 2027) (meaning t m 2252) (meaning t m 2741) (meaning t m 3073) (meaning t m 3292) (meaning t m 3449) (meaning t m 3452) (meaning t m 3461) (meaning t m 4376) (meaning t m 4604) (meaning t m 5284) source

theorem rule11427 (p2027 p2253 p2741 p2807 p2996 p3452 p4376 : Prop) (h : p2027 ∨ (¬ p2253) ∨ (¬ p2807) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p3452) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p2807) ∨ (¬ p2996) ∨ (¬ p3452) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2939 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 7)
  exact rule11427 (meaning t m 2027) (meaning t m 2253) (meaning t m 2741) (meaning t m 2807) (meaning t m 2996) (meaning t m 3452) (meaning t m 4376) source

theorem rule11432 (p2027 p3055 p3366 p3449 p3555 p4181 p4377 p4425 p5119 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p3555) ∨ (¬ p3449) ∨ (¬ p3055) ∨ (¬ p4181) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p4425)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4181) ∨ (¬ p4377) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial11432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2944 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11432 (meaning t m 2027) (meaning t m 3055) (meaning t m 3366) (meaning t m 3449) (meaning t m 3555) (meaning t m 4181) (meaning t m 4377) (meaning t m 4425) (meaning t m 5119) (meaning t m 5160) source

theorem rule11434 (p2027 p2139 p2220 p3055 p3146 p3266 p3584 p5254 p5514 : Prop) (h : (¬ p3146) ∨ (¬ p2139) ∨ (¬ p5254) ∨ (¬ p3055) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p5514) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3584) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial11434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory2946 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule11434 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 3055) (meaning t m 3146) (meaning t m 3266) (meaning t m 3584) (meaning t m 5254) (meaning t m 5514) source

theorem rule11436 (p2027 p2928 p3389 p3555 p4079 p4257 p4377 : Prop) (h : p2027 ∨ (¬ p4079) ∨ (¬ p3389) ∨ (¬ p3555) ∨ (¬ p4377) ∨ (¬ p2928) ∨ (¬ p4257)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3555) ∨ (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial11436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory2948 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7)
  exact rule11436 (meaning t m 2027) (meaning t m 2928) (meaning t m 3389) (meaning t m 3555) (meaning t m 4079) (meaning t m 4257) (meaning t m 4377) source

theorem rule11437 (p2027 p2139 p2657 p2761 p3051 p3246 p4236 p4256 p4286 p5123 : Prop) (h : (¬ p2657) ∨ (¬ p2761) ∨ (¬ p4286) ∨ (¬ p3051) ∨ (¬ p4236) ∨ (¬ p5123) ∨ (¬ p2139) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p3246)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial11437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory2949 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11437 (meaning t m 2027) (meaning t m 2139) (meaning t m 2657) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 4236) (meaning t m 4256) (meaning t m 4286) (meaning t m 5123) source

theorem rule11438 (p2027 p2156 p2657 p3125 p3366 p3370 p3461 p4236 p4256 p4286 p4377 p5123 : Prop) (h : (¬ p4236) ∨ (¬ p2657) ∨ (¬ p2156) ∨ (¬ p3461) ∨ (¬ p4256) ∨ (¬ p5123) ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p4286) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2657) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3461) ∨ (¬ p4236) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4377) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial11438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory2950 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11438 (meaning t m 2027) (meaning t m 2156) (meaning t m 2657) (meaning t m 3125) (meaning t m 3366) (meaning t m 3370) (meaning t m 3461) (meaning t m 4236) (meaning t m 4256) (meaning t m 4286) (meaning t m 4377) (meaning t m 5123) source

theorem rule11439 (p2027 p2156 p2252 p2274 p2396 p2630 p2657 p2741 p3370 p4035 p4377 p4641 p5171 : Prop) (h : (¬ p2274) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p2156) ∨ (¬ p2396) ∨ (¬ p3370) ∨ (¬ p2630) ∨ (¬ p5171) ∨ (¬ p2657) ∨ (¬ p4641) ∨ (¬ p2252) ∨ (¬ p2741) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2741) ∨ (¬ p3370) ∨ (¬ p4035) ∨ (¬ p4377) ∨ (¬ p4641) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial11439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory2951 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule11439 (meaning t m 2027) (meaning t m 2156) (meaning t m 2252) (meaning t m 2274) (meaning t m 2396) (meaning t m 2630) (meaning t m 2657) (meaning t m 2741) (meaning t m 3370) (meaning t m 4035) (meaning t m 4377) (meaning t m 4641) (meaning t m 5171) source

theorem rule11440 (p2027 p2470 p2630 p2656 p3879 p4315 p4610 : Prop) (h : (¬ p2470) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p4610) ∨ (¬ p2630) ∨ (¬ p4315) ∨ (¬ p3879)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial11440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory2952 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8)
  exact rule11440 (meaning t m 2027) (meaning t m 2470) (meaning t m 2630) (meaning t m 2656) (meaning t m 3879) (meaning t m 4315) (meaning t m 4610) source

theorem rule11441 (p2027 p3449 p3591 p3989 p4318 p4518 : Prop) (h : (¬ p3591) ∨ (¬ p4318) ∨ (¬ p3449) ∨ (¬ p4518) ∨ (¬ p3989) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3989) ∨ (¬ p4318) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial11441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory2953 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 5 6) (m.theta 6 8)
  exact rule11441 (meaning t m 2027) (meaning t m 3449) (meaning t m 3591) (meaning t m 3989) (meaning t m 4318) (meaning t m 4518) source

theorem rule11459 (p2027 p2139 p2156 p2187 p3365 p3979 p4035 p5119 p5284 : Prop) (h : (¬ p5119) ∨ (¬ p2187) ∨ (¬ p3979) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p2139) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p3365) ∨ (¬ p3979) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2955 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11459 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2187) (meaning t m 3365) (meaning t m 3979) (meaning t m 4035) (meaning t m 5119) (meaning t m 5284) source

theorem rule11460 (p2027 p2156 p2187 p3055 p3366 p3370 p3979 p4377 p4425 p5119 p5160 : Prop) (h : (¬ p5119) ∨ (¬ p2187) ∨ (¬ p3979) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p5160) ∨ (¬ p2156) ∨ (¬ p4425) ∨ (¬ p3055) ∨ (¬ p3370) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3979) ∨ (¬ p4377) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial11460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2956 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11460 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 3055) (meaning t m 3366) (meaning t m 3370) (meaning t m 3979) (meaning t m 4377) (meaning t m 4425) (meaning t m 5119) (meaning t m 5160) source

theorem rule11462 (p2027 p2139 p2156 p2274 p2396 p2657 p3276 p4236 p4641 p5170 p5284 : Prop) (h : (¬ p4236) ∨ (¬ p5170) ∨ (¬ p5284) ∨ (¬ p2274) ∨ (¬ p2657) ∨ (¬ p2156) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p2139) ∨ (¬ p3276) ∨ (¬ p4641)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2657) ∨ (¬ p3276) ∨ (¬ p4236) ∨ (¬ p4641) ∨ (¬ p5170) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5170)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2958 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule11462 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2657) (meaning t m 3276) (meaning t m 4236) (meaning t m 4641) (meaning t m 5170) (meaning t m 5284) source

theorem rule11464 (p2027 p2307 p2459 p2630 p2657 p2781 p2881 p4035 p4236 p4275 p5113 : Prop) (h : (¬ p2307) ∨ (¬ p2781) ∨ (¬ p2459) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p5113) ∨ (¬ p2881) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p2657) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2781) ∨ (¬ p2881) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4275) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial11464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory2960 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11464 (meaning t m 2027) (meaning t m 2307) (meaning t m 2459) (meaning t m 2630) (meaning t m 2657) (meaning t m 2781) (meaning t m 2881) (meaning t m 4035) (meaning t m 4236) (meaning t m 4275) (meaning t m 5113) source

theorem rule11465 (p2027 p2139 p2156 p2274 p2396 p2534 p2657 p3950 p4236 p4256 : Prop) (h : (¬ p2156) ∨ (¬ p2139) ∨ (¬ p3950) ∨ (¬ p4256) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial11465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory2961 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11465 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 2534) (meaning t m 2657) (meaning t m 3950) (meaning t m 4236) (meaning t m 4256) source

theorem rule11466 (p2027 p2187 p2307 p2781 p2810 p3097 p3365 p4256 p4384 : Prop) (h : p2027 ∨ (¬ p2781) ∨ (¬ p4256) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p2187) ∨ (¬ p4384)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p4256) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial11466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory2962 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule11466 (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2781) (meaning t m 2810) (meaning t m 3097) (meaning t m 3365) (meaning t m 4256) (meaning t m 4384) source

theorem rule11467 (p2027 p2528 p3919 p3931 p4340 p4383 p4967 p5564 : Prop) (h : (¬ p3931) ∨ (¬ p4383) ∨ (¬ p3919) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p5564) ∨ (¬ p4967) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3919) ∨ (¬ p3931) ∨ (¬ p4340) ∨ (¬ p4383) ∨ (¬ p4967) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4967)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2963 t (m.theta 2 8) (m.theta 3 7) (m.theta 3 8) (m.theta 4 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule11467 (meaning t m 2027) (meaning t m 2528) (meaning t m 3919) (meaning t m 3931) (meaning t m 4340) (meaning t m 4383) (meaning t m 4967) (meaning t m 5564) source

theorem rule11470 (p2027 p2440 p3580 p3931 p4646 p5503 : Prop) (h : (¬ p3931) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3580) ∨ (¬ p5503)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3580) ∨ (¬ p3931) ∨ (¬ p4646) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial11470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory2966 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 10)
  exact rule11470 (meaning t m 2027) (meaning t m 2440) (meaning t m 3580) (meaning t m 3931) (meaning t m 4646) (meaning t m 5503) source

theorem rule11472 (p2027 p2459 p2810 p2881 p3051 p3359 p3365 p3366 p3370 p4377 p4697 : Prop) (h : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p3366) ∨ (¬ p3365) ∨ (¬ p4697) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2810) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3359) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4697) := by
  classical
  tauto

theorem initial11472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4697)) := by
  have source := ElevenTheory.theory2968 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11472 (meaning t m 2027) (meaning t m 2459) (meaning t m 2810) (meaning t m 2881) (meaning t m 3051) (meaning t m 3359) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 4377) (meaning t m 4697) source

theorem rule11473 (p2027 p2139 p2881 p3051 p3055 p3941 p4425 p5119 p5160 : Prop) (h : (¬ p5119) ∨ p2027 ∨ (¬ p3941) ∨ (¬ p3055) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p5160) ∨ (¬ p2139) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial11473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2969 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11473 (meaning t m 2027) (meaning t m 2139) (meaning t m 2881) (meaning t m 3051) (meaning t m 3055) (meaning t m 3941) (meaning t m 4425) (meaning t m 5119) (meaning t m 5160) source

theorem rule11474 (p3370 p4031 p4210 : Prop) (h : p4210 ∨ (¬ p3370) ∨ (¬ p4031)) : (¬ p3370) ∨ (¬ p4031) ∨ (p4210) := by
  classical
  tauto

theorem initial11474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4031)) ∨ (meaning t m 4210) := by
  have source := ElevenTheory.theory2970 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5)
  exact rule11474 (meaning t m 3370) (meaning t m 4031) (meaning t m 4210) source

theorem rule11476 (p2027 p3572 p3690 p3755 p4362 p4660 : Prop) (h : (¬ p3690) ∨ p2027 ∨ (¬ p4362) ∨ (¬ p3755) ∨ (¬ p3572) ∨ (¬ p4660)) : (p2027) ∨ (¬ p3572) ∨ (¬ p3690) ∨ (¬ p3755) ∨ (¬ p4362) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial11476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory2972 t (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 5 7) (m.theta 7 9)
  exact rule11476 (meaning t m 2027) (meaning t m 3572) (meaning t m 3690) (meaning t m 3755) (meaning t m 4362) (meaning t m 4660) source

theorem rule11477 (p2027 p2341 p2797 p2963 p3246 p3366 p3519 p3569 p3644 p4035 p4236 p4376 p4399 p4663 p4988 : Prop) (h : (¬ p3246) ∨ (¬ p4663) ∨ (¬ p3519) ∨ (¬ p4035) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3569) ∨ (¬ p3366) ∨ (¬ p4988) ∨ (¬ p4399) ∨ (¬ p3644) ∨ (¬ p2341) ∨ (¬ p4236) ∨ (¬ p2797) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p3644) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4663) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial11477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4663)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory2973 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11477 (meaning t m 2027) (meaning t m 2341) (meaning t m 2797) (meaning t m 2963) (meaning t m 3246) (meaning t m 3366) (meaning t m 3519) (meaning t m 3569) (meaning t m 3644) (meaning t m 4035) (meaning t m 4236) (meaning t m 4376) (meaning t m 4399) (meaning t m 4663) (meaning t m 4988) source

theorem rule11478 (p2027 p2341 p3246 p3570 p3688 p3917 p3954 p4521 p4625 p4988 : Prop) (h : (¬ p4625) ∨ (¬ p3954) ∨ (¬ p4988) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4521) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3917) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4625) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial11478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory2974 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule11478 (meaning t m 2027) (meaning t m 2341) (meaning t m 3246) (meaning t m 3570) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4521) (meaning t m 4625) (meaning t m 4988) source

theorem rule11479 (p2027 p3422 p3874 p3888 p4432 p5586 : Prop) (h : (¬ p5586) ∨ (¬ p3874) ∨ (¬ p3888) ∨ (¬ p3422) ∨ (¬ p4432) ∨ p2027) : (p2027) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3888) ∨ (¬ p4432) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial11479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory2975 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 10) (m.theta 6 8)
  exact rule11479 (meaning t m 2027) (meaning t m 3422) (meaning t m 3874) (meaning t m 3888) (meaning t m 4432) (meaning t m 5586) source

theorem rule11480 (p2027 p2230 p2373 p3146 p3365 p4037 p4195 p4419 p4604 : Prop) (h : (¬ p4195) ∨ (¬ p4037) ∨ (¬ p4604) ∨ (¬ p4419) ∨ (¬ p3365) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4419) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial11480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory2976 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule11480 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3365) (meaning t m 4037) (meaning t m 4195) (meaning t m 4419) (meaning t m 4604) source

theorem rule11481 (p2027 p3690 p3830 p4366 p4914 p5362 : Prop) (h : (¬ p4366) ∨ (¬ p5362) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p4914) ∨ (¬ p3690)) : (p2027) ∨ (¬ p3690) ∨ (¬ p3830) ∨ (¬ p4366) ∨ (¬ p4914) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial11481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4914)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory2977 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 5 7) (m.theta 7 9)
  exact rule11481 (meaning t m 2027) (meaning t m 3690) (meaning t m 3830) (meaning t m 4366) (meaning t m 4914) (meaning t m 5362) source

theorem rule11482 (p2027 p2264 p2995 p3486 p3551 p4283 p4957 : Prop) (h : (¬ p4283) ∨ (¬ p4957) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2995) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3486) ∨ (¬ p3551) ∨ (¬ p4283) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial11482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory2978 t (m.theta 0 7) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule11482 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3486) (meaning t m 3551) (meaning t m 4283) (meaning t m 4957) source

theorem rule11483 (p2027 p2191 p2264 p2891 p4132 p4362 : Prop) (h : (¬ p4362) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p2264)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2264) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p4362) := by
  classical
  tauto

theorem initial11483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4362)) := by
  have source := ElevenTheory.theory2979 t (m.theta 1 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule11483 (meaning t m 2027) (meaning t m 2191) (meaning t m 2264) (meaning t m 2891) (meaning t m 4132) (meaning t m 4362) source

theorem rule11485 (p2027 p2318 p3097 p3609 p3857 p3961 p4401 p4861 : Prop) (h : (¬ p3961) ∨ (¬ p4401) ∨ (¬ p4861) ∨ (¬ p3609) ∨ (¬ p2318) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2318) ∨ (¬ p3097) ∨ (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4401) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial11485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory2981 t (m.theta 0 7) (m.theta 0 8) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 6 7) (m.theta 8 9)
  exact rule11485 (meaning t m 2027) (meaning t m 2318) (meaning t m 3097) (meaning t m 3609) (meaning t m 3857) (meaning t m 3961) (meaning t m 4401) (meaning t m 4861) source

theorem rule11486 (p2027 p2901 p3952 p4140 p4393 p5472 : Prop) (h : (¬ p2901) ∨ (¬ p4393) ∨ (¬ p5472) ∨ (¬ p3952) ∨ (¬ p4140) ∨ p2027) : (p2027) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4393) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial11486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory2982 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10) (m.theta 6 7)
  exact rule11486 (meaning t m 2027) (meaning t m 2901) (meaning t m 3952) (meaning t m 4140) (meaning t m 4393) (meaning t m 5472) source

theorem rule11488 (p2027 p2534 p3609 p4256 p4375 p4753 p4861 : Prop) (h : (¬ p4753) ∨ (¬ p4256) ∨ (¬ p4375) ∨ (¬ p3609) ∨ (¬ p2534) ∨ (¬ p4861) ∨ p2027) : (p2027) ∨ (¬ p2534) ∨ (¬ p3609) ∨ (¬ p4256) ∨ (¬ p4375) ∨ (¬ p4753) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial11488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4753)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory2984 t (m.theta 2 4) (m.theta 2 6) (m.theta 2 8) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule11488 (meaning t m 2027) (meaning t m 2534) (meaning t m 3609) (meaning t m 4256) (meaning t m 4375) (meaning t m 4753) (meaning t m 4861) source

theorem rule11489 (p2027 p2417 p2850 p3741 p3947 p4112 p4753 : Prop) (h : (¬ p2850) ∨ (¬ p2417) ∨ (¬ p3741) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p4112) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2850) ∨ (¬ p3741) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2985 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule11489 (meaning t m 2027) (meaning t m 2417) (meaning t m 2850) (meaning t m 3741) (meaning t m 3947) (meaning t m 4112) (meaning t m 4753) source

theorem rule11495 (p2027 p2589 p2619 p3347 p3582 p3880 p5214 : Prop) (h : (¬ p3582) ∨ (¬ p3347) ∨ (¬ p3880) ∨ (¬ p2619) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p5214)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2619) ∨ (¬ p3347) ∨ (¬ p3582) ∨ (¬ p3880) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial11495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2991 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 8)
  exact rule11495 (meaning t m 2027) (meaning t m 2589) (meaning t m 2619) (meaning t m 3347) (meaning t m 3582) (meaning t m 3880) (meaning t m 5214) source

theorem rule11496 (p2027 p2220 p2928 p3146 p3452 p3644 p4133 p4347 p4521 : Prop) (h : (¬ p3644) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2220) ∨ (¬ p4133) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2928) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial11496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory2992 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11496 (meaning t m 2027) (meaning t m 2220) (meaning t m 2928) (meaning t m 3146) (meaning t m 3452) (meaning t m 3644) (meaning t m 4133) (meaning t m 4347) (meaning t m 4521) source

theorem rule11497 (p2027 p2373 p2850 p3497 p4700 p4753 : Prop) (h : (¬ p4700) ∨ (¬ p2373) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2993 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule11497 (meaning t m 2027) (meaning t m 2373) (meaning t m 2850) (meaning t m 3497) (meaning t m 4700) (meaning t m 4753) source

theorem rule11498 (p2027 p2850 p3051 p4109 p4320 p4700 p4753 : Prop) (h : (¬ p4700) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p4320) ∨ (¬ p4109) ∨ (¬ p3051) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2994 t (m.theta 0 5) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule11498 (meaning t m 2027) (meaning t m 2850) (meaning t m 3051) (meaning t m 4109) (meaning t m 4320) (meaning t m 4700) (meaning t m 4753) source

theorem rule11499 (p2027 p2122 p3791 p4138 p4358 p5564 : Prop) (h : (¬ p3791) ∨ (¬ p4138) ∨ (¬ p2122) ∨ (¬ p5564) ∨ p2027 ∨ (¬ p4358)) : (p2027) ∨ (¬ p2122) ∨ (¬ p3791) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2995 t (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule11499 (meaning t m 2027) (meaning t m 2122) (meaning t m 3791) (meaning t m 4138) (meaning t m 4358) (meaning t m 5564) source

theorem rule11500 (p2027 p3227 p3333 p3379 p3834 p5214 : Prop) (h : (¬ p3834) ∨ (¬ p5214) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3227) ∨ (¬ p3333)) : (p2027) ∨ (¬ p3227) ∨ (¬ p3333) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial11500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2996 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 2 4) (m.theta 4 9)
  exact rule11500 (meaning t m 2027) (meaning t m 3227) (meaning t m 3333) (meaning t m 3379) (meaning t m 3834) (meaning t m 5214) source

theorem rule11503 (p2027 p2247 p2470 p2528 p2996 p3553 p4133 p4347 p5190 : Prop) (h : (¬ p5190) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p2470) ∨ (¬ p4347) ∨ (¬ p4133) ∨ (¬ p3553) ∨ (¬ p2996) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2999 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11503 (meaning t m 2027) (meaning t m 2247) (meaning t m 2470) (meaning t m 2528) (meaning t m 2996) (meaning t m 3553) (meaning t m 4133) (meaning t m 4347) (meaning t m 5190) source

theorem rule11504 (p2027 p3051 p4120 p4129 p4132 p5564 : Prop) (h : (¬ p4120) ∨ (¬ p4132) ∨ (¬ p3051) ∨ (¬ p5564) ∨ p2027 ∨ (¬ p4129)) : (p2027) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4129) ∨ (¬ p4132) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory3000 t (m.theta 0 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10) (m.theta 7 8)
  exact rule11504 (meaning t m 2027) (meaning t m 3051) (meaning t m 4120) (meaning t m 4129) (meaning t m 4132) (meaning t m 5564) source

theorem rule11506 (p2027 p2341 p2417 p2608 p3519 p3591 p3644 p4026 p4376 p4625 p5201 : Prop) (h : (¬ p2608) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p2417) ∨ (¬ p3519) ∨ (¬ p5201) ∨ (¬ p4625) ∨ (¬ p3644) ∨ (¬ p2341) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p3644) ∨ (¬ p4026) ∨ (¬ p4376) ∨ (¬ p4625) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial11506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory3002 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule11506 (meaning t m 2027) (meaning t m 2341) (meaning t m 2417) (meaning t m 2608) (meaning t m 3519) (meaning t m 3591) (meaning t m 3644) (meaning t m 4026) (meaning t m 4376) (meaning t m 4625) (meaning t m 5201) source

theorem rule11507 (p2027 p3093 p3486 p3555 p4516 p4555 : Prop) (h : (¬ p4516) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3093) ∨ (¬ p4555) ∨ p2027) : (p2027) ∨ (¬ p3093) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4516) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory3003 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 7)
  exact rule11507 (meaning t m 2027) (meaning t m 3093) (meaning t m 3486) (meaning t m 3555) (meaning t m 4516) (meaning t m 4555) source

theorem rule11510 (p2027 p2482 p3860 p3998 p5190 p5693 : Prop) (h : (¬ p5190) ∨ (¬ p3860) ∨ (¬ p3998) ∨ p2027 ∨ (¬ p2482) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2482) ∨ (¬ p3860) ∨ (¬ p3998) ∨ (¬ p5190) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial11510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory3006 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 8) (m.theta 1 8) (m.theta 8 10)
  exact rule11510 (meaning t m 2027) (meaning t m 2482) (meaning t m 3860) (meaning t m 3998) (meaning t m 5190) (meaning t m 5693) source

theorem rule11512 (p2027 p2608 p2911 p3389 p3519 p3834 p3941 p4321 p4376 p5119 : Prop) (h : (¬ p2608) ∨ (¬ p3834) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4321)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3834) ∨ (¬ p3941) ∨ (¬ p4321) ∨ (¬ p4376) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory3008 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11512 (meaning t m 2027) (meaning t m 2608) (meaning t m 2911) (meaning t m 3389) (meaning t m 3519) (meaning t m 3834) (meaning t m 3941) (meaning t m 4321) (meaning t m 4376) (meaning t m 5119) source

theorem rule11513 (p2027 p2459 p2911 p3365 p3366 p3389 p3519 p4037 p4195 p4376 p4604 : Prop) (h : (¬ p4195) ∨ (¬ p4604) ∨ (¬ p3519) ∨ (¬ p3366) ∨ (¬ p4376) ∨ (¬ p2459) ∨ (¬ p3389) ∨ (¬ p2911) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p3365)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4376) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial11513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory3009 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11513 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3365) (meaning t m 3366) (meaning t m 3389) (meaning t m 3519) (meaning t m 4037) (meaning t m 4195) (meaning t m 4376) (meaning t m 4604) source

theorem rule11514 (p2027 p2138 p2459 p2911 p3366 p3389 p3519 p3744 p3758 p4376 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p3758) ∨ (¬ p3744) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4376) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial11514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory3010 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11514 (meaning t m 2027) (meaning t m 2138) (meaning t m 2459) (meaning t m 2911) (meaning t m 3366) (meaning t m 3389) (meaning t m 3519) (meaning t m 3744) (meaning t m 3758) (meaning t m 4376) (meaning t m 4604) source

theorem rule11515 (p2027 p2138 p2307 p2781 p2911 p3921 p3941 p4322 p4385 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p2307) ∨ (¬ p3921) ∨ (¬ p2911) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3941) ∨ (¬ p4322) ∨ (¬ p2781) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p2911) ∨ (¬ p3921) ∨ (¬ p3941) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory3011 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 5) (m.theta 4 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11515 (meaning t m 2027) (meaning t m 2138) (meaning t m 2307) (meaning t m 2781) (meaning t m 2911) (meaning t m 3921) (meaning t m 3941) (meaning t m 4322) (meaning t m 4385) (meaning t m 5119) source

theorem rule11516 (p2027 p2299 p2911 p2922 p3365 p3366 p4315 p4320 p4376 p4559 : Prop) (h : (¬ p3366) ∨ (¬ p2922) ∨ (¬ p4559) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4376) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial11516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory3012 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule11516 (meaning t m 2027) (meaning t m 2299) (meaning t m 2911) (meaning t m 2922) (meaning t m 3365) (meaning t m 3366) (meaning t m 4315) (meaning t m 4320) (meaning t m 4376) (meaning t m 4559) source

theorem rule11518 (p2027 p2459 p2573 p3083 p3519 p3556 p3574 p3645 p3692 p4119 p4376 p4420 p4874 : Prop) (h : (¬ p3083) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4376) ∨ (¬ p4420) ∨ (¬ p4119) ∨ (¬ p3556) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p4874) ∨ (¬ p3645) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2573) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4376) ∨ (¬ p4420) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial11518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory3014 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11518 (meaning t m 2027) (meaning t m 2459) (meaning t m 2573) (meaning t m 3083) (meaning t m 3519) (meaning t m 3556) (meaning t m 3574) (meaning t m 3645) (meaning t m 3692) (meaning t m 4119) (meaning t m 4376) (meaning t m 4420) (meaning t m 4874) source

theorem rule11519 (p3343 p3359 : Prop) (h : (¬ p3359) ∨ (¬ p3343)) : (¬ p3343) ∨ (¬ p3359) := by
  classical
  tauto

theorem initial11519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3359)) := by
  have source := ElevenTheory.theory3015 (m.theta 3 4) (m.theta 4 9)
  exact rule11519 (meaning t m 3343) (meaning t m 3359) source

theorem rule11520 (p2027 p2313 p2386 p3083 p3574 p4157 p4405 : Prop) (h : (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4157) ∨ (¬ p2386) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4157) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial11520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory3016 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule11520 (meaning t m 2027) (meaning t m 2313) (meaning t m 2386) (meaning t m 3083) (meaning t m 3574) (meaning t m 4157) (meaning t m 4405) source

theorem rule11524 (p2027 p2331 p3323 p3425 p3461 p3659 p4786 p5123 p5558 : Prop) (h : (¬ p5123) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3461) ∨ (¬ p3659) ∨ (¬ p5558) ∨ (¬ p4786) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p3659) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial11524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory3020 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11524 (meaning t m 2027) (meaning t m 2331) (meaning t m 3323) (meaning t m 3425) (meaning t m 3461) (meaning t m 3659) (meaning t m 4786) (meaning t m 5123) (meaning t m 5558) source

theorem rule11525 (p2027 p2619 p3551 p4042 p4244 p4986 : Prop) (h : p2027 ∨ (¬ p4986) ∨ (¬ p3551) ∨ (¬ p4244) ∨ (¬ p4042) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3551) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4986) := by
  classical
  tauto

theorem initial11525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4986)) := by
  have source := ElevenTheory.theory3021 t (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule11525 (meaning t m 2027) (meaning t m 2619) (meaning t m 3551) (meaning t m 4042) (meaning t m 4244) (meaning t m 4986) source

theorem rule11526 (p2027 p2510 p2531 p3422 p3497 p3684 p4702 : Prop) (h : (¬ p3497) ∨ p2027 ∨ (¬ p4702) ∨ (¬ p2531) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p2510)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2531) ∨ (¬ p3422) ∨ (¬ p3497) ∨ (¬ p3684) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial11526 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory3022 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 8)
  exact rule11526 (meaning t m 2027) (meaning t m 2510) (meaning t m 2531) (meaning t m 3422) (meaning t m 3497) (meaning t m 3684) (meaning t m 4702) source

theorem rule11527 (p2027 p2578 p2667 p2727 p3422 p4154 p4753 : Prop) (h : p2027 ∨ (¬ p4154) ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p3422) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p3422) ∨ (¬ p4154) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory3023 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule11527 (meaning t m 2027) (meaning t m 2578) (meaning t m 2667) (meaning t m 2727) (meaning t m 3422) (meaning t m 4154) (meaning t m 4753) source

theorem rule11528 (p2027 p2307 p2745 p2797 p3549 p3567 p4245 : Prop) (h : (¬ p3567) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p4245) ∨ (¬ p2307) ∨ (¬ p2745) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial11528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory3024 t (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule11528 (meaning t m 2027) (meaning t m 2307) (meaning t m 2745) (meaning t m 2797) (meaning t m 3549) (meaning t m 3567) (meaning t m 4245) source

theorem rule11530 (p2027 p2542 p2659 p2870 p3556 p3698 p3904 : Prop) (h : (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3698) ∨ p2027 ∨ (¬ p2659) ∨ (¬ p2542) ∨ (¬ p3904)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3698) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial11530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory3026 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule11530 (meaning t m 2027) (meaning t m 2542) (meaning t m 2659) (meaning t m 2870) (meaning t m 3556) (meaning t m 3698) (meaning t m 3904) source

theorem rule11531 (p2027 p2177 p2307 p2459 p3055 p3366 p3684 p4866 p4948 p5016 p5059 : Prop) (h : (¬ p4866) ∨ (¬ p2459) ∨ (¬ p2177) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p5016) ∨ (¬ p2307) ∨ (¬ p5059) ∨ (¬ p4948) ∨ (¬ p3055) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p4866) ∨ (¬ p4948) ∨ (¬ p5016) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial11531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory3027 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11531 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2459) (meaning t m 3055) (meaning t m 3366) (meaning t m 3684) (meaning t m 4866) (meaning t m 4948) (meaning t m 5016) (meaning t m 5059) source

theorem rule11532 (p2027 p2247 p2299 p2319 p2341 p2396 p3662 p3951 p4208 p5017 : Prop) (h : (¬ p5017) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4208) ∨ (¬ p2396) ∨ (¬ p3662) ∨ (¬ p2341) ∨ (¬ p2299) ∨ (¬ p2319)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3662) ∨ (¬ p3951) ∨ (¬ p4208) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial11532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory3028 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11532 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2396) (meaning t m 3662) (meaning t m 3951) (meaning t m 4208) (meaning t m 5017) source

theorem rule11533 (p2027 p3365 p3516 p3817 p3819 p4024 p4105 p4845 : Prop) (h : (¬ p3817) ∨ (¬ p4845) ∨ (¬ p4024) ∨ (¬ p3365) ∨ (¬ p3516) ∨ p2027 ∨ (¬ p3819) ∨ (¬ p4105)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3516) ∨ (¬ p3817) ∨ (¬ p3819) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory3029 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 2 3) (m.theta 2 6) (m.theta 7 9)
  exact rule11533 (meaning t m 2027) (meaning t m 3365) (meaning t m 3516) (meaning t m 3817) (meaning t m 3819) (meaning t m 4024) (meaning t m 4105) (meaning t m 4845) source

theorem rule11534 (p2027 p2230 p2373 p3146 p3688 p3917 p3954 p4604 p5190 : Prop) (h : (¬ p3954) ∨ (¬ p4604) ∨ (¬ p2373) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p2230) ∨ (¬ p3688) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory3030 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule11534 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3146) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4604) (meaning t m 5190) source

theorem rule11535 (p2027 p2662 p3222 p3346 p4154 p4281 p4972 : Prop) (h : (¬ p4154) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p2662) ∨ (¬ p3222) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2662) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial11535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory3031 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9)
  exact rule11535 (meaning t m 2027) (meaning t m 2662) (meaning t m 3222) (meaning t m 3346) (meaning t m 4154) (meaning t m 4281) (meaning t m 4972) source

theorem rule11537 (p2027 p2933 p3426 p3434 p3540 p3817 p4375 p4727 : Prop) (h : (¬ p3817) ∨ (¬ p3540) ∨ (¬ p2933) ∨ (¬ p3434) ∨ (¬ p4727) ∨ (¬ p4375) ∨ p2027 ∨ (¬ p3426)) : (p2027) ∨ (¬ p2933) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3540) ∨ (¬ p3817) ∨ (¬ p4375) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial11537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory3033 t (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule11537 (meaning t m 2027) (meaning t m 2933) (meaning t m 3426) (meaning t m 3434) (meaning t m 3540) (meaning t m 3817) (meaning t m 4375) (meaning t m 4727) source

theorem rule11541 (p2027 p2850 p3367 p4242 p4608 p5369 : Prop) (h : (¬ p2850) ∨ (¬ p4242) ∨ (¬ p4608) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p5369)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4608) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial11541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4608)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory3037 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 8)
  exact rule11541 (meaning t m 2027) (meaning t m 2850) (meaning t m 3367) (meaning t m 4242) (meaning t m 4608) (meaning t m 5369) source

theorem rule11542 (p2441 p2590 p3581 : Prop) (h : p2441 ∨ (¬ p2590) ∨ (¬ p3581)) : (p2441) ∨ (¬ p2590) ∨ (¬ p3581) := by
  classical
  tauto

theorem initial11542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2441) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3581)) := by
  have source := ElevenTheory.theory3038 (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule11542 (meaning t m 2441) (meaning t m 2590) (meaning t m 3581) source

theorem rule11543 (p2027 p2751 p3073 p3572 p3857 p3859 p3961 p4155 : Prop) (h : p2027 ∨ (¬ p3859) ∨ (¬ p2751) ∨ (¬ p3572) ∨ (¬ p4155) ∨ (¬ p3961) ∨ (¬ p3857) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3073) ∨ (¬ p3572) ∨ (¬ p3857) ∨ (¬ p3859) ∨ (¬ p3961) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial11543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory3039 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 8 9)
  exact rule11543 (meaning t m 2027) (meaning t m 2751) (meaning t m 3073) (meaning t m 3572) (meaning t m 3857) (meaning t m 3859) (meaning t m 3961) (meaning t m 4155) source

theorem rule11544 (p2027 p2363 p3063 p3857 p4197 p5018 : Prop) (h : (¬ p4197) ∨ (¬ p3063) ∨ (¬ p5018) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3063) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p5018) := by
  classical
  tauto

theorem initial11544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 5018)) := by
  have source := ElevenTheory.theory3040 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule11544 (meaning t m 2027) (meaning t m 2363) (meaning t m 3063) (meaning t m 3857) (meaning t m 4197) (meaning t m 5018) source

theorem rule11545 (p2027 p3449 p3549 p3591 p4318 p4405 : Prop) (h : (¬ p3449) ∨ (¬ p4405) ∨ (¬ p3549) ∨ (¬ p4318) ∨ (¬ p3591) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4318) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial11545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory3041 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 6 7) (m.theta 6 8)
  exact rule11545 (meaning t m 2027) (meaning t m 3449) (meaning t m 3549) (meaning t m 3591) (meaning t m 4318) (meaning t m 4405) source

theorem rule11546 (p2027 p2737 p3093 p3365 p3873 p4870 : Prop) (h : (¬ p3873) ∨ (¬ p4870) ∨ (¬ p3093) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2737)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory3042 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3)
  exact rule11546 (meaning t m 2027) (meaning t m 2737) (meaning t m 3093) (meaning t m 3365) (meaning t m 3873) (meaning t m 4870) source

theorem rule11547 (p2027 p2685 p4315 p4333 p5661 p5740 : Prop) (h : (¬ p4315) ∨ (¬ p2685) ∨ (¬ p4333) ∨ (¬ p5661) ∨ p2027 ∨ (¬ p5740)) : (p2027) ∨ (¬ p2685) ∨ (¬ p4315) ∨ (¬ p4333) ∨ (¬ p5661) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial11547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 5661)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory3043 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 10) (m.theta 5 7)
  exact rule11547 (meaning t m 2027) (meaning t m 2685) (meaning t m 4315) (meaning t m 4333) (meaning t m 5661) (meaning t m 5740) source

theorem rule11549 (p2027 p2122 p2313 p2386 p3684 p4375 p4717 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p4375) ∨ (¬ p3684) ∨ (¬ p2386) ∨ (¬ p2122) ∨ (¬ p4717)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3684) ∨ (¬ p4375) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial11549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory3045 t (m.theta 0 6) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule11549 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2386) (meaning t m 3684) (meaning t m 4375) (meaning t m 4717) source

theorem rule11550 (p2027 p2312 p2507 p3016 p3309 p3742 p4279 : Prop) (h : p2027 ∨ (¬ p2507) ∨ (¬ p4279) ∨ (¬ p3742) ∨ (¬ p3016) ∨ (¬ p3309) ∨ (¬ p2312)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2507) ∨ (¬ p3016) ∨ (¬ p3309) ∨ (¬ p3742) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial11550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory3046 t (m.theta 0 7) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule11550 (meaning t m 2027) (meaning t m 2312) (meaning t m 2507) (meaning t m 3016) (meaning t m 3309) (meaning t m 3742) (meaning t m 4279) source

theorem rule11552 (p2027 p2312 p2341 p3309 p3553 p4067 p4761 : Prop) (h : p2027 ∨ (¬ p4761) ∨ (¬ p3309) ∨ (¬ p2341) ∨ (¬ p4067) ∨ (¬ p3553) ∨ (¬ p2312)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3309) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4761) := by
  classical
  tauto

theorem initial11552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4761)) := by
  have source := ElevenTheory.theory3048 t (m.theta 0 7) (m.theta 1 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule11552 (meaning t m 2027) (meaning t m 2312) (meaning t m 2341) (meaning t m 3309) (meaning t m 3553) (meaning t m 4067) (meaning t m 4761) source

theorem rule11554 (p2027 p3343 p3389 p3742 p3954 p4242 p4332 p4340 p5190 : Prop) (h : (¬ p4332) ∨ (¬ p4242) ∨ (¬ p3954) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p5190) ∨ (¬ p3389) ∨ (¬ p3343)) : (p2027) ∨ (¬ p3343) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4332) ∨ (¬ p4340) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory3050 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 8 9)
  exact rule11554 (meaning t m 2027) (meaning t m 3343) (meaning t m 3389) (meaning t m 3742) (meaning t m 3954) (meaning t m 4242) (meaning t m 4332) (meaning t m 4340) (meaning t m 5190) source

theorem rule11555 (p2027 p3276 p3355 p3549 p3591 p4107 p4322 p4395 p5190 : Prop) (h : (¬ p3276) ∨ (¬ p3591) ∨ (¬ p4395) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p4107) ∨ (¬ p5190) ∨ (¬ p3355)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory3051 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule11555 (meaning t m 2027) (meaning t m 3276) (meaning t m 3355) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4322) (meaning t m 4395) (meaning t m 5190) source

theorem rule11557 (p2027 p2104 p2743 p2774 p3537 p4845 : Prop) (h : p2027 ∨ (¬ p4845) ∨ (¬ p2104) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3537)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3537) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory3053 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8)
  exact rule11557 (meaning t m 2027) (meaning t m 2104) (meaning t m 2743) (meaning t m 2774) (meaning t m 3537) (meaning t m 4845) source

theorem rule11560 (p2027 p3083 p3389 p3583 p3694 p3742 p3954 p4158 p5190 : Prop) (h : (¬ p3694) ∨ (¬ p3954) ∨ (¬ p3389) ∨ (¬ p4158) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3583) ∨ (¬ p3083)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3389) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3742) ∨ (¬ p3954) ∨ (¬ p4158) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory3056 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8)
  exact rule11560 (meaning t m 2027) (meaning t m 3083) (meaning t m 3389) (meaning t m 3583) (meaning t m 3694) (meaning t m 3742) (meaning t m 3954) (meaning t m 4158) (meaning t m 5190) source

theorem rule11561 (p2027 p3426 p3568 p4253 p4260 p4846 : Prop) (h : (¬ p3426) ∨ (¬ p3568) ∨ (¬ p4253) ∨ (¬ p4260) ∨ (¬ p4846) ∨ p2027) : (p2027) ∨ (¬ p3426) ∨ (¬ p3568) ∨ (¬ p4253) ∨ (¬ p4260) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial11561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory3057 t (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 10)
  exact rule11561 (meaning t m 2027) (meaning t m 3426) (meaning t m 3568) (meaning t m 4253) (meaning t m 4260) (meaning t m 4846) source

theorem rule11562 (p2027 p2662 p2751 p2810 p2922 p3540 p4281 : Prop) (h : p2027 ∨ (¬ p2751) ∨ (¬ p4281) ∨ (¬ p2922) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2662) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial11562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory3058 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule11562 (meaning t m 2027) (meaning t m 2662) (meaning t m 2751) (meaning t m 2810) (meaning t m 2922) (meaning t m 3540) (meaning t m 4281) source

theorem rule11565 (p2027 p2145 p2449 p2685 p2696 p3646 p3950 p3989 p4347 : Prop) (h : (¬ p2145) ∨ (¬ p2449) ∨ (¬ p3950) ∨ (¬ p2685) ∨ (¬ p3989) ∨ (¬ p3646) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial11565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3061 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule11565 (meaning t m 2027) (meaning t m 2145) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) source

theorem rule11567 (p2027 p2922 p3093 p3540 p3541 p4108 p4870 : Prop) (h : (¬ p3093) ∨ (¬ p3541) ∨ (¬ p4870) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p4108) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3093) ∨ (¬ p3540) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory3063 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7)
  exact rule11567 (meaning t m 2027) (meaning t m 2922) (meaning t m 3093) (meaning t m 3540) (meaning t m 3541) (meaning t m 4108) (meaning t m 4870) source

theorem rule11568 (p2027 p2352 p2449 p2685 p2696 p2753 p3923 p4137 p4625 p4870 : Prop) (h : (¬ p4137) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p3923) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p4625) ∨ (¬ p2352) ∨ (¬ p2753) ∨ (¬ p4870)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3923) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory3064 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule11568 (meaning t m 2027) (meaning t m 2352) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3923) (meaning t m 4137) (meaning t m 4625) (meaning t m 4870) source

theorem rule11572 (p2027 p2341 p2630 p3659 p4066 p4357 p4650 : Prop) (h : (¬ p4066) ∨ (¬ p2341) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p4357) ∨ (¬ p2630) ∨ (¬ p4650)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2630) ∨ (¬ p3659) ∨ (¬ p4066) ∨ (¬ p4357) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial11572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory3068 t (m.theta 0 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule11572 (meaning t m 2027) (meaning t m 2341) (meaning t m 2630) (meaning t m 3659) (meaning t m 4066) (meaning t m 4357) (meaning t m 4650) source

theorem rule11573 (p2027 p2139 p2579 p3051 p3156 p3422 p3874 p3905 p4320 p4434 : Prop) (h : p2027 ∨ (¬ p4434) ∨ (¬ p4320) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3874) ∨ (¬ p2579) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2579) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4320) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial11573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory3069 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule11573 (meaning t m 2027) (meaning t m 2139) (meaning t m 2579) (meaning t m 3051) (meaning t m 3156) (meaning t m 3422) (meaning t m 3874) (meaning t m 3905) (meaning t m 4320) (meaning t m 4434) source

theorem rule11574 (p2027 p3438 p3449 p3834 p4181 p5122 : Prop) (h : (¬ p3438) ∨ (¬ p4181) ∨ (¬ p3449) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p3834)) : (p2027) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4181) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial11574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory3070 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 8 10) (m.theta 8 9)
  exact rule11574 (meaning t m 2027) (meaning t m 3438) (meaning t m 3449) (meaning t m 3834) (meaning t m 4181) (meaning t m 5122) source

theorem rule11575 (p2027 p3422 p3684 p4173 p4203 p4629 : Prop) (h : p2027 ∨ (¬ p4173) ∨ (¬ p4629) ∨ (¬ p4203) ∨ (¬ p3684) ∨ (¬ p3422)) : (p2027) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4173) ∨ (¬ p4203) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial11575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory3071 t (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule11575 (meaning t m 2027) (meaning t m 3422) (meaning t m 3684) (meaning t m 4173) (meaning t m 4203) (meaning t m 4629) source

theorem rule11576 (p2027 p2476 p2662 p2745 p3475 p3641 p4111 : Prop) (h : (¬ p2745) ∨ (¬ p2662) ∨ (¬ p3641) ∨ (¬ p4111) ∨ (¬ p2476) ∨ (¬ p3475) ∨ p2027) : (p2027) ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3475) ∨ (¬ p3641) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial11576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3072 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8)
  exact rule11576 (meaning t m 2027) (meaning t m 2476) (meaning t m 2662) (meaning t m 2745) (meaning t m 3475) (meaning t m 3641) (meaning t m 4111) source

theorem rule11577 (p2027 p2156 p2850 p4109 p4173 p4202 p5214 : Prop) (h : (¬ p5214) ∨ (¬ p2850) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4202) ∨ (¬ p4173) ∨ (¬ p4109)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2850) ∨ (¬ p4109) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial11577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory3073 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule11577 (meaning t m 2027) (meaning t m 2156) (meaning t m 2850) (meaning t m 4109) (meaning t m 4173) (meaning t m 4202) (meaning t m 5214) source

theorem rule11578 (p2027 p2651 p2741 p2811 p2829 p4111 p4845 : Prop) (h : (¬ p2651) ∨ (¬ p2811) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p4845) ∨ (¬ p4111) ∨ (¬ p2741)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2829) ∨ (¬ p4111) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory3074 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule11578 (meaning t m 2027) (meaning t m 2651) (meaning t m 2741) (meaning t m 2811) (meaning t m 2829) (meaning t m 4111) (meaning t m 4845) source

theorem rule11579 (p2027 p2122 p2312 p2641 p2996 p3984 p4155 p5225 : Prop) (h : (¬ p2641) ∨ (¬ p2122) ∨ (¬ p2312) ∨ (¬ p2996) ∨ p2027 ∨ (¬ p3984) ∨ (¬ p4155) ∨ (¬ p5225)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2312) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3984) ∨ (¬ p4155) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial11579 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory3075 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule11579 (meaning t m 2027) (meaning t m 2122) (meaning t m 2312) (meaning t m 2641) (meaning t m 2996) (meaning t m 3984) (meaning t m 4155) (meaning t m 5225) source

theorem rule11582 (p2098 p2104 : Prop) (h : (¬ p2104) ∨ (¬ p2098)) : (¬ p2098) ∨ (¬ p2104) := by
  classical
  tauto

theorem initial11582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2104)) := by
  have source := ElevenTheory.theory3078 (m.theta 0 2) (m.theta 2 8)
  exact rule11582 (meaning t m 2098) (meaning t m 2104) source

theorem rule11583 (p2972 p4363 : Prop) (h : (¬ p4363) ∨ (¬ p2972)) : (¬ p2972) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial11583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory3079 (m.theta 1 5) (m.theta 5 9)
  exact rule11583 (meaning t m 2972) (meaning t m 4363) source

theorem rule11585 (p2982 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p2982)) : (¬ p2982) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory3081 (m.theta 4 5) (m.theta 5 9)
  exact rule11585 (meaning t m 2982) (meaning t m 4948) source

theorem rule11589 (p3370 p4109 p4210 : Prop) (h : p3370 ∨ (¬ p4109) ∨ (¬ p4210)) : (p3370) ∨ (¬ p4109) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial11589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3370) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory3085 (m.theta 0 5) (m.theta 1 5) (m.theta 4 5)
  exact rule11589 (meaning t m 3370) (meaning t m 4109) (meaning t m 4210) source

theorem rule11591 (p2027 p3571 p3670 p4235 p4321 p4885 p5031 p5357 : Prop) (h : (¬ p4885) ∨ (¬ p5357) ∨ (¬ p3571) ∨ p2027 ∨ (¬ p4321) ∨ (¬ p4235) ∨ (¬ p3670) ∨ (¬ p5031)) : (p2027) ∨ (¬ p3571) ∨ (¬ p3670) ∨ (¬ p4235) ∨ (¬ p4321) ∨ (¬ p4885) ∨ (¬ p5031) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial11591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4885)) ∨ (¬ (meaning t m 5031)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory3087 t (m.theta 1 7) (m.theta 1 9) (m.theta 2 5) (m.theta 2 9) (m.theta 4 5) (m.theta 5 7) (m.theta 9 10)
  exact rule11591 (meaning t m 2027) (meaning t m 3571) (meaning t m 3670) (meaning t m 4235) (meaning t m 4321) (meaning t m 4885) (meaning t m 5031) (meaning t m 5357) source

theorem rule11595 (p2027 p2406 p2761 p2982 p3379 p3946 p4191 p4395 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p4191) ∨ (¬ p3946) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4395) ∨ (¬ p2406) ∨ (¬ p2982)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2761) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4395) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial11595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory3091 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule11595 (meaning t m 2027) (meaning t m 2406) (meaning t m 2761) (meaning t m 2982) (meaning t m 3379) (meaning t m 3946) (meaning t m 4191) (meaning t m 4395) (meaning t m 5021) source

theorem rule11598 (p2027 p2727 p3031 p3516 p3817 p4066 p4650 : Prop) (h : (¬ p2727) ∨ (¬ p4650) ∨ (¬ p3031) ∨ (¬ p4066) ∨ (¬ p3817) ∨ (¬ p3516) ∨ p2027) : (p2027) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3516) ∨ (¬ p3817) ∨ (¬ p4066) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial11598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory3094 t (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule11598 (meaning t m 2027) (meaning t m 2727) (meaning t m 3031) (meaning t m 3516) (meaning t m 3817) (meaning t m 4066) (meaning t m 4650) source

theorem rule11600 (p2027 p2220 p3097 p3646 p4405 p4441 : Prop) (h : p2027 ∨ (¬ p4441) ∨ (¬ p3646) ∨ (¬ p4405) ∨ (¬ p2220) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4405) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial11600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory3096 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule11600 (meaning t m 2027) (meaning t m 2220) (meaning t m 3097) (meaning t m 3646) (meaning t m 4405) (meaning t m 4441) source

theorem rule11602 (p2027 p2352 p2588 p3550 p4107 p4666 : Prop) (h : (¬ p2588) ∨ (¬ p4107) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p3550)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory3098 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule11602 (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 3550) (meaning t m 4107) (meaning t m 4666) source

theorem rule11604 (p2027 p2098 p2780 p3956 p4326 p5225 : Prop) (h : (¬ p5225) ∨ (¬ p2098) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4326) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2780) ∨ (¬ p3956) ∨ (¬ p4326) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial11604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory3100 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 4 6) (m.theta 6 8)
  exact rule11604 (meaning t m 2027) (meaning t m 2098) (meaning t m 2780) (meaning t m 3956) (meaning t m 4326) (meaning t m 5225) source

theorem rule11606 (p2027 p3083 p3543 p3742 p4107 p4279 p4404 p4427 p4666 : Prop) (h : (¬ p3543) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p4404) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p3083) ∨ (¬ p4427) ∨ (¬ p4279)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3543) ∨ (¬ p3742) ∨ (¬ p4107) ∨ (¬ p4279) ∨ (¬ p4404) ∨ (¬ p4427) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory3102 t (m.theta 0 7) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11606 (meaning t m 2027) (meaning t m 3083) (meaning t m 3543) (meaning t m 3742) (meaning t m 4107) (meaning t m 4279) (meaning t m 4404) (meaning t m 4427) (meaning t m 4666) source

theorem rule11607 (p2027 p2507 p3449 p3591 p3956 p4318 : Prop) (h : (¬ p4318) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p2507) ∨ (¬ p3956) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2507) ∨ (¬ p3449) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4318) := by
  classical
  tauto

theorem initial11607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4318)) := by
  have source := ElevenTheory.theory3103 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 4 6) (m.theta 6 8)
  exact rule11607 (meaning t m 2027) (meaning t m 2507) (meaning t m 3449) (meaning t m 3591) (meaning t m 3956) (meaning t m 4318) source

theorem rule11608 (p2027 p2499 p2922 p4710 p5472 p5514 : Prop) (h : (¬ p2922) ∨ (¬ p4710) ∨ (¬ p5472) ∨ p2027 ∨ (¬ p5514) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p4710) ∨ (¬ p5472) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial11608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5472)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory3104 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10) (m.theta 6 7)
  exact rule11608 (meaning t m 2027) (meaning t m 2499) (meaning t m 2922) (meaning t m 4710) (meaning t m 5472) (meaning t m 5514) source

theorem rule11609 (p2027 p2532 p3212 p4120 p4340 p4742 : Prop) (h : (¬ p4742) ∨ (¬ p2532) ∨ (¬ p4120) ∨ (¬ p4340) ∨ (¬ p3212) ∨ p2027) : (p2027) ∨ (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4340) ∨ (¬ p4742) := by
  classical
  tauto

theorem initial11609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4742)) := by
  have source := ElevenTheory.theory3105 t (m.theta 0 5) (m.theta 2 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule11609 (meaning t m 2027) (meaning t m 2532) (meaning t m 3212) (meaning t m 4120) (meaning t m 4340) (meaning t m 4742) source

theorem rule11610 (p2027 p2901 p3744 p4140 p4173 p4282 p4620 : Prop) (h : (¬ p3744) ∨ (¬ p4140) ∨ p2027 ∨ (¬ p4620) ∨ (¬ p4282) ∨ (¬ p4173) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial11610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory3106 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule11610 (meaning t m 2027) (meaning t m 2901) (meaning t m 3744) (meaning t m 4140) (meaning t m 4173) (meaning t m 4282) (meaning t m 4620) source

theorem rule11611 (p2027 p2088 p2427 p3691 p4261 p4492 p4590 p4629 : Prop) (h : (¬ p4492) ∨ (¬ p3691) ∨ (¬ p4590) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2088) ∨ (¬ p4629) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2427) ∨ (¬ p3691) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4590) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial11611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory3107 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 5) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 8 9)
  exact rule11611 (meaning t m 2027) (meaning t m 2088) (meaning t m 2427) (meaning t m 3691) (meaning t m 4261) (meaning t m 4492) (meaning t m 4590) (meaning t m 4629) source

theorem rule11613 (p2027 p2192 p2210 p2274 p2717 p3426 p3551 p4137 p4342 p4620 p5210 : Prop) (h : p2027 ∨ (¬ p4137) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p5210) ∨ (¬ p3551) ∨ (¬ p2274) ∨ (¬ p4620) ∨ (¬ p4342) ∨ (¬ p3426) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3551) ∨ (¬ p4137) ∨ (¬ p4342) ∨ (¬ p4620) ∨ (¬ p5210) := by
  classical
  tauto

theorem initial11613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5210)) := by
  have source := ElevenTheory.theory3109 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 5) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule11613 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2717) (meaning t m 3426) (meaning t m 3551) (meaning t m 4137) (meaning t m 4342) (meaning t m 4620) (meaning t m 5210) source

theorem rule11616 (p2027 p2088 p2630 p3567 p4114 p4340 p4364 p4972 : Prop) (h : (¬ p4340) ∨ (¬ p4114) ∨ (¬ p4972) ∨ (¬ p3567) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p4364)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2630) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial11616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory3112 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 6) (m.theta 8 9)
  exact rule11616 (meaning t m 2027) (meaning t m 2088) (meaning t m 2630) (meaning t m 3567) (meaning t m 4114) (meaning t m 4340) (meaning t m 4364) (meaning t m 4972) source

theorem rule11617 (p2027 p2307 p2641 p2751 p3567 p3822 p4841 : Prop) (h : (¬ p2641) ∨ (¬ p2751) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p4841) ∨ (¬ p2307) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2641) ∨ (¬ p2751) ∨ (¬ p3567) ∨ (¬ p3822) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial11617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory3113 t (m.theta 0 6) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule11617 (meaning t m 2027) (meaning t m 2307) (meaning t m 2641) (meaning t m 2751) (meaning t m 3567) (meaning t m 3822) (meaning t m 4841) source

theorem rule11618 (p2027 p2139 p2156 p2589 p3905 p4110 : Prop) (h : p2027 ∨ (¬ p2139) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p2589) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2589) ∨ (¬ p3905) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial11618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3114 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule11618 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2589) (meaning t m 3905) (meaning t m 4110) source

end SunPrize.SMT
