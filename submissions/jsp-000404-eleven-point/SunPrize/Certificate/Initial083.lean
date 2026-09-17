import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory067
import SunPrize.Certificate.Theory068
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule38851 (p3266 p3461 p4345 : Prop) (h : (¬ p3266) ∨ (¬ p4345) ∨ p3461) : (¬ p3266) ∨ (p3461) ∨ (¬ p4345) := by
  classical
  tauto

theorem initial38851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3266)) ∨ (meaning t m 3461) ∨ (¬ (meaning t m 4345)) := by
  have source := ElevenTheory.theory28107 (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38851 (meaning t m 3266) (meaning t m 3461) (meaning t m 4345) source

theorem rule38856 (p2027 p2352 p2363 p2573 p2608 p3519 p4324 p4366 p4376 p4424 p4669 : Prop) (h : (¬ p2573) ∨ (¬ p3519) ∨ (¬ p4324) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p2363) ∨ (¬ p4424) ∨ (¬ p4366) ∨ (¬ p4669)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p4324) ∨ (¬ p4366) ∨ (¬ p4376) ∨ (¬ p4424) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial38856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory28112 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38856 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2608) (meaning t m 3519) (meaning t m 4324) (meaning t m 4366) (meaning t m 4376) (meaning t m 4424) (meaning t m 4669) source

theorem rule38859 (p2027 p2470 p2528 p2780 p3266 p3366 p3519 p3822 p4260 p4376 p4831 : Prop) (h : (¬ p2780) ∨ (¬ p4260) ∨ (¬ p2528) ∨ (¬ p3519) ∨ (¬ p2470) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p4831) ∨ (¬ p3822) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2780) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4376) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial38859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory28115 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule38859 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2780) (meaning t m 3266) (meaning t m 3366) (meaning t m 3519) (meaning t m 3822) (meaning t m 4260) (meaning t m 4376) (meaning t m 4831) source

theorem rule38861 (p2027 p2220 p2963 p2982 p3366 p3519 p3822 p3880 p4107 p4236 p4328 p4376 p4395 p4399 : Prop) (h : (¬ p4328) ∨ (¬ p3519) ∨ (¬ p4107) ∨ (¬ p3880) ∨ (¬ p2220) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p2982) ∨ (¬ p4399) ∨ (¬ p4395) ∨ (¬ p3822) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2963) ∨ (¬ p2982) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3822) ∨ (¬ p3880) ∨ (¬ p4107) ∨ (¬ p4236) ∨ (¬ p4328) ∨ (¬ p4376) ∨ (¬ p4395) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial38861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory28117 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule38861 (meaning t m 2027) (meaning t m 2220) (meaning t m 2963) (meaning t m 2982) (meaning t m 3366) (meaning t m 3519) (meaning t m 3822) (meaning t m 3880) (meaning t m 4107) (meaning t m 4236) (meaning t m 4328) (meaning t m 4376) (meaning t m 4395) (meaning t m 4399) source

theorem rule38866 (p2474 p2482 : Prop) (h : p2474 ∨ p2482) : (p2474) ∨ (p2482) := by
  classical
  tauto

theorem initial38866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2474) ∨ (meaning t m 2482) := by
  have source := ElevenTheory.theory28122 (m.theta 0 4) (m.theta 0 8)
  exact rule38866 (meaning t m 2474) (meaning t m 2482) source

theorem rule38869 (p2476 p3346 p3358 : Prop) (h : (¬ p3358) ∨ (¬ p3346) ∨ p2476) : (p2476) ∨ (¬ p3346) ∨ (¬ p3358) := by
  classical
  tauto

theorem initial38869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3358)) := by
  have source := ElevenTheory.theory28125 (m.theta 0 4) (m.theta 4 8) (m.theta 4 9)
  exact rule38869 (meaning t m 2476) (meaning t m 3346) (meaning t m 3358) source

theorem rule38870 (p2027 p2341 p2608 p3146 p3266 p3543 p3591 p4132 p4435 p4793 p5254 : Prop) (h : (¬ p3146) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2341) ∨ (¬ p4132) ∨ (¬ p4793) ∨ (¬ p3266) ∨ (¬ p3591) ∨ (¬ p5254) ∨ (¬ p3543) ∨ (¬ p4435)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3543) ∨ (¬ p3591) ∨ (¬ p4132) ∨ (¬ p4435) ∨ (¬ p4793) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial38870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4793)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory28126 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 5 8) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule38870 (meaning t m 2027) (meaning t m 2341) (meaning t m 2608) (meaning t m 3146) (meaning t m 3266) (meaning t m 3543) (meaning t m 3591) (meaning t m 4132) (meaning t m 4435) (meaning t m 4793) (meaning t m 5254) source

theorem rule38871 (p2027 p2341 p3146 p3266 p3365 p3366 p3370 p4132 p4195 p4377 p4988 p5254 p5717 : Prop) (h : (¬ p3365) ∨ (¬ p5717) ∨ (¬ p5254) ∨ (¬ p4988) ∨ (¬ p3370) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2341) ∨ (¬ p4132) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p4132) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4988) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial38871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4988)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory28127 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 8) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule38871 (meaning t m 2027) (meaning t m 2341) (meaning t m 3146) (meaning t m 3266) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 4132) (meaning t m 4195) (meaning t m 4377) (meaning t m 4988) (meaning t m 5254) (meaning t m 5717) source

theorem rule38872 (p2027 p2579 p2761 p3347 p3370 p3422 p3516 p4257 p4377 p4444 p4697 p4988 p5160 : Prop) (h : p2027 ∨ (¬ p2761) ∨ (¬ p4988) ∨ (¬ p3370) ∨ (¬ p3516) ∨ (¬ p4377) ∨ (¬ p4444) ∨ (¬ p2579) ∨ (¬ p4257) ∨ (¬ p5160) ∨ (¬ p3347) ∨ (¬ p4697) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2761) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3422) ∨ (¬ p3516) ∨ (¬ p4257) ∨ (¬ p4377) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4988) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial38872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4988)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory28128 t (m.theta 0 4) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38872 (meaning t m 2027) (meaning t m 2579) (meaning t m 2761) (meaning t m 3347) (meaning t m 3370) (meaning t m 3422) (meaning t m 3516) (meaning t m 4257) (meaning t m 4377) (meaning t m 4444) (meaning t m 4697) (meaning t m 4988) (meaning t m 5160) source

theorem rule38874 (p2027 p2264 p2659 p3540 p3580 p3644 : Prop) (h : (¬ p3540) ∨ (¬ p3580) ∨ (¬ p2659) ∨ (¬ p3644) ∨ (¬ p2264) ∨ p2027) : (p2027) ∨ (¬ p2264) ∨ (¬ p2659) ∨ (¬ p3540) ∨ (¬ p3580) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial38874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory28130 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule38874 (meaning t m 2027) (meaning t m 2264) (meaning t m 2659) (meaning t m 3540) (meaning t m 3580) (meaning t m 3644) source

theorem rule38879 (p3497 p3952 p3988 : Prop) (h : (¬ p3952) ∨ (¬ p3988) ∨ p3497) : (p3497) ∨ (¬ p3952) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial38879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3497) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory28135 (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule38879 (meaning t m 3497) (meaning t m 3952) (meaning t m 3988) source

theorem rule38881 (p2027 p3201 p3569 p3684 p4320 p4702 : Prop) (h : (¬ p4702) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p3684) ∨ (¬ p3569) ∨ (¬ p3201)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial38881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory28137 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule38881 (meaning t m 2027) (meaning t m 3201) (meaning t m 3569) (meaning t m 3684) (meaning t m 4320) (meaning t m 4702) source

theorem rule38882 (p2027 p2578 p3422 p3684 p3952 p4356 p4702 : Prop) (h : (¬ p4356) ∨ (¬ p2578) ∨ (¬ p3952) ∨ (¬ p4702) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p3422)) : (p2027) ∨ (¬ p2578) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p3952) ∨ (¬ p4356) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial38882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory28138 t (m.theta 0 6) (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule38882 (meaning t m 2027) (meaning t m 2578) (meaning t m 3422) (meaning t m 3684) (meaning t m 3952) (meaning t m 4356) (meaning t m 4702) source

theorem rule38885 (p2027 p2284 p2946 p3172 p4312 p4507 : Prop) (h : p2027 ∨ (¬ p2284) ∨ (¬ p4507) ∨ (¬ p4312) ∨ (¬ p2946) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4312) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial38885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory28141 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8)
  exact rule38885 (meaning t m 2027) (meaning t m 2284) (meaning t m 2946) (meaning t m 3172) (meaning t m 4312) (meaning t m 4507) source

theorem rule38887 (p2027 p2241 p2579 p3189 p3256 p3822 p4107 p4390 p4669 p5193 : Prop) (h : (¬ p4107) ∨ (¬ p5193) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p2579) ∨ (¬ p4669) ∨ (¬ p4390)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2579) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4390) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial38887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28143 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 2 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule38887 (meaning t m 2027) (meaning t m 2241) (meaning t m 2579) (meaning t m 3189) (meaning t m 3256) (meaning t m 3822) (meaning t m 4107) (meaning t m 4390) (meaning t m 4669) (meaning t m 5193) source

theorem rule38892 (p2744 p4759 p4866 : Prop) (h : (¬ p4759) ∨ (¬ p2744) ∨ p4866) : (¬ p2744) ∨ (¬ p4759) ∨ (p4866) := by
  classical
  tauto

theorem initial38892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4759)) ∨ (meaning t m 4866) := by
  have source := ElevenTheory.theory28148 t (m.theta 1 2) (m.theta 1 3) (m.theta 1 6)
  exact rule38892 (meaning t m 2744) (meaning t m 4759) (meaning t m 4866) source

theorem rule38893 (p1992 p2027 p2608 p2860 p3474 p3555 p4173 : Prop) (h : (¬ p2608) ∨ (¬ p3555) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p2860) ∨ p3474) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2860) ∨ (p3474) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial38893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory28149 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule38893 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2860) (meaning t m 3474) (meaning t m 3555) (meaning t m 4173) source

theorem rule38894 (p1985 p2901 p3474 p5053 : Prop) (h : (¬ p1985) ∨ p3474 ∨ (¬ p2901) ∨ p5053) : (¬ p1985) ∨ (¬ p2901) ∨ (p3474) ∨ (p5053) := by
  classical
  tauto

theorem initial38894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (¬ (meaning t m 2901)) ∨ (meaning t m 3474) ∨ (meaning t m 5053) := by
  have source := ElevenTheory.theory28150 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule38894 (meaning t m 1985) (meaning t m 2901) (meaning t m 3474) (meaning t m 5053) source

theorem rule38902 (p2027 p2264 p2588 p2807 p3055 p3570 p3584 p4556 p4786 : Prop) (h : (¬ p2588) ∨ (¬ p4786) ∨ (¬ p3584) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2807) ∨ (¬ p3570) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2588) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3570) ∨ (¬ p3584) ∨ (¬ p4556) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial38902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory28158 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule38902 (meaning t m 2027) (meaning t m 2264) (meaning t m 2588) (meaning t m 2807) (meaning t m 3055) (meaning t m 3570) (meaning t m 3584) (meaning t m 4556) (meaning t m 4786) source

theorem rule38905 (p2027 p2246 p2264 p2459 p2608 p2744 p2807 p3591 p4026 p4604 : Prop) (h : (¬ p2459) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p4026) ∨ (¬ p4604) ∨ (¬ p3591) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial38905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory28161 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38905 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2459) (meaning t m 2608) (meaning t m 2744) (meaning t m 2807) (meaning t m 3591) (meaning t m 4026) (meaning t m 4604) source

theorem rule38906 (p1990 p2027 p2177 p2284 p2997 p3570 p4320 : Prop) (h : (¬ p2177) ∨ (¬ p3570) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p1990) ∨ p2997 ∨ (¬ p4320)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2284) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial38906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory28162 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule38906 (meaning t m 1990) (meaning t m 2027) (meaning t m 2177) (meaning t m 2284) (meaning t m 2997) (meaning t m 3570) (meaning t m 4320) source

theorem rule38908 (p2027 p2246 p2608 p2744 p2946 p3146 p3156 p3591 p4026 p4604 : Prop) (h : (¬ p2608) ∨ (¬ p4026) ∨ (¬ p4604) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial38908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory28164 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule38908 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3591) (meaning t m 4026) (meaning t m 4604) source

theorem rule38909 (p4746 p4800 p4902 : Prop) (h : (¬ p4800) ∨ (¬ p4902) ∨ p4746) : (p4746) ∨ (¬ p4800) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial38909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4746) ∨ (¬ (meaning t m 4800)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28165 t (m.theta 2 8) (m.theta 5 8) (m.theta 7 8)
  exact rule38909 (meaning t m 4746) (meaning t m 4800) (meaning t m 4902) source

theorem rule38910 (p3685 p4782 p4968 : Prop) (h : (¬ p3685) ∨ (¬ p4782) ∨ p4968) : (¬ p3685) ∨ (¬ p4782) ∨ (p4968) := by
  classical
  tauto

theorem initial38910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4782)) ∨ (meaning t m 4968) := by
  have source := ElevenTheory.theory28166 t (m.theta 2 3) (m.theta 2 7) (m.theta 2 8)
  exact rule38910 (meaning t m 3685) (meaning t m 4782) (meaning t m 4968) source

theorem rule38914 (p3609 p4019 p4200 : Prop) (h : (¬ p4200) ∨ (¬ p3609) ∨ p4019) : (¬ p3609) ∨ (p4019) ∨ (¬ p4200) := by
  classical
  tauto

theorem initial38914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3609)) ∨ (meaning t m 4019) ∨ (¬ (meaning t m 4200)) := by
  have source := ElevenTheory.theory28170 (m.theta 2 8) (m.theta 8 10) (m.theta 8 9)
  exact rule38914 (meaning t m 3609) (meaning t m 4019) (meaning t m 4200) source

theorem rule38917 (p2027 p2122 p2241 p2313 p2727 p3083 p4358 p4596 p5021 : Prop) (h : (¬ p2313) ∨ (¬ p4358) ∨ (¬ p5021) ∨ (¬ p2727) ∨ (¬ p2241) ∨ (¬ p3083) ∨ (¬ p4596) ∨ (¬ p2122) ∨ p2027) : (p2027) ∨ (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p4358) ∨ (¬ p4596) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial38917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory28173 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38917 (meaning t m 2027) (meaning t m 2122) (meaning t m 2241) (meaning t m 2313) (meaning t m 2727) (meaning t m 3083) (meaning t m 4358) (meaning t m 4596) (meaning t m 5021) source

theorem rule38918 (p2027 p2241 p2387 p2992 p3156 p3609 p4347 p4746 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p4746) ∨ (¬ p2992) ∨ (¬ p4347) ∨ (¬ p3156) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3609) ∨ (¬ p4347) ∨ (¬ p4746) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial38918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4746)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory28174 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule38918 (meaning t m 2027) (meaning t m 2241) (meaning t m 2387) (meaning t m 2992) (meaning t m 3156) (meaning t m 3609) (meaning t m 4347) (meaning t m 4746) (meaning t m 5021) source

theorem rule38923 (p1994 p2027 p2103 p2169 p2363 p2727 p3177 p4340 p4360 : Prop) (h : (¬ p1994) ∨ p2169 ∨ (¬ p3177) ∨ (¬ p4360) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4340) ∨ (¬ p2103)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2103) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2727) ∨ (¬ p3177) ∨ (¬ p4340) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial38923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2103)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory28179 t (m.theta 0 8) (m.theta 1 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule38923 (meaning t m 1994) (meaning t m 2027) (meaning t m 2103) (meaning t m 2169) (meaning t m 2363) (meaning t m 2727) (meaning t m 3177) (meaning t m 4340) (meaning t m 4360) source

theorem rule38924 (p2027 p2122 p2313 p2373 p2542 p2651 p2778 p4358 p4433 p4786 : Prop) (h : p2027 ∨ (¬ p2778) ∨ (¬ p4358) ∨ (¬ p2542) ∨ (¬ p2313) ∨ (¬ p2122) ∨ (¬ p2651) ∨ (¬ p4433) ∨ (¬ p2373) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2778) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial38924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory28180 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule38924 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2373) (meaning t m 2542) (meaning t m 2651) (meaning t m 2778) (meaning t m 4358) (meaning t m 4433) (meaning t m 4786) source

theorem rule38927 (p2027 p2104 p2668 p2774 p4843 p4857 : Prop) (h : (¬ p2668) ∨ (¬ p4843) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p4857)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2668) ∨ (¬ p2774) ∨ (¬ p4843) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial38927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4843)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory28183 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8)
  exact rule38927 (meaning t m 2027) (meaning t m 2104) (meaning t m 2668) (meaning t m 2774) (meaning t m 4843) (meaning t m 4857) source

theorem rule38928 (p2850 p3574 p3660 p4343 : Prop) (h : (¬ p4343) ∨ (¬ p3660) ∨ (¬ p2850) ∨ (¬ p3574)) : (¬ p2850) ∨ (¬ p3574) ∨ (¬ p3660) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial38928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory28184 (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule38928 (meaning t m 2850) (meaning t m 3574) (meaning t m 3660) (meaning t m 4343) source

theorem rule38930 (p2027 p2774 p3055 p3684 p4390 p4717 : Prop) (h : p2027 ∨ (¬ p4717) ∨ (¬ p4390) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4390) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial38930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory28186 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule38930 (meaning t m 2027) (meaning t m 2774) (meaning t m 3055) (meaning t m 3684) (meaning t m 4390) (meaning t m 4717) source

theorem rule38934 (p1987 p2027 p2462 p2737 p2761 p3588 p5228 p5387 : Prop) (h : (¬ p5387) ∨ p2462 ∨ (¬ p5228) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2737) ∨ (¬ p3588)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2737) ∨ (¬ p2761) ∨ (¬ p3588) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial38934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory28190 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 2 9) (m.theta 7 9) (m.theta 9 10)
  exact rule38934 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2737) (meaning t m 2761) (meaning t m 3588) (meaning t m 5228) (meaning t m 5387) source

theorem rule38937 (p1982 p2027 p2588 p2997 p3461 p3564 p4444 : Prop) (h : (¬ p1982) ∨ (¬ p4444) ∨ p2997 ∨ (¬ p2588) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p3461)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial38937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory28193 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38937 (meaning t m 1982) (meaning t m 2027) (meaning t m 2588) (meaning t m 2997) (meaning t m 3461) (meaning t m 3564) (meaning t m 4444) source

theorem rule38939 (p1976 p2027 p2579 p2938 p3422 p3684 p3905 p4235 : Prop) (h : (¬ p1976) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p4235) ∨ p2938 ∨ (¬ p3684)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2579) ∨ (p2938) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p3905) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial38939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory28195 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule38939 (meaning t m 1976) (meaning t m 2027) (meaning t m 2579) (meaning t m 2938) (meaning t m 3422) (meaning t m 3684) (meaning t m 3905) (meaning t m 4235) source

theorem rule38940 (p2027 p2298 p2797 p3567 p3572 p3654 p4624 : Prop) (h : (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4624) ∨ (¬ p3572) ∨ (¬ p2298) ∨ (¬ p3654) ∨ p2027) : (p2027) ∨ (¬ p2298) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3572) ∨ (¬ p3654) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial38940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory28196 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9)
  exact rule38940 (meaning t m 2027) (meaning t m 2298) (meaning t m 2797) (meaning t m 3567) (meaning t m 3572) (meaning t m 3654) (meaning t m 4624) source

theorem rule38946 (p2027 p2459 p2608 p2911 p3389 p3519 p3555 p4363 p4376 p5059 : Prop) (h : (¬ p5059) ∨ (¬ p4363) ∨ (¬ p3519) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p4376) ∨ (¬ p3389) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p4376) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial38946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory28202 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38946 (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 2911) (meaning t m 3389) (meaning t m 3519) (meaning t m 3555) (meaning t m 4363) (meaning t m 4376) (meaning t m 5059) source

theorem rule38949 (p2027 p2246 p2341 p2459 p2498 p2608 p2744 p3266 p3591 p4104 p5254 p5514 : Prop) (h : (¬ p4104) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2341) ∨ (¬ p5514) ∨ (¬ p2459) ∨ (¬ p3591) ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p2246) ∨ (¬ p2498)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2498) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p3591) ∨ (¬ p4104) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial38949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory28205 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 4 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule38949 (meaning t m 2027) (meaning t m 2246) (meaning t m 2341) (meaning t m 2459) (meaning t m 2498) (meaning t m 2608) (meaning t m 2744) (meaning t m 3266) (meaning t m 3591) (meaning t m 4104) (meaning t m 5254) (meaning t m 5514) source

theorem rule38950 (p2027 p2284 p2341 p3553 p3691 p4386 p4555 : Prop) (h : (¬ p3553) ∨ (¬ p2284) ∨ (¬ p4386) ∨ (¬ p2341) ∨ (¬ p4555) ∨ (¬ p3691) ∨ p2027) : (p2027) ∨ (¬ p2284) ∨ (¬ p2341) ∨ (¬ p3553) ∨ (¬ p3691) ∨ (¬ p4386) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial38950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory28206 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule38950 (meaning t m 2027) (meaning t m 2284) (meaning t m 2341) (meaning t m 3553) (meaning t m 3691) (meaning t m 4386) (meaning t m 4555) source

theorem rule38951 (p1995 p2027 p2589 p2938 p3193 p3355 p4235 : Prop) (h : p2938 ∨ (¬ p1995) ∨ (¬ p2589) ∨ (¬ p3193) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3355)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2589) ∨ (p2938) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial38951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory28207 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7)
  exact rule38951 (meaning t m 1995) (meaning t m 2027) (meaning t m 2589) (meaning t m 2938) (meaning t m 3193) (meaning t m 3355) (meaning t m 4235) source

theorem rule38952 (p2027 p2138 p2246 p2341 p2449 p2744 p3366 p3553 p3744 p3758 p4104 p4625 : Prop) (h : (¬ p4625) ∨ (¬ p4104) ∨ (¬ p3758) ∨ (¬ p3744) ∨ (¬ p2138) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2449) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2341) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3553) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4104) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial38952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory28208 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule38952 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2341) (meaning t m 2449) (meaning t m 2744) (meaning t m 3366) (meaning t m 3553) (meaning t m 3744) (meaning t m 3758) (meaning t m 4104) (meaning t m 4625) source

theorem rule38958 (p1992 p2027 p2230 p2881 p2938 p3238 p3551 p4257 p5197 : Prop) (h : p2938 ∨ (¬ p4257) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3238) ∨ (¬ p1992) ∨ (¬ p2230) ∨ (¬ p5197)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3238) ∨ (¬ p3551) ∨ (¬ p4257) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial38958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory28214 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule38958 (meaning t m 1992) (meaning t m 2027) (meaning t m 2230) (meaning t m 2881) (meaning t m 2938) (meaning t m 3238) (meaning t m 3551) (meaning t m 4257) (meaning t m 5197) source

theorem rule38963 (p3422 p4422 p5160 : Prop) (h : (¬ p4422) ∨ (¬ p5160) ∨ (¬ p3422)) : (¬ p3422) ∨ (¬ p4422) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial38963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory28219 (m.theta 2 4) (m.theta 4 6) (m.theta 4 9)
  exact rule38963 (meaning t m 3422) (meaning t m 4422) (meaning t m 5160) source

theorem rule38964 (p2027 p2138 p2241 p2449 p3027 p3744 p3758 p4625 p4736 : Prop) (h : (¬ p3027) ∨ (¬ p3744) ∨ (¬ p4736) ∨ (¬ p4625) ∨ (¬ p2449) ∨ (¬ p2138) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4625) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28220 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule38964 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3744) (meaning t m 3758) (meaning t m 4625) (meaning t m 4736) source

theorem rule38967 (p2027 p2156 p2707 p3156 p3425 p3873 p3952 p4242 p4399 p4746 p5190 : Prop) (h : (¬ p3873) ∨ (¬ p4746) ∨ (¬ p3425) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p3156) ∨ (¬ p2156) ∨ (¬ p5190) ∨ (¬ p2707) ∨ (¬ p4242)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2707) ∨ (¬ p3156) ∨ (¬ p3425) ∨ (¬ p3873) ∨ (¬ p3952) ∨ (¬ p4242) ∨ (¬ p4399) ∨ (¬ p4746) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial38967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4746)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28223 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule38967 (meaning t m 2027) (meaning t m 2156) (meaning t m 2707) (meaning t m 3156) (meaning t m 3425) (meaning t m 3873) (meaning t m 3952) (meaning t m 4242) (meaning t m 4399) (meaning t m 4746) (meaning t m 5190) source

theorem rule38968 (p1975 p2027 p2274 p2622 p2743 p2839 p2860 : Prop) (h : (¬ p2743) ∨ (¬ p2839) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2860) ∨ p2622 ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial38968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory28224 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule38968 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2622) (meaning t m 2743) (meaning t m 2839) (meaning t m 2860) source

theorem rule38969 (p3371 p4338 p4869 : Prop) (h : (¬ p3371) ∨ (¬ p4338) ∨ p4869) : (¬ p3371) ∨ (¬ p4338) ∨ (p4869) := by
  classical
  tauto

theorem initial38969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4338)) ∨ (meaning t m 4869) := by
  have source := ElevenTheory.theory28225 (m.theta 1 2) (m.theta 1 5) (m.theta 1 6)
  exact rule38969 (meaning t m 3371) (meaning t m 4338) (meaning t m 4869) source

theorem rule38970 (p2027 p2707 p3583 p4320 p4344 p5053 : Prop) (h : (¬ p3583) ∨ (¬ p5053) ∨ (¬ p4344) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3583) ∨ (¬ p4320) ∨ (¬ p4344) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial38970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory28226 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7)
  exact rule38970 (meaning t m 2027) (meaning t m 2707) (meaning t m 3583) (meaning t m 4320) (meaning t m 4344) (meaning t m 5053) source

theorem rule38971 (p1984 p2027 p2169 p2707 p3425 p3688 p3873 p4358 : Prop) (h : (¬ p1984) ∨ (¬ p3873) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p3425) ∨ (¬ p3688) ∨ p2169 ∨ (¬ p4358)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2707) ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial38971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory28227 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 8)
  exact rule38971 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2707) (meaning t m 3425) (meaning t m 3688) (meaning t m 3873) (meaning t m 4358) source

theorem rule38973 (p2027 p2449 p2737 p2807 p2811 p3055 p3238 p3951 p4030 p4734 p4948 : Prop) (h : (¬ p3951) ∨ (¬ p4030) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p3238) ∨ (¬ p4948) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3951) ∨ (¬ p4030) ∨ (¬ p4734) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial38973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory28229 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 9)
  exact rule38973 (meaning t m 2027) (meaning t m 2449) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3055) (meaning t m 3238) (meaning t m 3951) (meaning t m 4030) (meaning t m 4734) (meaning t m 4948) source

theorem rule38977 (p2027 p2427 p2881 p3551 p4533 p4984 : Prop) (h : (¬ p2881) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p4984) ∨ (¬ p4533) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4533) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial38977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4533)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory28233 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule38977 (meaning t m 2027) (meaning t m 2427) (meaning t m 2881) (meaning t m 3551) (meaning t m 4533) (meaning t m 4984) source

theorem rule38980 (p2027 p2274 p2313 p3365 p3366 p3537 p3609 p3645 p3744 p4198 p4243 p4604 p5052 : Prop) (h : (¬ p2313) ∨ (¬ p3645) ∨ (¬ p2274) ∨ (¬ p4604) ∨ (¬ p4243) ∨ (¬ p5052) ∨ (¬ p4198) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3365) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3645) ∨ (¬ p3744) ∨ (¬ p4198) ∨ (¬ p4243) ∨ (¬ p4604) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial38980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28236 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule38980 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 3365) (meaning t m 3366) (meaning t m 3537) (meaning t m 3609) (meaning t m 3645) (meaning t m 3744) (meaning t m 4198) (meaning t m 4243) (meaning t m 4604) (meaning t m 5052) source

theorem rule38981 (p2027 p2295 p2387 p2667 p3527 p4138 p5145 : Prop) (h : (¬ p2295) ∨ (¬ p4138) ∨ (¬ p2667) ∨ (¬ p2387) ∨ (¬ p5145) ∨ p2027 ∨ (¬ p3527)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p3527) ∨ (¬ p4138) ∨ (¬ p5145) := by
  classical
  tauto

theorem initial38981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5145)) := by
  have source := ElevenTheory.theory28237 t (m.theta 0 6) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule38981 (meaning t m 2027) (meaning t m 2295) (meaning t m 2387) (meaning t m 2667) (meaning t m 3527) (meaning t m 4138) (meaning t m 5145) source

theorem rule38982 (p2027 p2313 p3365 p3366 p3537 p3645 p3690 p4019 p4140 p4198 p4243 p4381 p5052 p5119 : Prop) (h : (¬ p3645) ∨ (¬ p4140) ∨ (¬ p5052) ∨ (¬ p3690) ∨ (¬ p4198) ∨ (¬ p3366) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p4243) ∨ (¬ p3365) ∨ (¬ p3537) ∨ (¬ p2313) ∨ (¬ p4019) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2313) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3645) ∨ (¬ p3690) ∨ (¬ p4019) ∨ (¬ p4140) ∨ (¬ p4198) ∨ (¬ p4243) ∨ (¬ p4381) ∨ (¬ p5052) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial38982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5052)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory28238 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 8) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule38982 (meaning t m 2027) (meaning t m 2313) (meaning t m 3365) (meaning t m 3366) (meaning t m 3537) (meaning t m 3645) (meaning t m 3690) (meaning t m 4019) (meaning t m 4140) (meaning t m 4198) (meaning t m 4243) (meaning t m 4381) (meaning t m 5052) (meaning t m 5119) source

theorem rule38983 (p2027 p2753 p2761 p3333 p3365 p3367 p3645 p4032 p4243 p4322 p4638 p5052 : Prop) (h : (¬ p3333) ∨ (¬ p4032) ∨ (¬ p3645) ∨ (¬ p3365) ∨ (¬ p4243) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p2761) ∨ p2753 ∨ (¬ p4638) ∨ (¬ p5052) ∨ (¬ p3367)) : (p2027) ∨ (p2753) ∨ (¬ p2761) ∨ (¬ p3333) ∨ (¬ p3365) ∨ (¬ p3367) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4243) ∨ (¬ p4322) ∨ (¬ p4638) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial38983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (meaning t m 2753) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28239 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 9) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule38983 (meaning t m 2027) (meaning t m 2753) (meaning t m 2761) (meaning t m 3333) (meaning t m 3365) (meaning t m 3367) (meaning t m 3645) (meaning t m 4032) (meaning t m 4243) (meaning t m 4322) (meaning t m 4638) (meaning t m 5052) source

theorem rule38984 (p2027 p2406 p2579 p2742 p3471 p3660 p3905 p4281 p4782 : Prop) (h : (¬ p2579) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p4281) ∨ (¬ p2406) ∨ (¬ p2742) ∨ (¬ p3660) ∨ (¬ p3471) ∨ (¬ p4782)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2579) ∨ (¬ p2742) ∨ (¬ p3471) ∨ (¬ p3660) ∨ (¬ p3905) ∨ (¬ p4281) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial38984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory28240 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 7) (m.theta 4 5) (m.theta 4 6)
  exact rule38984 (meaning t m 2027) (meaning t m 2406) (meaning t m 2579) (meaning t m 2742) (meaning t m 3471) (meaning t m 3660) (meaning t m 3905) (meaning t m 4281) (meaning t m 4782) source

theorem rule38985 (p2027 p2476 p2717 p3389 p4383 p5087 : Prop) (h : (¬ p2717) ∨ (¬ p4383) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p5087) ∨ p2027) : (p2027) ∨ (¬ p2476) ∨ (¬ p2717) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p5087) := by
  classical
  tauto

theorem initial38985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5087)) := by
  have source := ElevenTheory.theory28241 t (m.theta 0 4) (m.theta 2 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule38985 (meaning t m 2027) (meaning t m 2476) (meaning t m 2717) (meaning t m 3389) (meaning t m 4383) (meaning t m 5087) source

theorem rule38988 (p2027 p2717 p2901 p3497 p4132 p4898 : Prop) (h : (¬ p4898) ∨ (¬ p4132) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p4132) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial38988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory28244 t (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule38988 (meaning t m 2027) (meaning t m 2717) (meaning t m 2901) (meaning t m 3497) (meaning t m 4132) (meaning t m 4898) source

theorem rule38989 (p3985 p4744 p4861 : Prop) (h : (¬ p3985) ∨ (¬ p4861) ∨ p4744) : (¬ p3985) ∨ (p4744) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial38989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3985)) ∨ (meaning t m 4744) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory28245 (m.theta 2 5) (m.theta 2 6) (m.theta 2 8)
  exact rule38989 (meaning t m 3985) (meaning t m 4744) (meaning t m 4861) source

theorem rule38991 (p2027 p2248 p3166 p3256 p3688 p3692 p3954 p4138 p4358 p4902 : Prop) (h : (¬ p3256) ∨ (¬ p4902) ∨ (¬ p3954) ∨ (¬ p3166) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4138) ∨ (¬ p3688) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2248) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3688) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial38991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28247 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 8) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38991 (meaning t m 2027) (meaning t m 2248) (meaning t m 3166) (meaning t m 3256) (meaning t m 3688) (meaning t m 3692) (meaning t m 3954) (meaning t m 4138) (meaning t m 4358) (meaning t m 4902) source

theorem rule38993 (p3690 p3692 p4119 p4443 : Prop) (h : (¬ p4119) ∨ (¬ p3692) ∨ (¬ p4443) ∨ p3690) : (p3690) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial38993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3690) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory28249 (m.theta 5 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38993 (meaning t m 3690) (meaning t m 3692) (meaning t m 4119) (meaning t m 4443) source

theorem rule38995 (p2027 p3497 p3609 p3692 p4744 p5053 : Prop) (h : (¬ p3609) ∨ (¬ p4744) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p5053) ∨ (¬ p3497)) : (p2027) ∨ (¬ p3497) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p4744) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial38995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory28251 t (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule38995 (meaning t m 2027) (meaning t m 3497) (meaning t m 3609) (meaning t m 3692) (meaning t m 4744) (meaning t m 5053) source

theorem rule38997 (p2027 p2717 p3551 p3587 p3758 p4283 p4558 : Prop) (h : (¬ p4283) ∨ (¬ p3587) ∨ (¬ p3758) ∨ (¬ p4558) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3587) ∨ (¬ p3758) ∨ (¬ p4283) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial38997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory28253 t (m.theta 0 7) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule38997 (meaning t m 2027) (meaning t m 2717) (meaning t m 3551) (meaning t m 3587) (meaning t m 3758) (meaning t m 4283) (meaning t m 4558) source

theorem rule39002 (p1980 p2027 p2323 p2352 p2651 p3016 p3324 : Prop) (h : (¬ p2352) ∨ (¬ p3324) ∨ (¬ p1980) ∨ p2027 ∨ p2323 ∨ (¬ p2651) ∨ (¬ p3016)) : (¬ p1980) ∨ (p2027) ∨ (p2323) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial39002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory28258 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule39002 (meaning t m 1980) (meaning t m 2027) (meaning t m 2323) (meaning t m 2352) (meaning t m 2651) (meaning t m 3016) (meaning t m 3324) source

theorem rule39005 (p2027 p2132 p2707 p2743 p3425 p5052 : Prop) (h : (¬ p2132) ∨ (¬ p3425) ∨ (¬ p5052) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial39005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28261 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule39005 (meaning t m 2027) (meaning t m 2132) (meaning t m 2707) (meaning t m 2743) (meaning t m 3425) (meaning t m 5052) source

theorem rule39010 (p3986 p4718 p4973 : Prop) (h : (¬ p3986) ∨ (¬ p4718) ∨ p4973) : (¬ p3986) ∨ (¬ p4718) ∨ (p4973) := by
  classical
  tauto

theorem initial39010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4718)) ∨ (meaning t m 4973) := by
  have source := ElevenTheory.theory28266 t (m.theta 3 6) (m.theta 4 6) (m.theta 5 6)
  exact rule39010 (meaning t m 3986) (meaning t m 4718) (meaning t m 4973) source

theorem rule39012 (p2027 p2299 p2319 p2341 p2748 p2779 p2829 p3365 p3742 p4111 p4712 p4734 : Prop) (h : (¬ p4734) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p2779) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p3365) ∨ (¬ p2829) ∨ (¬ p2748) ∨ (¬ p2319) ∨ (¬ p2299) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p2779) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4111) ∨ (¬ p4712) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28268 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39012 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2748) (meaning t m 2779) (meaning t m 2829) (meaning t m 3365) (meaning t m 3742) (meaning t m 4111) (meaning t m 4712) (meaning t m 4734) source

theorem rule39014 (p2027 p2870 p3758 p3989 p4140 p4501 : Prop) (h : (¬ p4140) ∨ (¬ p3989) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4140) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial39014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory28270 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule39014 (meaning t m 2027) (meaning t m 2870) (meaning t m 3758) (meaning t m 3989) (meaning t m 4140) (meaning t m 4501) source

theorem rule39015 (p2027 p2143 p2459 p2819 p2829 p3365 p3366 p3556 p3692 p4119 p4133 p5052 : Prop) (h : (¬ p3365) ∨ (¬ p4119) ∨ (¬ p3692) ∨ (¬ p2829) ∨ (¬ p2819) ∨ (¬ p4133) ∨ (¬ p2143) ∨ (¬ p5052) ∨ (¬ p2459) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3366)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2459) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4133) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial39015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28271 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39015 (meaning t m 2027) (meaning t m 2143) (meaning t m 2459) (meaning t m 2819) (meaning t m 2829) (meaning t m 3365) (meaning t m 3366) (meaning t m 3556) (meaning t m 3692) (meaning t m 4119) (meaning t m 4133) (meaning t m 5052) source

theorem rule39016 (p2027 p2383 p3125 p3585 p3954 p3989 p5017 p5160 p5325 : Prop) (h : (¬ p3954) ∨ (¬ p5325) ∨ (¬ p3125) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p5017) ∨ (¬ p5160) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3125) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p5017) ∨ (¬ p5160) ∨ (¬ p5325) := by
  classical
  tauto

theorem initial39016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5325)) := by
  have source := ElevenTheory.theory28272 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule39016 (meaning t m 2027) (meaning t m 2383) (meaning t m 3125) (meaning t m 3585) (meaning t m 3954) (meaning t m 3989) (meaning t m 5017) (meaning t m 5160) (meaning t m 5325) source

theorem rule39017 (p2027 p2608 p2761 p2829 p3346 p3483 p4425 p4621 p5193 : Prop) (h : (¬ p4425) ∨ (¬ p3346) ∨ (¬ p2761) ∨ (¬ p4621) ∨ (¬ p5193) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3483)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p2829) ∨ (¬ p3346) ∨ (¬ p3483) ∨ (¬ p4425) ∨ (¬ p4621) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28273 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule39017 (meaning t m 2027) (meaning t m 2608) (meaning t m 2761) (meaning t m 2829) (meaning t m 3346) (meaning t m 3483) (meaning t m 4425) (meaning t m 4621) (meaning t m 5193) source

theorem rule39021 (p1992 p2027 p2427 p2765 p3363 p3556 p3585 p3904 p4110 : Prop) (h : (¬ p1992) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p3585) ∨ (¬ p3363) ∨ p2765 ∨ (¬ p4110) ∨ (¬ p3904)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3363) ∨ (¬ p3556) ∨ (¬ p3585) ∨ (¬ p3904) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial39021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory28277 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule39021 (meaning t m 1992) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 3363) (meaning t m 3556) (meaning t m 3585) (meaning t m 3904) (meaning t m 4110) source

theorem rule39023 (p2027 p2982 p3707 p4386 p4388 p4429 p4702 p5284 : Prop) (h : p2027 ∨ (¬ p4388) ∨ (¬ p3707) ∨ (¬ p2982) ∨ (¬ p4429) ∨ (¬ p4702) ∨ (¬ p5284) ∨ (¬ p4386)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3707) ∨ (¬ p4386) ∨ (¬ p4388) ∨ (¬ p4429) ∨ (¬ p4702) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial39023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4386)) ∨ (¬ (meaning t m 4388)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4702)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory28279 t (m.theta 1 9) (m.theta 3 5) (m.theta 3 7) (m.theta 3 9) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule39023 (meaning t m 2027) (meaning t m 2982) (meaning t m 3707) (meaning t m 4386) (meaning t m 4388) (meaning t m 4429) (meaning t m 4702) (meaning t m 5284) source

theorem rule39024 (p2027 p2579 p2608 p3537 p3609 p3956 p5118 p5193 p5580 : Prop) (h : (¬ p3537) ∨ (¬ p2579) ∨ (¬ p3609) ∨ (¬ p2608) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p3956) ∨ (¬ p5193)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3956) ∨ (¬ p5118) ∨ (¬ p5193) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28280 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule39024 (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 3537) (meaning t m 3609) (meaning t m 3956) (meaning t m 5118) (meaning t m 5193) (meaning t m 5580) source

theorem rule39025 (p2027 p2459 p2911 p3389 p3583 p3954 p4385 p5059 p5190 : Prop) (h : p2027 ∨ (¬ p3389) ∨ (¬ p5059) ∨ (¬ p5190) ∨ (¬ p3583) ∨ (¬ p2911) ∨ (¬ p2459) ∨ (¬ p3954) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p5059) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial39025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory28281 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule39025 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3389) (meaning t m 3583) (meaning t m 3954) (meaning t m 4385) (meaning t m 5059) (meaning t m 5190) source

theorem rule39028 (p2027 p2299 p2373 p2598 p2850 p3549 p3591 p4733 p4902 : Prop) (h : (¬ p2373) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p4902) ∨ (¬ p2598) ∨ (¬ p4733) ∨ (¬ p2299) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28284 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule39028 (meaning t m 2027) (meaning t m 2299) (meaning t m 2373) (meaning t m 2598) (meaning t m 2850) (meaning t m 3549) (meaning t m 3591) (meaning t m 4733) (meaning t m 4902) source

theorem rule39029 (p2027 p2373 p2459 p2598 p2850 p3860 p4261 p4733 p4902 : Prop) (h : p2027 ∨ (¬ p2598) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p4902) ∨ (¬ p4733) ∨ (¬ p3860) ∨ (¬ p2850) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4733) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28285 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39029 (meaning t m 2027) (meaning t m 2373) (meaning t m 2459) (meaning t m 2598) (meaning t m 2850) (meaning t m 3860) (meaning t m 4261) (meaning t m 4733) (meaning t m 4902) source

theorem rule39032 (p2027 p2331 p3063 p3172 p4761 p4769 : Prop) (h : (¬ p3063) ∨ (¬ p4769) ∨ (¬ p4761) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p3063) ∨ (¬ p3172) ∨ (¬ p4761) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial39032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4761)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory28288 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule39032 (meaning t m 2027) (meaning t m 2331) (meaning t m 3063) (meaning t m 3172) (meaning t m 4761) (meaning t m 4769) source

theorem rule39033 (p2027 p2143 p2299 p3097 p3365 p3434 p3471 p3646 p4668 p5052 : Prop) (h : (¬ p3471) ∨ (¬ p3646) ∨ (¬ p2299) ∨ (¬ p2143) ∨ (¬ p5052) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p4668) ∨ (¬ p3365) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3646) ∨ (¬ p4668) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial39033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28289 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39033 (meaning t m 2027) (meaning t m 2143) (meaning t m 2299) (meaning t m 3097) (meaning t m 3365) (meaning t m 3434) (meaning t m 3471) (meaning t m 3646) (meaning t m 4668) (meaning t m 5052) source

theorem rule39038 (p1984 p2027 p2245 p2355 p2449 p2657 p2727 p3031 p3817 : Prop) (h : (¬ p2245) ∨ (¬ p1984) ∨ (¬ p3031) ∨ p2027 ∨ p2355 ∨ (¬ p2727) ∨ (¬ p2657) ∨ (¬ p2449) ∨ (¬ p3817)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (p2355) ∨ (¬ p2449) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial39038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory28294 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule39038 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2355) (meaning t m 2449) (meaning t m 2657) (meaning t m 2727) (meaning t m 3031) (meaning t m 3817) source

theorem rule39043 (p1982 p2027 p2264 p2388 p2459 p3027 p3662 : Prop) (h : p2388 ∨ (¬ p3662) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2459) ∨ (¬ p2264)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2264) ∨ (p2388) ∨ (¬ p2459) ∨ (¬ p3027) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial39043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory28299 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39043 (meaning t m 1982) (meaning t m 2027) (meaning t m 2264) (meaning t m 2388) (meaning t m 2459) (meaning t m 3027) (meaning t m 3662) source

theorem rule39044 (p2027 p2132 p2274 p2860 p2911 p3548 p4366 p4712 p4733 : Prop) (h : (¬ p3548) ∨ (¬ p2911) ∨ (¬ p4712) ∨ (¬ p2132) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p4366) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2860) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4712) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28300 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule39044 (meaning t m 2027) (meaning t m 2132) (meaning t m 2274) (meaning t m 2860) (meaning t m 2911) (meaning t m 3548) (meaning t m 4366) (meaning t m 4712) (meaning t m 4733) source

theorem rule39050 (p2027 p2563 p3256 p3365 p3366 p3537 p3645 p3646 p4030 p4202 p4752 p4948 p4967 p5059 : Prop) (h : (¬ p4030) ∨ (¬ p4752) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3256) ∨ (¬ p3537) ∨ (¬ p4967) ∨ (¬ p5059) ∨ (¬ p4202) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p3645) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3537) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4752) ∨ (¬ p4948) ∨ (¬ p4967) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial39050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 4967)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory28306 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule39050 (meaning t m 2027) (meaning t m 2563) (meaning t m 3256) (meaning t m 3365) (meaning t m 3366) (meaning t m 3537) (meaning t m 3645) (meaning t m 3646) (meaning t m 4030) (meaning t m 4202) (meaning t m 4752) (meaning t m 4948) (meaning t m 4967) (meaning t m 5059) source

theorem rule39051 (p2027 p3365 p3434 p3461 p3471 p3645 p3646 p4030 p4202 p4205 p4322 p4625 p4752 : Prop) (h : (¬ p3434) ∨ (¬ p4205) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4202) ∨ (¬ p3645) ∨ (¬ p3365) ∨ (¬ p4752) ∨ (¬ p4030) ∨ (¬ p4322) ∨ (¬ p3461) ∨ (¬ p3646) ∨ (¬ p4625)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3434) ∨ (¬ p3461) ∨ (¬ p3471) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4030) ∨ (¬ p4202) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p4625) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial39051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4205)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory28307 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule39051 (meaning t m 2027) (meaning t m 3365) (meaning t m 3434) (meaning t m 3461) (meaning t m 3471) (meaning t m 3645) (meaning t m 3646) (meaning t m 4030) (meaning t m 4202) (meaning t m 4205) (meaning t m 4322) (meaning t m 4625) (meaning t m 4752) source

theorem rule39053 (p2027 p2143 p2743 p3319 p3946 p4198 p4869 p5052 : Prop) (h : (¬ p3946) ∨ (¬ p4198) ∨ (¬ p5052) ∨ (¬ p4869) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3319) ∨ (¬ p2143)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2743) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4869) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial39053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory28309 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 9)
  exact rule39053 (meaning t m 2027) (meaning t m 2143) (meaning t m 2743) (meaning t m 3319) (meaning t m 3946) (meaning t m 4198) (meaning t m 4869) (meaning t m 5052) source

theorem rule39055 (p1999 p2027 p2622 p2743 p3367 p3422 p3564 : Prop) (h : (¬ p1999) ∨ (¬ p3422) ∨ p2622 ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2743) ∨ (¬ p3564)) : (¬ p1999) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial39055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory28311 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9)
  exact rule39055 (meaning t m 1999) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3422) (meaning t m 3564) source

theorem rule39056 (p2027 p2284 p2313 p2553 p2577 p2696 p3136 p3660 p3880 p4507 p4729 : Prop) (h : (¬ p3136) ∨ (¬ p2696) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4729) ∨ (¬ p2553) ∨ (¬ p2313) ∨ (¬ p3660) ∨ (¬ p2577) ∨ (¬ p4507)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3660) ∨ (¬ p3880) ∨ (¬ p4507) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial39056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4507)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory28312 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule39056 (meaning t m 2027) (meaning t m 2284) (meaning t m 2313) (meaning t m 2553) (meaning t m 2577) (meaning t m 2696) (meaning t m 3136) (meaning t m 3660) (meaning t m 3880) (meaning t m 4507) (meaning t m 4729) source

theorem rule39057 (p2027 p2088 p2137 p2839 p2928 p3055 p3644 p3692 p4030 p4238 p4734 p4902 : Prop) (h : (¬ p4238) ∨ (¬ p4030) ∨ (¬ p2088) ∨ (¬ p3644) ∨ (¬ p3692) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p4902) ∨ (¬ p3055) ∨ (¬ p2839) ∨ (¬ p2137) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p3644) ∨ (¬ p3692) ∨ (¬ p4030) ∨ (¬ p4238) ∨ (¬ p4734) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial39057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory28313 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 8) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39057 (meaning t m 2027) (meaning t m 2088) (meaning t m 2137) (meaning t m 2839) (meaning t m 2928) (meaning t m 3055) (meaning t m 3644) (meaning t m 3692) (meaning t m 4030) (meaning t m 4238) (meaning t m 4734) (meaning t m 4902) source

theorem rule39058 (p2027 p2299 p2717 p2753 p3379 p3471 p3486 p3555 p4559 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4559) ∨ (¬ p3471) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3379) ∨ (¬ p3471) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4559) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28314 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39058 (meaning t m 2027) (meaning t m 2299) (meaning t m 2717) (meaning t m 2753) (meaning t m 3379) (meaning t m 3471) (meaning t m 3486) (meaning t m 3555) (meaning t m 4559) (meaning t m 5216) source

theorem rule39059 (p2749 p3859 p5316 : Prop) (h : (¬ p2749) ∨ (¬ p3859) ∨ p5316) : (¬ p2749) ∨ (¬ p3859) ∨ (p5316) := by
  classical
  tauto

theorem initial39059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3859)) ∨ (meaning t m 5316) := by
  have source := ElevenTheory.theory28315 (m.theta 1 2) (m.theta 1 3) (m.theta 1 8)
  exact rule39059 (meaning t m 2749) (meaning t m 3859) (meaning t m 5316) source

theorem rule39062 (p2027 p2098 p2313 p2553 p2787 p3609 p3692 p3956 p4433 : Prop) (h : (¬ p2787) ∨ (¬ p3609) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2098) ∨ (¬ p3692) ∨ (¬ p2313) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2787) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial39062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory28318 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule39062 (meaning t m 2027) (meaning t m 2098) (meaning t m 2313) (meaning t m 2553) (meaning t m 2787) (meaning t m 3609) (meaning t m 3692) (meaning t m 3956) (meaning t m 4433) source

theorem rule39063 (p2027 p2246 p2749 p2870 p2946 p3246 p3379 p3548 p4316 p4366 p4668 p5216 : Prop) (h : (¬ p2870) ∨ (¬ p4316) ∨ (¬ p2749) ∨ (¬ p5216) ∨ (¬ p3379) ∨ (¬ p3246) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p2946) ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2749) ∨ (¬ p2870) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4316) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28319 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39063 (meaning t m 2027) (meaning t m 2246) (meaning t m 2749) (meaning t m 2870) (meaning t m 2946) (meaning t m 3246) (meaning t m 3379) (meaning t m 3548) (meaning t m 4316) (meaning t m 4366) (meaning t m 4668) (meaning t m 5216) source

theorem rule39065 (p2027 p2589 p2753 p2774 p2819 p3347 p3979 p4322 p4948 p5119 p5216 : Prop) (h : (¬ p2819) ∨ (¬ p3979) ∨ (¬ p3347) ∨ (¬ p4948) ∨ (¬ p5216) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2774) ∨ (¬ p5119) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3347) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4948) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28321 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39065 (meaning t m 2027) (meaning t m 2589) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3347) (meaning t m 3979) (meaning t m 4322) (meaning t m 4948) (meaning t m 5119) (meaning t m 5216) source

theorem rule39068 (p2027 p2753 p2774 p2819 p3379 p3834 p3979 p4321 p5119 p5216 : Prop) (h : (¬ p2774) ∨ (¬ p2819) ∨ (¬ p2753) ∨ (¬ p3979) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3379) ∨ (¬ p4321) ∨ (¬ p3834)) : (p2027) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p3979) ∨ (¬ p4321) ∨ (¬ p5119) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28324 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39068 (meaning t m 2027) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3379) (meaning t m 3834) (meaning t m 3979) (meaning t m 4321) (meaning t m 5119) (meaning t m 5216) source

theorem rule39069 (p2027 p2246 p2498 p2749 p3166 p3256 p3379 p3591 p3692 p3956 p4433 p5216 : Prop) (h : p2027 ∨ (¬ p3166) ∨ (¬ p3379) ∨ (¬ p2749) ∨ (¬ p5216) ∨ (¬ p2246) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p2498) ∨ (¬ p4433) ∨ (¬ p3591) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2498) ∨ (¬ p2749) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial39069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory28325 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39069 (meaning t m 2027) (meaning t m 2246) (meaning t m 2498) (meaning t m 2749) (meaning t m 3166) (meaning t m 3256) (meaning t m 3379) (meaning t m 3591) (meaning t m 3692) (meaning t m 3956) (meaning t m 4433) (meaning t m 5216) source

theorem rule39072 (p2027 p2104 p2247 p2363 p2518 p2744 p3366 p3379 p4340 p4596 : Prop) (h : (¬ p2518) ∨ (¬ p2104) ∨ (¬ p3379) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2744) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4596)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4340) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial39072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory28328 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 8) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39072 (meaning t m 2027) (meaning t m 2104) (meaning t m 2247) (meaning t m 2363) (meaning t m 2518) (meaning t m 2744) (meaning t m 3366) (meaning t m 3379) (meaning t m 4340) (meaning t m 4596) source

theorem rule39073 (p3483 p3744 p4428 : Prop) (h : (¬ p3483) ∨ (¬ p4428) ∨ (¬ p3744)) : (¬ p3483) ∨ (¬ p3744) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial39073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory28329 (m.theta 2 6) (m.theta 5 6) (m.theta 6 9)
  exact rule39073 (meaning t m 3483) (meaning t m 3744) (meaning t m 4428) source

theorem rule39074 (p2027 p2136 p2246 p2363 p2417 p2437 p2651 p2744 p3366 p3646 p3657 p3692 p3988 p4503 : Prop) (h : (¬ p2651) ∨ (¬ p3988) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3692) ∨ (¬ p2136) ∨ (¬ p3646) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2744) ∨ (¬ p4503) ∨ (¬ p2363) ∨ (¬ p3657)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3646) ∨ (¬ p3657) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial39074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory28330 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39074 (meaning t m 2027) (meaning t m 2136) (meaning t m 2246) (meaning t m 2363) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2744) (meaning t m 3366) (meaning t m 3646) (meaning t m 3657) (meaning t m 3692) (meaning t m 3988) (meaning t m 4503) source

theorem rule39075 (p2027 p2136 p2246 p2417 p2437 p2651 p2744 p3366 p3646 p3950 p3989 p4347 : Prop) (h : (¬ p2651) ∨ (¬ p3950) ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p2136) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2744) ∨ (¬ p3646) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial39075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory28331 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39075 (meaning t m 2027) (meaning t m 2136) (meaning t m 2246) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2744) (meaning t m 3366) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) source

theorem rule39078 (p2027 p2651 p2780 p3276 p3343 p4358 p4786 p5123 p5580 : Prop) (h : (¬ p2780) ∨ (¬ p4358) ∨ (¬ p5580) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p2651) ∨ (¬ p3343) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4358) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28334 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39078 (meaning t m 2027) (meaning t m 2651) (meaning t m 2780) (meaning t m 3276) (meaning t m 3343) (meaning t m 4358) (meaning t m 4786) (meaning t m 5123) (meaning t m 5580) source

theorem rule39079 (p2027 p2210 p2437 p2630 p2696 p2753 p3549 p3591 p4276 p4877 : Prop) (h : (¬ p4877) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4276) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p2210) ∨ (¬ p3549) ∨ (¬ p2437) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4276) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial39079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory28335 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7)
  exact rule39079 (meaning t m 2027) (meaning t m 2210) (meaning t m 2437) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 3549) (meaning t m 3591) (meaning t m 4276) (meaning t m 4877) source

theorem rule39080 (p2027 p2138 p2651 p3276 p3343 p3694 p4786 p5123 p5568 : Prop) (h : (¬ p3694) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p2138) ∨ (¬ p4786) ∨ (¬ p2651) ∨ (¬ p5568) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3694) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial39080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory28336 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39080 (meaning t m 2027) (meaning t m 2138) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 3694) (meaning t m 4786) (meaning t m 5123) (meaning t m 5568) source

theorem rule39085 (p2027 p2138 p2192 p3371 p3758 p4734 : Prop) (h : (¬ p2192) ∨ (¬ p3371) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2192) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28341 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule39085 (meaning t m 2027) (meaning t m 2138) (meaning t m 2192) (meaning t m 3371) (meaning t m 3758) (meaning t m 4734) source

theorem rule39086 (p2027 p2248 p2352 p2651 p3016 p3097 p3555 p4173 p4405 : Prop) (h : (¬ p4173) ∨ (¬ p2352) ∨ (¬ p3555) ∨ (¬ p3097) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p4405) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial39086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory28342 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39086 (meaning t m 2027) (meaning t m 2248) (meaning t m 2352) (meaning t m 2651) (meaning t m 3016) (meaning t m 3097) (meaning t m 3555) (meaning t m 4173) (meaning t m 4405) source

theorem rule39096 (p2010 p2027 p2622 p2717 p3365 p3471 p3644 : Prop) (h : (¬ p2717) ∨ p2622 ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p3644) ∨ (¬ p2010)) : (¬ p2010) ∨ (p2027) ∨ (p2622) ∨ (¬ p2717) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial39096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory28352 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule39096 (meaning t m 2010) (meaning t m 2027) (meaning t m 2622) (meaning t m 2717) (meaning t m 3365) (meaning t m 3471) (meaning t m 3644) source

theorem rule39100 (p2027 p2396 p2881 p3644 p3690 p4276 : Prop) (h : (¬ p4276) ∨ (¬ p2396) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p3690) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial39100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory28356 t (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39100 (meaning t m 2027) (meaning t m 2396) (meaning t m 2881) (meaning t m 3644) (meaning t m 3690) (meaning t m 4276) source

theorem rule39102 (p2027 p2248 p2651 p3276 p3343 p3549 p3591 p4260 p4831 : Prop) (h : p2027 ∨ (¬ p3549) ∨ (¬ p3343) ∨ (¬ p4831) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3276) ∨ (¬ p4260) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial39102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory28358 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule39102 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 3549) (meaning t m 3591) (meaning t m 4260) (meaning t m 4831) source

theorem rule39103 (p2027 p2589 p3333 p3389 p3876 p4953 : Prop) (h : (¬ p4953) ∨ (¬ p2589) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p3333) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3333) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial39103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory28359 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 9)
  exact rule39103 (meaning t m 2027) (meaning t m 2589) (meaning t m 3333) (meaning t m 3389) (meaning t m 3876) (meaning t m 4953) source

theorem rule39109 (p2027 p2248 p2264 p2807 p3570 p3688 p3822 p3954 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p2807) ∨ (¬ p3954) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3570) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial39109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory28365 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39109 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2807) (meaning t m 3570) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) (meaning t m 4556) source

theorem rule39113 (p2005 p2027 p2299 p2766 p3016 p3742 p3921 p4348 : Prop) (h : (¬ p2005) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3921) ∨ p2766 ∨ (¬ p2299) ∨ (¬ p3016)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2299) ∨ (p2766) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28369 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39113 (meaning t m 2005) (meaning t m 2027) (meaning t m 2299) (meaning t m 2766) (meaning t m 3016) (meaning t m 3742) (meaning t m 3921) (meaning t m 4348) source

theorem rule39118 (p1998 p2027 p2220 p2765 p3146 p3646 p4348 : Prop) (h : p2765 ∨ (¬ p4348) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p1998) ∨ (¬ p3646) ∨ (¬ p2220)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2220) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p3646) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28374 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39118 (meaning t m 1998) (meaning t m 2027) (meaning t m 2220) (meaning t m 2765) (meaning t m 3146) (meaning t m 3646) (meaning t m 4348) source

theorem rule39119 (p2027 p2138 p2331 p2668 p2737 p2811 p3146 p4134 p4243 p4261 p4492 p4734 : Prop) (h : (¬ p2138) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3146) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p2811) ∨ (¬ p4243) ∨ (¬ p2737) ∨ (¬ p4134) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4243) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28375 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39119 (meaning t m 2027) (meaning t m 2138) (meaning t m 2331) (meaning t m 2668) (meaning t m 2737) (meaning t m 2811) (meaning t m 3146) (meaning t m 4134) (meaning t m 4243) (meaning t m 4261) (meaning t m 4492) (meaning t m 4734) source

theorem rule39121 (p2027 p2246 p2663 p2751 p2810 p3389 p3742 : Prop) (h : (¬ p2663) ∨ (¬ p2751) ∨ (¬ p3389) ∨ (¬ p2810) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2663) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3389) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial39121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory28377 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule39121 (meaning t m 2027) (meaning t m 2246) (meaning t m 2663) (meaning t m 2751) (meaning t m 2810) (meaning t m 3389) (meaning t m 3742) source

theorem rule39122 (p2027 p2363 p2737 p2780 p3136 p3156 p4024 p4261 p4371 p4433 p4734 : Prop) (h : (¬ p2780) ∨ (¬ p2363) ∨ (¬ p4371) ∨ (¬ p4734) ∨ (¬ p4261) ∨ (¬ p4024) ∨ p2027 ∨ (¬ p4433) ∨ (¬ p3136) ∨ (¬ p2737) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p4024) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p4433) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial39122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory28378 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39122 (meaning t m 2027) (meaning t m 2363) (meaning t m 2737) (meaning t m 2780) (meaning t m 3136) (meaning t m 3156) (meaning t m 4024) (meaning t m 4261) (meaning t m 4371) (meaning t m 4433) (meaning t m 4734) source

theorem rule39125 (p1998 p2027 p2114 p2737 p2811 p3166 p3256 p4348 : Prop) (h : (¬ p4348) ∨ p2027 ∨ (¬ p2811) ∨ (¬ p2737) ∨ (¬ p3256) ∨ p2114 ∨ (¬ p3166) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28381 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39125 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2811) (meaning t m 3166) (meaning t m 3256) (meaning t m 4348) source

theorem rule39132 (p1997 p2027 p2114 p2542 p2573 p3367 p3574 p3759 : Prop) (h : (¬ p3759) ∨ (¬ p3574) ∨ (¬ p2573) ∨ p2027 ∨ p2114 ∨ (¬ p3367) ∨ (¬ p1997) ∨ (¬ p2542)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3574) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial39132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory28388 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule39132 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2542) (meaning t m 2573) (meaning t m 3367) (meaning t m 3574) (meaning t m 3759) source

theorem rule39133 (p2027 p2685 p2696 p2753 p3645 p3646 p3744 p3931 p4191 p4826 p4877 : Prop) (h : (¬ p4191) ∨ (¬ p3645) ∨ p2027 ∨ (¬ p2753) ∨ (¬ p3646) ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p4826) ∨ (¬ p3744) ∨ (¬ p2685) ∨ (¬ p3931)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3931) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial39133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory28389 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule39133 (meaning t m 2027) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3645) (meaning t m 3646) (meaning t m 3744) (meaning t m 3931) (meaning t m 4191) (meaning t m 4826) (meaning t m 4877) source

theorem rule39141 (p2027 p2248 p2417 p2437 p2651 p3461 p3834 p4321 p4625 : Prop) (h : (¬ p2437) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p4321) ∨ (¬ p2417) ∨ (¬ p2248) ∨ (¬ p3461) ∨ (¬ p2651) ∨ (¬ p3834)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3461) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial39141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory28397 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule39141 (meaning t m 2027) (meaning t m 2248) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3461) (meaning t m 3834) (meaning t m 4321) (meaning t m 4625) source

theorem rule39142 (p2027 p2341 p2663 p3553 p3572 p4790 p5201 : Prop) (h : (¬ p2663) ∨ (¬ p3572) ∨ (¬ p4790) ∨ (¬ p5201) ∨ (¬ p2341) ∨ (¬ p3553) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2663) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4790) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial39142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory28398 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule39142 (meaning t m 2027) (meaning t m 2341) (meaning t m 2663) (meaning t m 3553) (meaning t m 3572) (meaning t m 4790) (meaning t m 5201) source

theorem rule39145 (p2027 p2210 p2417 p2598 p2753 p3201 p3548 p4366 p4668 p4877 : Prop) (h : (¬ p3548) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial39145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory28401 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39145 (meaning t m 2027) (meaning t m 2210) (meaning t m 2417) (meaning t m 2598) (meaning t m 2753) (meaning t m 3201) (meaning t m 3548) (meaning t m 4366) (meaning t m 4668) (meaning t m 4877) source

theorem rule39147 (p2027 p2210 p2696 p2753 p3005 p3256 p3817 p4366 p4669 p4877 : Prop) (h : (¬ p4669) ∨ (¬ p2696) ∨ (¬ p4366) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p3256) ∨ (¬ p4877) ∨ (¬ p3005) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial39147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory28403 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39147 (meaning t m 2027) (meaning t m 2210) (meaning t m 2696) (meaning t m 2753) (meaning t m 3005) (meaning t m 3256) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) (meaning t m 4877) source

theorem rule39149 (p2027 p2630 p2696 p3083 p3555 p3989 p4173 p4596 p4733 : Prop) (h : (¬ p3989) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p4733) ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p4596) ∨ (¬ p3083)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial39149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory28405 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule39149 (meaning t m 2027) (meaning t m 2630) (meaning t m 2696) (meaning t m 3083) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) (meaning t m 4596) (meaning t m 4733) source

theorem rule39152 (p2027 p2247 p2387 p2744 p2778 p3366 p3399 p4075 p4347 p4444 p4826 : Prop) (h : (¬ p4347) ∨ (¬ p4826) ∨ (¬ p3399) ∨ (¬ p4075) ∨ p2027 ∨ (¬ p2778) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2247) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory28408 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39152 (meaning t m 2027) (meaning t m 2247) (meaning t m 2387) (meaning t m 2744) (meaning t m 2778) (meaning t m 3366) (meaning t m 3399) (meaning t m 4075) (meaning t m 4347) (meaning t m 4444) (meaning t m 4826) source

theorem rule39159 (p3073 p3542 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3542) ∨ (¬ p3073)) : (¬ p3073) ∨ (¬ p3542) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28415 (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39159 (meaning t m 3073) (meaning t m 3542) (meaning t m 4348) source

theorem rule39160 (p2027 p2810 p2958 p3051 p3486 p3487 p4202 p4790 : Prop) (h : (¬ p4790) ∨ p2027 ∨ (¬ p2810) ∨ (¬ p3487) ∨ (¬ p3051) ∨ (¬ p4202) ∨ (¬ p2958) ∨ (¬ p3486)) : (p2027) ∨ (¬ p2810) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p3487) ∨ (¬ p4202) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial39160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory28416 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 5 7)
  exact rule39160 (meaning t m 2027) (meaning t m 2810) (meaning t m 2958) (meaning t m 3051) (meaning t m 3486) (meaning t m 3487) (meaning t m 4202) (meaning t m 4790) source

theorem rule39164 (p2027 p2608 p2972 p3369 p4032 p4377 : Prop) (h : p2027 ∨ (¬ p3369) ∨ (¬ p4377) ∨ (¬ p2608) ∨ (¬ p2972) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2972) ∨ (¬ p3369) ∨ (¬ p4032) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial39164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory28420 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 9)
  exact rule39164 (meaning t m 2027) (meaning t m 2608) (meaning t m 2972) (meaning t m 3369) (meaning t m 4032) (meaning t m 4377) source

theorem rule39167 (p2027 p2579 p2588 p3073 p3449 p3945 p4107 p4118 p4550 p5193 : Prop) (h : (¬ p4550) ∨ (¬ p3945) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p2588) ∨ (¬ p4118) ∨ (¬ p2579) ∨ (¬ p5193) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3945) ∨ (¬ p4107) ∨ (¬ p4118) ∨ (¬ p4550) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28423 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39167 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3073) (meaning t m 3449) (meaning t m 3945) (meaning t m 4107) (meaning t m 4118) (meaning t m 4550) (meaning t m 5193) source

theorem rule39171 (p2001 p2027 p2177 p2210 p2247 p2462 p2744 p3156 p3366 p3540 p3644 p3905 p4107 p4282 : Prop) (h : p2027 ∨ p2462 ∨ (¬ p4107) ∨ (¬ p2744) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p3644) ∨ (¬ p2210) ∨ (¬ p3905) ∨ (¬ p2001) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p4282) ∨ (¬ p3540)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2462) ∨ (¬ p2744) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial39171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory28427 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39171 (meaning t m 2001) (meaning t m 2027) (meaning t m 2177) (meaning t m 2210) (meaning t m 2247) (meaning t m 2462) (meaning t m 2744) (meaning t m 3156) (meaning t m 3366) (meaning t m 3540) (meaning t m 3644) (meaning t m 3905) (meaning t m 4107) (meaning t m 4282) source

theorem rule39172 (p2027 p2166 p2210 p2247 p2579 p2744 p3366 p3422 p3874 p3905 p4434 : Prop) (h : (¬ p2210) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3874) ∨ (¬ p2166) ∨ (¬ p4434) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3905) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial39172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory28428 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 8)
  exact rule39172 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2579) (meaning t m 2744) (meaning t m 3366) (meaning t m 3422) (meaning t m 3874) (meaning t m 3905) (meaning t m 4434) source

theorem rule39173 (p2027 p2528 p3692 p3988 p4235 p4355 p4555 : Prop) (h : (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p4355) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4235) ∨ (¬ p4355) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial39173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory28429 t (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule39173 (meaning t m 2027) (meaning t m 2528) (meaning t m 3692) (meaning t m 3988) (meaning t m 4235) (meaning t m 4355) (meaning t m 4555) source

theorem rule39175 (p1998 p2027 p2528 p2914 p3641 p3876 p4348 : Prop) (h : (¬ p2528) ∨ p2914 ∨ (¬ p4348) ∨ (¬ p1998) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p3641)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2528) ∨ (p2914) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial39175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory28431 t (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39175 (meaning t m 1998) (meaning t m 2027) (meaning t m 2528) (meaning t m 2914) (meaning t m 3641) (meaning t m 3876) (meaning t m 4348) source

theorem rule39176 (p2027 p2246 p2651 p2744 p2780 p3276 p3343 p3366 p4358 p5123 p5580 : Prop) (h : (¬ p2651) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2744) ∨ (¬ p4358) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p3343) ∨ (¬ p3276) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p4358) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial39176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory28432 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule39176 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 2780) (meaning t m 3276) (meaning t m 3343) (meaning t m 3366) (meaning t m 4358) (meaning t m 5123) (meaning t m 5580) source

theorem rule39185 (p2010 p2027 p2518 p2699 p3201 p3379 p3874 : Prop) (h : p2699 ∨ (¬ p2010) ∨ p2027 ∨ (¬ p2518) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p3874)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2518) ∨ (p2699) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial39185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory28441 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8)
  exact rule39185 (meaning t m 2010) (meaning t m 2027) (meaning t m 2518) (meaning t m 2699) (meaning t m 3201) (meaning t m 3379) (meaning t m 3874) source

theorem rule39187 (p2027 p2579 p2588 p2608 p2737 p3755 p4107 p4658 p5193 : Prop) (h : (¬ p2737) ∨ (¬ p5193) ∨ (¬ p4658) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4107) ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p3755)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4658) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4658)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28443 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule39187 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2608) (meaning t m 2737) (meaning t m 3755) (meaning t m 4107) (meaning t m 4658) (meaning t m 5193) source

theorem rule39192 (p1997 p2027 p2313 p2764 p4107 p4110 p4356 p4381 : Prop) (h : (¬ p1997) ∨ p2764 ∨ (¬ p4381) ∨ (¬ p4356) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4107) ∨ (¬ p2313)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2313) ∨ (p2764) ∨ (¬ p4107) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial39192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory28448 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule39192 (meaning t m 1997) (meaning t m 2027) (meaning t m 2313) (meaning t m 2764) (meaning t m 4107) (meaning t m 4110) (meaning t m 4356) (meaning t m 4381) source

theorem rule39193 (p2027 p2579 p2588 p3073 p3266 p3449 p4260 p4831 p5193 : Prop) (h : (¬ p3449) ∨ (¬ p5193) ∨ (¬ p2579) ∨ (¬ p3266) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p4260) ∨ (¬ p2588) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3266) ∨ (¬ p3449) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28449 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39193 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3073) (meaning t m 3266) (meaning t m 3449) (meaning t m 4260) (meaning t m 4831) (meaning t m 5193) source

theorem rule39194 (p1997 p2027 p2177 p2406 p2928 p2997 p3644 : Prop) (h : (¬ p2177) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2928) ∨ (¬ p1997) ∨ p2997) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2406) ∨ (¬ p2928) ∨ (p2997) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial39194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory28450 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39194 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2406) (meaning t m 2928) (meaning t m 2997) (meaning t m 3644) source

theorem rule39197 (p1990 p2027 p2563 p3128 p3461 p4210 p4363 p5030 p5387 : Prop) (h : (¬ p2563) ∨ (¬ p4363) ∨ p2027 ∨ (¬ p4210) ∨ (¬ p1990) ∨ (¬ p5030) ∨ (¬ p3461) ∨ p3128 ∨ (¬ p5387)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p3128) ∨ (¬ p3461) ∨ (¬ p4210) ∨ (¬ p4363) ∨ (¬ p5030) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial39197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 5030)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory28453 t (m.theta 1 5) (m.theta 2 9) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule39197 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 3128) (meaning t m 3461) (meaning t m 4210) (meaning t m 4363) (meaning t m 5030) (meaning t m 5387) source

theorem rule39199 (p2027 p2137 p3051 p3083 p3698 p4320 p4610 p4700 : Prop) (h : (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4610) ∨ (¬ p3698) ∨ (¬ p2137) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p3083)) : (p2027) ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3083) ∨ (¬ p3698) ∨ (¬ p4320) ∨ (¬ p4610) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial39199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory28455 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7)
  exact rule39199 (meaning t m 2027) (meaning t m 2137) (meaning t m 3051) (meaning t m 3083) (meaning t m 3698) (meaning t m 4320) (meaning t m 4610) (meaning t m 4700) source

theorem rule39200 (p2027 p2104 p2247 p2744 p3037 p3366 p3399 p3931 p4340 p4444 p4826 : Prop) (h : (¬ p3037) ∨ (¬ p4826) ∨ (¬ p3366) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2104) ∨ (¬ p3931) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3931) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory28456 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 8) (m.theta 3 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39200 (meaning t m 2027) (meaning t m 2104) (meaning t m 2247) (meaning t m 2744) (meaning t m 3037) (meaning t m 3366) (meaning t m 3399) (meaning t m 3931) (meaning t m 4340) (meaning t m 4444) (meaning t m 4826) source

theorem rule39201 (p1998 p2027 p2230 p2233 p2264 p2982 p2995 p4208 : Prop) (h : (¬ p2264) ∨ p2233 ∨ (¬ p2995) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4208) ∨ (¬ p2982) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2264) ∨ (¬ p2982) ∨ (¬ p2995) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial39201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory28457 t (m.theta 0 4) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8)
  exact rule39201 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2264) (meaning t m 2982) (meaning t m 2995) (meaning t m 4208) source

theorem rule39203 (p2027 p2139 p2220 p2579 p3256 p3422 p3874 p3905 p4312 p4348 p4438 : Prop) (h : (¬ p4348) ∨ (¬ p3256) ∨ (¬ p3422) ∨ (¬ p2139) ∨ (¬ p4312) ∨ (¬ p2220) ∨ (¬ p3874) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p4438) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3256) ∨ (¬ p3422) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p4312) ∨ (¬ p4348) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial39203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory28459 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39203 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 2579) (meaning t m 3256) (meaning t m 3422) (meaning t m 3874) (meaning t m 3905) (meaning t m 4312) (meaning t m 4348) (meaning t m 4438) source

theorem rule39204 (p2027 p3266 p3440 p3609 p4321 p5313 : Prop) (h : (¬ p3266) ∨ (¬ p4321) ∨ p2027 ∨ (¬ p5313) ∨ (¬ p3440) ∨ (¬ p3609)) : (p2027) ∨ (¬ p3266) ∨ (¬ p3440) ∨ (¬ p3609) ∨ (¬ p4321) ∨ (¬ p5313) := by
  classical
  tauto

theorem initial39204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5313)) := by
  have source := ElevenTheory.theory28460 t (m.theta 1 8) (m.theta 1 9) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule39204 (meaning t m 2027) (meaning t m 3266) (meaning t m 3440) (meaning t m 3609) (meaning t m 4321) (meaning t m 5313) source

theorem rule39206 (p2027 p2542 p2727 p3848 p4949 p5171 : Prop) (h : p2027 ∨ (¬ p2727) ∨ (¬ p2542) ∨ (¬ p5171) ∨ (¬ p4949) ∨ (¬ p3848)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p3848) ∨ (¬ p4949) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial39206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4949)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory28462 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9)
  exact rule39206 (meaning t m 2027) (meaning t m 2542) (meaning t m 2727) (meaning t m 3848) (meaning t m 4949) (meaning t m 5171) source

theorem rule39207 (p2027 p2143 p2449 p2696 p3005 p3556 p3570 p3583 p3919 p4668 p4737 : Prop) (h : p2027 ∨ (¬ p3583) ∨ (¬ p4737) ∨ (¬ p2143) ∨ (¬ p3570) ∨ (¬ p3005) ∨ (¬ p4668) ∨ (¬ p2449) ∨ (¬ p3919) ∨ (¬ p2696) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3919) ∨ (¬ p4668) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial39207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory28463 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39207 (meaning t m 2027) (meaning t m 2143) (meaning t m 2449) (meaning t m 2696) (meaning t m 3005) (meaning t m 3556) (meaning t m 3570) (meaning t m 3583) (meaning t m 3919) (meaning t m 4668) (meaning t m 4737) source

theorem rule39208 (p2027 p2299 p2579 p2588 p2608 p2737 p3005 p4550 p5193 : Prop) (h : (¬ p4550) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2608) ∨ (¬ p5193) ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p4550) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28464 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule39208 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2608) (meaning t m 2737) (meaning t m 3005) (meaning t m 4550) (meaning t m 5193) source

theorem rule39209 (p2027 p2143 p2696 p3005 p3256 p3583 p3646 p3744 p4604 p4737 : Prop) (h : (¬ p2143) ∨ (¬ p3646) ∨ (¬ p4604) ∨ (¬ p3744) ∨ (¬ p3583) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3256) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4604) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial39209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory28465 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule39209 (meaning t m 2027) (meaning t m 2143) (meaning t m 2696) (meaning t m 3005) (meaning t m 3256) (meaning t m 3583) (meaning t m 3646) (meaning t m 3744) (meaning t m 4604) (meaning t m 4737) source

theorem rule39210 (p2027 p2387 p2819 p3985 p4244 p4356 p4555 : Prop) (h : (¬ p4244) ∨ (¬ p4356) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p4555) ∨ (¬ p3985)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p3985) ∨ (¬ p4244) ∨ (¬ p4356) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial39210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory28466 t (m.theta 0 6) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule39210 (meaning t m 2027) (meaning t m 2387) (meaning t m 2819) (meaning t m 3985) (meaning t m 4244) (meaning t m 4356) (meaning t m 4555) source

theorem rule39211 (p1997 p2027 p2542 p2608 p2630 p2699 p2737 : Prop) (h : (¬ p1997) ∨ p2699 ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2542) ∨ (¬ p2608)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2737) := by
  classical
  tauto

theorem initial39211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) := by
  have source := ElevenTheory.theory28467 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule39211 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2608) (meaning t m 2630) (meaning t m 2699) (meaning t m 2737) source

theorem rule39212 (p1994 p2027 p2274 p2578 p2588 p2667 p2727 p2765 p4154 : Prop) (h : p2765 ∨ (¬ p2588) ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p2274) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p2727)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (p2765) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial39212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory28468 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule39212 (meaning t m 1994) (meaning t m 2027) (meaning t m 2274) (meaning t m 2578) (meaning t m 2588) (meaning t m 2667) (meaning t m 2727) (meaning t m 2765) (meaning t m 4154) source

theorem rule39215 (p1994 p2027 p2187 p2387 p2440 p2997 p3097 p4031 p4198 : Prop) (h : (¬ p1994) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p2440) ∨ (¬ p4198) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p2387)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2440) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p4031) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial39215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory28471 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39215 (meaning t m 1994) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2440) (meaning t m 2997) (meaning t m 3097) (meaning t m 4031) (meaning t m 4198) source

theorem rule39216 (p2027 p2960 p3516 p3690 p4320 p4988 : Prop) (h : (¬ p3516) ∨ (¬ p4320) ∨ (¬ p4988) ∨ (¬ p2960) ∨ p2027 ∨ (¬ p3690)) : (p2027) ∨ (¬ p2960) ∨ (¬ p3516) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial39216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory28472 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule39216 (meaning t m 2027) (meaning t m 2960) (meaning t m 3516) (meaning t m 3690) (meaning t m 4320) (meaning t m 4988) source

theorem rule39217 (p1998 p2027 p2264 p2699 p3399 p3631 p3947 : Prop) (h : p2699 ∨ (¬ p3947) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p3399) ∨ (¬ p3631)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial39217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory28473 t (m.theta 0 1) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39217 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2699) (meaning t m 3399) (meaning t m 3631) (meaning t m 3947) source

theorem rule39219 (p2027 p2139 p2534 p3051 p3055 p3115 p3874 p4320 p4450 : Prop) (h : (¬ p4320) ∨ (¬ p3055) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p4450) ∨ (¬ p2139) ∨ (¬ p3115) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2534) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3874) ∨ (¬ p4320) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial39219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory28475 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 9) (m.theta 8 9)
  exact rule39219 (meaning t m 2027) (meaning t m 2139) (meaning t m 2534) (meaning t m 3051) (meaning t m 3055) (meaning t m 3115) (meaning t m 3874) (meaning t m 4320) (meaning t m 4450) source

theorem rule39221 (p2027 p2761 p3055 p3399 p3584 p3631 p4736 p5254 p5514 : Prop) (h : p2027 ∨ (¬ p2761) ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p4736) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p5514) ∨ (¬ p5254)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3055) ∨ (¬ p3399) ∨ (¬ p3584) ∨ (¬ p3631) ∨ (¬ p4736) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial39221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory28477 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule39221 (meaning t m 2027) (meaning t m 2761) (meaning t m 3055) (meaning t m 3399) (meaning t m 3584) (meaning t m 3631) (meaning t m 4736) (meaning t m 5254) (meaning t m 5514) source

theorem rule39222 (p2312 p3821 p4107 : Prop) (h : (¬ p2312) ∨ (¬ p4107) ∨ p3821) : (¬ p2312) ∨ (p3821) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial39222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2312)) ∨ (meaning t m 3821) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory28478 (m.theta 0 7) (m.theta 6 7) (m.theta 7 9)
  exact rule39222 (meaning t m 2312) (meaning t m 3821) (meaning t m 4107) source

theorem rule39225 (p2027 p2579 p2744 p3051 p3115 p3347 p3370 p3956 p4257 p4320 p4347 p4365 p4450 : Prop) (h : (¬ p3051) ∨ (¬ p4320) ∨ (¬ p4257) ∨ (¬ p3347) ∨ (¬ p2744) ∨ (¬ p3370) ∨ (¬ p4365) ∨ (¬ p2579) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3051) ∨ (¬ p3115) ∨ (¬ p3347) ∨ (¬ p3370) ∨ (¬ p3956) ∨ (¬ p4257) ∨ (¬ p4320) ∨ (¬ p4347) ∨ (¬ p4365) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial39225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory28481 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule39225 (meaning t m 2027) (meaning t m 2579) (meaning t m 2744) (meaning t m 3051) (meaning t m 3115) (meaning t m 3347) (meaning t m 3370) (meaning t m 3956) (meaning t m 4257) (meaning t m 4320) (meaning t m 4347) (meaning t m 4365) (meaning t m 4450) source

theorem rule39229 (p2027 p2166 p2210 p2247 p2363 p2744 p2780 p3366 p4078 p4340 p4433 : Prop) (h : (¬ p2210) ∨ (¬ p2166) ∨ (¬ p4340) ∨ (¬ p2363) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p4078) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial39229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory28485 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 2 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39229 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2363) (meaning t m 2744) (meaning t m 2780) (meaning t m 3366) (meaning t m 4078) (meaning t m 4340) (meaning t m 4433) source

theorem rule39230 (p1990 p2027 p2247 p2284 p2688 p3830 p4208 p4387 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p4387) ∨ (¬ p1990) ∨ (¬ p2247) ∨ (¬ p3830) ∨ (¬ p2284) ∨ (¬ p4208)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2284) ∨ (p2688) ∨ (¬ p3830) ∨ (¬ p4208) ∨ (¬ p4387) := by
  classical
  tauto

theorem initial39230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4387)) := by
  have source := ElevenTheory.theory28486 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule39230 (meaning t m 1990) (meaning t m 2027) (meaning t m 2247) (meaning t m 2284) (meaning t m 2688) (meaning t m 3830) (meaning t m 4208) (meaning t m 4387) source

theorem rule39231 (p2027 p2241 p2363 p2780 p2992 p3156 p4078 p4340 p4433 p4736 : Prop) (h : (¬ p2780) ∨ (¬ p3156) ∨ (¬ p4736) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p4340) ∨ (¬ p2363) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p4078)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p2780) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4433) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial39231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28487 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule39231 (meaning t m 2027) (meaning t m 2241) (meaning t m 2363) (meaning t m 2780) (meaning t m 2992) (meaning t m 3156) (meaning t m 4078) (meaning t m 4340) (meaning t m 4433) (meaning t m 4736) source

theorem rule39235 (p2027 p2299 p2579 p2588 p2696 p2743 p3537 p3589 p4802 p5193 : Prop) (h : (¬ p4802) ∨ (¬ p5193) ∨ (¬ p3589) ∨ (¬ p2696) ∨ (¬ p3537) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3589) ∨ (¬ p4802) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4802)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28491 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule39235 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2696) (meaning t m 2743) (meaning t m 3537) (meaning t m 3589) (meaning t m 4802) (meaning t m 5193) source

theorem rule39238 (p2027 p2241 p2264 p2363 p2476 p2534 p3027 p4503 p5193 : Prop) (h : (¬ p2534) ∨ (¬ p2476) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p4503) ∨ (¬ p2264) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3027)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3027) ∨ (¬ p4503) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28494 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39238 (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 3027) (meaning t m 4503) (meaning t m 5193) source

theorem rule39245 (p2027 p2396 p2668 p3947 p4067 p4405 : Prop) (h : (¬ p4067) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p3947) ∨ (¬ p2396) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2668) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial39245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory28501 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule39245 (meaning t m 2027) (meaning t m 2396) (meaning t m 2668) (meaning t m 3947) (meaning t m 4067) (meaning t m 4405) source

theorem rule39246 (p2027 p2122 p2177 p3570 p4204 p4401 : Prop) (h : (¬ p4204) ∨ (¬ p3570) ∨ (¬ p4401) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial39246 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory28502 t (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule39246 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 3570) (meaning t m 4204) (meaning t m 4401) source

theorem rule39247 (p2027 p2210 p2247 p2579 p2744 p2891 p3366 p3422 p3876 p3905 p4647 : Prop) (h : (¬ p2579) ∨ (¬ p4647) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3876) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p2891) ∨ (¬ p3366) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial39247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory28503 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7)
  exact rule39247 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2579) (meaning t m 2744) (meaning t m 2891) (meaning t m 3366) (meaning t m 3422) (meaning t m 3876) (meaning t m 3905) (meaning t m 4647) source

theorem rule39249 (p1994 p2027 p2462 p2578 p2588 p2630 p2667 p4107 p4195 : Prop) (h : (¬ p2578) ∨ p2027 ∨ (¬ p2667) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p2588) ∨ p2462 ∨ (¬ p1994) ∨ (¬ p4107)) : (¬ p1994) ∨ (p2027) ∨ (p2462) ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2630) ∨ (¬ p2667) ∨ (¬ p4107) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial39249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory28505 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule39249 (meaning t m 1994) (meaning t m 2027) (meaning t m 2462) (meaning t m 2578) (meaning t m 2588) (meaning t m 2630) (meaning t m 2667) (meaning t m 4107) (meaning t m 4195) source

theorem rule39251 (p2027 p2210 p2780 p2881 p2891 p3822 p4107 p4666 p4736 : Prop) (h : (¬ p4736) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p4666) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2780) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial39251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory28507 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39251 (meaning t m 2027) (meaning t m 2210) (meaning t m 2780) (meaning t m 2881) (meaning t m 2891) (meaning t m 3822) (meaning t m 4107) (meaning t m 4666) (meaning t m 4736) source

theorem rule39253 (p2027 p2241 p2299 p2449 p2579 p2588 p3027 p4668 p5193 : Prop) (h : (¬ p2588) ∨ (¬ p2579) ∨ (¬ p4668) ∨ (¬ p2299) ∨ (¬ p2449) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3027)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3027) ∨ (¬ p4668) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28509 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39253 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2449) (meaning t m 2579) (meaning t m 2588) (meaning t m 3027) (meaning t m 4668) (meaning t m 5193) source

theorem rule39254 (p2027 p2138 p2247 p2449 p2744 p3037 p3366 p3399 p3692 p3694 p3950 : Prop) (h : (¬ p2449) ∨ (¬ p3399) ∨ (¬ p2247) ∨ (¬ p3037) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p3694) ∨ (¬ p2744) ∨ (¬ p2138) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial39254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory28510 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39254 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2449) (meaning t m 2744) (meaning t m 3037) (meaning t m 3366) (meaning t m 3399) (meaning t m 3692) (meaning t m 3694) (meaning t m 3950) source

theorem rule39257 (p2027 p2139 p2220 p3055 p3256 p3584 p3956 p4312 p4348 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p4312) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p4348) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3055) ∨ (¬ p3256) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4312) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial39257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory28513 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39257 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 3055) (meaning t m 3256) (meaning t m 3584) (meaning t m 3956) (meaning t m 4312) (meaning t m 4348) (meaning t m 4503) source

theorem rule39259 (p1989 p2027 p2387 p2819 p2997 p3822 p4173 p4356 : Prop) (h : (¬ p2387) ∨ p2027 ∨ p2997 ∨ (¬ p4173) ∨ (¬ p1989) ∨ (¬ p3822) ∨ (¬ p4356) ∨ (¬ p2819)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (p2997) ∨ (¬ p3822) ∨ (¬ p4173) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial39259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory28515 t (m.theta 0 6) (m.theta 1 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39259 (meaning t m 1989) (meaning t m 2027) (meaning t m 2387) (meaning t m 2819) (meaning t m 2997) (meaning t m 3822) (meaning t m 4173) (meaning t m 4356) source

theorem rule39264 (p2027 p2088 p2727 p4066 p4261 p4262 p4590 p4650 : Prop) (h : (¬ p4590) ∨ (¬ p4261) ∨ (¬ p2727) ∨ (¬ p4650) ∨ p2027 ∨ (¬ p4066) ∨ (¬ p4262) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2727) ∨ (¬ p4066) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4590) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial39264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory28520 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 7) (m.theta 8 9)
  exact rule39264 (meaning t m 2027) (meaning t m 2088) (meaning t m 2727) (meaning t m 4066) (meaning t m 4261) (meaning t m 4262) (meaning t m 4590) (meaning t m 4650) source

theorem rule39266 (p1994 p2027 p2440 p2764 p3744 p4110 p4191 : Prop) (h : (¬ p2440) ∨ p2764 ∨ (¬ p4191) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p4110)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2764) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial39266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory28522 t (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule39266 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2764) (meaning t m 3744) (meaning t m 4110) (meaning t m 4191) source

theorem rule39271 (p1998 p2027 p2761 p2881 p3434 p3437 p4322 p4402 : Prop) (h : p2027 ∨ (¬ p4402) ∨ (¬ p2761) ∨ (¬ p1998) ∨ p3437 ∨ (¬ p2881) ∨ (¬ p3434) ∨ (¬ p4322)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2761) ∨ (¬ p2881) ∨ (¬ p3434) ∨ (p3437) ∨ (¬ p4322) ∨ (¬ p4402) := by
  classical
  tauto

theorem initial39271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3434)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) := by
  have source := ElevenTheory.theory28527 t (m.theta 2 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule39271 (meaning t m 1998) (meaning t m 2027) (meaning t m 2761) (meaning t m 2881) (meaning t m 3434) (meaning t m 3437) (meaning t m 4322) (meaning t m 4402) source

theorem rule39274 (p3146 p3690 p3747 p4445 : Prop) (h : (¬ p4445) ∨ (¬ p3747) ∨ (¬ p3690) ∨ (¬ p3146)) : (¬ p3146) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p4445) := by
  classical
  tauto

theorem initial39274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4445)) := by
  have source := ElevenTheory.theory28530 (m.theta 5 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39274 (meaning t m 3146) (meaning t m 3690) (meaning t m 3747) (meaning t m 4445) source

theorem rule39276 (p2027 p2241 p3027 p3646 p3744 p3931 p4191 p4524 p4826 : Prop) (h : (¬ p4524) ∨ (¬ p3646) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p2241) ∨ (¬ p3931) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3931) ∨ (¬ p4191) ∨ (¬ p4524) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory28532 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule39276 (meaning t m 2027) (meaning t m 2241) (meaning t m 3027) (meaning t m 3646) (meaning t m 3744) (meaning t m 3931) (meaning t m 4191) (meaning t m 4524) (meaning t m 4826) source

theorem rule39277 (p2027 p2104 p2247 p2744 p3366 p3399 p4075 p4340 p4444 p4826 : Prop) (h : (¬ p3399) ∨ (¬ p2744) ∨ (¬ p4075) ∨ (¬ p3366) ∨ (¬ p4826) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p2104) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p4340) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial39277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory28533 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule39277 (meaning t m 2027) (meaning t m 2104) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 4075) (meaning t m 4340) (meaning t m 4444) (meaning t m 4826) source

theorem rule39280 (p1977 p2027 p2860 p2938 p2957 p3646 p3662 p4244 : Prop) (h : (¬ p3662) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p2957) ∨ p2938 ∨ (¬ p4244) ∨ (¬ p3646) ∨ (¬ p2860)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2860) ∨ (p2938) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial39280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory28536 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule39280 (meaning t m 1977) (meaning t m 2027) (meaning t m 2860) (meaning t m 2938) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) (meaning t m 4244) source

theorem rule39281 (p3547 p4427 : Prop) (h : p3547 ∨ p4427) : (p3547) ∨ (p4427) := by
  classical
  tauto

theorem initial39281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3547) ∨ (meaning t m 4427) := by
  have source := ElevenTheory.theory28537 (m.theta 1 7) (m.theta 6 7)
  exact rule39281 (meaning t m 3547) (meaning t m 4427) source

theorem rule39282 (p2027 p3876 p3914 p4210 p4375 p4435 p4512 p4644 : Prop) (h : (¬ p4210) ∨ (¬ p4512) ∨ (¬ p4435) ∨ (¬ p4644) ∨ (¬ p3914) ∨ (¬ p3876) ∨ (¬ p4375) ∨ p2027) : (p2027) ∨ (¬ p3876) ∨ (¬ p3914) ∨ (¬ p4210) ∨ (¬ p4375) ∨ (¬ p4435) ∨ (¬ p4512) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial39282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory28538 t (m.theta 1 5) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 7) (m.theta 6 10)
  exact rule39282 (meaning t m 2027) (meaning t m 3876) (meaning t m 3914) (meaning t m 4210) (meaning t m 4375) (meaning t m 4435) (meaning t m 4512) (meaning t m 4644) source

theorem rule39285 (p1987 p2027 p2187 p2387 p2957 p2997 p3097 p4198 p4315 : Prop) (h : (¬ p2957) ∨ (¬ p4315) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p4198) ∨ (¬ p2387)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p4198) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial39285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory28541 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39285 (meaning t m 1987) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2957) (meaning t m 2997) (meaning t m 3097) (meaning t m 4198) (meaning t m 4315) source

theorem rule39286 (p2027 p2247 p2589 p2744 p3366 p3695 p3707 p3758 p3830 p3905 p4393 p5254 : Prop) (h : (¬ p2744) ∨ (¬ p4393) ∨ (¬ p2247) ∨ (¬ p5254) ∨ (¬ p3707) ∨ (¬ p3366) ∨ (¬ p3758) ∨ (¬ p2589) ∨ (¬ p3830) ∨ (¬ p3695) ∨ p2027 ∨ (¬ p3905)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3695) ∨ (¬ p3707) ∨ (¬ p3758) ∨ (¬ p3830) ∨ (¬ p3905) ∨ (¬ p4393) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial39286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory28542 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 10) (m.theta 9 10)
  exact rule39286 (meaning t m 2027) (meaning t m 2247) (meaning t m 2589) (meaning t m 2744) (meaning t m 3366) (meaning t m 3695) (meaning t m 3707) (meaning t m 3758) (meaning t m 3830) (meaning t m 3905) (meaning t m 4393) (meaning t m 5254) source

theorem rule39287 (p2027 p2247 p2534 p2744 p3055 p3366 p3449 p3874 p4181 p5122 : Prop) (h : (¬ p4181) ∨ (¬ p3449) ∨ (¬ p2744) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p2534) ∨ (¬ p3366) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p4181) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial39287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory28543 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule39287 (meaning t m 2027) (meaning t m 2247) (meaning t m 2534) (meaning t m 2744) (meaning t m 3055) (meaning t m 3366) (meaning t m 3449) (meaning t m 3874) (meaning t m 4181) (meaning t m 5122) source

theorem rule39289 (p2166 p3556 p3645 p4119 : Prop) (h : (¬ p4119) ∨ (¬ p3645) ∨ (¬ p3556) ∨ (¬ p2166)) : (¬ p2166) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial39289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory28545 (m.theta 0 5) (m.theta 1 5) (m.theta 5 7) (m.theta 5 8)
  exact rule39289 (meaning t m 2166) (meaning t m 3556) (meaning t m 3645) (meaning t m 4119) source

theorem rule39294 (p2027 p2177 p2241 p2992 p3115 p3551 p4107 p4395 p5210 : Prop) (h : (¬ p5210) ∨ (¬ p2992) ∨ (¬ p4395) ∨ (¬ p2241) ∨ (¬ p3551) ∨ (¬ p2177) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p3115)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5210) := by
  classical
  tauto

theorem initial39294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5210)) := by
  have source := ElevenTheory.theory28550 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39294 (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2992) (meaning t m 3115) (meaning t m 3551) (meaning t m 4107) (meaning t m 4395) (meaning t m 5210) source

theorem rule39298 (p1987 p2027 p2187 p2997 p3097 p3923 p4282 p4315 p4512 : Prop) (h : p2997 ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p3923) ∨ (¬ p4512) ∨ (¬ p3097) ∨ (¬ p4315) ∨ (¬ p4282)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2187) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3923) ∨ (¬ p4282) ∨ (¬ p4315) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial39298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory28554 t (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule39298 (meaning t m 1987) (meaning t m 2027) (meaning t m 2187) (meaning t m 2997) (meaning t m 3097) (meaning t m 3923) (meaning t m 4282) (meaning t m 4315) (meaning t m 4512) source

theorem rule39304 (p2027 p2299 p2579 p2588 p2608 p2707 p3434 p4668 p5193 : Prop) (h : (¬ p4668) ∨ (¬ p2579) ∨ (¬ p5193) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2299) ∨ (¬ p2707) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4668) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28560 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39304 (meaning t m 2027) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2608) (meaning t m 2707) (meaning t m 3434) (meaning t m 4668) (meaning t m 5193) source

theorem rule39305 (p2027 p2427 p3246 p4136 p4324 p4882 : Prop) (h : (¬ p4136) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4324) ∨ (¬ p4882) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial39305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory28561 t (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule39305 (meaning t m 2027) (meaning t m 2427) (meaning t m 3246) (meaning t m 4136) (meaning t m 4324) (meaning t m 4882) source

theorem rule39307 (p2007 p2027 p2241 p2699 p3189 p4009 p4286 : Prop) (h : p2699 ∨ (¬ p2007) ∨ (¬ p4009) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p4286)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p4009) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial39307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory28563 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 10)
  exact rule39307 (meaning t m 2007) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3189) (meaning t m 4009) (meaning t m 4286) source

theorem rule39310 (p2027 p2579 p2588 p2696 p3506 p3589 p3755 p4260 p4831 p5193 : Prop) (h : (¬ p4831) ∨ (¬ p5193) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p2696) ∨ (¬ p3589) ∨ (¬ p4260) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3589) ∨ (¬ p3755) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28566 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule39310 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2696) (meaning t m 3506) (meaning t m 3589) (meaning t m 3755) (meaning t m 4260) (meaning t m 4831) (meaning t m 5193) source

theorem rule39312 (p2027 p2532 p2982 p3880 p4261 p4494 : Prop) (h : (¬ p4494) ∨ (¬ p2532) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p2982) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4261) ∨ (¬ p4494) := by
  classical
  tauto

theorem initial39312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4494)) := by
  have source := ElevenTheory.theory28568 t (m.theta 1 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule39312 (meaning t m 2027) (meaning t m 2532) (meaning t m 2982) (meaning t m 3880) (meaning t m 4261) (meaning t m 4494) source

theorem rule39313 (p2027 p2608 p2707 p3434 p3646 p3950 p3989 p4347 p4524 : Prop) (h : (¬ p3646) ∨ (¬ p4524) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p2707) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2608) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial39313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory28569 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule39313 (meaning t m 2027) (meaning t m 2608) (meaning t m 2707) (meaning t m 3434) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) (meaning t m 4524) source

theorem rule39315 (p2027 p2417 p2850 p3686 p4324 p4644 : Prop) (h : (¬ p4324) ∨ p2027 ∨ (¬ p3686) ∨ (¬ p4644) ∨ (¬ p2850) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2850) ∨ (¬ p3686) ∨ (¬ p4324) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial39315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory28571 t (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule39315 (meaning t m 2027) (meaning t m 2417) (meaning t m 2850) (meaning t m 3686) (meaning t m 4324) (meaning t m 4644) source

theorem rule39319 (p2027 p2363 p2476 p2534 p2608 p2707 p2717 p4503 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p2534) ∨ (¬ p2717) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4503) ∨ (¬ p2476) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p4503) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial39319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory28575 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule39319 (meaning t m 2027) (meaning t m 2363) (meaning t m 2476) (meaning t m 2534) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 4503) (meaning t m 5193) source

theorem rule39321 (p2780 p3589 p3591 p3918 : Prop) (h : (¬ p3918) ∨ (¬ p3589) ∨ (¬ p3591) ∨ p2780) : (p2780) ∨ (¬ p3589) ∨ (¬ p3591) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial39321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2780) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory28577 (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 6)
  exact rule39321 (meaning t m 2780) (meaning t m 3589) (meaning t m 3591) (meaning t m 3918) source

theorem rule39322 (p2027 p2449 p2761 p2807 p3055 p3584 p4786 p5254 p5514 : Prop) (h : (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p5254) ∨ (¬ p4786) ∨ (¬ p3584) ∨ (¬ p5514) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4786) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial39322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory28578 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule39322 (meaning t m 2027) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3055) (meaning t m 3584) (meaning t m 4786) (meaning t m 5254) (meaning t m 5514) source

theorem rule39323 (p2027 p2210 p2247 p2744 p2780 p2972 p3366 p4347 p4358 p4450 : Prop) (h : (¬ p2247) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4347) ∨ (¬ p2972) ∨ (¬ p4450) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial39323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory28579 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule39323 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2744) (meaning t m 2780) (meaning t m 2972) (meaning t m 3366) (meaning t m 4347) (meaning t m 4358) (meaning t m 4450) source

theorem rule39324 (p2027 p2177 p2241 p2311 p2992 p3115 p3551 p4107 p4395 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p2241) ∨ (¬ p4395) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p3551) ∨ (¬ p2311) ∨ (¬ p2177) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2311) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial39324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory28580 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39324 (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2311) (meaning t m 2992) (meaning t m 3115) (meaning t m 3551) (meaning t m 4107) (meaning t m 4395) (meaning t m 5021) source

theorem rule39325 (p1992 p2027 p2177 p2462 p3588 p3659 p4107 : Prop) (h : (¬ p1992) ∨ (¬ p3588) ∨ (¬ p2177) ∨ (¬ p3659) ∨ p2462 ∨ p2027 ∨ (¬ p4107)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial39325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory28581 t (m.theta 1 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule39325 (meaning t m 1992) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3588) (meaning t m 3659) (meaning t m 4107) source

theorem rule39327 (p2027 p2241 p2299 p2313 p2992 p3115 p4348 p4450 p5021 : Prop) (h : (¬ p2241) ∨ (¬ p2313) ∨ (¬ p4348) ∨ (¬ p2299) ∨ (¬ p5021) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p4450) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial39327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory28583 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule39327 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2313) (meaning t m 2992) (meaning t m 3115) (meaning t m 4348) (meaning t m 4450) (meaning t m 5021) source

end SunPrize.SMT
