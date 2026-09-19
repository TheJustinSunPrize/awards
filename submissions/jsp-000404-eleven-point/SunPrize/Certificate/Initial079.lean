import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory063
import SunPrize.Certificate.Theory064
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule36629 (p2027 p3016 p3741 p3868 p4112 p4391 p4717 : Prop) (h : (¬ p3741) ∨ (¬ p3016) ∨ (¬ p4717) ∨ (¬ p4112) ∨ (¬ p4391) ∨ p2027 ∨ (¬ p3868)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4112) ∨ (¬ p4391) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial36629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory25885 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 10)
  exact rule36629 (meaning t m 2027) (meaning t m 3016) (meaning t m 3741) (meaning t m 3868) (meaning t m 4112) (meaning t m 4391) (meaning t m 4717) source

theorem rule36631 (p1984 p2509 p3008 p3452 p4598 : Prop) (h : (¬ p3452) ∨ (¬ p1984) ∨ p3008 ∨ (¬ p2509) ∨ p4598) : (¬ p1984) ∨ (¬ p2509) ∨ (p3008) ∨ (¬ p3452) ∨ (p4598) := by
  classical
  tauto

theorem initial36631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3452)) ∨ (meaning t m 4598) := by
  have source := ElevenTheory.theory25887 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8)
  exact rule36631 (meaning t m 1984) (meaning t m 2509) (meaning t m 3008) (meaning t m 3452) (meaning t m 4598) source

theorem rule36639 (p2002 p2027 p2753 p2766 p2774 p3266 p4379 p5387 : Prop) (h : (¬ p5387) ∨ (¬ p2002) ∨ p2027 ∨ (¬ p3266) ∨ p2766 ∨ (¬ p4379) ∨ (¬ p2774) ∨ (¬ p2753)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2753) ∨ (p2766) ∨ (¬ p2774) ∨ (¬ p3266) ∨ (¬ p4379) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial36639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory25895 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36639 (meaning t m 2002) (meaning t m 2027) (meaning t m 2753) (meaning t m 2766) (meaning t m 2774) (meaning t m 3266) (meaning t m 4379) (meaning t m 5387) source

theorem rule36644 (p2027 p2441 p2870 p4129 p4885 p5503 : Prop) (h : p2027 ∨ (¬ p4885) ∨ (¬ p2870) ∨ (¬ p4129) ∨ (¬ p2441) ∨ (¬ p5503)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p4129) ∨ (¬ p4885) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial36644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4885)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory25900 t (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10)
  exact rule36644 (meaning t m 2027) (meaning t m 2441) (meaning t m 2870) (meaning t m 4129) (meaning t m 4885) (meaning t m 5503) source

theorem rule36649 (p2027 p2696 p2797 p3540 p4228 p4278 p4381 p4729 p5250 : Prop) (h : (¬ p3540) ∨ (¬ p4278) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5250) ∨ p2027 ∨ (¬ p4228)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3540) ∨ (¬ p4228) ∨ (¬ p4278) ∨ (¬ p4381) ∨ (¬ p4729) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial36649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory25905 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule36649 (meaning t m 2027) (meaning t m 2696) (meaning t m 2797) (meaning t m 3540) (meaning t m 4228) (meaning t m 4278) (meaning t m 4381) (meaning t m 4729) (meaning t m 5250) source

theorem rule36650 (p2027 p2138 p2246 p2352 p2651 p2744 p3016 p3366 p3570 p4133 p4244 : Prop) (h : (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p2744) ∨ (¬ p2352) ∨ (¬ p3016)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial36650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory25906 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule36650 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2352) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3366) (meaning t m 3570) (meaning t m 4133) (meaning t m 4244) source

theorem rule36651 (p2027 p2241 p2313 p2553 p2992 p3156 p3956 p4433 p5021 : Prop) (h : (¬ p2313) ∨ (¬ p2992) ∨ (¬ p5021) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2241) ∨ (¬ p4433) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial36651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory25907 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule36651 (meaning t m 2027) (meaning t m 2241) (meaning t m 2313) (meaning t m 2553) (meaning t m 2992) (meaning t m 3156) (meaning t m 3956) (meaning t m 4433) (meaning t m 5021) source

theorem rule36652 (p2027 p2668 p3969 p4134 p5579 p5717 : Prop) (h : (¬ p5579) ∨ (¬ p5717) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3969) ∨ (¬ p4134) ∨ (¬ p5579) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial36652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 5579)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory25908 t (m.theta 3 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule36652 (meaning t m 2027) (meaning t m 2668) (meaning t m 3969) (meaning t m 4134) (meaning t m 5579) (meaning t m 5717) source

theorem rule36653 (p2027 p2440 p3016 p3880 p4203 p4507 : Prop) (h : (¬ p4203) ∨ (¬ p4507) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3880) ∨ (¬ p4203) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial36653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory25909 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule36653 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 3880) (meaning t m 4203) (meaning t m 4507) source

theorem rule36656 (p3542 p4261 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3542) ∨ p4261) : (¬ p3542) ∨ (p4261) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial36656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3542)) ∨ (meaning t m 4261) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory25912 (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36656 (meaning t m 3542) (meaning t m 4261) (meaning t m 4348) source

theorem rule36657 (p1981 p2027 p2088 p2373 p2765 p3696 p4110 p4347 : Prop) (h : (¬ p4110) ∨ (¬ p2373) ∨ p2765 ∨ (¬ p3696) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p4347) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2373) ∨ (p2765) ∨ (¬ p3696) ∨ (¬ p4110) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial36657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory25913 t (m.theta 0 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule36657 (meaning t m 1981) (meaning t m 2027) (meaning t m 2088) (meaning t m 2373) (meaning t m 2765) (meaning t m 3696) (meaning t m 4110) (meaning t m 4347) source

theorem rule36659 (p2020 p2027 p2323 p2373 p2542 p2651 p3969 : Prop) (h : (¬ p2651) ∨ p2323 ∨ (¬ p2542) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p2020)) : (¬ p2020) ∨ (p2027) ∨ (p2323) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial36659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory25915 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10)
  exact rule36659 (meaning t m 2020) (meaning t m 2027) (meaning t m 2323) (meaning t m 2373) (meaning t m 2542) (meaning t m 2651) (meaning t m 3969) source

theorem rule36661 (p2027 p2138 p2246 p2331 p2363 p2668 p2744 p3366 p3690 p4244 p4669 : Prop) (h : (¬ p4244) ∨ (¬ p4669) ∨ (¬ p2363) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p2744) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2246) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25917 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule36661 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2744) (meaning t m 3366) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) source

theorem rule36665 (p2027 p2246 p2744 p2958 p3212 p3366 p3425 p3659 p3680 p4191 p4330 p4348 : Prop) (h : (¬ p4191) ∨ (¬ p3659) ∨ (¬ p3366) ∨ (¬ p4348) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p2958) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p3212) ∨ (¬ p4330) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3680) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial36665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory25921 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 5 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule36665 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2958) (meaning t m 3212) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 3680) (meaning t m 4191) (meaning t m 4330) (meaning t m 4348) source

theorem rule36671 (p2027 p2363 p2911 p2930 p3544 p4138 p4261 : Prop) (h : (¬ p2930) ∨ p2027 ∨ (¬ p4138) ∨ (¬ p2911) ∨ (¬ p3544) ∨ (¬ p2363) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2911) ∨ (¬ p2930) ∨ (¬ p3544) ∨ (¬ p4138) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial36671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory25927 t (m.theta 1 7) (m.theta 1 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36671 (meaning t m 2027) (meaning t m 2363) (meaning t m 2911) (meaning t m 2930) (meaning t m 3544) (meaning t m 4138) (meaning t m 4261) source

theorem rule36672 (p2027 p2230 p2299 p2440 p3083 p3549 p3591 p4420 p5190 : Prop) (h : (¬ p4420) ∨ (¬ p3549) ∨ (¬ p2299) ∨ (¬ p3591) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4420) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial36672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory25928 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule36672 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2440) (meaning t m 3083) (meaning t m 3549) (meaning t m 3591) (meaning t m 4420) (meaning t m 5190) source

theorem rule36676 (p2027 p2870 p3758 p4140 p4393 p5472 : Prop) (h : (¬ p3758) ∨ (¬ p4140) ∨ (¬ p5472) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p4393)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p4140) ∨ (¬ p4393) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial36676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory25932 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10) (m.theta 6 7)
  exact rule36676 (meaning t m 2027) (meaning t m 2870) (meaning t m 3758) (meaning t m 4140) (meaning t m 4393) (meaning t m 5472) source

theorem rule36682 (p2027 p2246 p2417 p2437 p2608 p2651 p2744 p3570 p4366 p4668 p4909 : Prop) (h : (¬ p2608) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3570) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4909) ∨ (¬ p2417) ∨ (¬ p4668) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3570) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial36682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory25938 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36682 (meaning t m 2027) (meaning t m 2246) (meaning t m 2417) (meaning t m 2437) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3570) (meaning t m 4366) (meaning t m 4668) (meaning t m 4909) source

theorem rule36686 (p2707 p3537 p4805 : Prop) (h : (¬ p2707) ∨ (¬ p4805) ∨ p3537) : (¬ p2707) ∨ (p3537) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial36686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (meaning t m 3537) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory25942 (m.theta 1 2) (m.theta 2 7) (m.theta 2 8)
  exact rule36686 (meaning t m 2707) (meaning t m 3537) (meaning t m 4805) source

theorem rule36692 (p2027 p2743 p2972 p3371 p4385 p5052 : Prop) (h : (¬ p3371) ∨ (¬ p2972) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p4385) ∨ (¬ p2743)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p4385) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial36692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory25948 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 9)
  exact rule36692 (meaning t m 2027) (meaning t m 2743) (meaning t m 2972) (meaning t m 3371) (meaning t m 4385) (meaning t m 5052) source

theorem rule36697 (p2027 p2248 p2651 p3083 p3954 p4149 p4379 p5119 p5387 : Prop) (h : (¬ p5387) ∨ (¬ p3083) ∨ (¬ p4149) ∨ p2027 ∨ (¬ p4379) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p3954) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3954) ∨ (¬ p4149) ∨ (¬ p4379) ∨ (¬ p5119) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial36697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory25953 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 9) (m.theta 3 4) (m.theta 4 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36697 (meaning t m 2027) (meaning t m 2248) (meaning t m 2651) (meaning t m 3083) (meaning t m 3954) (meaning t m 4149) (meaning t m 4379) (meaning t m 5119) (meaning t m 5387) source

theorem rule36698 (p2027 p2475 p2518 p3238 p3961 p4283 p4320 p4702 : Prop) (h : (¬ p3961) ∨ (¬ p2518) ∨ (¬ p2475) ∨ (¬ p4283) ∨ (¬ p4702) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p4320)) : (p2027) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3238) ∨ (¬ p3961) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial36698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory25954 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7)
  exact rule36698 (meaning t m 2027) (meaning t m 2475) (meaning t m 2518) (meaning t m 3238) (meaning t m 3961) (meaning t m 4283) (meaning t m 4320) (meaning t m 4702) source

theorem rule36701 (p1995 p2027 p2881 p2927 p2938 p3379 p3644 p4366 : Prop) (h : (¬ p2881) ∨ p2938 ∨ (¬ p3379) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2927) ∨ (¬ p1995) ∨ (¬ p3644)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2881) ∨ (¬ p2927) ∨ (p2938) ∨ (¬ p3379) ∨ (¬ p3644) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial36701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2927)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory25957 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule36701 (meaning t m 1995) (meaning t m 2027) (meaning t m 2881) (meaning t m 2927) (meaning t m 2938) (meaning t m 3379) (meaning t m 3644) (meaning t m 4366) source

theorem rule36702 (p2027 p2247 p2744 p2780 p3073 p3366 p3449 p3822 p4107 p4669 : Prop) (h : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p4107) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25958 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule36702 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 2780) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) source

theorem rule36708 (p2027 p2138 p2247 p2744 p3366 p3399 p3570 p3631 p4244 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p2138) ∨ (¬ p3570) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p4244) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial36708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory25964 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36708 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3570) (meaning t m 3631) (meaning t m 4244) (meaning t m 4668) source

theorem rule36715 (p3246 p3692 p4119 p4443 : Prop) (h : (¬ p4443) ∨ (¬ p3246) ∨ (¬ p4119) ∨ (¬ p3692)) : (¬ p3246) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial36715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory25971 (m.theta 5 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule36715 (meaning t m 3246) (meaning t m 3692) (meaning t m 4119) (meaning t m 4443) source

theorem rule36718 (p2027 p2230 p2440 p2774 p3083 p3425 p3475 p3519 p3590 p3659 p4420 p4845 : Prop) (h : (¬ p4420) ∨ (¬ p3659) ∨ (¬ p3425) ∨ (¬ p3590) ∨ (¬ p3475) ∨ (¬ p2774) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p4845) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2774) ∨ (¬ p3083) ∨ (¬ p3425) ∨ (¬ p3475) ∨ (¬ p3519) ∨ (¬ p3590) ∨ (¬ p3659) ∨ (¬ p4420) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial36718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory25974 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8)
  exact rule36718 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2774) (meaning t m 3083) (meaning t m 3425) (meaning t m 3475) (meaning t m 3519) (meaning t m 3590) (meaning t m 3659) (meaning t m 4420) (meaning t m 4845) source

theorem rule36719 (p2027 p2264 p2459 p2589 p2807 p2850 p3905 p4697 p4786 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p2850) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p4697) ∨ (¬ p3905) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial36719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory25975 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule36719 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2589) (meaning t m 2807) (meaning t m 2850) (meaning t m 3905) (meaning t m 4697) (meaning t m 4786) (meaning t m 5160) source

theorem rule36724 (p2027 p2137 p2839 p3051 p3055 p3246 p3644 p3876 p4668 p4734 : Prop) (h : (¬ p2839) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3051) ∨ (¬ p2137) ∨ (¬ p4668) ∨ (¬ p4734) ∨ (¬ p3055) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial36724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory25980 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36724 (meaning t m 2027) (meaning t m 2137) (meaning t m 2839) (meaning t m 3051) (meaning t m 3055) (meaning t m 3246) (meaning t m 3644) (meaning t m 3876) (meaning t m 4668) (meaning t m 4734) source

theorem rule36727 (p1994 p2027 p2252 p2417 p2727 p2914 p3414 p3947 : Prop) (h : p2027 ∨ (¬ p2252) ∨ (¬ p2727) ∨ (¬ p3947) ∨ (¬ p3414) ∨ (¬ p1994) ∨ p2914 ∨ (¬ p2417)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2417) ∨ (¬ p2727) ∨ (p2914) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial36727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory25983 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule36727 (meaning t m 1994) (meaning t m 2027) (meaning t m 2252) (meaning t m 2417) (meaning t m 2727) (meaning t m 2914) (meaning t m 3414) (meaning t m 3947) source

theorem rule36728 (p2027 p2307 p3055 p3323 p3568 p3684 p3987 p4368 p4786 p4948 : Prop) (h : (¬ p3055) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p4368) ∨ (¬ p3987) ∨ (¬ p2307) ∨ (¬ p3568) ∨ (¬ p3323) ∨ (¬ p4786) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3684) ∨ (¬ p3987) ∨ (¬ p4368) ∨ (¬ p4786) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial36728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory25984 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule36728 (meaning t m 2027) (meaning t m 2307) (meaning t m 3055) (meaning t m 3323) (meaning t m 3568) (meaning t m 3684) (meaning t m 3987) (meaning t m 4368) (meaning t m 4786) (meaning t m 4948) source

theorem rule36731 (p1976 p2027 p2274 p2588 p2590 p2765 p3055 p3684 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p3684) ∨ (¬ p1976) ∨ (¬ p3055) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (p2765) ∨ (¬ p3055) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial36731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory25987 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule36731 (meaning t m 1976) (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 2590) (meaning t m 2765) (meaning t m 3055) (meaning t m 3684) source

theorem rule36736 (p2027 p2531 p3201 p3497 p3684 p3875 p4702 : Prop) (h : (¬ p3201) ∨ p2027 ∨ (¬ p2531) ∨ (¬ p3497) ∨ (¬ p4702) ∨ (¬ p3684) ∨ (¬ p3875)) : (p2027) ∨ (¬ p2531) ∨ (¬ p3201) ∨ (¬ p3497) ∨ (¬ p3684) ∨ (¬ p3875) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial36736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory25992 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8)
  exact rule36736 (meaning t m 2027) (meaning t m 2531) (meaning t m 3201) (meaning t m 3497) (meaning t m 3684) (meaning t m 3875) (meaning t m 4702) source

theorem rule36737 (p2027 p2470 p2542 p2579 p4256 p4715 : Prop) (h : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p4715) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4256)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p4256) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial36737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory25993 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule36737 (meaning t m 2027) (meaning t m 2470) (meaning t m 2542) (meaning t m 2579) (meaning t m 4256) (meaning t m 4715) source

theorem rule36741 (p2027 p2246 p2608 p2744 p3286 p3506 p3860 p3950 p4261 p4381 : Prop) (h : (¬ p2744) ∨ (¬ p2246) ∨ (¬ p3286) ∨ (¬ p3860) ∨ (¬ p3506) ∨ (¬ p2608) ∨ (¬ p3950) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p4381)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial36741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory25997 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36741 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3286) (meaning t m 3506) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 4381) source

theorem rule36745 (p2295 p2668 p3955 : Prop) (h : (¬ p3955) ∨ (¬ p2668) ∨ p2295) : (p2295) ∨ (¬ p2668) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial36745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2295) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory26001 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36745 (meaning t m 2295) (meaning t m 2668) (meaning t m 3955) source

theorem rule36747 (p1994 p2027 p2651 p2766 p3414 p3553 p4348 : Prop) (h : (¬ p1994) ∨ (¬ p2651) ∨ (¬ p3414) ∨ p2766 ∨ (¬ p3553) ∨ p2027 ∨ (¬ p4348)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial36747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26003 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule36747 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2766) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) source

theorem rule36754 (p2027 p3055 p3166 p3256 p3266 p3584 p4786 p5254 p5514 : Prop) (h : (¬ p3166) ∨ (¬ p3055) ∨ (¬ p4786) ∨ (¬ p5254) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p3256) ∨ (¬ p5514) ∨ (¬ p3266)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3584) ∨ (¬ p4786) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial36754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory26010 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule36754 (meaning t m 2027) (meaning t m 3055) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3584) (meaning t m 4786) (meaning t m 5254) (meaning t m 5514) source

theorem rule36755 (p1997 p2027 p2114 p2542 p2573 p3367 p3574 p3759 : Prop) (h : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p1997) ∨ p2114 ∨ (¬ p3759) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3574)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3574) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial36755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory26011 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule36755 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2542) (meaning t m 2573) (meaning t m 3367) (meaning t m 3574) (meaning t m 3759) source

theorem rule36758 (p2027 p2192 p2440 p3948 p4110 p4814 : Prop) (h : (¬ p4814) ∨ (¬ p3948) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2440) ∨ (¬ p3948) ∨ (¬ p4110) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial36758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory26014 t (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule36758 (meaning t m 2027) (meaning t m 2192) (meaning t m 2440) (meaning t m 3948) (meaning t m 4110) (meaning t m 4814) source

theorem rule36760 (p1994 p2027 p2440 p2765 p3105 p3758 p4031 p4032 : Prop) (h : (¬ p4032) ∨ (¬ p2440) ∨ (¬ p3758) ∨ (¬ p4031) ∨ (¬ p1994) ∨ p2027 ∨ p2765 ∨ (¬ p3105)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2765) ∨ (¬ p3105) ∨ (¬ p3758) ∨ (¬ p4031) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial36760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory26016 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule36760 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2765) (meaning t m 3105) (meaning t m 3758) (meaning t m 4031) (meaning t m 4032) source

theorem rule36763 (p2027 p2166 p2608 p2744 p3369 p4120 p4365 : Prop) (h : (¬ p3369) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p4365) ∨ (¬ p2744) ∨ (¬ p4120) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial36763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory26019 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 8)
  exact rule36763 (meaning t m 2027) (meaning t m 2166) (meaning t m 2608) (meaning t m 2744) (meaning t m 3369) (meaning t m 4120) (meaning t m 4365) source

theorem rule36767 (p1994 p2027 p2440 p2766 p3556 p3570 p4031 p4348 : Prop) (h : (¬ p2440) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p4348) ∨ p2766 ∨ (¬ p4031) ∨ (¬ p3556) ∨ (¬ p3570)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2766) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4031) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial36767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26023 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule36767 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2766) (meaning t m 3556) (meaning t m 3570) (meaning t m 4031) (meaning t m 4348) source

theorem rule36768 (p1994 p2027 p2230 p2440 p2766 p3540 p3644 p4348 : Prop) (h : p2766 ∨ (¬ p4348) ∨ (¬ p3644) ∨ (¬ p2440) ∨ (¬ p1994) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3540)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial36768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26024 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule36768 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2766) (meaning t m 3540) (meaning t m 3644) (meaning t m 4348) source

theorem rule36769 (p2027 p2246 p2274 p2284 p2608 p2744 p2946 p3591 p3923 p4501 : Prop) (h : (¬ p3923) ∨ (¬ p2284) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p4501) ∨ (¬ p2274) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial36769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory26025 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36769 (meaning t m 2027) (meaning t m 2246) (meaning t m 2274) (meaning t m 2284) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3591) (meaning t m 3923) (meaning t m 4501) source

theorem rule36771 (p2027 p2470 p2528 p2577 p2797 p3292 p3567 p3680 p4787 p5059 p5284 : Prop) (h : (¬ p2577) ∨ (¬ p2470) ∨ (¬ p3292) ∨ (¬ p5059) ∨ (¬ p3567) ∨ (¬ p2797) ∨ (¬ p4787) ∨ (¬ p3680) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p2528)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2577) ∨ (¬ p2797) ∨ (¬ p3292) ∨ (¬ p3567) ∨ (¬ p3680) ∨ (¬ p4787) ∨ (¬ p5059) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial36771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory26027 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36771 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2577) (meaning t m 2797) (meaning t m 3292) (meaning t m 3567) (meaning t m 3680) (meaning t m 4787) (meaning t m 5059) (meaning t m 5284) source

theorem rule36778 (p2027 p2396 p2663 p2774 p3172 p3309 p3363 p3585 p3918 p3950 p4118 p4737 : Prop) (h : (¬ p3172) ∨ (¬ p3918) ∨ (¬ p2774) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p3585) ∨ (¬ p4118) ∨ (¬ p2663) ∨ (¬ p3363)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2663) ∨ (¬ p2774) ∨ (¬ p3172) ∨ (¬ p3309) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3918) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial36778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory26034 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 3 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule36778 (meaning t m 2027) (meaning t m 2396) (meaning t m 2663) (meaning t m 2774) (meaning t m 3172) (meaning t m 3309) (meaning t m 3363) (meaning t m 3585) (meaning t m 3918) (meaning t m 3950) (meaning t m 4118) (meaning t m 4737) source

theorem rule36779 (p1994 p2027 p2230 p2387 p2440 p2577 p2622 p2819 p4426 : Prop) (h : p2027 ∨ (¬ p1994) ∨ (¬ p2440) ∨ (¬ p4426) ∨ (¬ p2819) ∨ p2622 ∨ (¬ p2230) ∨ (¬ p2577) ∨ (¬ p2387)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2440) ∨ (¬ p2577) ∨ (p2622) ∨ (¬ p2819) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial36779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2577)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory26035 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 6 8)
  exact rule36779 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2387) (meaning t m 2440) (meaning t m 2577) (meaning t m 2622) (meaning t m 2819) (meaning t m 4426) source

theorem rule36781 (p2027 p2373 p3696 p3998 p4359 p4882 p5612 : Prop) (h : (¬ p5612) ∨ (¬ p4359) ∨ (¬ p3998) ∨ (¬ p3696) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p4882)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3696) ∨ (¬ p3998) ∨ (¬ p4359) ∨ (¬ p4882) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial36781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4882)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory26037 t (m.theta 0 8) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10)
  exact rule36781 (meaning t m 2027) (meaning t m 2373) (meaning t m 3696) (meaning t m 3998) (meaning t m 4359) (meaning t m 4882) (meaning t m 5612) source

theorem rule36783 (p1976 p2027 p2177 p2462 p3425 p3659 p4107 : Prop) (h : (¬ p3659) ∨ (¬ p3425) ∨ (¬ p2177) ∨ (¬ p4107) ∨ p2462 ∨ (¬ p1976) ∨ p2027) : (¬ p1976) ∨ (p2027) ∨ (¬ p2177) ∨ (p2462) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial36783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory26039 t (m.theta 0 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36783 (meaning t m 1976) (meaning t m 2027) (meaning t m 2177) (meaning t m 2462) (meaning t m 3425) (meaning t m 3659) (meaning t m 4107) source

theorem rule36784 (p2027 p2579 p3355 p4037 p4331 p4973 : Prop) (h : (¬ p2579) ∨ (¬ p3355) ∨ (¬ p4331) ∨ p2027 ∨ (¬ p4973) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3355) ∨ (¬ p4037) ∨ (¬ p4331) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial36784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory26040 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule36784 (meaning t m 2027) (meaning t m 2579) (meaning t m 3355) (meaning t m 4037) (meaning t m 4331) (meaning t m 4973) source

theorem rule36785 (p2027 p2295 p3246 p3922 p4026 p4396 p4559 : Prop) (h : (¬ p4026) ∨ (¬ p4559) ∨ p2027 ∨ (¬ p3922) ∨ (¬ p4396) ∨ (¬ p2295) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3246) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial36785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory26041 t (m.theta 1 6) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule36785 (meaning t m 2027) (meaning t m 2295) (meaning t m 3246) (meaning t m 3922) (meaning t m 4026) (meaning t m 4396) (meaning t m 4559) source

theorem rule36786 (p2027 p2363 p2383 p2781 p3055 p3684 p3880 p4348 p4905 : Prop) (h : (¬ p3684) ∨ (¬ p3880) ∨ (¬ p2383) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2781) ∨ (¬ p4905) ∨ (¬ p2363) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial36786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory26042 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36786 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2781) (meaning t m 3055) (meaning t m 3684) (meaning t m 3880) (meaning t m 4348) (meaning t m 4905) source

theorem rule36788 (p1994 p2027 p2462 p2881 p3644 p3690 p3742 : Prop) (h : (¬ p3742) ∨ p2462 ∨ (¬ p1994) ∨ (¬ p3644) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3690)) : (¬ p1994) ∨ (p2027) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p3690) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial36788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory26044 t (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36788 (meaning t m 1994) (meaning t m 2027) (meaning t m 2462) (meaning t m 2881) (meaning t m 3644) (meaning t m 3690) (meaning t m 3742) source

theorem rule36789 (p2246 p2331 p3189 p4341 : Prop) (h : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p4341) ∨ p3189) : (¬ p2246) ∨ (¬ p2331) ∨ (p3189) ∨ (¬ p4341) := by
  classical
  tauto

theorem initial36789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 3189) ∨ (¬ (meaning t m 4341)) := by
  have source := ElevenTheory.theory26045 (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8)
  exact rule36789 (meaning t m 2246) (meaning t m 2331) (meaning t m 3189) (meaning t m 4341) source

theorem rule36792 (p2027 p2187 p2248 p2284 p2499 p2588 p2946 p3452 p4405 : Prop) (h : (¬ p2588) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4405)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial36792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory26048 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36792 (meaning t m 2027) (meaning t m 2187) (meaning t m 2248) (meaning t m 2284) (meaning t m 2499) (meaning t m 2588) (meaning t m 2946) (meaning t m 3452) (meaning t m 4405) source

theorem rule36793 (p2774 p2811 p4236 p4841 : Prop) (h : (¬ p4236) ∨ (¬ p2811) ∨ (¬ p4841) ∨ (¬ p2774)) : (¬ p2774) ∨ (¬ p2811) ∨ (¬ p4236) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial36793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory26049 (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6)
  exact rule36793 (meaning t m 2774) (meaning t m 2811) (meaning t m 4236) (meaning t m 4841) source

theorem rule36797 (p1997 p2027 p2542 p2662 p2764 p3540 p4278 p4381 : Prop) (h : p2764 ∨ (¬ p2662) ∨ (¬ p4278) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p2542) ∨ (¬ p3540)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2662) ∨ (p2764) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial36797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory26053 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule36797 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2662) (meaning t m 2764) (meaning t m 3540) (meaning t m 4278) (meaning t m 4381) source

theorem rule36802 (p2027 p3497 p4149 p4355 p4702 p5568 : Prop) (h : (¬ p3497) ∨ (¬ p4355) ∨ (¬ p4702) ∨ (¬ p4149) ∨ (¬ p5568) ∨ p2027) : (p2027) ∨ (¬ p3497) ∨ (¬ p4149) ∨ (¬ p4355) ∨ (¬ p4702) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial36802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4702)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory26058 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule36802 (meaning t m 2027) (meaning t m 3497) (meaning t m 4149) (meaning t m 4355) (meaning t m 4702) (meaning t m 5568) source

theorem rule36804 (p2027 p2264 p2459 p3955 p4347 p4361 : Prop) (h : (¬ p2459) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4361) ∨ (¬ p3955) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial36804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory26060 t (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36804 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 3955) (meaning t m 4347) (meaning t m 4361) source

theorem rule36806 (p1997 p2027 p2230 p2476 p2534 p3146 p3578 : Prop) (h : (¬ p1997) ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2230) ∨ (¬ p2534) ∨ (¬ p3146) ∨ p3578) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (p3578) := by
  classical
  tauto

theorem initial36806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) := by
  have source := ElevenTheory.theory26062 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule36806 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2534) (meaning t m 3146) (meaning t m 3578) source

theorem rule36807 (p2027 p2109 p2707 p2881 p3960 p4242 p4895 : Prop) (h : (¬ p4242) ∨ (¬ p2109) ∨ (¬ p3960) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p4895) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2109) ∨ (¬ p2707) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial36807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2109)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory26063 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 5 7) (m.theta 7 8)
  exact rule36807 (meaning t m 2027) (meaning t m 2109) (meaning t m 2707) (meaning t m 2881) (meaning t m 3960) (meaning t m 4242) (meaning t m 4895) source

theorem rule36808 (p1994 p2027 p2651 p2764 p3414 p3947 p4381 : Prop) (h : (¬ p3414) ∨ p2764 ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3947) ∨ (¬ p2651) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2764) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial36808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory26064 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule36808 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2764) (meaning t m 3414) (meaning t m 3947) (meaning t m 4381) source

theorem rule36809 (p2027 p2406 p2470 p2509 p2579 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2579) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial36809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory26065 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule36809 (meaning t m 2027) (meaning t m 2406) (meaning t m 2470) (meaning t m 2509) (meaning t m 2579) (meaning t m 4715) source

theorem rule36811 (p1984 p2027 p2247 p2459 p2633 p2996 p3919 p4118 : Prop) (h : p2633 ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p1984) ∨ (¬ p4118) ∨ (¬ p3919) ∨ (¬ p2459)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3919) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial36811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory26067 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36811 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2633) (meaning t m 2996) (meaning t m 3919) (meaning t m 4118) source

theorem rule36813 (p2027 p2241 p2427 p3189 p3347 p3556 p3880 p3904 p3954 p5063 p5216 : Prop) (h : (¬ p3556) ∨ (¬ p3904) ∨ (¬ p3189) ∨ (¬ p3347) ∨ (¬ p3880) ∨ (¬ p2241) ∨ (¬ p5216) ∨ (¬ p5063) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2427) ∨ (¬ p3189) ∨ (¬ p3347) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p5063) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial36813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5063)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory26069 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule36813 (meaning t m 2027) (meaning t m 2241) (meaning t m 2427) (meaning t m 3189) (meaning t m 3347) (meaning t m 3556) (meaning t m 3880) (meaning t m 3904) (meaning t m 3954) (meaning t m 5063) (meaning t m 5216) source

theorem rule36814 (p1982 p2027 p2528 p2662 p2842 p3083 p3201 p3540 : Prop) (h : (¬ p1982) ∨ (¬ p3083) ∨ (¬ p2528) ∨ (¬ p3201) ∨ (¬ p2662) ∨ p2027 ∨ (¬ p3540) ∨ p2842) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2662) ∨ (p2842) ∨ (¬ p3083) ∨ (¬ p3201) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial36814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory26070 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 8 9)
  exact rule36814 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2662) (meaning t m 2842) (meaning t m 3083) (meaning t m 3201) (meaning t m 3540) source

theorem rule36815 (p2027 p2248 p2509 p2946 p3115 p3452 p3680 p4286 p5123 : Prop) (h : p2027 ∨ (¬ p3452) ∨ (¬ p5123) ∨ (¬ p4286) ∨ (¬ p2509) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p2248) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2509) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial36815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory26071 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36815 (meaning t m 2027) (meaning t m 2248) (meaning t m 2509) (meaning t m 2946) (meaning t m 3115) (meaning t m 3452) (meaning t m 3680) (meaning t m 4286) (meaning t m 5123) source

theorem rule36824 (p2027 p3346 p3670 p4231 p4375 p4425 p4727 : Prop) (h : (¬ p3670) ∨ (¬ p4727) ∨ p2027 ∨ (¬ p4375) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p4231)) : (p2027) ∨ (¬ p3346) ∨ (¬ p3670) ∨ (¬ p4231) ∨ (¬ p4375) ∨ (¬ p4425) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial36824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4231)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory26080 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 2 9) (m.theta 4 9) (m.theta 9 10)
  exact rule36824 (meaning t m 2027) (meaning t m 3346) (meaning t m 3670) (meaning t m 4231) (meaning t m 4375) (meaning t m 4425) (meaning t m 4727) source

theorem rule36825 (p2027 p2459 p2630 p2696 p3083 p3544 p4261 p4366 p4420 p4733 : Prop) (h : (¬ p4366) ∨ (¬ p4420) ∨ (¬ p2630) ∨ (¬ p4261) ∨ (¬ p3544) ∨ (¬ p4733) ∨ (¬ p3083) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2696)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4366) ∨ (¬ p4420) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial36825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26081 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 1 8) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36825 (meaning t m 2027) (meaning t m 2459) (meaning t m 2630) (meaning t m 2696) (meaning t m 3083) (meaning t m 3544) (meaning t m 4261) (meaning t m 4366) (meaning t m 4420) (meaning t m 4733) source

theorem rule36830 (p1994 p2027 p2440 p2588 p2850 p2997 p3584 : Prop) (h : p2997 ∨ (¬ p1994) ∨ (¬ p3584) ∨ (¬ p2588) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p2850)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2588) ∨ (¬ p2850) ∨ (p2997) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial36830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory26086 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule36830 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2588) (meaning t m 2850) (meaning t m 2997) (meaning t m 3584) source

theorem rule36831 (p1989 p2027 p2210 p2764 p3817 p4366 p4381 : Prop) (h : p2027 ∨ (¬ p3817) ∨ (¬ p1989) ∨ (¬ p4381) ∨ (¬ p2210) ∨ p2764 ∨ (¬ p4366)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2764) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial36831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory26087 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule36831 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2764) (meaning t m 3817) (meaning t m 4366) (meaning t m 4381) source

theorem rule36832 (p2027 p2440 p2860 p3582 p4110 p4753 : Prop) (h : (¬ p4753) ∨ (¬ p2440) ∨ (¬ p3582) ∨ (¬ p2860) ∨ p2027 ∨ (¬ p4110)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2860) ∨ (¬ p3582) ∨ (¬ p4110) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial36832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory26088 t (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule36832 (meaning t m 2027) (meaning t m 2440) (meaning t m 2860) (meaning t m 3582) (meaning t m 4110) (meaning t m 4753) source

theorem rule36833 (p2027 p2210 p2247 p2744 p2780 p2972 p3366 p3822 p4107 p4395 : Prop) (h : (¬ p2744) ∨ (¬ p4395) ∨ (¬ p2247) ∨ (¬ p3822) ∨ (¬ p2210) ∨ (¬ p3366) ∨ (¬ p2972) ∨ (¬ p2780) ∨ (¬ p4107) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial36833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory26089 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule36833 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2744) (meaning t m 2780) (meaning t m 2972) (meaning t m 3366) (meaning t m 3822) (meaning t m 4107) (meaning t m 4395) source

theorem rule36834 (p2027 p2254 p2363 p2952 p3063 p3093 p3680 p4314 p5059 p5284 : Prop) (h : (¬ p5059) ∨ (¬ p3093) ∨ (¬ p2363) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3680) ∨ (¬ p3063) ∨ (¬ p4314) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p5059) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial36834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4314)) ∨ (¬ (meaning t m 5059)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory26090 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule36834 (meaning t m 2027) (meaning t m 2254) (meaning t m 2363) (meaning t m 2952) (meaning t m 3063) (meaning t m 3093) (meaning t m 3680) (meaning t m 4314) (meaning t m 5059) (meaning t m 5284) source

theorem rule36837 (p2027 p2166 p2210 p2247 p2299 p2579 p2744 p3366 p3822 p3905 p4390 p4902 : Prop) (h : (¬ p4902) ∨ (¬ p2299) ∨ (¬ p3822) ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p3366) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3905) ∨ (¬ p4390) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4390) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial36837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory26093 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule36837 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2299) (meaning t m 2579) (meaning t m 2744) (meaning t m 3366) (meaning t m 3822) (meaning t m 3905) (meaning t m 4390) (meaning t m 4902) source

theorem rule36842 (p1992 p2027 p2743 p2764 p3172 p3361 p4118 p4444 : Prop) (h : (¬ p3361) ∨ p2027 ∨ (¬ p4444) ∨ p2764 ∨ (¬ p1992) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p4118) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial36842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory26098 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule36842 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2764) (meaning t m 3172) (meaning t m 3361) (meaning t m 4118) (meaning t m 4444) source

theorem rule36844 (p2001 p2027 p2088 p2202 p2475 p3641 p3684 p3692 : Prop) (h : (¬ p2001) ∨ (¬ p2088) ∨ p2202 ∨ p2027 ∨ (¬ p3641) ∨ (¬ p2475) ∨ (¬ p3692) ∨ (¬ p3684)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2088) ∨ (p2202) ∨ (¬ p2475) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial36844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory26100 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule36844 (meaning t m 2001) (meaning t m 2027) (meaning t m 2088) (meaning t m 2202) (meaning t m 2475) (meaning t m 3641) (meaning t m 3684) (meaning t m 3692) source

theorem rule36851 (p2027 p2122 p2588 p3574 p4375 p4753 : Prop) (h : (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p4375) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial36851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory26107 t (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule36851 (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 3574) (meaning t m 4375) (meaning t m 4753) source

theorem rule36852 (p1984 p2027 p2274 p2765 p3688 p3822 p3954 : Prop) (h : (¬ p3688) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p1984) ∨ p2765 ∨ (¬ p2274)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial36852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory26108 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule36852 (meaning t m 1984) (meaning t m 2027) (meaning t m 2274) (meaning t m 2765) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) source

theorem rule36853 (p1981 p2027 p2352 p2573 p2622 p2743 p3367 p3759 : Prop) (h : (¬ p3759) ∨ (¬ p3367) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2743) ∨ p2622 ∨ (¬ p2352) ∨ (¬ p2573)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial36853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory26109 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule36853 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2573) (meaning t m 2622) (meaning t m 2743) (meaning t m 3367) (meaning t m 3759) source

theorem rule36854 (p2027 p2307 p2497 p2850 p3549 p3567 p4030 p4389 p4715 : Prop) (h : (¬ p4030) ∨ (¬ p3567) ∨ (¬ p4389) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p4715) ∨ (¬ p3549) ∨ (¬ p2850) ∨ (¬ p2497)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2850) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4030) ∨ (¬ p4389) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial36854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory26110 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule36854 (meaning t m 2027) (meaning t m 2307) (meaning t m 2497) (meaning t m 2850) (meaning t m 3549) (meaning t m 3567) (meaning t m 4030) (meaning t m 4389) (meaning t m 4715) source

theorem rule36855 (p3096 p4889 p5222 : Prop) (h : (¬ p3096) ∨ (¬ p4889) ∨ p5222) : (¬ p3096) ∨ (¬ p4889) ∨ (p5222) := by
  classical
  tauto

theorem initial36855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4889)) ∨ (meaning t m 5222) := by
  have source := ElevenTheory.theory26111 t (m.theta 2 6) (m.theta 4 6) (m.theta 5 6)
  exact rule36855 (meaning t m 3096) (meaning t m 4889) (meaning t m 5222) source

theorem rule36861 (p2027 p2187 p2248 p2284 p2946 p3551 p3609 p4261 p4863 p5206 p5307 : Prop) (h : (¬ p5206) ∨ (¬ p2187) ∨ (¬ p3551) ∨ (¬ p5307) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2248) ∨ (¬ p3609) ∨ (¬ p4863) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3551) ∨ (¬ p3609) ∨ (¬ p4261) ∨ (¬ p4863) ∨ (¬ p5206) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial36861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4863)) ∨ (¬ (meaning t m 5206)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory26117 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 7) (m.theta 1 8) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36861 (meaning t m 2027) (meaning t m 2187) (meaning t m 2248) (meaning t m 2284) (meaning t m 2946) (meaning t m 3551) (meaning t m 3609) (meaning t m 4261) (meaning t m 4863) (meaning t m 5206) (meaning t m 5307) source

theorem rule36863 (p2027 p2247 p2744 p3055 p3073 p3366 p3449 p3876 p4278 p4669 : Prop) (h : (¬ p3073) ∨ (¬ p4278) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p4669) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3055) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory26119 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule36863 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3055) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3876) (meaning t m 4278) (meaning t m 4669) source

theorem rule36868 (p2027 p2139 p2220 p3055 p3115 p3497 p3876 p4278 p4395 : Prop) (h : (¬ p3055) ∨ (¬ p4395) ∨ (¬ p2220) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4278) ∨ (¬ p3876) ∨ (¬ p2139) ∨ p2027) : (p2027) ∨ (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial36868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory26124 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule36868 (meaning t m 2027) (meaning t m 2139) (meaning t m 2220) (meaning t m 3055) (meaning t m 3115) (meaning t m 3497) (meaning t m 3876) (meaning t m 4278) (meaning t m 4395) source

theorem rule36869 (p1975 p2027 p2299 p2319 p2341 p3319 p3818 p3946 : Prop) (h : (¬ p2341) ∨ p3818 ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2319) ∨ (¬ p2299) ∨ (¬ p3946) ∨ (¬ p3319)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3319) ∨ (p3818) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial36869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3319)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory26125 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule36869 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 3319) (meaning t m 3818) (meaning t m 3946) source

theorem rule36870 (p2027 p2387 p2743 p2785 p3063 p4845 p4869 : Prop) (h : (¬ p4869) ∨ (¬ p2743) ∨ (¬ p3063) ∨ (¬ p2785) ∨ (¬ p4845) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2743) ∨ (¬ p2785) ∨ (¬ p3063) ∨ (¬ p4845) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial36870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4845)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory26126 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule36870 (meaning t m 2027) (meaning t m 2387) (meaning t m 2743) (meaning t m 2785) (meaning t m 3063) (meaning t m 4845) (meaning t m 4869) source

theorem rule36871 (p2027 p2122 p2246 p2313 p2744 p2778 p3286 p3366 p3506 p3917 p4396 p4444 p4669 : Prop) (h : (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4669) ∨ (¬ p2246) ∨ (¬ p2778) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p2313) ∨ (¬ p4396) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3286) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3917) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory26127 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 9) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36871 (meaning t m 2027) (meaning t m 2122) (meaning t m 2246) (meaning t m 2313) (meaning t m 2744) (meaning t m 2778) (meaning t m 3286) (meaning t m 3366) (meaning t m 3506) (meaning t m 3917) (meaning t m 4396) (meaning t m 4444) (meaning t m 4669) source

theorem rule36878 (p2001 p2027 p2230 p2233 p3156 p3727 p5740 : Prop) (h : (¬ p2001) ∨ p2233 ∨ p2027 ∨ (¬ p3727) ∨ (¬ p3156) ∨ (¬ p5740) ∨ (¬ p2230)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p3156) ∨ (¬ p3727) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial36878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory26134 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 10) (m.theta 5 8)
  exact rule36878 (meaning t m 2001) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 3156) (meaning t m 3727) (meaning t m 5740) source

theorem rule36879 (p2027 p2247 p2299 p2744 p2780 p3366 p3399 p3822 p4075 p5564 : Prop) (h : (¬ p3366) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p2299) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p5564) ∨ (¬ p3399) ∨ (¬ p2744) ∨ (¬ p4075)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3822) ∨ (¬ p4075) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial36879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory26135 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule36879 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2744) (meaning t m 2780) (meaning t m 3366) (meaning t m 3399) (meaning t m 3822) (meaning t m 4075) (meaning t m 5564) source

theorem rule36881 (p2493 p3574 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2493) ∨ (¬ p3574)) : (¬ p2493) ∨ (¬ p3574) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial36881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory26137 (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule36881 (meaning t m 2493) (meaning t m 3574) (meaning t m 4116) source

theorem rule36882 (p2027 p2307 p2743 p3822 p4845 p4869 p5016 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p4869) ∨ (¬ p4845) ∨ (¬ p2743) ∨ (¬ p5016) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2743) ∨ (¬ p3822) ∨ (¬ p4845) ∨ (¬ p4869) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial36882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4845)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory26138 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule36882 (meaning t m 2027) (meaning t m 2307) (meaning t m 2743) (meaning t m 3822) (meaning t m 4845) (meaning t m 4869) (meaning t m 5016) source

theorem rule36883 (p2027 p2383 p2743 p4358 p4845 p4869 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2383) ∨ (¬ p4869) ∨ (¬ p4845) ∨ (¬ p4358)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2743) ∨ (¬ p4358) ∨ (¬ p4845) ∨ (¬ p4869) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial36883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4845)) ∨ (¬ (meaning t m 4869)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory26139 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule36883 (meaning t m 2027) (meaning t m 2383) (meaning t m 2743) (meaning t m 4358) (meaning t m 4845) (meaning t m 4869) (meaning t m 5016) source

theorem rule36889 (p2027 p2241 p2641 p2668 p3201 p3540 p3874 p4384 p5193 : Prop) (h : (¬ p2241) ∨ (¬ p4384) ∨ (¬ p5193) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p4384) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial36889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory26145 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8)
  exact rule36889 (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2668) (meaning t m 3201) (meaning t m 3540) (meaning t m 3874) (meaning t m 4384) (meaning t m 5193) source

theorem rule36893 (p2027 p2191 p2532 p2972 p3857 p4529 : Prop) (h : (¬ p4529) ∨ (¬ p2191) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p2972) ∨ (¬ p2532)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2532) ∨ (¬ p2972) ∨ (¬ p3857) ∨ (¬ p4529) := by
  classical
  tauto

theorem initial36893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4529)) := by
  have source := ElevenTheory.theory26149 t (m.theta 0 8) (m.theta 1 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule36893 (meaning t m 2027) (meaning t m 2191) (meaning t m 2532) (meaning t m 2972) (meaning t m 3857) (meaning t m 4529) source

theorem rule36895 (p2027 p2177 p3055 p3093 p3309 p3876 p4278 p4666 p4736 : Prop) (h : p2027 ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p4736) ∨ (¬ p3309) ∨ (¬ p2177) ∨ (¬ p4666) ∨ (¬ p4278) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial36895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory26151 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36895 (meaning t m 2027) (meaning t m 2177) (meaning t m 3055) (meaning t m 3093) (meaning t m 3309) (meaning t m 3876) (meaning t m 4278) (meaning t m 4666) (meaning t m 4736) source

theorem rule36896 (p2027 p2220 p2542 p3096 p3574 p4109 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p2542) ∨ (¬ p2220) ∨ (¬ p3096) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p4109) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial36896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory26152 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8)
  exact rule36896 (meaning t m 2027) (meaning t m 2220) (meaning t m 2542) (meaning t m 3096) (meaning t m 3574) (meaning t m 4109) (meaning t m 4509) source

theorem rule36903 (p2027 p2619 p4129 p4136 p4423 p4904 : Prop) (h : p2027 ∨ (¬ p2619) ∨ (¬ p4136) ∨ (¬ p4423) ∨ (¬ p4129) ∨ (¬ p4904)) : (p2027) ∨ (¬ p2619) ∨ (¬ p4129) ∨ (¬ p4136) ∨ (¬ p4423) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial36903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory26159 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10)
  exact rule36903 (meaning t m 2027) (meaning t m 2619) (meaning t m 4129) (meaning t m 4136) (meaning t m 4423) (meaning t m 4904) source

theorem rule36906 (p2027 p2534 p2657 p2685 p3506 p3683 p3874 p3950 p4381 p4661 p4787 : Prop) (h : (¬ p4787) ∨ (¬ p3874) ∨ (¬ p2685) ∨ (¬ p3506) ∨ (¬ p3683) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p4661) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2685) ∨ (¬ p3506) ∨ (¬ p3683) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4381) ∨ (¬ p4661) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial36906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4661)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory26162 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 3 9) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36906 (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 2685) (meaning t m 3506) (meaning t m 3683) (meaning t m 3874) (meaning t m 3950) (meaning t m 4381) (meaning t m 4661) (meaning t m 4787) source

theorem rule36907 (p2027 p2284 p3146 p3661 p4118 p4507 : Prop) (h : p2027 ∨ (¬ p4118) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4507) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial36907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory26163 t (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule36907 (meaning t m 2027) (meaning t m 2284) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 4507) source

theorem rule36911 (p1998 p2027 p2938 p3146 p3156 p4320 p4348 : Prop) (h : p2938 ∨ (¬ p1998) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p3146) ∨ (¬ p3156)) : (¬ p1998) ∨ (p2027) ∨ (p2938) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4320) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial36911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26167 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule36911 (meaning t m 1998) (meaning t m 2027) (meaning t m 2938) (meaning t m 3146) (meaning t m 3156) (meaning t m 4320) (meaning t m 4348) source

theorem rule36913 (p2027 p2589 p2659 p3156 p3413 p3694 p3695 : Prop) (h : (¬ p2659) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p3695) ∨ (¬ p3413) ∨ (¬ p3156) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p3156) ∨ (¬ p3413) ∨ (¬ p3694) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial36913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory26169 t (m.theta 0 4) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule36913 (meaning t m 2027) (meaning t m 2589) (meaning t m 2659) (meaning t m 3156) (meaning t m 3413) (meaning t m 3694) (meaning t m 3695) source

theorem rule36917 (p2027 p2166 p3554 p3872 p4129 p4442 p4509 : Prop) (h : (¬ p3554) ∨ (¬ p2166) ∨ (¬ p4509) ∨ (¬ p4442) ∨ (¬ p4129) ∨ p2027 ∨ (¬ p3872)) : (p2027) ∨ (¬ p2166) ∨ (¬ p3554) ∨ (¬ p3872) ∨ (¬ p4129) ∨ (¬ p4442) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial36917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory26173 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8) (m.theta 7 10)
  exact rule36917 (meaning t m 2027) (meaning t m 2166) (meaning t m 3554) (meaning t m 3872) (meaning t m 4129) (meaning t m 4442) (meaning t m 4509) source

theorem rule36923 (p2027 p2230 p2630 p2656 p3572 p3740 p4644 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p3740) ∨ (¬ p2630) ∨ (¬ p3572) ∨ (¬ p4644) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3572) ∨ (¬ p3740) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial36923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory26179 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule36923 (meaning t m 2027) (meaning t m 2230) (meaning t m 2630) (meaning t m 2656) (meaning t m 3572) (meaning t m 3740) (meaning t m 4644) source

theorem rule36927 (p1991 p2027 p2190 p2440 p2534 p2657 p2765 p3146 p4607 : Prop) (h : (¬ p1991) ∨ (¬ p2657) ∨ (¬ p2534) ∨ p2765 ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2190) ∨ (¬ p2440) ∨ (¬ p4607)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2190) ∨ (¬ p2440) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (p2765) ∨ (¬ p3146) ∨ (¬ p4607) := by
  classical
  tauto

theorem initial36927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4607)) := by
  have source := ElevenTheory.theory26183 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule36927 (meaning t m 1991) (meaning t m 2027) (meaning t m 2190) (meaning t m 2440) (meaning t m 2534) (meaning t m 2657) (meaning t m 2765) (meaning t m 3146) (meaning t m 4607) source

theorem rule36934 (p2027 p2751 p3027 p3256 p4044 p4340 p4359 p4392 : Prop) (h : (¬ p2751) ∨ (¬ p4340) ∨ (¬ p4392) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p4044) ∨ (¬ p4359) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial36934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory26190 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 2 8) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule36934 (meaning t m 2027) (meaning t m 2751) (meaning t m 3027) (meaning t m 3256) (meaning t m 4044) (meaning t m 4340) (meaning t m 4359) (meaning t m 4392) source

theorem rule36938 (p2027 p2230 p2440 p3475 p3572 p3759 p4650 : Prop) (h : (¬ p3572) ∨ (¬ p4650) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3759) ∨ (¬ p3475)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p3759) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial36938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory26194 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule36938 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 3475) (meaning t m 3572) (meaning t m 3759) (meaning t m 4650) source

theorem rule36943 (p1977 p2027 p2462 p2911 p2996 p3553 p4278 : Prop) (h : p2462 ∨ (¬ p2911) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2996) ∨ (¬ p3553)) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2911) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory26199 t (m.theta 1 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36943 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2911) (meaning t m 2996) (meaning t m 3553) (meaning t m 4278) source

theorem rule36950 (p1987 p2027 p2104 p2202 p2440 p2696 p3083 p5369 : Prop) (h : (¬ p3083) ∨ p2202 ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p5369) ∨ (¬ p2104)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2104) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial36950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory26206 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule36950 (meaning t m 1987) (meaning t m 2027) (meaning t m 2104) (meaning t m 2202) (meaning t m 2440) (meaning t m 2696) (meaning t m 3083) (meaning t m 5369) source

theorem rule36953 (p2027 p2098 p2138 p3952 p4188 p4316 p4509 : Prop) (h : (¬ p2098) ∨ (¬ p4188) ∨ (¬ p4316) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3952) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p3952) ∨ (¬ p4188) ∨ (¬ p4316) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial36953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory26209 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule36953 (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 3952) (meaning t m 4188) (meaning t m 4316) (meaning t m 4509) source

theorem rule36955 (p2027 p2177 p2553 p3016 p3878 p4041 : Prop) (h : (¬ p3016) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p4041) ∨ p2027 ∨ (¬ p3878)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p4041) := by
  classical
  tauto

theorem initial36955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4041)) := by
  have source := ElevenTheory.theory26211 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule36955 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 3016) (meaning t m 3878) (meaning t m 4041) source

theorem rule36957 (p2027 p2440 p2579 p3016 p3389 p4646 : Prop) (h : (¬ p3389) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p3016) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial36957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory26213 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule36957 (meaning t m 2027) (meaning t m 2440) (meaning t m 2579) (meaning t m 3016) (meaning t m 3389) (meaning t m 4646) source

theorem rule36960 (p3325 p3822 p4358 : Prop) (h : (¬ p4358) ∨ (¬ p3325) ∨ p3822) : (¬ p3325) ∨ (p3822) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial36960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3325)) ∨ (meaning t m 3822) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory26216 (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36960 (meaning t m 3325) (meaning t m 3822) (meaning t m 4358) source

theorem rule36964 (p1989 p2027 p2169 p3323 p3324 p3744 p4173 : Prop) (h : p2027 ∨ p2169 ∨ (¬ p4173) ∨ (¬ p1989) ∨ (¬ p3324) ∨ (¬ p3744) ∨ (¬ p3323)) : (¬ p1989) ∨ (p2027) ∨ (p2169) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3744) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial36964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory26220 t (m.theta 1 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule36964 (meaning t m 1989) (meaning t m 2027) (meaning t m 2169) (meaning t m 3323) (meaning t m 3324) (meaning t m 3744) (meaning t m 4173) source

theorem rule36970 (p1987 p2027 p2476 p2696 p3008 p3083 p3574 p3905 : Prop) (h : p3008 ∨ (¬ p3574) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p1987) ∨ (¬ p3905) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2696) ∨ (p3008) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial36970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory26226 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule36970 (meaning t m 1987) (meaning t m 2027) (meaning t m 2476) (meaning t m 2696) (meaning t m 3008) (meaning t m 3083) (meaning t m 3574) (meaning t m 3905) source

theorem rule36973 (p1987 p2027 p2696 p2911 p2914 p3425 p3659 : Prop) (h : (¬ p1987) ∨ p2914 ∨ (¬ p2911) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3659)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial36973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory26229 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule36973 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 2911) (meaning t m 2914) (meaning t m 3425) (meaning t m 3659) source

theorem rule36976 (p2027 p2156 p2619 p2928 p3452 p3644 p3758 p4521 p4902 : Prop) (h : (¬ p4521) ∨ (¬ p3644) ∨ (¬ p4902) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2156) ∨ (¬ p3758) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2619) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p3758) ∨ (¬ p4521) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial36976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory26232 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule36976 (meaning t m 2027) (meaning t m 2156) (meaning t m 2619) (meaning t m 2928) (meaning t m 3452) (meaning t m 3644) (meaning t m 3758) (meaning t m 4521) (meaning t m 4902) source

theorem rule36977 (p2027 p2132 p2252 p2657 p2750 p2753 p3105 p3680 p4256 p4286 p5123 : Prop) (h : (¬ p2750) ∨ (¬ p2252) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5123) ∨ (¬ p2753) ∨ (¬ p2657) ∨ (¬ p3105) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial36977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory26233 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36977 (meaning t m 2027) (meaning t m 2132) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3105) (meaning t m 3680) (meaning t m 4256) (meaning t m 4286) (meaning t m 5123) source

theorem rule36979 (p1987 p2027 p2169 p2363 p2737 p3688 p4078 p4340 : Prop) (h : p2169 ∨ (¬ p1987) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2363) ∨ (¬ p3688) ∨ (¬ p4078)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4078) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial36979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory26235 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule36979 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2737) (meaning t m 3688) (meaning t m 4078) (meaning t m 4340) source

theorem rule36980 (p1998 p2027 p2177 p2202 p2563 p3051 p3646 p4140 : Prop) (h : (¬ p4140) ∨ (¬ p3051) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2177) ∨ p2202 ∨ (¬ p2563)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial36980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory26236 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36980 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2202) (meaning t m 2563) (meaning t m 3051) (meaning t m 3646) (meaning t m 4140) source

theorem rule36981 (p2027 p2254 p2657 p3093 p3319 p3461 p4256 p4286 p5123 : Prop) (h : (¬ p4256) ∨ (¬ p3319) ∨ (¬ p4286) ∨ (¬ p3093) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p2254) ∨ (¬ p2657)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial36981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory26237 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36981 (meaning t m 2027) (meaning t m 2254) (meaning t m 2657) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 4256) (meaning t m 4286) (meaning t m 5123) source

theorem rule36984 (p2027 p2475 p3083 p3574 p4113 p4358 p5222 : Prop) (h : (¬ p3574) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p2475) ∨ (¬ p4358) ∨ (¬ p4113) ∨ (¬ p5222)) : (p2027) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p3574) ∨ (¬ p4113) ∨ (¬ p4358) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial36984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory26240 t (m.theta 0 8) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule36984 (meaning t m 2027) (meaning t m 2475) (meaning t m 3083) (meaning t m 3574) (meaning t m 4113) (meaning t m 4358) (meaning t m 5222) source

theorem rule36987 (p1987 p2027 p2274 p2696 p2765 p2780 p3568 p4337 : Prop) (h : p2765 ∨ (¬ p2274) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4337) ∨ (¬ p3568) ∨ (¬ p2780)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2696) ∨ (p2765) ∨ (¬ p2780) ∨ (¬ p3568) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial36987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory26243 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule36987 (meaning t m 1987) (meaning t m 2027) (meaning t m 2274) (meaning t m 2696) (meaning t m 2765) (meaning t m 2780) (meaning t m 3568) (meaning t m 4337) source

theorem rule36989 (p2027 p2352 p2387 p3660 p4235 p4356 p4555 : Prop) (h : (¬ p4356) ∨ (¬ p4555) ∨ (¬ p4235) ∨ (¬ p3660) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3660) ∨ (¬ p4235) ∨ (¬ p4356) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial36989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory26245 t (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule36989 (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 3660) (meaning t m 4235) (meaning t m 4356) (meaning t m 4555) source

theorem rule36995 (p2027 p2144 p2220 p2780 p3694 p4392 p4842 : Prop) (h : (¬ p3694) ∨ (¬ p2780) ∨ (¬ p2144) ∨ p2027 ∨ (¬ p4842) ∨ (¬ p4392) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2780) ∨ (¬ p3694) ∨ (¬ p4392) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial36995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory26251 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 5 8)
  exact rule36995 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2780) (meaning t m 3694) (meaning t m 4392) (meaning t m 4842) source

theorem rule36998 (p2027 p2254 p2274 p2829 p2952 p3471 p3568 p3588 p3589 p4153 p4889 : Prop) (h : (¬ p3589) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p2254) ∨ (¬ p4153) ∨ (¬ p2274) ∨ (¬ p4889) ∨ (¬ p2952) ∨ (¬ p2829) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2274) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3471) ∨ (¬ p3568) ∨ (¬ p3588) ∨ (¬ p3589) ∨ (¬ p4153) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial36998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory26254 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule36998 (meaning t m 2027) (meaning t m 2254) (meaning t m 2274) (meaning t m 2829) (meaning t m 2952) (meaning t m 3471) (meaning t m 3568) (meaning t m 3588) (meaning t m 3589) (meaning t m 4153) (meaning t m 4889) source

theorem rule36999 (p1998 p2027 p2122 p2177 p2765 p3125 p3917 : Prop) (h : (¬ p1998) ∨ (¬ p2177) ∨ p2765 ∨ (¬ p3917) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2122)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial36999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory26255 t (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule36999 (meaning t m 1998) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2765) (meaning t m 3125) (meaning t m 3917) source

theorem rule37000 (p1982 p2027 p2274 p2459 p2668 p2765 p3550 p3568 : Prop) (h : (¬ p3568) ∨ (¬ p2274) ∨ p2027 ∨ p2765 ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p3550) ∨ (¬ p2668)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2459) ∨ (¬ p2668) ∨ (p2765) ∨ (¬ p3550) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial37000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory26256 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37000 (meaning t m 1982) (meaning t m 2027) (meaning t m 2274) (meaning t m 2459) (meaning t m 2668) (meaning t m 2765) (meaning t m 3550) (meaning t m 3568) source

theorem rule37004 (p2027 p2122 p2177 p2247 p2774 p3497 p3662 p4733 p4905 : Prop) (h : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4905) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3662) ∨ (¬ p2247) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2774) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4733) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial37004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory26260 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule37004 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2247) (meaning t m 2774) (meaning t m 3497) (meaning t m 3662) (meaning t m 4733) (meaning t m 4905) source

theorem rule37005 (p2027 p2307 p2542 p2589 p2655 p2786 p2819 p3822 p4256 p4384 p4789 : Prop) (h : (¬ p4384) ∨ (¬ p3822) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2786) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial37005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory26261 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule37005 (meaning t m 2027) (meaning t m 2307) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2786) (meaning t m 2819) (meaning t m 3822) (meaning t m 4256) (meaning t m 4384) (meaning t m 4789) source

theorem rule37006 (p2027 p3537 p3588 p3821 p3959 p4666 p4804 : Prop) (h : (¬ p4804) ∨ (¬ p3959) ∨ (¬ p3537) ∨ (¬ p3821) ∨ (¬ p4666) ∨ (¬ p3588) ∨ p2027) : (p2027) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3821) ∨ (¬ p3959) ∨ (¬ p4666) ∨ (¬ p4804) := by
  classical
  tauto

theorem initial37006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4804)) := by
  have source := ElevenTheory.theory26262 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8) (m.theta 7 9)
  exact rule37006 (meaning t m 2027) (meaning t m 3537) (meaning t m 3588) (meaning t m 3821) (meaning t m 3959) (meaning t m 4666) (meaning t m 4804) source

theorem rule37009 (p2027 p2589 p2655 p2786 p3461 p3497 p3654 p3692 p3950 p4241 p4381 p4789 : Prop) (h : (¬ p3654) ∨ p2027 ∨ (¬ p2786) ∨ (¬ p4789) ∨ (¬ p3461) ∨ (¬ p2655) ∨ (¬ p3692) ∨ (¬ p4241) ∨ (¬ p3497) ∨ (¬ p2589) ∨ (¬ p4381) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2786) ∨ (¬ p3461) ∨ (¬ p3497) ∨ (¬ p3654) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4241) ∨ (¬ p4381) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial37009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory26265 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37009 (meaning t m 2027) (meaning t m 2589) (meaning t m 2655) (meaning t m 2786) (meaning t m 3461) (meaning t m 3497) (meaning t m 3654) (meaning t m 3692) (meaning t m 3950) (meaning t m 4241) (meaning t m 4381) (meaning t m 4789) source

theorem rule37010 (p2027 p2318 p2501 p2911 p3549 p3551 p3920 : Prop) (h : (¬ p2501) ∨ p2027 ∨ (¬ p2318) ∨ (¬ p3551) ∨ (¬ p2911) ∨ (¬ p3920) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2501) ∨ (¬ p2911) ∨ (¬ p3549) ∨ (¬ p3551) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial37010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory26266 t (m.theta 0 7) (m.theta 1 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37010 (meaning t m 2027) (meaning t m 2318) (meaning t m 2501) (meaning t m 2911) (meaning t m 3549) (meaning t m 3551) (meaning t m 3920) source

theorem rule37012 (p2459 p3073 p5307 : Prop) (h : (¬ p5307) ∨ (¬ p2459) ∨ p3073) : (¬ p2459) ∨ (p3073) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial37012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (meaning t m 3073) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory26268 (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37012 (meaning t m 2459) (meaning t m 3073) (meaning t m 5307) source

theorem rule37014 (p2027 p2252 p2383 p2440 p2657 p2750 p2753 p2786 p3609 p3880 p4348 p4857 p4905 : Prop) (h : (¬ p2786) ∨ (¬ p4857) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2657) ∨ (¬ p2440) ∨ (¬ p4348) ∨ (¬ p3880) ∨ (¬ p4905) ∨ (¬ p2383)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p3609) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4857) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial37014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4857)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory26270 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37014 (meaning t m 2027) (meaning t m 2252) (meaning t m 2383) (meaning t m 2440) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 2786) (meaning t m 3609) (meaning t m 3880) (meaning t m 4348) (meaning t m 4857) (meaning t m 4905) source

theorem rule37020 (p2027 p2252 p2383 p2542 p2589 p2655 p2750 p2753 p2786 p3609 p4256 p4348 p4438 p4857 : Prop) (h : (¬ p4348) ∨ (¬ p2252) ∨ (¬ p2786) ∨ p2027 ∨ (¬ p4857) ∨ (¬ p3609) ∨ (¬ p2589) ∨ (¬ p4256) ∨ (¬ p2753) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2383) ∨ (¬ p4438) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2383) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2786) ∨ (¬ p3609) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial37020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory26276 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37020 (meaning t m 2027) (meaning t m 2252) (meaning t m 2383) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2750) (meaning t m 2753) (meaning t m 2786) (meaning t m 3609) (meaning t m 4256) (meaning t m 4348) (meaning t m 4438) (meaning t m 4857) source

theorem rule37021 (p1998 p2027 p2938 p3246 p3947 p4009 p4044 p5558 : Prop) (h : (¬ p3947) ∨ p2938 ∨ p2027 ∨ (¬ p5558) ∨ (¬ p3246) ∨ (¬ p1998) ∨ (¬ p4009) ∨ (¬ p4044)) : (¬ p1998) ∨ (p2027) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4009) ∨ (¬ p4044) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial37021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory26277 t (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule37021 (meaning t m 1998) (meaning t m 2027) (meaning t m 2938) (meaning t m 3246) (meaning t m 3947) (meaning t m 4009) (meaning t m 4044) (meaning t m 5558) source

theorem rule37022 (p2027 p3343 p3857 p3858 p4256 p4685 p4695 : Prop) (h : (¬ p3858) ∨ (¬ p4685) ∨ (¬ p3857) ∨ (¬ p3343) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p4695)) : (p2027) ∨ (¬ p3343) ∨ (¬ p3857) ∨ (¬ p3858) ∨ (¬ p4256) ∨ (¬ p4685) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial37022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3858)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4685)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory26278 t (m.theta 0 8) (m.theta 1 8) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule37022 (meaning t m 2027) (meaning t m 3343) (meaning t m 3857) (meaning t m 3858) (meaning t m 4256) (meaning t m 4685) (meaning t m 4695) source

theorem rule37025 (p2027 p2187 p3097 p3550 p4107 p4666 : Prop) (h : (¬ p2187) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p3097)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial37025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory26281 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule37025 (meaning t m 2027) (meaning t m 2187) (meaning t m 3097) (meaning t m 3550) (meaning t m 4107) (meaning t m 4666) source

theorem rule37027 (p2027 p2132 p2177 p2247 p2870 p2996 p3947 p4140 p4666 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p4140) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2870) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4140) ∨ (¬ p4666) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory26283 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37027 (meaning t m 2027) (meaning t m 2132) (meaning t m 2177) (meaning t m 2247) (meaning t m 2870) (meaning t m 2996) (meaning t m 3947) (meaning t m 4140) (meaning t m 4666) (meaning t m 4733) source

theorem rule37029 (p1987 p2027 p2737 p2911 p2914 p3588 p3659 : Prop) (h : (¬ p2737) ∨ (¬ p1987) ∨ (¬ p3588) ∨ p2914 ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3659)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3588) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial37029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory26285 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule37029 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2911) (meaning t m 2914) (meaning t m 3588) (meaning t m 3659) source

theorem rule37033 (p1976 p2027 p3365 p3952 p4206 p4315 p4393 : Prop) (h : (¬ p3365) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p4315) ∨ p4206 ∨ (¬ p1976) ∨ (¬ p4393)) : (¬ p1976) ∨ (p2027) ∨ (¬ p3365) ∨ (¬ p3952) ∨ (p4206) ∨ (¬ p4315) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial37033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3952)) ∨ (meaning t m 4206) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory26289 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10)
  exact rule37033 (meaning t m 1976) (meaning t m 2027) (meaning t m 3365) (meaning t m 3952) (meaning t m 4206) (meaning t m 4315) (meaning t m 4393) source

theorem rule37038 (p2027 p2476 p2655 p3367 p3641 p4236 p4734 : Prop) (h : (¬ p2655) ∨ (¬ p3641) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p4734) ∨ (¬ p4236) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2655) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p4236) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial37038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory26294 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8)
  exact rule37038 (meaning t m 2027) (meaning t m 2476) (meaning t m 2655) (meaning t m 3367) (meaning t m 3641) (meaning t m 4236) (meaning t m 4734) source

theorem rule37041 (p2025 p3982 p4321 p5123 : Prop) (h : p5123 ∨ (¬ p2025) ∨ (¬ p4321) ∨ p3982) : (¬ p2025) ∨ (p3982) ∨ (¬ p4321) ∨ (p5123) := by
  classical
  tauto

theorem initial37041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2025)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4321)) ∨ (meaning t m 5123) := by
  have source := ElevenTheory.theory26297 t (m.theta 1 9) (m.theta 8 10) (m.theta 9 10)
  exact rule37041 (meaning t m 2025) (meaning t m 3982) (meaning t m 4321) (meaning t m 5123) source

theorem rule37047 (p1982 p2027 p2202 p2352 p2363 p3422 p3684 : Prop) (h : (¬ p2352) ∨ p2027 ∨ p2202 ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p1982) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial37047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory26303 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule37047 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2352) (meaning t m 2363) (meaning t m 3422) (meaning t m 3684) source

theorem rule37048 (p1991 p2027 p2518 p2657 p2914 p2928 p4256 : Prop) (h : p2027 ∨ (¬ p1991) ∨ (¬ p2657) ∨ (¬ p2518) ∨ (¬ p4256) ∨ p2914 ∨ (¬ p2928)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (p2914) ∨ (¬ p2928) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial37048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory26304 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule37048 (meaning t m 1991) (meaning t m 2027) (meaning t m 2518) (meaning t m 2657) (meaning t m 2914) (meaning t m 2928) (meaning t m 4256) source

theorem rule37049 (p2027 p2210 p2254 p2657 p2891 p3246 p3574 p4137 p4625 : Prop) (h : (¬ p3246) ∨ (¬ p2210) ∨ (¬ p4625) ∨ (¬ p2891) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2657) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial37049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory26305 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule37049 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2657) (meaning t m 2891) (meaning t m 3246) (meaning t m 3574) (meaning t m 4137) (meaning t m 4625) source

theorem rule37051 (p2027 p2588 p3343 p3574 p4331 p4624 : Prop) (h : p2027 ∨ (¬ p4624) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p4331) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4331) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial37051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory26307 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7) (m.theta 6 9)
  exact rule37051 (meaning t m 2027) (meaning t m 2588) (meaning t m 3343) (meaning t m 3574) (meaning t m 4331) (meaning t m 4624) source

theorem rule37052 (p2027 p2098 p2138 p2252 p2655 p2748 p3146 p3540 p3644 p4188 p5049 p5118 p5558 : Prop) (h : (¬ p2098) ∨ (¬ p3540) ∨ (¬ p4188) ∨ (¬ p5558) ∨ (¬ p2138) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p5118) ∨ (¬ p3146) ∨ (¬ p2655) ∨ (¬ p2252) ∨ (¬ p2748)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2252) ∨ (¬ p2655) ∨ (¬ p2748) ∨ (¬ p3146) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4188) ∨ (¬ p5049) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial37052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 5049)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory26308 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 2 8) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37052 (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 2252) (meaning t m 2655) (meaning t m 2748) (meaning t m 3146) (meaning t m 3540) (meaning t m 3644) (meaning t m 4188) (meaning t m 5049) (meaning t m 5118) (meaning t m 5558) source

theorem rule37053 (p2027 p2579 p2608 p3537 p3969 p4137 p4188 p4191 p5119 p5193 : Prop) (h : (¬ p2608) ∨ (¬ p4188) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p3537) ∨ (¬ p5193) ∨ (¬ p4191) ∨ (¬ p5119) ∨ (¬ p3969)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3969) ∨ (¬ p4137) ∨ (¬ p4188) ∨ (¬ p4191) ∨ (¬ p5119) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial37053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory26309 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule37053 (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 3537) (meaning t m 3969) (meaning t m 4137) (meaning t m 4188) (meaning t m 4191) (meaning t m 5119) (meaning t m 5193) source

theorem rule37059 (p1977 p2027 p2388 p2509 p2901 p3054 p3402 p3641 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p1977) ∨ (¬ p3402) ∨ p2027 ∨ (¬ p3641) ∨ p2388 ∨ (¬ p2901) ∨ (¬ p3054) ∨ (¬ p2509)) : (¬ p1977) ∨ (p2027) ∨ (p2388) ∨ (¬ p2509) ∨ (¬ p2901) ∨ (¬ p3054) ∨ (¬ p3402) ∨ (¬ p3641) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial37059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory26315 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 8) (m.theta 5 7)
  exact rule37059 (meaning t m 1977) (meaning t m 2027) (meaning t m 2388) (meaning t m 2509) (meaning t m 2901) (meaning t m 3054) (meaning t m 3402) (meaning t m 3641) (meaning t m 4244) source

theorem rule37060 (p2027 p2499 p2573 p2881 p2922 p3425 p3659 p4079 p4277 p4736 : Prop) (h : (¬ p2573) ∨ (¬ p2499) ∨ (¬ p4736) ∨ (¬ p4079) ∨ (¬ p3659) ∨ (¬ p3425) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p4277) ∨ p2027) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4079) ∨ (¬ p4277) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial37060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory26316 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 7) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule37060 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2881) (meaning t m 2922) (meaning t m 3425) (meaning t m 3659) (meaning t m 4079) (meaning t m 4277) (meaning t m 4736) source

theorem rule37062 (p2274 p2588 p3096 : Prop) (h : p3096 ∨ (¬ p2274) ∨ (¬ p2588)) : (¬ p2274) ∨ (¬ p2588) ∨ (p3096) := by
  classical
  tauto

theorem initial37062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 3096) := by
  have source := ElevenTheory.theory26318 (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule37062 (meaning t m 2274) (meaning t m 2588) (meaning t m 3096) source

theorem rule37070 (p2027 p2166 p2307 p3549 p3743 p4509 p4512 : Prop) (h : (¬ p3549) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2166) ∨ (¬ p4512) ∨ (¬ p3743) ∨ (¬ p4509)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4509) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial37070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4509)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory26326 t (m.theta 0 6) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule37070 (meaning t m 2027) (meaning t m 2166) (meaning t m 2307) (meaning t m 3549) (meaning t m 3743) (meaning t m 4509) (meaning t m 4512) source

theorem rule37071 (p1975 p2027 p2295 p2323 p2641 p3286 p3848 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2295) ∨ (¬ p1975) ∨ (¬ p3286) ∨ (¬ p3848)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p3286) ∨ (¬ p3848) := by
  classical
  tauto

theorem initial37071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3848)) := by
  have source := ElevenTheory.theory26327 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 7)
  exact rule37071 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2323) (meaning t m 2641) (meaning t m 3286) (meaning t m 3848) source

theorem rule37074 (p2027 p2741 p2797 p2839 p4154 p5052 : Prop) (h : (¬ p2741) ∨ (¬ p5052) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2741) ∨ (¬ p2797) ∨ (¬ p2839) ∨ (¬ p4154) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial37074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory26330 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6)
  exact rule37074 (meaning t m 2027) (meaning t m 2741) (meaning t m 2797) (meaning t m 2839) (meaning t m 4154) (meaning t m 5052) source

theorem rule37081 (p1981 p2027 p2323 p2641 p2651 p2668 p4111 : Prop) (h : (¬ p2668) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p1981) ∨ p2323) : (¬ p1981) ∨ (p2027) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2651) ∨ (¬ p2668) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial37081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory26337 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule37081 (meaning t m 1981) (meaning t m 2027) (meaning t m 2323) (meaning t m 2641) (meaning t m 2651) (meaning t m 2668) (meaning t m 4111) source

theorem rule37088 (p2008 p2027 p2287 p2707 p3323 p3688 p3917 : Prop) (h : (¬ p2707) ∨ (¬ p2008) ∨ (¬ p3917) ∨ (¬ p3688) ∨ p2287 ∨ p2027 ∨ (¬ p3323)) : (¬ p2008) ∨ (p2027) ∨ (p2287) ∨ (¬ p2707) ∨ (¬ p3323) ∨ (¬ p3688) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial37088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory26344 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9)
  exact rule37088 (meaning t m 2008) (meaning t m 2027) (meaning t m 2287) (meaning t m 2707) (meaning t m 3323) (meaning t m 3688) (meaning t m 3917) source

theorem rule37090 (p1992 p2027 p2598 p2780 p2997 p3585 p3822 : Prop) (h : (¬ p1992) ∨ (¬ p3585) ∨ p2997 ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3822) ∨ (¬ p2780)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3585) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial37090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory26346 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7)
  exact rule37090 (meaning t m 1992) (meaning t m 2027) (meaning t m 2598) (meaning t m 2780) (meaning t m 2997) (meaning t m 3585) (meaning t m 3822) source

theorem rule37091 (p3552 p4325 p4475 : Prop) (h : p4475 ∨ (¬ p4325) ∨ (¬ p3552)) : (¬ p3552) ∨ (¬ p4325) ∨ (p4475) := by
  classical
  tauto

theorem initial37091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4325)) ∨ (meaning t m 4475) := by
  have source := ElevenTheory.theory26347 (m.theta 2 7) (m.theta 3 7) (m.theta 6 7)
  exact rule37091 (meaning t m 3552) (meaning t m 4325) (meaning t m 4475) source

theorem rule37092 (p1979 p2027 p2579 p2608 p2766 p2839 p2860 p3952 p3956 p4347 p5193 : Prop) (h : p2027 ∨ (¬ p1979) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p2608) ∨ (¬ p2579) ∨ p2766 ∨ (¬ p2839) ∨ (¬ p3952) ∨ (¬ p5193) ∨ (¬ p2860)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3952) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial37092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory26348 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule37092 (meaning t m 1979) (meaning t m 2027) (meaning t m 2579) (meaning t m 2608) (meaning t m 2766) (meaning t m 2839) (meaning t m 2860) (meaning t m 3952) (meaning t m 3956) (meaning t m 4347) (meaning t m 5193) source

theorem rule37093 (p2027 p2192 p2743 p3371 p3758 p5052 : Prop) (h : (¬ p2743) ∨ (¬ p5052) ∨ (¬ p3371) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2743) ∨ (¬ p3371) ∨ (¬ p3758) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial37093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory26349 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule37093 (meaning t m 2027) (meaning t m 2192) (meaning t m 2743) (meaning t m 3371) (meaning t m 3758) (meaning t m 5052) source

theorem rule37095 (p1986 p2027 p2766 p2780 p3366 p3367 p4347 p4358 : Prop) (h : (¬ p4347) ∨ (¬ p3367) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p3366) ∨ p2766 ∨ (¬ p4358)) : (¬ p1986) ∨ (p2027) ∨ (p2766) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p4347) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial37095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory26351 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule37095 (meaning t m 1986) (meaning t m 2027) (meaning t m 2766) (meaning t m 2780) (meaning t m 3366) (meaning t m 3367) (meaning t m 4347) (meaning t m 4358) source

theorem rule37098 (p2027 p2104 p2911 p3471 p4800 p5083 : Prop) (h : (¬ p4800) ∨ (¬ p5083) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2911) ∨ (¬ p3471) ∨ (¬ p4800) ∨ (¬ p5083) := by
  classical
  tauto

theorem initial37098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4800)) ∨ (¬ (meaning t m 5083)) := by
  have source := ElevenTheory.theory26354 t (m.theta 0 2) (m.theta 2 7) (m.theta 2 8) (m.theta 4 7) (m.theta 7 8)
  exact rule37098 (meaning t m 2027) (meaning t m 2104) (meaning t m 2911) (meaning t m 3471) (meaning t m 4800) (meaning t m 5083) source

theorem rule37099 (p2027 p2192 p2210 p2254 p2274 p2911 p3414 p3553 p4712 : Prop) (h : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p4712) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2254) ∨ (¬ p3414) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2274) ∨ (¬ p2911) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial37099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory26355 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule37099 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2274) (meaning t m 2911) (meaning t m 3414) (meaning t m 3553) (meaning t m 4712) source

theorem rule37101 (p1986 p2027 p2598 p2766 p3425 p3644 p4106 p4348 : Prop) (h : (¬ p4106) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p3425) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p3644)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p3425) ∨ (¬ p3644) ∨ (¬ p4106) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial37101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory26357 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37101 (meaning t m 1986) (meaning t m 2027) (meaning t m 2598) (meaning t m 2766) (meaning t m 3425) (meaning t m 3644) (meaning t m 4106) (meaning t m 4348) source

theorem rule37109 (p1988 p2027 p2187 p2192 p2363 p2873 p3266 : Prop) (h : (¬ p2192) ∨ p2873 ∨ (¬ p2363) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2187) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (p2873) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial37109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory26365 t (m.theta 1 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule37109 (meaning t m 1988) (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2363) (meaning t m 2873) (meaning t m 3266) source

theorem rule37112 (p1981 p2881 p2938 p4133 : Prop) (h : (¬ p2881) ∨ (¬ p1981) ∨ p2938 ∨ p4133) : (¬ p1981) ∨ (¬ p2881) ∨ (p2938) ∨ (p4133) := by
  classical
  tauto

theorem initial37112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (meaning t m 4133) := by
  have source := ElevenTheory.theory26368 t (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule37112 (meaning t m 1981) (meaning t m 2881) (meaning t m 2938) (meaning t m 4133) source

theorem rule37113 (p3583 p4242 p4359 : Prop) (h : (¬ p3583) ∨ (¬ p4359) ∨ p4242) : (¬ p3583) ∨ (p4242) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial37113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3583)) ∨ (meaning t m 4242) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory26369 (m.theta 1 2) (m.theta 2 5) (m.theta 2 8)
  exact rule37113 (meaning t m 3583) (meaning t m 4242) (meaning t m 4359) source

theorem rule37114 (p2027 p2598 p2952 p3136 p4236 p4752 : Prop) (h : (¬ p3136) ∨ (¬ p4236) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p4752) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial37114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory26370 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule37114 (meaning t m 2027) (meaning t m 2598) (meaning t m 2952) (meaning t m 3136) (meaning t m 4236) (meaning t m 4752) source

theorem rule37115 (p2027 p2774 p2952 p3136 p4236 p4845 : Prop) (h : (¬ p3136) ∨ (¬ p4236) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p4845) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4236) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial37115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory26371 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5)
  exact rule37115 (meaning t m 2027) (meaning t m 2774) (meaning t m 2952) (meaning t m 3136) (meaning t m 4236) (meaning t m 4845) source

theorem rule37116 (p1975 p2027 p2295 p2331 p2622 p2952 p3136 : Prop) (h : p2027 ∨ (¬ p3136) ∨ (¬ p2331) ∨ p2622 ∨ (¬ p2952) ∨ (¬ p1975) ∨ (¬ p2295)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2622) ∨ (¬ p2952) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial37116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory26372 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule37116 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2622) (meaning t m 2952) (meaning t m 3136) source

theorem rule37117 (p1981 p2027 p2331 p2622 p2668 p2952 p3136 : Prop) (h : p2027 ∨ (¬ p3136) ∨ (¬ p2331) ∨ (¬ p2952) ∨ p2622 ∨ (¬ p1981) ∨ (¬ p2668)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2331) ∨ (p2622) ∨ (¬ p2668) ∨ (¬ p2952) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial37117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory26373 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 8)
  exact rule37117 (meaning t m 1981) (meaning t m 2027) (meaning t m 2331) (meaning t m 2622) (meaning t m 2668) (meaning t m 2952) (meaning t m 3136) source

theorem rule37118 (p2003 p2027 p2387 p2622 p2743 p2819 p2829 : Prop) (h : (¬ p2819) ∨ (¬ p2003) ∨ p2027 ∨ p2622 ∨ (¬ p2387) ∨ (¬ p2743) ∨ (¬ p2829)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2387) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2819) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial37118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory26374 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule37118 (meaning t m 2003) (meaning t m 2027) (meaning t m 2387) (meaning t m 2622) (meaning t m 2743) (meaning t m 2819) (meaning t m 2829) source

theorem rule37121 (p2027 p2156 p2274 p2396 p3585 p3954 p4521 p4641 p5160 : Prop) (h : (¬ p4521) ∨ (¬ p2156) ∨ (¬ p5160) ∨ (¬ p3954) ∨ (¬ p4641) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial37121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory26377 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule37121 (meaning t m 2027) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 3585) (meaning t m 3954) (meaning t m 4521) (meaning t m 4641) (meaning t m 5160) source

theorem rule37122 (p1998 p2027 p2177 p2499 p3008 p3801 p4260 p5507 : Prop) (h : p3008 ∨ (¬ p4260) ∨ (¬ p2177) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3801) ∨ (¬ p5507)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2499) ∨ (p3008) ∨ (¬ p3801) ∨ (¬ p4260) ∨ (¬ p5507) := by
  classical
  tauto

theorem initial37122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3801)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 5507)) := by
  have source := ElevenTheory.theory26378 t (m.theta 1 4) (m.theta 4 10) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule37122 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2499) (meaning t m 3008) (meaning t m 3801) (meaning t m 4260) (meaning t m 5507) source

theorem rule37123 (p2027 p2307 p2696 p2779 p3055 p3097 p3125 p3985 p5049 p5160 p5325 : Prop) (h : (¬ p2307) ∨ (¬ p3055) ∨ (¬ p2696) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p3985) ∨ (¬ p5325) ∨ (¬ p2779) ∨ (¬ p5160) ∨ (¬ p5049)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2696) ∨ (¬ p2779) ∨ (¬ p3055) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3985) ∨ (¬ p5049) ∨ (¬ p5160) ∨ (¬ p5325) := by
  classical
  tauto

theorem initial37123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 5049)) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5325)) := by
  have source := ElevenTheory.theory26379 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 2 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule37123 (meaning t m 2027) (meaning t m 2307) (meaning t m 2696) (meaning t m 2779) (meaning t m 3055) (meaning t m 3097) (meaning t m 3125) (meaning t m 3985) (meaning t m 5049) (meaning t m 5160) (meaning t m 5325) source

theorem rule37124 (p2027 p2247 p2761 p3051 p3246 p4360 p4521 p5123 p5600 : Prop) (h : (¬ p4360) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p5600) ∨ (¬ p4521) ∨ (¬ p3051) ∨ (¬ p2247) ∨ (¬ p3246) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4360) ∨ (¬ p4521) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial37124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory26380 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule37124 (meaning t m 2027) (meaning t m 2247) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 4360) (meaning t m 4521) (meaning t m 5123) (meaning t m 5600) source

theorem rule37125 (p2668 p3745 p3989 : Prop) (h : (¬ p2668) ∨ (¬ p3745) ∨ (¬ p3989)) : (¬ p2668) ∨ (¬ p3745) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial37125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory26381 (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule37125 (meaning t m 2668) (meaning t m 3745) (meaning t m 3989) source

theorem rule37126 (p2187 p2668 p3745 : Prop) (h : (¬ p2668) ∨ (¬ p3745) ∨ p2187) : (p2187) ∨ (¬ p2668) ∨ (¬ p3745) := by
  classical
  tauto

theorem initial37126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3745)) := by
  have source := ElevenTheory.theory26382 (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule37126 (meaning t m 2187) (meaning t m 2668) (meaning t m 3745) source

theorem rule37127 (p2027 p2696 p2779 p3055 p3461 p3654 p3985 p4381 p4641 p5049 p5160 : Prop) (h : p2027 ∨ (¬ p3055) ∨ (¬ p2696) ∨ (¬ p5160) ∨ (¬ p4641) ∨ (¬ p3654) ∨ (¬ p4381) ∨ (¬ p3985) ∨ (¬ p5049) ∨ (¬ p3461) ∨ (¬ p2779)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2779) ∨ (¬ p3055) ∨ (¬ p3461) ∨ (¬ p3654) ∨ (¬ p3985) ∨ (¬ p4381) ∨ (¬ p4641) ∨ (¬ p5049) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial37127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5049)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory26383 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 2 6) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule37127 (meaning t m 2027) (meaning t m 2696) (meaning t m 2779) (meaning t m 3055) (meaning t m 3461) (meaning t m 3654) (meaning t m 3985) (meaning t m 4381) (meaning t m 4641) (meaning t m 5049) (meaning t m 5160) source

theorem rule37130 (p2668 p3956 p4389 : Prop) (h : (¬ p4389) ∨ (¬ p2668) ∨ (¬ p3956)) : (¬ p2668) ∨ (¬ p3956) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial37130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory26386 (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule37130 (meaning t m 2668) (meaning t m 3956) (meaning t m 4389) source

theorem rule37131 (p2027 p3256 p3692 p4110 p4355 p4437 p4509 : Prop) (h : (¬ p4509) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p4437) ∨ (¬ p4355) ∨ (¬ p4110)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4110) ∨ (¬ p4355) ∨ (¬ p4437) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial37131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4437)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory26387 t (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule37131 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 4110) (meaning t m 4355) (meaning t m 4437) (meaning t m 4509) source

theorem rule37134 (p4436 p4492 p4874 : Prop) (h : (¬ p4492) ∨ (¬ p4874) ∨ p4436) : (p4436) ∨ (¬ p4492) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial37134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4436) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory26390 (m.theta 1 2) (m.theta 1 5) (m.theta 1 8)
  exact rule37134 (meaning t m 4436) (meaning t m 4492) (meaning t m 4874) source

theorem rule37135 (p1987 p2027 p2202 p2563 p2737 p3583 p3758 : Prop) (h : (¬ p2737) ∨ (¬ p3583) ∨ (¬ p2563) ∨ (¬ p3758) ∨ (¬ p1987) ∨ p2027 ∨ p2202) : (¬ p1987) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2737) ∨ (¬ p3583) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial37135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory26391 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule37135 (meaning t m 1987) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2737) (meaning t m 3583) (meaning t m 3758) source

theorem rule37137 (p2027 p2737 p2797 p2963 p4236 p4734 : Prop) (h : (¬ p4236) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2963) ∨ (¬ p4734)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial37137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory26393 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6)
  exact rule37137 (meaning t m 2027) (meaning t m 2737) (meaning t m 2797) (meaning t m 2963) (meaning t m 4236) (meaning t m 4734) source

theorem rule37139 (p2027 p2138 p2911 p3367 p3389 p3759 p3989 p4173 p4243 p4503 p4734 : Prop) (h : (¬ p3389) ∨ (¬ p4243) ∨ (¬ p4173) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3759) ∨ (¬ p2138) ∨ (¬ p4734) ∨ (¬ p2911) ∨ (¬ p4503) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4503) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial37139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory26395 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule37139 (meaning t m 2027) (meaning t m 2138) (meaning t m 2911) (meaning t m 3367) (meaning t m 3389) (meaning t m 3759) (meaning t m 3989) (meaning t m 4173) (meaning t m 4243) (meaning t m 4503) (meaning t m 4734) source

theorem rule37140 (p2027 p2248 p2352 p2651 p3016 p3588 p3659 p3954 p4133 : Prop) (h : (¬ p3588) ∨ (¬ p2651) ∨ (¬ p2248) ∨ (¬ p2352) ∨ (¬ p3016) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p4133) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2352) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial37140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory26396 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8)
  exact rule37140 (meaning t m 2027) (meaning t m 2248) (meaning t m 2352) (meaning t m 2651) (meaning t m 3016) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4133) source

theorem rule37145 (p1997 p2027 p2545 p2901 p2992 p4111 p4235 : Prop) (h : p2027 ∨ p2545 ∨ (¬ p4235) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p1997) ∨ (¬ p2901)) : (¬ p1997) ∨ (p2027) ∨ (p2545) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial37145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory26401 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule37145 (meaning t m 1997) (meaning t m 2027) (meaning t m 2545) (meaning t m 2901) (meaning t m 2992) (meaning t m 4111) (meaning t m 4235) source

theorem rule37146 (p2027 p2139 p2911 p3051 p3365 p3941 p4001 p4035 p5119 p5284 : Prop) (h : (¬ p2911) ∨ (¬ p3365) ∨ (¬ p4001) ∨ p2027 ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p3051) ∨ (¬ p4035) ∨ (¬ p2139) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2911) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3941) ∨ (¬ p4001) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial37146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory26402 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 9) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule37146 (meaning t m 2027) (meaning t m 2139) (meaning t m 2911) (meaning t m 3051) (meaning t m 3365) (meaning t m 3941) (meaning t m 4001) (meaning t m 4035) (meaning t m 5119) (meaning t m 5284) source

theorem rule37147 (p1987 p2027 p2417 p2737 p2914 p3363 p3585 p3821 p5197 : Prop) (h : p2914 ∨ (¬ p5197) ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p3821) ∨ (¬ p2737) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2417)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2737) ∨ (p2914) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3821) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial37147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory26403 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9)
  exact rule37147 (meaning t m 1987) (meaning t m 2027) (meaning t m 2417) (meaning t m 2737) (meaning t m 2914) (meaning t m 3363) (meaning t m 3585) (meaning t m 3821) (meaning t m 5197) source

theorem rule37148 (p2027 p2957 p3646 p3755 p4039 p4315 p5046 : Prop) (h : (¬ p4039) ∨ (¬ p4315) ∨ (¬ p3755) ∨ (¬ p2957) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p5046)) : (p2027) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4039) ∨ (¬ p4315) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial37148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory26404 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 6) (m.theta 5 9)
  exact rule37148 (meaning t m 2027) (meaning t m 2957) (meaning t m 3646) (meaning t m 3755) (meaning t m 4039) (meaning t m 4315) (meaning t m 5046) source

theorem rule37152 (p2027 p2132 p2166 p2655 p2743 p3146 p3361 p3540 p4278 p4418 p4669 p4737 : Prop) (h : (¬ p4669) ∨ (¬ p2132) ∨ (¬ p2743) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p4737) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4418) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p2655) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3361) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4418) ∨ (¬ p4669) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial37152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory26408 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule37152 (meaning t m 2027) (meaning t m 2132) (meaning t m 2166) (meaning t m 2655) (meaning t m 2743) (meaning t m 3146) (meaning t m 3361) (meaning t m 3540) (meaning t m 4278) (meaning t m 4418) (meaning t m 4669) (meaning t m 4737) source

theorem rule37157 (p4243 p4363 p4385 : Prop) (h : (¬ p4243) ∨ (¬ p4363) ∨ p4385) : (¬ p4243) ∨ (¬ p4363) ∨ (p4385) := by
  classical
  tauto

theorem initial37157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4363)) ∨ (meaning t m 4385) := by
  have source := ElevenTheory.theory26413 (m.theta 1 5) (m.theta 2 5) (m.theta 5 9)
  exact rule37157 (meaning t m 4243) (meaning t m 4363) (meaning t m 4385) source

theorem rule37162 (p2027 p2331 p2459 p2476 p2534 p3005 p4117 p4195 p4550 p4729 : Prop) (h : (¬ p2534) ∨ (¬ p3005) ∨ (¬ p4195) ∨ (¬ p2331) ∨ (¬ p2476) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4117) ∨ (¬ p4550)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3005) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4550) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial37162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory26418 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37162 (meaning t m 2027) (meaning t m 2331) (meaning t m 2459) (meaning t m 2476) (meaning t m 2534) (meaning t m 3005) (meaning t m 4117) (meaning t m 4195) (meaning t m 4550) (meaning t m 4729) source

theorem rule37166 (p2220 p2957 p3156 : Prop) (h : p2957 ∨ (¬ p2220) ∨ p3156) : (¬ p2220) ∨ (p2957) ∨ (p3156) := by
  classical
  tauto

theorem initial37166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (meaning t m 2957) ∨ (meaning t m 3156) := by
  have source := ElevenTheory.theory26422 (m.theta 0 5) (m.theta 3 5) (m.theta 5 8)
  exact rule37166 (meaning t m 2220) (meaning t m 2957) (meaning t m 3156) source

theorem rule37172 (p1979 p2027 p2608 p2699 p2839 p2870 p4320 : Prop) (h : (¬ p2839) ∨ p2027 ∨ (¬ p1979) ∨ p2699 ∨ (¬ p2608) ∨ (¬ p2870) ∨ (¬ p4320)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial37172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory26428 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule37172 (meaning t m 1979) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2870) (meaning t m 4320) source

theorem rule37176 (p2027 p3537 p3585 p3684 p4610 p5373 : Prop) (h : (¬ p5373) ∨ (¬ p3684) ∨ (¬ p3585) ∨ (¬ p4610) ∨ p2027 ∨ (¬ p3537)) : (p2027) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4610) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial37176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory26432 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 8)
  exact rule37176 (meaning t m 2027) (meaning t m 3537) (meaning t m 3585) (meaning t m 3684) (meaning t m 4610) (meaning t m 5373) source

theorem rule37181 (p2005 p2027 p2873 p3422 p3631 p3876 p4278 p4431 : Prop) (h : p2873 ∨ (¬ p3631) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p2005) ∨ (¬ p4431) ∨ (¬ p4278) ∨ (¬ p3876)) : (¬ p2005) ∨ (p2027) ∨ (p2873) ∨ (¬ p3422) ∨ (¬ p3631) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial37181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory26437 t (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule37181 (meaning t m 2005) (meaning t m 2027) (meaning t m 2873) (meaning t m 3422) (meaning t m 3631) (meaning t m 3876) (meaning t m 4278) (meaning t m 4431) source

end SunPrize.SMT
