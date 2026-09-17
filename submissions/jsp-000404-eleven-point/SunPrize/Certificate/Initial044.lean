import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory028
import SunPrize.Certificate.Theory029
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule19861 (p2839 p3054 p3585 : Prop) (h : (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3054)) : (¬ p2839) ∨ (¬ p3054) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial19861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory9117 (m.theta 1 2) (m.theta 2 4) (m.theta 2 5)
  exact rule19861 (meaning t m 2839) (meaning t m 3054) (meaning t m 3585) source

theorem rule19863 (p3707 p4322 p4388 : Prop) (h : (¬ p4322) ∨ (¬ p3707) ∨ (¬ p4388)) : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4388) := by
  classical
  tauto

theorem initial19863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4388)) := by
  have source := ElevenTheory.theory9119 (m.theta 1 9) (m.theta 5 9) (m.theta 9 10)
  exact rule19863 (meaning t m 3707) (meaning t m 4322) (meaning t m 4388) source

theorem rule19864 (p2027 p3707 p4322 p4385 p4878 p4942 : Prop) (h : (¬ p4878) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4942)) : (p2027) ∨ (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4878) ∨ (¬ p4942) := by
  classical
  tauto

theorem initial19864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4878)) ∨ (¬ (meaning t m 4942)) := by
  have source := ElevenTheory.theory9120 t (m.theta 1 5) (m.theta 1 9) (m.theta 2 5) (m.theta 5 9) (m.theta 9 10)
  exact rule19864 (meaning t m 2027) (meaning t m 3707) (meaning t m 4322) (meaning t m 4385) (meaning t m 4878) (meaning t m 4942) source

theorem rule19866 (p2761 p3773 p5299 : Prop) (h : (¬ p2761) ∨ (¬ p3773) ∨ (¬ p5299)) : (¬ p2761) ∨ (¬ p3773) ∨ (¬ p5299) := by
  classical
  tauto

theorem initial19866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 5299)) := by
  have source := ElevenTheory.theory9122 (m.theta 0 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19866 (meaning t m 2761) (meaning t m 3773) (meaning t m 5299) source

theorem rule19867 (p3506 p4381 p4656 : Prop) (h : (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4656)) : (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial19867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory9123 (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19867 (meaning t m 3506) (meaning t m 4381) (meaning t m 4656) source

theorem rule19868 (p2657 p2807 p4112 : Prop) (h : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p4112)) : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial19868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory9124 (m.theta 0 3) (m.theta 3 4) (m.theta 3 7)
  exact rule19868 (meaning t m 2657) (meaning t m 2807) (meaning t m 4112) source

theorem rule19869 (p2363 p4326 p4340 : Prop) (h : (¬ p4340) ∨ (¬ p2363) ∨ (¬ p4326)) : (¬ p2363) ∨ (¬ p4326) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial19869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory9125 (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19869 (meaning t m 2363) (meaning t m 4326) (meaning t m 4340) source

theorem rule19870 (p2341 p3543 p3548 : Prop) (h : (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3543)) : (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial19870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory9126 (m.theta 0 7) (m.theta 1 7) (m.theta 7 8)
  exact rule19870 (meaning t m 2341) (meaning t m 3543) (meaning t m 3548) source

theorem rule19871 (p2901 p3952 p4204 : Prop) (h : (¬ p3952) ∨ (¬ p2901) ∨ (¬ p4204)) : (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial19871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory9127 (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule19871 (meaning t m 2901) (meaning t m 3952) (meaning t m 4204) source

theorem rule19873 (p2598 p3425 p5085 : Prop) (h : (¬ p2598) ∨ (¬ p3425) ∨ (¬ p5085)) : (¬ p2598) ∨ (¬ p3425) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial19873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory9129 (m.theta 0 2) (m.theta 2 4) (m.theta 2 7)
  exact rule19873 (meaning t m 2598) (meaning t m 3425) (meaning t m 5085) source

theorem rule19874 (p2027 p2589 p2608 p2737 p3005 p3989 p4110 p4771 p5193 : Prop) (h : (¬ p4110) ∨ (¬ p4771) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p2608) ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4771) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial19874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory9130 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule19874 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 2737) (meaning t m 3005) (meaning t m 3989) (meaning t m 4110) (meaning t m 4771) (meaning t m 5193) source

theorem rule19875 (p2027 p2341 p2459 p2952 p3266 p3952 p4393 p4850 p5248 : Prop) (h : (¬ p4850) ∨ (¬ p2341) ∨ (¬ p3266) ∨ (¬ p2459) ∨ (¬ p4393) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p5248)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5248) := by
  classical
  tauto

theorem initial19875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4850)) ∨ (¬ (meaning t m 5248)) := by
  have source := ElevenTheory.theory9131 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19875 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2952) (meaning t m 3266) (meaning t m 3952) (meaning t m 4393) (meaning t m 4850) (meaning t m 5248) source

theorem rule19876 (p2027 p2341 p2459 p2952 p3266 p3952 p4393 p4850 p5254 : Prop) (h : (¬ p4850) ∨ (¬ p2341) ∨ (¬ p3266) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p4393) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p5254)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial19876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4850)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory9132 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19876 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2952) (meaning t m 3266) (meaning t m 3952) (meaning t m 4393) (meaning t m 4850) (meaning t m 5254) source

theorem rule19880 (p2331 p2657 p4421 p5170 : Prop) (h : (¬ p5170) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4421)) : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4421) ∨ (¬ p5170) := by
  classical
  tauto

theorem initial19880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 5170)) := by
  have source := ElevenTheory.theory9136 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 9)
  exact rule19880 (meaning t m 2331) (meaning t m 2657) (meaning t m 4421) (meaning t m 5170) source

theorem rule19881 (p2331 p2657 p4194 : Prop) (h : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4194)) : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial19881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory9137 (m.theta 0 3) (m.theta 3 4) (m.theta 3 6)
  exact rule19881 (meaning t m 2331) (meaning t m 2657) (meaning t m 4194) source

theorem rule19882 (p2027 p3461 p3990 p4348 p4444 p4503 : Prop) (h : (¬ p4444) ∨ (¬ p4348) ∨ (¬ p3461) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p3990)) : (p2027) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial19882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory9138 t (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19882 (meaning t m 2027) (meaning t m 3461) (meaning t m 3990) (meaning t m 4348) (meaning t m 4444) (meaning t m 4503) source

theorem rule19883 (p2553 p3568 p3984 : Prop) (h : (¬ p3568) ∨ (¬ p2553) ∨ (¬ p3984)) : (¬ p2553) ∨ (¬ p3568) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial19883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory9139 (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19883 (meaning t m 2553) (meaning t m 3568) (meaning t m 3984) source

theorem rule19884 (p2396 p3547 p3817 : Prop) (h : (¬ p3817) ∨ (¬ p3547) ∨ (¬ p2396)) : (¬ p2396) ∨ (¬ p3547) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial19884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory9140 (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule19884 (meaning t m 2396) (meaning t m 3547) (meaning t m 3817) source

theorem rule19885 (p2027 p2476 p3355 p4261 p4685 p4695 : Prop) (h : (¬ p2476) ∨ (¬ p4261) ∨ (¬ p3355) ∨ p2027 ∨ (¬ p4685) ∨ (¬ p4695)) : (p2027) ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4261) ∨ (¬ p4685) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial19885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4685)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory9141 t (m.theta 0 4) (m.theta 1 8) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule19885 (meaning t m 2027) (meaning t m 2476) (meaning t m 3355) (meaning t m 4261) (meaning t m 4685) (meaning t m 4695) source

theorem rule19888 (p3266 p4425 p4695 : Prop) (h : (¬ p3266) ∨ (¬ p4425) ∨ (¬ p4695)) : (¬ p3266) ∨ (¬ p4425) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial19888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory9144 (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19888 (meaning t m 3266) (meaning t m 4425) (meaning t m 4695) source

theorem rule19889 (p2972 p4385 p4418 : Prop) (h : (¬ p4385) ∨ (¬ p2972) ∨ (¬ p4418)) : (¬ p2972) ∨ (¬ p4385) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial19889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory9145 (m.theta 1 5) (m.theta 2 5) (m.theta 5 9)
  exact rule19889 (meaning t m 2972) (meaning t m 4385) (meaning t m 4418) source

theorem rule19890 (p2027 p2972 p3371 p3585 p4385 p4884 : Prop) (h : p2027 ∨ (¬ p4884) ∨ (¬ p4385) ∨ (¬ p3585) ∨ (¬ p2972) ∨ (¬ p3371)) : (p2027) ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p4385) ∨ (¬ p4884) := by
  classical
  tauto

theorem initial19890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4884)) := by
  have source := ElevenTheory.theory9146 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 9)
  exact rule19890 (meaning t m 2027) (meaning t m 2972) (meaning t m 3371) (meaning t m 3585) (meaning t m 4385) (meaning t m 4884) source

theorem rule19891 (p2230 p2656 p3574 p3660 : Prop) (h : (¬ p3574) ∨ (¬ p2656) ∨ (¬ p2230) ∨ (¬ p3660)) : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3574) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial19891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory9147 (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19891 (meaning t m 2230) (meaning t m 2656) (meaning t m 3574) (meaning t m 3660) source

theorem rule19892 (p2797 p3572 p4156 : Prop) (h : (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4156)) : (¬ p2797) ∨ (¬ p3572) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial19892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory9148 (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule19892 (meaning t m 2797) (meaning t m 3572) (meaning t m 4156) source

theorem rule19898 (p2383 p3923 p5016 : Prop) (h : (¬ p3923) ∨ (¬ p2383) ∨ (¬ p5016)) : (¬ p2383) ∨ (¬ p3923) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial19898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory9154 (m.theta 0 6) (m.theta 1 6) (m.theta 6 8)
  exact rule19898 (meaning t m 2383) (meaning t m 3923) (meaning t m 5016) source

theorem rule19904 (p2027 p2156 p2850 p3096 p3370 p3584 p4632 : Prop) (h : p2027 ∨ (¬ p2850) ∨ (¬ p3584) ∨ (¬ p3370) ∨ (¬ p4632) ∨ (¬ p2156) ∨ (¬ p3096)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3370) ∨ (¬ p3584) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial19904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory9160 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule19904 (meaning t m 2027) (meaning t m 2156) (meaning t m 2850) (meaning t m 3096) (meaning t m 3370) (meaning t m 3584) (meaning t m 4632) source

theorem rule19905 (p2850 p3584 p3660 : Prop) (h : (¬ p3584) ∨ (¬ p2850) ∨ (¬ p3660)) : (¬ p2850) ∨ (¬ p3584) ∨ (¬ p3660) := by
  classical
  tauto

theorem initial19905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3660)) := by
  have source := ElevenTheory.theory9161 (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19905 (meaning t m 2850) (meaning t m 3584) (meaning t m 3660) source

theorem rule19906 (p1994 p2027 p2873 p2922 p3379 p3555 p3742 : Prop) (h : p2873 ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p2922) ∨ (¬ p1994) ∨ p2027 ∨ (¬ p3742)) : (¬ p1994) ∨ (p2027) ∨ (p2873) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial19906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory9162 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7)
  exact rule19906 (meaning t m 1994) (meaning t m 2027) (meaning t m 2873) (meaning t m 2922) (meaning t m 3379) (meaning t m 3555) (meaning t m 3742) source

theorem rule19909 (p1977 p2241 p2248 p2323 : Prop) (h : p2323 ∨ p2248 ∨ (¬ p2241) ∨ (¬ p1977)) : (¬ p1977) ∨ (¬ p2241) ∨ (p2248) ∨ (p2323) := by
  classical
  tauto

theorem initial19909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2248) ∨ (meaning t m 2323) := by
  have source := ElevenTheory.theory9165 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule19909 (meaning t m 1977) (meaning t m 2241) (meaning t m 2248) (meaning t m 2323) source

theorem rule19911 (p3434 p4106 p4278 : Prop) (h : (¬ p4106) ∨ (¬ p3434) ∨ (¬ p4278)) : (¬ p3434) ∨ (¬ p4106) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial19911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory9167 (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule19911 (meaning t m 3434) (meaning t m 4106) (meaning t m 4278) source

theorem rule19922 (p2493 p3584 p3590 : Prop) (h : (¬ p3590) ∨ (¬ p3584) ∨ (¬ p2493)) : (¬ p2493) ∨ (¬ p3584) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial19922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory9178 (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule19922 (meaning t m 2493) (meaning t m 3584) (meaning t m 3590) source

theorem rule19924 (p2753 p3471 p3585 p3686 : Prop) (h : (¬ p3471) ∨ (¬ p2753) ∨ (¬ p3585) ∨ (¬ p3686)) : (¬ p2753) ∨ (¬ p3471) ∨ (¬ p3585) ∨ (¬ p3686) := by
  classical
  tauto

theorem initial19924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3686)) := by
  have source := ElevenTheory.theory9180 (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7)
  exact rule19924 (meaning t m 2753) (meaning t m 3471) (meaning t m 3585) (meaning t m 3686) source

theorem rule19927 (p3461 p4321 p5152 : Prop) (h : (¬ p3461) ∨ (¬ p4321) ∨ (¬ p5152)) : (¬ p3461) ∨ (¬ p4321) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial19927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory9183 (m.theta 1 9) (m.theta 6 9) (m.theta 9 10)
  exact rule19927 (meaning t m 3461) (meaning t m 4321) (meaning t m 5152) source

theorem rule19928 (p3266 p4381 p4443 : Prop) (h : (¬ p3266) ∨ (¬ p4381) ∨ (¬ p4443)) : (¬ p3266) ∨ (¬ p4381) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial19928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory9184 (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19928 (meaning t m 3266) (meaning t m 4381) (meaning t m 4443) source

theorem rule19929 (p2417 p3921 p4107 : Prop) (h : (¬ p3921) ∨ (¬ p2417) ∨ (¬ p4107)) : (¬ p2417) ∨ (¬ p3921) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial19929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory9185 (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule19929 (meaning t m 2417) (meaning t m 3921) (meaning t m 4107) source

theorem rule19930 (p3389 p3759 p3876 : Prop) (h : (¬ p3759) ∨ (¬ p3389) ∨ (¬ p3876)) : (¬ p3389) ∨ (¬ p3759) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial19930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory9186 (m.theta 0 4) (m.theta 2 4) (m.theta 4 7)
  exact rule19930 (meaning t m 3389) (meaning t m 3759) (meaning t m 3876) source

theorem rule19933 (p2427 p4192 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p2427) ∨ (¬ p4192)) : (¬ p2427) ∨ (¬ p4192) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial19933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory9189 (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule19933 (meaning t m 2427) (meaning t m 4192) (meaning t m 4948) source

theorem rule19935 (p2027 p2187 p2307 p2387 p3549 p4514 : Prop) (h : p2027 ∨ (¬ p4514) ∨ (¬ p3549) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3549) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial19935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory9191 t (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19935 (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2387) (meaning t m 3549) (meaning t m 4514) source

theorem rule19937 (p2743 p3599 p5453 : Prop) (h : (¬ p2743) ∨ (¬ p3599) ∨ (¬ p5453)) : (¬ p2743) ∨ (¬ p3599) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial19937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory9193 (m.theta 1 2) (m.theta 2 3) (m.theta 2 9)
  exact rule19937 (meaning t m 2743) (meaning t m 3599) (meaning t m 5453) source

theorem rule19938 (p2352 p2588 p3955 : Prop) (h : (¬ p3955) ∨ (¬ p2588) ∨ (¬ p2352)) : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial19938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory9194 (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19938 (meaning t m 2352) (meaning t m 2588) (meaning t m 3955) source

theorem rule19939 (p2295 p3822 p4328 : Prop) (h : (¬ p2295) ∨ (¬ p3822) ∨ (¬ p4328)) : (¬ p2295) ∨ (¬ p3822) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial19939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory9195 (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule19939 (meaning t m 2295) (meaning t m 3822) (meaning t m 4328) source

theorem rule19940 (p3266 p4321 p4352 : Prop) (h : (¬ p3266) ∨ (¬ p4321) ∨ (¬ p4352)) : (¬ p3266) ∨ (¬ p4321) ∨ (¬ p4352) := by
  classical
  tauto

theorem initial19940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4352)) := by
  have source := ElevenTheory.theory9196 (m.theta 1 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19940 (meaning t m 3266) (meaning t m 4321) (meaning t m 4352) source

theorem rule19941 (p2383 p3946 p3990 : Prop) (h : (¬ p3946) ∨ (¬ p2383) ∨ (¬ p3990)) : (¬ p2383) ∨ (¬ p3946) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial19941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory9197 (m.theta 0 6) (m.theta 6 8) (m.theta 6 9)
  exact rule19941 (meaning t m 2383) (meaning t m 3946) (meaning t m 3990) source

theorem rule19942 (p2307 p3097 p3743 : Prop) (h : (¬ p3743) ∨ (¬ p2307) ∨ (¬ p3097)) : (¬ p2307) ∨ (¬ p3097) ∨ (¬ p3743) := by
  classical
  tauto

theorem initial19942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3743)) := by
  have source := ElevenTheory.theory9198 (m.theta 0 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19942 (meaning t m 2307) (meaning t m 3097) (meaning t m 3743) source

theorem rule19943 (p2619 p3758 p3988 : Prop) (h : (¬ p2619) ∨ (¬ p3758) ∨ (¬ p3988)) : (¬ p2619) ∨ (¬ p3758) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial19943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory9199 (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule19943 (meaning t m 2619) (meaning t m 3758) (meaning t m 3988) source

theorem rule19944 (p3063 p3549 p3955 : Prop) (h : (¬ p3549) ∨ (¬ p3063) ∨ (¬ p3955)) : (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial19944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory9200 (m.theta 1 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19944 (meaning t m 3063) (meaning t m 3549) (meaning t m 3955) source

theorem rule19945 (p2406 p2509 p4355 : Prop) (h : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p4355)) : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial19945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory9201 (m.theta 1 4) (m.theta 4 5) (m.theta 4 8)
  exact rule19945 (meaning t m 2406) (meaning t m 2509) (meaning t m 4355) source

theorem rule19947 (p2363 p3692 p4441 : Prop) (h : (¬ p3692) ∨ (¬ p2363) ∨ (¬ p4441)) : (¬ p2363) ∨ (¬ p3692) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial19947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory9203 (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19947 (meaning t m 2363) (meaning t m 3692) (meaning t m 4441) source

theorem rule19949 (p3166 p3292 p5111 : Prop) (h : (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5111)) : (¬ p3166) ∨ (¬ p3292) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial19949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory9205 (m.theta 0 3) (m.theta 3 8) (m.theta 3 9)
  exact rule19949 (meaning t m 3166) (meaning t m 3292) (meaning t m 5111) source

theorem rule19951 (p2641 p3662 p4153 : Prop) (h : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p4153)) : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial19951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory9207 (m.theta 1 3) (m.theta 3 5) (m.theta 3 6)
  exact rule19951 (meaning t m 2641) (meaning t m 3662) (meaning t m 4153) source

theorem rule19952 (p2027 p2717 p2810 p3553 p4652 p4781 : Prop) (h : p2027 ∨ (¬ p2810) ∨ (¬ p2717) ∨ (¬ p4652) ∨ (¬ p3553) ∨ (¬ p4781)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3553) ∨ (¬ p4652) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial19952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4652)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory9208 t (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule19952 (meaning t m 2027) (meaning t m 2717) (meaning t m 2810) (meaning t m 3553) (meaning t m 4652) (meaning t m 4781) source

theorem rule19954 (p3073 p4347 p4993 : Prop) (h : (¬ p3073) ∨ (¬ p4347) ∨ (¬ p4993)) : (¬ p3073) ∨ (¬ p4347) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial19954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory9210 (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19954 (meaning t m 3073) (meaning t m 4347) (meaning t m 4993) source

theorem rule19956 (p2027 p2810 p3005 p3238 p4346 p4607 p4811 : Prop) (h : (¬ p3005) ∨ (¬ p2810) ∨ (¬ p4346) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p4607)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial19956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory9212 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8)
  exact rule19956 (meaning t m 2027) (meaning t m 2810) (meaning t m 3005) (meaning t m 3238) (meaning t m 4346) (meaning t m 4607) (meaning t m 4811) source

theorem rule19957 (p2027 p2509 p2810 p3005 p4346 p4811 : Prop) (h : (¬ p3005) ∨ (¬ p2810) ∨ (¬ p4346) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4346) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial19957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory9213 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule19957 (meaning t m 2027) (meaning t m 2509) (meaning t m 2810) (meaning t m 3005) (meaning t m 4346) (meaning t m 4811) source

theorem rule19959 (p3527 p3659 p4424 : Prop) (h : (¬ p3659) ∨ (¬ p3527) ∨ (¬ p4424)) : (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial19959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory9215 (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule19959 (meaning t m 3527) (meaning t m 3659) (meaning t m 4424) source

theorem rule19960 (p2027 p2230 p2437 p3238 p3540 p4811 : Prop) (h : (¬ p3238) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p3540) ∨ (¬ p2230) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2437) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial19960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory9216 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19960 (meaning t m 2027) (meaning t m 2230) (meaning t m 2437) (meaning t m 3238) (meaning t m 3540) (meaning t m 4811) source

theorem rule19961 (p2027 p2911 p3941 p4278 p4445 p5122 : Prop) (h : p2027 ∨ (¬ p3941) ∨ (¬ p4278) ∨ (¬ p2911) ∨ (¬ p4445) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3941) ∨ (¬ p4278) ∨ (¬ p4445) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial19961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory9217 t (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10) (m.theta 8 9)
  exact rule19961 (meaning t m 2027) (meaning t m 2911) (meaning t m 3941) (meaning t m 4278) (meaning t m 4445) (meaning t m 5122) source

theorem rule19964 (p2027 p2299 p3516 p3527 p3577 p3817 p4477 : Prop) (h : (¬ p2299) ∨ (¬ p3577) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p4477) ∨ (¬ p3516) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3516) ∨ (¬ p3527) ∨ (¬ p3577) ∨ (¬ p3817) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial19964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory9220 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19964 (meaning t m 2027) (meaning t m 2299) (meaning t m 3516) (meaning t m 3527) (meaning t m 3577) (meaning t m 3817) (meaning t m 4477) source

theorem rule19967 (p2027 p2299 p3527 p4435 p4452 p5472 : Prop) (h : (¬ p4435) ∨ (¬ p4452) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p5472)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3527) ∨ (¬ p4435) ∨ (¬ p4452) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial19967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory9223 t (m.theta 1 6) (m.theta 1 7) (m.theta 6 10) (m.theta 6 7) (m.theta 7 8)
  exact rule19967 (meaning t m 2027) (meaning t m 2299) (meaning t m 3527) (meaning t m 4435) (meaning t m 4452) (meaning t m 5472) source

theorem rule19968 (p3821 p4063 p4823 : Prop) (h : (¬ p4063) ∨ (¬ p3821) ∨ (¬ p4823)) : (¬ p3821) ∨ (¬ p4063) ∨ (¬ p4823) := by
  classical
  tauto

theorem initial19968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4063)) ∨ (¬ (meaning t m 4823)) := by
  have source := ElevenTheory.theory9224 (m.theta 0 7) (m.theta 7 10) (m.theta 7 9)
  exact rule19968 (meaning t m 3821) (meaning t m 4063) (meaning t m 4823) source

theorem rule19969 (p2528 p4261 p4687 : Prop) (h : (¬ p2528) ∨ (¬ p4261) ∨ (¬ p4687)) : (¬ p2528) ∨ (¬ p4261) ∨ (¬ p4687) := by
  classical
  tauto

theorem initial19969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4687)) := by
  have source := ElevenTheory.theory9225 (m.theta 1 8) (m.theta 4 8) (m.theta 8 9)
  exact rule19969 (meaning t m 2528) (meaning t m 4261) (meaning t m 4687) source

theorem rule19970 (p2027 p2528 p3083 p3453 p4261 p4811 : Prop) (h : (¬ p2528) ∨ (¬ p3083) ∨ (¬ p4811) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p3453)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial19970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3453)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory9226 t (m.theta 1 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule19970 (meaning t m 2027) (meaning t m 2528) (meaning t m 3083) (meaning t m 3453) (meaning t m 4261) (meaning t m 4811) source

theorem rule19973 (p2313 p2383 p3955 : Prop) (h : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3955)) : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial19973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory9229 (m.theta 0 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19973 (meaning t m 2313) (meaning t m 2383) (meaning t m 3955) source

theorem rule19978 (p2027 p2819 p2829 p3588 p4405 p4471 : Prop) (h : (¬ p4405) ∨ (¬ p3588) ∨ p2027 ∨ (¬ p4471) ∨ (¬ p2829) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4405) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial19978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory9234 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8)
  exact rule19978 (meaning t m 2027) (meaning t m 2819) (meaning t m 2829) (meaning t m 3588) (meaning t m 4405) (meaning t m 4471) source

theorem rule19979 (p3256 p3692 p4312 : Prop) (h : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4312)) : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4312) := by
  classical
  tauto

theorem initial19979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4312)) := by
  have source := ElevenTheory.theory9235 (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule19979 (meaning t m 3256) (meaning t m 3692) (meaning t m 4312) source

theorem rule19981 (p2274 p2313 p4356 : Prop) (h : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p4356)) : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial19981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory9237 (m.theta 0 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19981 (meaning t m 2274) (meaning t m 2313) (meaning t m 4356) source

theorem rule19982 (p2850 p3238 p4030 : Prop) (h : (¬ p3238) ∨ (¬ p4030) ∨ (¬ p2850)) : (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial19982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory9238 (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule19982 (meaning t m 2850) (meaning t m 3238) (meaning t m 4030) source

theorem rule19983 (p3105 p3698 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p3105) ∨ (¬ p3698)) : (¬ p3105) ∨ (¬ p3698) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial19983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory9239 (m.theta 2 5) (m.theta 4 5) (m.theta 5 9)
  exact rule19983 (meaning t m 3105) (meaning t m 3698) (meaning t m 4948) source

theorem rule19984 (p2406 p2509 p3741 p3875 : Prop) (h : (¬ p2509) ∨ (¬ p2406) ∨ (¬ p3741) ∨ (¬ p3875)) : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3741) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial19984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory9240 (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule19984 (meaning t m 2406) (meaning t m 2509) (meaning t m 3741) (meaning t m 3875) source

theorem rule19985 (p2651 p3414 p3580 : Prop) (h : (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3580)) : (¬ p2651) ∨ (¬ p3414) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial19985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory9241 (m.theta 0 3) (m.theta 3 4) (m.theta 3 7)
  exact rule19985 (meaning t m 2651) (meaning t m 3414) (meaning t m 3580) source

theorem rule19987 (p2027 p2630 p2946 p2963 p4315 p4972 : Prop) (h : (¬ p2946) ∨ (¬ p4315) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4315) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial19987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory9243 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule19987 (meaning t m 2027) (meaning t m 2630) (meaning t m 2946) (meaning t m 2963) (meaning t m 4315) (meaning t m 4972) source

theorem rule19988 (p2027 p2651 p2685 p3414 p4195 p4972 : Prop) (h : (¬ p4972) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4195) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p4195) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial19988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory9244 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule19988 (meaning t m 2027) (meaning t m 2651) (meaning t m 2685) (meaning t m 3414) (meaning t m 4195) (meaning t m 4972) source

theorem rule19989 (p2870 p3698 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p3698) ∨ (¬ p2870)) : (¬ p2870) ∨ (¬ p3698) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial19989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory9245 (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule19989 (meaning t m 2870) (meaning t m 3698) (meaning t m 4235) source

theorem rule19992 (p2299 p2396 p3657 : Prop) (h : (¬ p2299) ∨ (¬ p3657) ∨ (¬ p2396)) : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial19992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory9248 (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19992 (meaning t m 2299) (meaning t m 2396) (meaning t m 3657) source

theorem rule19993 (p2027 p2449 p2807 p3172 p4548 p4668 : Prop) (h : (¬ p4548) ∨ (¬ p3172) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p4668) ∨ (¬ p2449)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p4548) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial19993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory9249 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 7 9)
  exact rule19993 (meaning t m 2027) (meaning t m 2449) (meaning t m 2807) (meaning t m 3172) (meaning t m 4548) (meaning t m 4668) source

theorem rule19994 (p2807 p3292 p4661 : Prop) (h : (¬ p2807) ∨ (¬ p3292) ∨ (¬ p4661)) : (¬ p2807) ∨ (¬ p3292) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial19994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory9250 (m.theta 0 3) (m.theta 3 7) (m.theta 3 9)
  exact rule19994 (meaning t m 2807) (meaning t m 3292) (meaning t m 4661) source

theorem rule19996 (p2748 p3136 p4111 p4700 : Prop) (h : (¬ p2748) ∨ (¬ p4700) ∨ (¬ p4111) ∨ (¬ p3136)) : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p4111) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial19996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory9252 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule19996 (meaning t m 2748) (meaning t m 3136) (meaning t m 4111) (meaning t m 4700) source

theorem rule19999 (p2563 p3952 p4241 : Prop) (h : (¬ p3952) ∨ (¬ p2563) ∨ (¬ p4241)) : (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial19999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory9255 (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule19999 (meaning t m 2563) (meaning t m 3952) (meaning t m 4241) source

theorem rule20001 (p2220 p3556 p4119 : Prop) (h : (¬ p4119) ∨ (¬ p3556) ∨ (¬ p2220)) : (¬ p2220) ∨ (¬ p3556) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial20001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory9257 (m.theta 0 5) (m.theta 5 7) (m.theta 5 8)
  exact rule20001 (meaning t m 2220) (meaning t m 3556) (meaning t m 4119) source

theorem rule20002 (p2563 p4334 p4948 : Prop) (h : (¬ p2563) ∨ (¬ p4334) ∨ (¬ p4948)) : (¬ p2563) ∨ (¬ p4334) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial20002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory9258 (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule20002 (meaning t m 2563) (meaning t m 4334) (meaning t m 4948) source

theorem rule20003 (p2996 p3842 p4429 : Prop) (h : (¬ p3842) ∨ (¬ p2996) ∨ (¬ p4429)) : (¬ p2996) ∨ (¬ p3842) ∨ (¬ p4429) := by
  classical
  tauto

theorem initial20003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4429)) := by
  have source := ElevenTheory.theory9259 (m.theta 1 3) (m.theta 3 7) (m.theta 3 9)
  exact rule20003 (meaning t m 2996) (meaning t m 3842) (meaning t m 4429) source

theorem rule20004 (p2406 p3574 p3660 p4116 : Prop) (h : (¬ p3574) ∨ (¬ p2406) ∨ (¬ p4116) ∨ (¬ p3660)) : (¬ p2406) ∨ (¬ p3574) ∨ (¬ p3660) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial20004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory9260 (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule20004 (meaning t m 2406) (meaning t m 3574) (meaning t m 3660) (meaning t m 4116) source

theorem rule20005 (p2588 p3564 p4025 : Prop) (h : (¬ p3564) ∨ (¬ p2588) ∨ (¬ p4025)) : (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial20005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory9261 (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule20005 (meaning t m 2588) (meaning t m 3564) (meaning t m 4025) source

theorem rule20006 (p2922 p3742 p4116 : Prop) (h : (¬ p2922) ∨ (¬ p4116) ∨ (¬ p3742)) : (¬ p2922) ∨ (¬ p3742) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial20006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory9262 (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule20006 (meaning t m 2922) (meaning t m 3742) (meaning t m 4116) source

theorem rule20007 (p2192 p3412 p3952 : Prop) (h : (¬ p2192) ∨ (¬ p3412) ∨ (¬ p3952)) : (¬ p2192) ∨ (¬ p3412) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial20007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory9263 (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule20007 (meaning t m 2192) (meaning t m 3412) (meaning t m 3952) source

theorem rule20010 (p2187 p3923 p4516 : Prop) (h : (¬ p4516) ∨ (¬ p3923) ∨ (¬ p2187)) : (¬ p2187) ∨ (¬ p3923) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial20010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory9266 (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule20010 (meaning t m 2187) (meaning t m 3923) (meaning t m 4516) source

theorem rule20011 (p3073 p4340 p4967 p5074 : Prop) (h : (¬ p5074) ∨ (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4967)) : (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4967) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial20011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4967)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory9267 (m.theta 1 8) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule20011 (meaning t m 3073) (meaning t m 4340) (meaning t m 4967) (meaning t m 5074) source

theorem rule20012 (p3027 p4111 p4112 : Prop) (h : (¬ p4111) ∨ (¬ p3027) ∨ (¬ p4112)) : (¬ p3027) ∨ (¬ p4111) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial20012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory9268 (m.theta 1 3) (m.theta 3 4) (m.theta 3 7)
  exact rule20012 (meaning t m 3027) (meaning t m 4111) (meaning t m 4112) source

theorem rule20017 (p2992 p4111 p4700 : Prop) (h : (¬ p4111) ∨ (¬ p2992) ∨ (¬ p4700)) : (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial20017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory9273 (m.theta 1 3) (m.theta 3 4) (m.theta 3 5)
  exact rule20017 (meaning t m 2992) (meaning t m 4111) (meaning t m 4700) source

theorem rule20019 (p2331 p3414 p4156 : Prop) (h : (¬ p4156) ∨ (¬ p2331) ∨ (¬ p3414)) : (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial20019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory9275 (m.theta 0 3) (m.theta 3 6) (m.theta 3 7)
  exact rule20019 (meaning t m 2331) (meaning t m 3414) (meaning t m 4156) source

theorem rule20024 (p2641 p4111 p4194 : Prop) (h : (¬ p4111) ∨ (¬ p2641) ∨ (¬ p4194)) : (¬ p2641) ∨ (¬ p4111) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial20024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory9280 (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule20024 (meaning t m 2641) (meaning t m 4111) (meaning t m 4194) source

theorem rule20027 (p2177 p3659 p4475 : Prop) (h : (¬ p2177) ∨ (¬ p3659) ∨ (¬ p4475)) : (¬ p2177) ∨ (¬ p3659) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial20027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory9283 (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20027 (meaning t m 2177) (meaning t m 3659) (meaning t m 4475) source

theorem rule20028 (p3189 p3878 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p3189) ∨ (¬ p3878)) : (¬ p3189) ∨ (¬ p3878) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial20028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory9284 (m.theta 1 3) (m.theta 3 4) (m.theta 3 8)
  exact rule20028 (meaning t m 3189) (meaning t m 3878) (meaning t m 4111) source

theorem rule20029 (p2696 p3425 p4781 : Prop) (h : (¬ p3425) ∨ (¬ p2696) ∨ (¬ p4781)) : (¬ p2696) ∨ (¬ p3425) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial20029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory9285 (m.theta 0 2) (m.theta 2 3) (m.theta 2 7)
  exact rule20029 (meaning t m 2696) (meaning t m 3425) (meaning t m 4781) source

theorem rule20030 (p2027 p2177 p3027 p4360 p4548 p4570 : Prop) (h : p2027 ∨ (¬ p3027) ∨ (¬ p4570) ∨ (¬ p2177) ∨ (¬ p4548) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial20030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory9286 t (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule20030 (meaning t m 2027) (meaning t m 2177) (meaning t m 3027) (meaning t m 4360) (meaning t m 4548) (meaning t m 4570) source

theorem rule20033 (p2027 p2573 p2911 p3551 p4708 p5197 : Prop) (h : (¬ p2573) ∨ (¬ p3551) ∨ (¬ p4708) ∨ p2027 ∨ (¬ p5197) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4708) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial20033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4708)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory9289 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule20033 (meaning t m 2027) (meaning t m 2573) (meaning t m 2911) (meaning t m 3551) (meaning t m 4708) (meaning t m 5197) source

theorem rule20035 (p2027 p2373 p2387 p2406 p2459 p3379 p4347 p4902 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p3379) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p4902) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial20035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory9291 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20035 (meaning t m 2027) (meaning t m 2373) (meaning t m 2387) (meaning t m 2406) (meaning t m 2459) (meaning t m 3379) (meaning t m 4347) (meaning t m 4902) (meaning t m 5021) source

theorem rule20036 (p1977 p2499 p2507 p3402 p3818 : Prop) (h : p3818 ∨ (¬ p1977) ∨ (¬ p3402) ∨ (¬ p2499) ∨ p2507) : (¬ p1977) ∨ (¬ p2499) ∨ (p2507) ∨ (¬ p3402) ∨ (p3818) := by
  classical
  tauto

theorem initial20036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2507) ∨ (¬ (meaning t m 3402)) ∨ (meaning t m 3818) := by
  have source := ElevenTheory.theory9292 t (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6)
  exact rule20036 (meaning t m 1977) (meaning t m 2499) (meaning t m 2507) (meaning t m 3402) (meaning t m 3818) source

theorem rule20040 (p3842 p4111 p5170 : Prop) (h : (¬ p4111) ∨ (¬ p3842) ∨ (¬ p5170)) : (¬ p3842) ∨ (¬ p4111) ∨ (¬ p5170) := by
  classical
  tauto

theorem initial20040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 5170)) := by
  have source := ElevenTheory.theory9296 (m.theta 1 3) (m.theta 3 4) (m.theta 3 9)
  exact rule20040 (meaning t m 3842) (meaning t m 4111) (meaning t m 5170) source

theorem rule20042 (p2299 p2881 p4275 : Prop) (h : (¬ p2299) ∨ (¬ p4275) ∨ (¬ p2881)) : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial20042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory9298 (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule20042 (meaning t m 2299) (meaning t m 2881) (meaning t m 4275) source

theorem rule20045 (p2027 p2751 p2992 p3156 p3694 p4392 : Prop) (h : (¬ p2992) ∨ p2027 ∨ (¬ p2751) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p4392)) : (p2027) ∨ (¬ p2751) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial20045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory9301 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule20045 (meaning t m 2027) (meaning t m 2751) (meaning t m 2992) (meaning t m 3156) (meaning t m 3694) (meaning t m 4392) source

theorem rule20046 (p3156 p3694 p5051 : Prop) (h : (¬ p3694) ∨ (¬ p3156) ∨ (¬ p5051)) : (¬ p3156) ∨ (¬ p3694) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial20046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory9302 (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule20046 (meaning t m 3156) (meaning t m 3694) (meaning t m 5051) source

theorem rule20048 (p2641 p2996 p4156 : Prop) (h : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4156)) : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial20048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory9304 (m.theta 1 3) (m.theta 3 6) (m.theta 3 7)
  exact rule20048 (meaning t m 2641) (meaning t m 2996) (meaning t m 4156) source

theorem rule20052 (p2797 p4153 p4315 : Prop) (h : (¬ p4153) ∨ (¬ p2797) ∨ (¬ p4315)) : (¬ p2797) ∨ (¬ p4153) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial20052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory9308 (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule20052 (meaning t m 2797) (meaning t m 4153) (meaning t m 4315) source

theorem rule20053 (p2027 p2737 p2797 p3585 p4343 p4975 : Prop) (h : (¬ p2737) ∨ p2027 ∨ (¬ p4343) ∨ (¬ p4975) ∨ (¬ p2797) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial20053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory9309 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6)
  exact rule20053 (meaning t m 2027) (meaning t m 2737) (meaning t m 2797) (meaning t m 3585) (meaning t m 4343) (meaning t m 4975) source

theorem rule20056 (p2313 p3204 p3309 : Prop) (h : (¬ p3309) ∨ (¬ p2313) ∨ (¬ p3204)) : (¬ p2313) ∨ (¬ p3204) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial20056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory9312 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule20056 (meaning t m 2313) (meaning t m 3204) (meaning t m 3309) source

theorem rule20057 (p2027 p2241 p2313 p3309 p4756 p5015 : Prop) (h : (¬ p2313) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4756) ∨ (¬ p5015)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p4756) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial20057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4756)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory9313 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 6 7)
  exact rule20057 (meaning t m 2027) (meaning t m 2241) (meaning t m 2313) (meaning t m 3309) (meaning t m 4756) (meaning t m 5015) source

theorem rule20058 (p2027 p2192 p2241 p2274 p2396 p2750 p3371 p3860 p3950 p4261 : Prop) (h : (¬ p2396) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p3371) ∨ (¬ p3950) ∨ (¬ p2241) ∨ (¬ p4261) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3860)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial20058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory9314 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule20058 (meaning t m 2027) (meaning t m 2192) (meaning t m 2241) (meaning t m 2274) (meaning t m 2396) (meaning t m 2750) (meaning t m 3371) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) source

theorem rule20060 (p3506 p4425 p5171 : Prop) (h : (¬ p4425) ∨ (¬ p3506) ∨ (¬ p5171)) : (¬ p3506) ∨ (¬ p4425) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial20060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory9316 (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule20060 (meaning t m 3506) (meaning t m 4425) (meaning t m 5171) source

theorem rule20061 (p2027 p2313 p2608 p3309 p4866 p5015 : Prop) (h : (¬ p2313) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4866) ∨ (¬ p5015) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4866) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial20061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory9317 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 7)
  exact rule20061 (meaning t m 2027) (meaning t m 2313) (meaning t m 2608) (meaning t m 3309) (meaning t m 4866) (meaning t m 5015) source

theorem rule20062 (p2780 p3471 p3689 : Prop) (h : (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3689)) : (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3689) := by
  classical
  tauto

theorem initial20062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3689)) := by
  have source := ElevenTheory.theory9318 (m.theta 0 2) (m.theta 2 6) (m.theta 2 7)
  exact rule20062 (meaning t m 2780) (meaning t m 3471) (meaning t m 3689) source

theorem rule20063 (p2313 p2778 p3471 p4475 : Prop) (h : (¬ p2778) ∨ (¬ p3471) ∨ (¬ p2313) ∨ (¬ p4475)) : (¬ p2313) ∨ (¬ p2778) ∨ (¬ p3471) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial20063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory9319 (m.theta 0 2) (m.theta 0 6) (m.theta 2 7) (m.theta 6 7)
  exact rule20063 (meaning t m 2313) (meaning t m 2778) (meaning t m 3471) (meaning t m 4475) source

theorem rule20064 (p2504 p2579 p3093 p4108 : Prop) (h : (¬ p3093) ∨ (¬ p2504) ∨ (¬ p4108) ∨ (¬ p2579)) : (¬ p2504) ∨ (¬ p2579) ∨ (¬ p3093) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial20064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory9320 (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 6)
  exact rule20064 (meaning t m 2504) (meaning t m 2579) (meaning t m 3093) (meaning t m 4108) source

theorem rule20065 (p2027 p2313 p2500 p3309 p3379 p5015 : Prop) (h : (¬ p2500) ∨ p2027 ∨ (¬ p5015) ∨ (¬ p3379) ∨ (¬ p2313) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2500) ∨ (¬ p3309) ∨ (¬ p3379) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial20065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2500)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory9321 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7)
  exact rule20065 (meaning t m 2027) (meaning t m 2313) (meaning t m 2500) (meaning t m 3309) (meaning t m 3379) (meaning t m 5015) source

theorem rule20066 (p3399 p3591 p4105 : Prop) (h : (¬ p3591) ∨ (¬ p3399) ∨ (¬ p4105)) : (¬ p3399) ∨ (¬ p3591) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial20066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory9322 (m.theta 0 1) (m.theta 1 6) (m.theta 1 7)
  exact rule20066 (meaning t m 3399) (meaning t m 3591) (meaning t m 4105) source

theorem rule20067 (p2192 p4034 p4110 : Prop) (h : (¬ p4034) ∨ (¬ p4110) ∨ (¬ p2192)) : (¬ p2192) ∨ (¬ p4034) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial20067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory9323 (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule20067 (meaning t m 2192) (meaning t m 4034) (meaning t m 4110) source

theorem rule20069 (p3256 p4347 p4769 : Prop) (h : (¬ p3256) ∨ (¬ p4347) ∨ (¬ p4769)) : (¬ p3256) ∨ (¬ p4347) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial20069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory9325 (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule20069 (meaning t m 3256) (meaning t m 4347) (meaning t m 4769) source

theorem rule20071 (p2363 p3857 p4113 : Prop) (h : (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4113)) : (¬ p2363) ∨ (¬ p3857) ∨ (¬ p4113) := by
  classical
  tauto

theorem initial20071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4113)) := by
  have source := ElevenTheory.theory9327 (m.theta 0 8) (m.theta 6 8) (m.theta 8 9)
  exact rule20071 (meaning t m 2363) (meaning t m 3857) (meaning t m 4113) source

theorem rule20074 (p2022 p2307 p2315 p2344 : Prop) (h : p2344 ∨ p2315 ∨ (¬ p2307) ∨ (¬ p2022)) : (¬ p2022) ∨ (¬ p2307) ∨ (p2315) ∨ (p2344) := by
  classical
  tauto

theorem initial20074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2315) ∨ (meaning t m 2344) := by
  have source := ElevenTheory.theory9330 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7)
  exact rule20074 (meaning t m 2022) (meaning t m 2307) (meaning t m 2315) (meaning t m 2344) source

theorem rule20076 (p2427 p3747 p3880 : Prop) (h : (¬ p3880) ∨ (¬ p2427) ∨ (¬ p3747)) : (¬ p2427) ∨ (¬ p3747) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial20076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory9332 (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule20076 (meaning t m 2427) (meaning t m 3747) (meaning t m 3880) source

theorem rule20078 (p2027 p2307 p3549 p3954 p4202 p4512 p5020 p5216 : Prop) (h : (¬ p4202) ∨ (¬ p5216) ∨ (¬ p4512) ∨ (¬ p3954) ∨ (¬ p3549) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p5020)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p5020) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial20078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 5020)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory9334 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 1 6) (m.theta 6 7)
  exact rule20078 (meaning t m 2027) (meaning t m 2307) (meaning t m 3549) (meaning t m 3954) (meaning t m 4202) (meaning t m 4512) (meaning t m 5020) (meaning t m 5216) source

theorem rule20082 (p2406 p2440 p4116 : Prop) (h : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p4116)) : (¬ p2406) ∨ (¬ p2440) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial20082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory9338 (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule20082 (meaning t m 2406) (meaning t m 2440) (meaning t m 4116) source

theorem rule20083 (p3449 p3555 p4492 : Prop) (h : (¬ p3555) ∨ (¬ p3449) ∨ (¬ p4492)) : (¬ p3449) ∨ (¬ p3555) ∨ (¬ p4492) := by
  classical
  tauto

theorem initial20083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4492)) := by
  have source := ElevenTheory.theory9339 (m.theta 0 1) (m.theta 1 5) (m.theta 1 8)
  exact rule20083 (meaning t m 3449) (meaning t m 3555) (meaning t m 4492) source

theorem rule20084 (p2459 p3692 p4042 : Prop) (h : (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4042)) : (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4042) := by
  classical
  tauto

theorem initial20084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4042)) := by
  have source := ElevenTheory.theory9340 (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20084 (meaning t m 2459) (meaning t m 3692) (meaning t m 4042) source

theorem rule20088 (p2881 p3553 p4333 : Prop) (h : (¬ p3553) ∨ (¬ p2881) ∨ (¬ p4333)) : (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial20088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory9344 (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule20088 (meaning t m 2881) (meaning t m 3553) (meaning t m 4333) source

theorem rule20089 (p2177 p3945 p4107 : Prop) (h : (¬ p3945) ∨ (¬ p2177) ∨ (¬ p4107)) : (¬ p2177) ∨ (¬ p3945) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial20089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory9345 (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule20089 (meaning t m 2177) (meaning t m 3945) (meaning t m 4107) source

theorem rule20090 (p2027 p2247 p3037 p3399 p3662 p4919 : Prop) (h : (¬ p3399) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p4919) ∨ (¬ p3037)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3662) ∨ (¬ p4919) := by
  classical
  tauto

theorem initial20090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4919)) := by
  have source := ElevenTheory.theory9346 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 3 7)
  exact rule20090 (meaning t m 2027) (meaning t m 2247) (meaning t m 3037) (meaning t m 3399) (meaning t m 3662) (meaning t m 4919) source

theorem rule20091 (p2459 p4200 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p2459) ∨ (¬ p4200)) : (¬ p2459) ∨ (¬ p4200) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial20091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4200)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory9347 (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule20091 (meaning t m 2459) (meaning t m 4200) (meaning t m 5558) source

theorem rule20092 (p3941 p4403 p5590 : Prop) (h : (¬ p5590) ∨ (¬ p3941) ∨ (¬ p4403)) : (¬ p3941) ∨ (¬ p4403) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial20092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory9348 (m.theta 0 8) (m.theta 7 8) (m.theta 8 10)
  exact rule20092 (meaning t m 3941) (meaning t m 4403) (meaning t m 5590) source

theorem rule20093 (p2027 p2220 p2284 p3497 p3556 p4555 : Prop) (h : p2027 ∨ (¬ p4555) ∨ (¬ p3556) ∨ (¬ p3497) ∨ (¬ p2284) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial20093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory9349 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule20093 (meaning t m 2027) (meaning t m 2220) (meaning t m 2284) (meaning t m 3497) (meaning t m 3556) (meaning t m 4555) source

theorem rule20094 (p2027 p2563 p3051 p3646 p4320 p4702 : Prop) (h : (¬ p3646) ∨ (¬ p2563) ∨ (¬ p4702) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p4320)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial20094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory9350 t (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule20094 (meaning t m 2027) (meaning t m 2563) (meaning t m 3051) (meaning t m 3646) (meaning t m 4320) (meaning t m 4702) source

theorem rule20095 (p2210 p3452 p4202 : Prop) (h : (¬ p4202) ∨ (¬ p3452) ∨ (¬ p2210)) : (¬ p2210) ∨ (¬ p3452) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial20095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory9351 (m.theta 0 1) (m.theta 1 4) (m.theta 1 5)
  exact rule20095 (meaning t m 2210) (meaning t m 3452) (meaning t m 4202) source

theorem rule20099 (p2373 p2533 p4948 : Prop) (h : (¬ p2373) ∨ (¬ p2533) ∨ (¬ p4948)) : (¬ p2373) ∨ (¬ p2533) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial20099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory9355 (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule20099 (meaning t m 2373) (meaning t m 2533) (meaning t m 4948) source

theorem rule20101 (p2027 p2104 p2132 p2166 p4740 p4960 p5051 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p5051) ∨ (¬ p4960) ∨ (¬ p2104) ∨ (¬ p2166) ∨ (¬ p4740)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p4740) ∨ (¬ p4960) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial20101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 4740)) ∨ (¬ (meaning t m 4960)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory9357 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8)
  exact rule20101 (meaning t m 2027) (meaning t m 2104) (meaning t m 2132) (meaning t m 2166) (meaning t m 4740) (meaning t m 4960) (meaning t m 5051) source

theorem rule20103 (p3680 p3949 p4444 : Prop) (h : (¬ p3680) ∨ (¬ p4444) ∨ (¬ p3949)) : (¬ p3680) ∨ (¬ p3949) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial20103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory9359 (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20103 (meaning t m 3680) (meaning t m 3949) (meaning t m 4444) source

theorem rule20105 (p2027 p2088 p2911 p3919 p3960 p4118 p4327 : Prop) (h : (¬ p4118) ∨ (¬ p3919) ∨ p2027 ∨ (¬ p3960) ∨ (¬ p4327) ∨ (¬ p2911) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2911) ∨ (¬ p3919) ∨ (¬ p3960) ∨ (¬ p4118) ∨ (¬ p4327) := by
  classical
  tauto

theorem initial20105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4327)) := by
  have source := ElevenTheory.theory9361 t (m.theta 0 8) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule20105 (meaning t m 2027) (meaning t m 2088) (meaning t m 2911) (meaning t m 3919) (meaning t m 3960) (meaning t m 4118) (meaning t m 4327) source

theorem rule20107 (p2563 p4173 p4210 : Prop) (h : (¬ p4210) ∨ (¬ p4173) ∨ (¬ p2563)) : (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial20107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory9363 (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule20107 (meaning t m 2563) (meaning t m 4173) (meaning t m 4210) source

theorem rule20112 (p2860 p4173 p4243 : Prop) (h : (¬ p4173) ∨ (¬ p2860) ∨ (¬ p4243)) : (¬ p2860) ∨ (¬ p4173) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial20112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory9368 (m.theta 1 5) (m.theta 2 5) (m.theta 5 6)
  exact rule20112 (meaning t m 2860) (meaning t m 4173) (meaning t m 4243) source

theorem rule20115 (p3246 p3570 p3657 : Prop) (h : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3657)) : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial20115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory9371 (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule20115 (meaning t m 3246) (meaning t m 3570) (meaning t m 3657) source

theorem rule20116 (p2579 p3363 p3422 : Prop) (h : (¬ p2579) ∨ (¬ p3422) ∨ (¬ p3363)) : (¬ p2579) ∨ (¬ p3363) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial20116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory9372 (m.theta 0 4) (m.theta 2 4) (m.theta 4 6)
  exact rule20116 (meaning t m 2579) (meaning t m 3363) (meaning t m 3422) source

theorem rule20117 (p2027 p2241 p2589 p3189 p3256 p3690 p4235 p4669 p5193 : Prop) (h : (¬ p3189) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3690) ∨ (¬ p4669) ∨ (¬ p5193) ∨ (¬ p2241) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial20117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory9373 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule20117 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3189) (meaning t m 3256) (meaning t m 3690) (meaning t m 4235) (meaning t m 4669) (meaning t m 5193) source

theorem rule20120 (p2027 p2727 p2946 p3414 p3662 p4650 : Prop) (h : (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p4650) ∨ p2027 ∨ (¬ p3662)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial20120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory9376 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule20120 (meaning t m 2027) (meaning t m 2727) (meaning t m 2946) (meaning t m 3414) (meaning t m 3662) (meaning t m 4650) source

theorem rule20121 (p3367 p3588 p5085 : Prop) (h : (¬ p3588) ∨ (¬ p3367) ∨ (¬ p5085)) : (¬ p3367) ∨ (¬ p3588) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial20121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory9377 (m.theta 1 2) (m.theta 2 4) (m.theta 2 7)
  exact rule20121 (meaning t m 3367) (meaning t m 3588) (meaning t m 5085) source

theorem rule20123 (p3367 p3688 p4375 : Prop) (h : (¬ p3688) ∨ (¬ p3367) ∨ (¬ p4375)) : (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial20123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory9379 (m.theta 1 2) (m.theta 2 4) (m.theta 2 6)
  exact rule20123 (meaning t m 3367) (meaning t m 3688) (meaning t m 4375) source

theorem rule20126 (p2027 p2589 p2608 p3537 p3609 p3690 p4235 p4669 p5193 : Prop) (h : p2027 ∨ (¬ p4669) ∨ (¬ p3690) ∨ (¬ p2608) ∨ (¬ p2589) ∨ (¬ p5193) ∨ (¬ p4235) ∨ (¬ p3537) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial20126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory9382 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule20126 (meaning t m 2027) (meaning t m 2589) (meaning t m 2608) (meaning t m 3537) (meaning t m 3609) (meaning t m 3690) (meaning t m 4235) (meaning t m 4669) (meaning t m 5193) source

theorem rule20127 (p2598 p2780 p4375 : Prop) (h : (¬ p2780) ∨ (¬ p2598) ∨ (¬ p4375)) : (¬ p2598) ∨ (¬ p2780) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial20127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory9383 (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule20127 (meaning t m 2598) (meaning t m 2780) (meaning t m 4375) source

theorem rule20128 (p2499 p3016 p3487 : Prop) (h : (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3487)) : (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial20128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory9384 (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule20128 (meaning t m 2499) (meaning t m 3016) (meaning t m 3487) source

theorem rule20130 (p2027 p2528 p3857 p4197 p4235 p4355 p4356 p4555 : Prop) (h : (¬ p4355) ∨ (¬ p2528) ∨ (¬ p4197) ∨ (¬ p3857) ∨ (¬ p4235) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p4356)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4235) ∨ (¬ p4355) ∨ (¬ p4356) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial20130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory9386 t (m.theta 0 6) (m.theta 0 8) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule20130 (meaning t m 2027) (meaning t m 2528) (meaning t m 3857) (meaning t m 4197) (meaning t m 4235) (meaning t m 4355) (meaning t m 4356) (meaning t m 4555) source

theorem rule20131 (p2641 p4121 p4194 p4360 : Prop) (h : (¬ p2641) ∨ (¬ p4360) ∨ (¬ p4194) ∨ (¬ p4121)) : (¬ p2641) ∨ (¬ p4121) ∨ (¬ p4194) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial20131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory9387 (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule20131 (meaning t m 2641) (meaning t m 4121) (meaning t m 4194) (meaning t m 4360) source

theorem rule20133 (p2641 p4341 p4360 : Prop) (h : (¬ p2641) ∨ (¬ p4360) ∨ (¬ p4341)) : (¬ p2641) ∨ (¬ p4341) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial20133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory9389 (m.theta 1 3) (m.theta 3 6) (m.theta 3 8)
  exact rule20133 (meaning t m 2641) (meaning t m 4341) (meaning t m 4360) source

theorem rule20136 (p2499 p3422 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p2499) ∨ (¬ p3422)) : (¬ p2499) ∨ (¬ p3422) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial20136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory9392 (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule20136 (meaning t m 2499) (meaning t m 3422) (meaning t m 4030) source

theorem rule20138 (p3399 p3954 p4400 : Prop) (h : (¬ p3954) ∨ (¬ p3399) ∨ (¬ p4400)) : (¬ p3399) ∨ (¬ p3954) ∨ (¬ p4400) := by
  classical
  tauto

theorem initial20138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4400)) := by
  have source := ElevenTheory.theory9394 (m.theta 0 1) (m.theta 1 2) (m.theta 1 7)
  exact rule20138 (meaning t m 3399) (meaning t m 3954) (meaning t m 4400) source

theorem rule20144 (p2027 p3654 p3954 p4026 p4870 p5020 : Prop) (h : (¬ p3954) ∨ (¬ p4026) ∨ (¬ p4870) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p5020)) : (p2027) ∨ (¬ p3654) ∨ (¬ p3954) ∨ (¬ p4026) ∨ (¬ p4870) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial20144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory9400 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 6 9)
  exact rule20144 (meaning t m 2027) (meaning t m 3654) (meaning t m 3954) (meaning t m 4026) (meaning t m 4870) (meaning t m 5020) source

theorem rule20146 (p2870 p3698 p4192 p4948 : Prop) (h : (¬ p3698) ∨ (¬ p4948) ∨ (¬ p2870) ∨ (¬ p4192)) : (¬ p2870) ∨ (¬ p3698) ∨ (¬ p4192) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial20146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory9402 (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule20146 (meaning t m 2870) (meaning t m 3698) (meaning t m 4192) (meaning t m 4948) source

theorem rule20151 (p3438 p3707 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3707) ∨ (¬ p3438)) : (¬ p3438) ∨ (¬ p3707) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial20151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory9407 (m.theta 1 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20151 (meaning t m 3438) (meaning t m 3707) (meaning t m 4444) source

theorem rule20158 (p2132 p3425 p3587 : Prop) (h : (¬ p2132) ∨ (¬ p3587) ∨ (¬ p3425)) : (¬ p2132) ∨ (¬ p3425) ∨ (¬ p3587) := by
  classical
  tauto

theorem initial20158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3587)) := by
  have source := ElevenTheory.theory9414 (m.theta 0 2) (m.theta 2 5) (m.theta 2 7)
  exact rule20158 (meaning t m 2132) (meaning t m 3425) (meaning t m 3587) source

theorem rule20159 (p2098 p2138 p4359 : Prop) (h : (¬ p2138) ∨ (¬ p2098) ∨ (¬ p4359)) : (¬ p2098) ∨ (¬ p2138) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial20159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory9415 (m.theta 0 2) (m.theta 2 5) (m.theta 2 8)
  exact rule20159 (meaning t m 2098) (meaning t m 2138) (meaning t m 4359) source

theorem rule20160 (p3246 p3571 p3817 : Prop) (h : (¬ p3571) ∨ (¬ p3246) ∨ (¬ p3817)) : (¬ p3246) ∨ (¬ p3571) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial20160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory9416 (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule20160 (meaning t m 3246) (meaning t m 3571) (meaning t m 3817) source

theorem rule20162 (p2542 p3742 p4186 p4355 : Prop) (h : (¬ p2542) ∨ (¬ p4186) ∨ (¬ p3742) ∨ (¬ p4355)) : (¬ p2542) ∨ (¬ p3742) ∨ (¬ p4186) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial20162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory9418 (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8)
  exact rule20162 (meaning t m 2542) (meaning t m 3742) (meaning t m 4186) (meaning t m 4355) source

theorem rule20163 (p3680 p4321 p4387 : Prop) (h : (¬ p4321) ∨ (¬ p3680) ∨ (¬ p4387)) : (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4387) := by
  classical
  tauto

theorem initial20163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4387)) := by
  have source := ElevenTheory.theory9419 (m.theta 1 9) (m.theta 5 9) (m.theta 9 10)
  exact rule20163 (meaning t m 3680) (meaning t m 4321) (meaning t m 4387) source

theorem rule20164 (p2027 p2982 p3680 p4282 p4321 p4702 p4938 : Prop) (h : p2027 ∨ (¬ p4702) ∨ (¬ p2982) ∨ (¬ p4321) ∨ (¬ p4282) ∨ (¬ p3680) ∨ (¬ p4938)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4282) ∨ (¬ p4321) ∨ (¬ p4702) ∨ (¬ p4938) := by
  classical
  tauto

theorem initial20164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4702)) ∨ (¬ (meaning t m 4938)) := by
  have source := ElevenTheory.theory9420 t (m.theta 1 5) (m.theta 1 9) (m.theta 3 5) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule20164 (meaning t m 2027) (meaning t m 2982) (meaning t m 3680) (meaning t m 4282) (meaning t m 4321) (meaning t m 4702) (meaning t m 4938) source

theorem rule20166 (p2630 p3019 p4195 : Prop) (h : (¬ p4195) ∨ (¬ p2630) ∨ (¬ p3019)) : (¬ p2630) ∨ (¬ p3019) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial20166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory9422 (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule20166 (meaning t m 2630) (meaning t m 3019) (meaning t m 4195) source

theorem rule20171 (p3309 p3568 p4319 : Prop) (h : (¬ p3309) ∨ (¬ p4319) ∨ (¬ p3568)) : (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial20171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory9427 (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule20171 (meaning t m 3309) (meaning t m 3568) (meaning t m 4319) source

theorem rule20172 (p3055 p3471 p3686 : Prop) (h : (¬ p3471) ∨ (¬ p3055) ∨ (¬ p3686)) : (¬ p3055) ∨ (¬ p3471) ∨ (¬ p3686) := by
  classical
  tauto

theorem initial20172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3686)) := by
  have source := ElevenTheory.theory9428 (m.theta 0 2) (m.theta 2 4) (m.theta 2 7)
  exact rule20172 (meaning t m 3055) (meaning t m 3471) (meaning t m 3686) source

theorem rule20173 (p2295 p2588 p4389 : Prop) (h : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p4389)) : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial20173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory9429 (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule20173 (meaning t m 2295) (meaning t m 2588) (meaning t m 4389) source

theorem rule20174 (p2295 p3019 p3742 p3921 : Prop) (h : (¬ p2295) ∨ (¬ p3921) ∨ (¬ p3742) ∨ (¬ p3019)) : (¬ p2295) ∨ (¬ p3019) ∨ (¬ p3742) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial20174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory9430 (m.theta 3 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7)
  exact rule20174 (meaning t m 2295) (meaning t m 3019) (meaning t m 3742) (meaning t m 3921) source

theorem rule20175 (p2363 p4200 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p2363) ∨ (¬ p4200)) : (¬ p2363) ∨ (¬ p4200) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial20175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4200)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory9431 (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule20175 (meaning t m 2363) (meaning t m 4200) (meaning t m 5580) source

theorem rule20184 (p2027 p2136 p2619 p2737 p3366 p4120 p5049 : Prop) (h : (¬ p4120) ∨ (¬ p2619) ∨ (¬ p3366) ∨ (¬ p2737) ∨ (¬ p2136) ∨ p2027 ∨ (¬ p5049)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4120) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial20184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory9440 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8)
  exact rule20184 (meaning t m 2027) (meaning t m 2136) (meaning t m 2619) (meaning t m 2737) (meaning t m 3366) (meaning t m 4120) (meaning t m 5049) source

theorem rule20186 (p2459 p2534 p4404 : Prop) (h : (¬ p2534) ∨ (¬ p2459) ∨ (¬ p4404)) : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4404) := by
  classical
  tauto

theorem initial20186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 4404)) := by
  have source := ElevenTheory.theory9442 (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20186 (meaning t m 2459) (meaning t m 2534) (meaning t m 4404) source

theorem rule20188 (p2190 p2870 p3694 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p2190)) : (¬ p2190) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial20188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory9444 (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule20188 (meaning t m 2190) (meaning t m 2870) (meaning t m 3694) (meaning t m 4204) source

theorem rule20190 (p3434 p3576 p3817 : Prop) (h : (¬ p3434) ∨ (¬ p3576) ∨ (¬ p3817)) : (¬ p3434) ∨ (¬ p3576) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial20190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory9446 (m.theta 1 7) (m.theta 2 7) (m.theta 7 9)
  exact rule20190 (meaning t m 3434) (meaning t m 3576) (meaning t m 3817) source

theorem rule20191 (p2027 p3343 p4256 p4348 p4438 p4695 : Prop) (h : (¬ p3343) ∨ (¬ p4695) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p4438) ∨ (¬ p4348)) : (p2027) ∨ (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial20191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory9447 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 8) (m.theta 8 9)
  exact rule20191 (meaning t m 2027) (meaning t m 3343) (meaning t m 4256) (meaning t m 4348) (meaning t m 4438) (meaning t m 4695) source

theorem rule20194 (p3323 p4137 p4389 : Prop) (h : (¬ p4389) ∨ (¬ p3323) ∨ (¬ p4137)) : (¬ p3323) ∨ (¬ p4137) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial20194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory9450 (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule20194 (meaning t m 3323) (meaning t m 4137) (meaning t m 4389) source

theorem rule20195 (p2027 p2528 p3266 p4322 p4335 p4383 p4902 : Prop) (h : (¬ p4322) ∨ (¬ p3266) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p4383) ∨ (¬ p4902) ∨ (¬ p4335)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4383) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial20195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory9451 t (m.theta 4 8) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule20195 (meaning t m 2027) (meaning t m 2528) (meaning t m 3266) (meaning t m 4322) (meaning t m 4335) (meaning t m 4383) (meaning t m 4902) source

theorem rule20196 (p2532 p3266 p4322 : Prop) (h : (¬ p4322) ∨ (¬ p3266) ∨ (¬ p2532)) : (¬ p2532) ∨ (¬ p3266) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial20196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory9452 (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20196 (meaning t m 2532) (meaning t m 3266) (meaning t m 4322) source

theorem rule20197 (p2027 p2138 p2470 p3362 p3364 p3874 p5049 : Prop) (h : (¬ p5049) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p2470) ∨ (¬ p3364) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2470) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial20197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory9453 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8)
  exact rule20197 (meaning t m 2027) (meaning t m 2138) (meaning t m 2470) (meaning t m 3362) (meaning t m 3364) (meaning t m 3874) (meaning t m 5049) source

theorem rule20198 (p2027 p2138 p3355 p3362 p3364 p5049 p5160 : Prop) (h : p2027 ∨ (¬ p3362) ∨ (¬ p3355) ∨ (¬ p3364) ∨ (¬ p2138) ∨ (¬ p5049) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p5049) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial20198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 5049)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory9454 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 9)
  exact rule20198 (meaning t m 2027) (meaning t m 2138) (meaning t m 3355) (meaning t m 3362) (meaning t m 3364) (meaning t m 5049) (meaning t m 5160) source

theorem rule20199 (p2963 p3286 p4196 p4349 : Prop) (h : (¬ p2963) ∨ (¬ p4349) ∨ (¬ p3286) ∨ (¬ p4196)) : (¬ p2963) ∨ (¬ p3286) ∨ (¬ p4196) ∨ (¬ p4349) := by
  classical
  tauto

theorem initial20199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4349)) := by
  have source := ElevenTheory.theory9455 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 3 9)
  exact rule20199 (meaning t m 2963) (meaning t m 3286) (meaning t m 4196) (meaning t m 4349) source

theorem rule20202 (p2027 p2144 p2657 p3212 p3680 p3742 p4444 p4669 p4789 p4829 p5503 : Prop) (h : (¬ p2144) ∨ (¬ p3212) ∨ (¬ p4789) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p3742) ∨ (¬ p4669) ∨ (¬ p2657) ∨ (¬ p3680) ∨ (¬ p5503) ∨ (¬ p4829)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4789) ∨ (¬ p4829) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial20202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4829)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory9458 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20202 (meaning t m 2027) (meaning t m 2144) (meaning t m 2657) (meaning t m 3212) (meaning t m 3680) (meaning t m 3742) (meaning t m 4444) (meaning t m 4669) (meaning t m 4789) (meaning t m 4829) (meaning t m 5503) source

theorem rule20205 (p2589 p3237 p3355 : Prop) (h : (¬ p2589) ∨ (¬ p3355) ∨ (¬ p3237)) : (¬ p2589) ∨ (¬ p3237) ∨ (¬ p3355) := by
  classical
  tauto

theorem initial20205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3355)) := by
  have source := ElevenTheory.theory9461 (m.theta 0 4) (m.theta 4 5) (m.theta 4 9)
  exact rule20205 (meaning t m 2589) (meaning t m 3237) (meaning t m 3355) source

theorem rule20207 (p2027 p2542 p2659 p3222 p3238 p3346 : Prop) (h : p2027 ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) := by
  classical
  tauto

theorem initial20207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3346)) := by
  have source := ElevenTheory.theory9463 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9)
  exact rule20207 (meaning t m 2027) (meaning t m 2542) (meaning t m 2659) (meaning t m 3222) (meaning t m 3238) (meaning t m 3346) source

theorem rule20208 (p2579 p3355 p3746 : Prop) (h : (¬ p3355) ∨ (¬ p2579) ∨ (¬ p3746)) : (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3746) := by
  classical
  tauto

theorem initial20208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3746)) := by
  have source := ElevenTheory.theory9464 (m.theta 0 4) (m.theta 4 6) (m.theta 4 9)
  exact rule20208 (meaning t m 2579) (meaning t m 3355) (meaning t m 3746) source

theorem rule20211 (p3192 p3346 p3389 : Prop) (h : (¬ p3389) ∨ (¬ p3346) ∨ (¬ p3192)) : (¬ p3192) ∨ (¬ p3346) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial20211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory9467 (m.theta 0 4) (m.theta 4 7) (m.theta 4 9)
  exact rule20211 (meaning t m 3192) (meaning t m 3346) (meaning t m 3389) source

theorem rule20212 (p2363 p4138 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p2363) ∨ (¬ p4138)) : (¬ p2363) ∨ (¬ p4138) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial20212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory9468 (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule20212 (meaning t m 2363) (meaning t m 4138) (meaning t m 4348) source

theorem rule20213 (p2298 p2449 p4107 : Prop) (h : (¬ p2449) ∨ (¬ p4107) ∨ (¬ p2298)) : (¬ p2298) ∨ (¬ p2449) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial20213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory9469 (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule20213 (meaning t m 2298) (meaning t m 2449) (meaning t m 4107) source

theorem rule20214 (p2528 p4347 p4432 : Prop) (h : (¬ p4347) ∨ (¬ p2528) ∨ (¬ p4432)) : (¬ p2528) ∨ (¬ p4347) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial20214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory9470 (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule20214 (meaning t m 2528) (meaning t m 4347) (meaning t m 4432) source

theorem rule20216 (p2003 p2780 p2787 p3586 : Prop) (h : (¬ p2003) ∨ p3586 ∨ (¬ p2780) ∨ p2787) : (¬ p2003) ∨ (¬ p2780) ∨ (p2787) ∨ (p3586) := by
  classical
  tauto

theorem initial20216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2787) ∨ (meaning t m 3586) := by
  have source := ElevenTheory.theory9472 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6)
  exact rule20216 (meaning t m 2003) (meaning t m 2780) (meaning t m 2787) (meaning t m 3586) source

theorem rule20217 (p2027 p2608 p3527 p3551 p3820 p3873 p4793 : Prop) (h : (¬ p3873) ∨ p2027 ∨ (¬ p3820) ∨ (¬ p4793) ∨ (¬ p2608) ∨ (¬ p3551) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial20217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory9473 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 7 8)
  exact rule20217 (meaning t m 2027) (meaning t m 2608) (meaning t m 3527) (meaning t m 3551) (meaning t m 3820) (meaning t m 3873) (meaning t m 4793) source

theorem rule20218 (p3516 p3575 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3516) ∨ (¬ p3575)) : (¬ p3516) ∨ (¬ p3575) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial20218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory9474 (m.theta 0 7) (m.theta 4 7) (m.theta 7 9)
  exact rule20218 (meaning t m 3516) (meaning t m 3575) (meaning t m 4278) source

theorem rule20219 (p2027 p2190 p3097 p3969 p4405 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p3097) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2190)) : (p2027) ∨ (¬ p2190) ∨ (¬ p3097) ∨ (¬ p3969) ∨ (¬ p4405) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial20219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory9475 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 10)
  exact rule20219 (meaning t m 2027) (meaning t m 2190) (meaning t m 3097) (meaning t m 3969) (meaning t m 4405) (meaning t m 5580) source

theorem rule20221 (p2396 p4278 p4710 : Prop) (h : (¬ p2396) ∨ (¬ p4278) ∨ (¬ p4710)) : (¬ p2396) ∨ (¬ p4278) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial20221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory9477 (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule20221 (meaning t m 2396) (meaning t m 4278) (meaning t m 4710) source

theorem rule20223 (p3266 p4191 p4345 : Prop) (h : (¬ p3266) ∨ (¬ p4191) ∨ (¬ p4345)) : (¬ p3266) ∨ (¬ p4191) ∨ (¬ p4345) := by
  classical
  tauto

theorem initial20223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4345)) := by
  have source := ElevenTheory.theory9479 (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule20223 (meaning t m 3266) (meaning t m 4191) (meaning t m 4345) source

theorem rule20225 (p2187 p2387 p4356 : Prop) (h : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p4356)) : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial20225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory9481 (m.theta 0 6) (m.theta 5 6) (m.theta 6 8)
  exact rule20225 (meaning t m 2187) (meaning t m 2387) (meaning t m 4356) source

theorem rule20236 (p2006 p2027 p2132 p2274 p2765 p2780 p3822 : Prop) (h : (¬ p2006) ∨ (¬ p2132) ∨ p2765 ∨ p2027 ∨ (¬ p2780) ∨ (¬ p2274) ∨ (¬ p3822)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p2780) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial20236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory9492 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule20236 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2274) (meaning t m 2765) (meaning t m 2780) (meaning t m 3822) source

theorem rule20239 (p2027 p2138 p2946 p4111 p4117 p4243 p4365 p4704 : Prop) (h : (¬ p4365) ∨ (¬ p4243) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p2138) ∨ (¬ p4704) ∨ (¬ p4117)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2946) ∨ (¬ p4111) ∨ (¬ p4117) ∨ (¬ p4243) ∨ (¬ p4365) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial20239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory9495 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule20239 (meaning t m 2027) (meaning t m 2138) (meaning t m 2946) (meaning t m 4111) (meaning t m 4117) (meaning t m 4243) (meaning t m 4365) (meaning t m 4704) source

theorem rule20240 (p2027 p3097 p3644 p3952 p4237 p4276 p4378 : Prop) (h : (¬ p3952) ∨ (¬ p3097) ∨ (¬ p3644) ∨ (¬ p4378) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p4237)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3644) ∨ (¬ p3952) ∨ (¬ p4237) ∨ (¬ p4276) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial20240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory9496 t (m.theta 3 5) (m.theta 3 8) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule20240 (meaning t m 2027) (meaning t m 3097) (meaning t m 3644) (meaning t m 3952) (meaning t m 4237) (meaning t m 4276) (meaning t m 4378) source

theorem rule20241 (p3333 p3876 p4635 : Prop) (h : (¬ p4635) ∨ (¬ p3333) ∨ (¬ p3876)) : (¬ p3333) ∨ (¬ p3876) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial20241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory9497 (m.theta 2 4) (m.theta 4 7) (m.theta 4 9)
  exact rule20241 (meaning t m 3333) (meaning t m 3876) (meaning t m 4635) source

theorem rule20243 (p1979 p2027 p2657 p2727 p2749 p2946 p3586 p3688 : Prop) (h : (¬ p2657) ∨ p3586 ∨ p2027 ∨ (¬ p2749) ∨ (¬ p2727) ∨ (¬ p1979) ∨ (¬ p2946) ∨ (¬ p3688)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (p3586) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial20243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory9499 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5)
  exact rule20243 (meaning t m 1979) (meaning t m 2027) (meaning t m 2657) (meaning t m 2727) (meaning t m 2749) (meaning t m 2946) (meaning t m 3586) (meaning t m 3688) source

theorem rule20244 (p2727 p3019 p4154 : Prop) (h : (¬ p3019) ∨ (¬ p2727) ∨ (¬ p4154)) : (¬ p2727) ∨ (¬ p3019) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial20244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory9500 (m.theta 1 3) (m.theta 3 4) (m.theta 3 6)
  exact rule20244 (meaning t m 2727) (meaning t m 3019) (meaning t m 4154) source

theorem rule20248 (p3527 p3570 p4909 : Prop) (h : (¬ p3570) ∨ (¬ p3527) ∨ (¬ p4909)) : (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial20248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory9504 (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule20248 (meaning t m 3527) (meaning t m 3570) (meaning t m 4909) source

end SunPrize.SMT
