import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory008
import SunPrize.Certificate.Theory009
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule10778 (p2027 p2177 p2437 p2481 p3960 p4256 p4276 : Prop) (h : (¬ p3960) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p4256) ∨ (¬ p4276)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial10778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory2290 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule10778 (meaning t m 2027) (meaning t m 2177) (meaning t m 2437) (meaning t m 2481) (meaning t m 3960) (meaning t m 4256) (meaning t m 4276) source

theorem rule10779 (p2027 p2751 p3038 p3572 p3631 p3821 p4155 : Prop) (h : (¬ p3038) ∨ (¬ p3821) ∨ (¬ p2751) ∨ (¬ p3631) ∨ (¬ p4155) ∨ (¬ p3572) ∨ p2027) : (p2027) ∨ (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3572) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial10779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory2291 t (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9)
  exact rule10779 (meaning t m 2027) (meaning t m 2751) (meaning t m 3038) (meaning t m 3572) (meaning t m 3631) (meaning t m 3821) (meaning t m 4155) source

theorem rule10781 (p2027 p2311 p2598 p2753 p2850 p3204 p3550 p3551 p3727 p4347 p4444 p4870 p5400 : Prop) (h : (¬ p5400) ∨ (¬ p3550) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2850) ∨ (¬ p4444) ∨ (¬ p3727) ∨ (¬ p2753) ∨ (¬ p3204) ∨ (¬ p4870) ∨ (¬ p3551) ∨ (¬ p2311) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3550) ∨ (¬ p3551) ∨ (¬ p3727) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4870) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial10781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory2293 t (m.theta 0 2) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 10) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule10781 (meaning t m 2027) (meaning t m 2311) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 3204) (meaning t m 3550) (meaning t m 3551) (meaning t m 3727) (meaning t m 4347) (meaning t m 4444) (meaning t m 4870) (meaning t m 5400) source

theorem rule10782 (p2027 p2440 p2531 p3083 p5433 p5569 : Prop) (h : (¬ p3083) ∨ (¬ p2531) ∨ p2027 ∨ (¬ p5433) ∨ (¬ p2440) ∨ (¬ p5569)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2531) ∨ (¬ p3083) ∨ (¬ p5433) ∨ (¬ p5569) := by
  classical
  tauto

theorem initial10782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 5433)) ∨ (¬ (meaning t m 5569)) := by
  have source := ElevenTheory.theory2294 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 10) (m.theta 5 8)
  exact rule10782 (meaning t m 2027) (meaning t m 2440) (meaning t m 2531) (meaning t m 3083) (meaning t m 5433) (meaning t m 5569) source

theorem rule10783 (p2027 p2598 p2753 p2850 p2982 p3204 p3266 p3946 p4191 p4450 p4870 : Prop) (h : (¬ p2598) ∨ (¬ p4450) ∨ (¬ p2982) ∨ (¬ p3266) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3946) ∨ (¬ p2753) ∨ (¬ p4870) ∨ (¬ p3204)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3204) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial10783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory2295 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10783 (meaning t m 2027) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 2982) (meaning t m 3204) (meaning t m 3266) (meaning t m 3946) (meaning t m 4191) (meaning t m 4450) (meaning t m 4870) source

theorem rule10784 (p2027 p2584 p2589 p2667 p2685 p3579 p4195 p4646 : Prop) (h : (¬ p2589) ∨ (¬ p2584) ∨ (¬ p3579) ∨ (¬ p2667) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p2685) ∨ (¬ p3579) ∨ (¬ p4195) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial10784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2296 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7)
  exact rule10784 (meaning t m 2027) (meaning t m 2584) (meaning t m 2589) (meaning t m 2667) (meaning t m 2685) (meaning t m 3579) (meaning t m 4195) (meaning t m 4646) source

theorem rule10786 (p3105 p4385 : Prop) (h : (¬ p4385) ∨ (¬ p3105)) : (¬ p3105) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial10786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory2298 (m.theta 2 5) (m.theta 5 9)
  exact rule10786 (meaning t m 3105) (meaning t m 4385) source

theorem rule10787 (p2027 p2493 p2589 p3347 p4203 p4948 p5043 : Prop) (h : (¬ p3347) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p5043) ∨ (¬ p4203) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p4203) ∨ (¬ p4948) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial10787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory2299 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9)
  exact rule10787 (meaning t m 2027) (meaning t m 2493) (meaning t m 2589) (meaning t m 3347) (meaning t m 4203) (meaning t m 4948) (meaning t m 5043) source

theorem rule10789 (p2829 p3688 : Prop) (h : (¬ p3688) ∨ (¬ p2829)) : (¬ p2829) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial10789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory2301 (m.theta 1 2) (m.theta 2 6)
  exact rule10789 (meaning t m 2829) (meaning t m 3688) source

theorem rule10791 (p2027 p2363 p3266 p4322 p4335 p4433 : Prop) (h : (¬ p4433) ∨ (¬ p4335) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial10791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory2303 t (m.theta 5 8) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule10791 (meaning t m 2027) (meaning t m 2363) (meaning t m 3266) (meaning t m 4322) (meaning t m 4335) (meaning t m 4433) source

theorem rule10792 (p2027 p3461 p3692 p3990 p4433 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3990) ∨ (¬ p4433) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3461)) : (p2027) ∨ (¬ p3461) ∨ (¬ p3692) ∨ (¬ p3990) ∨ (¬ p4433) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial10792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory2304 t (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10792 (meaning t m 2027) (meaning t m 3461) (meaning t m 3692) (meaning t m 3990) (meaning t m 4433) (meaning t m 4444) source

theorem rule10793 (p2027 p2829 p3574 p3585 p4390 p4753 : Prop) (h : (¬ p4753) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p2829) ∨ p2027) : (p2027) ∨ (¬ p2829) ∨ (¬ p3574) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial10793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2305 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6)
  exact rule10793 (meaning t m 2027) (meaning t m 2829) (meaning t m 3574) (meaning t m 3585) (meaning t m 4390) (meaning t m 4753) source

theorem rule10794 (p2027 p2493 p3379 p3555 p4034 p4717 : Prop) (h : (¬ p3379) ∨ (¬ p2493) ∨ (¬ p4034) ∨ p2027 ∨ (¬ p4717) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2306 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6)
  exact rule10794 (meaning t m 2027) (meaning t m 2493) (meaning t m 3379) (meaning t m 3555) (meaning t m 4034) (meaning t m 4717) source

theorem rule10795 (p2027 p3201 p3486 p3569 p3684 p4629 : Prop) (h : (¬ p3684) ∨ (¬ p3569) ∨ (¬ p3201) ∨ (¬ p4629) ∨ p2027 ∨ (¬ p3486)) : (p2027) ∨ (¬ p3201) ∨ (¬ p3486) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial10795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory2307 t (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule10795 (meaning t m 2027) (meaning t m 3201) (meaning t m 3486) (meaning t m 3569) (meaning t m 3684) (meaning t m 4629) source

theorem rule10796 (p2027 p2138 p2493 p2598 p3590 p3698 p4717 : Prop) (h : (¬ p4717) ∨ (¬ p2598) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p2493) ∨ (¬ p3698)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2493) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p3698) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2308 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6)
  exact rule10796 (meaning t m 2027) (meaning t m 2138) (meaning t m 2493) (meaning t m 2598) (meaning t m 3590) (meaning t m 3698) (meaning t m 4717) source

theorem rule10797 (p2027 p2579 p2829 p3585 p4390 p4727 : Prop) (h : p2027 ∨ (¬ p4727) ∨ (¬ p2579) ∨ (¬ p4390) ∨ (¬ p3585) ∨ (¬ p2829)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial10797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory2309 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule10797 (meaning t m 2027) (meaning t m 2579) (meaning t m 2829) (meaning t m 3585) (meaning t m 4390) (meaning t m 4727) source

theorem rule10798 (p2027 p2829 p3585 p3684 p4390 p4717 : Prop) (h : (¬ p3585) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p4717) ∨ (¬ p4390)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4390) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2310 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule10798 (meaning t m 2027) (meaning t m 2829) (meaning t m 3585) (meaning t m 3684) (meaning t m 4390) (meaning t m 4717) source

theorem rule10799 (p2027 p2528 p3016 p3878 p4118 p4595 : Prop) (h : (¬ p3878) ∨ (¬ p2528) ∨ (¬ p3016) ∨ (¬ p4595) ∨ p2027 ∨ (¬ p4118)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p4118) ∨ (¬ p4595) := by
  classical
  tauto

theorem initial10799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4595)) := by
  have source := ElevenTheory.theory2311 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule10799 (meaning t m 2027) (meaning t m 2528) (meaning t m 3016) (meaning t m 3878) (meaning t m 4118) (meaning t m 4595) source

theorem rule10800 (p2027 p2707 p3585 p3658 p3684 p4646 : Prop) (h : (¬ p3684) ∨ (¬ p3658) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3684) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial10800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2312 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7)
  exact rule10800 (meaning t m 2027) (meaning t m 2707) (meaning t m 3585) (meaning t m 3658) (meaning t m 3684) (meaning t m 4646) source

theorem rule10801 (p2027 p2138 p2774 p4185 p4244 p4555 : Prop) (h : (¬ p2138) ∨ (¬ p4555) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4185) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4185) ∨ (¬ p4244) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2313 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7)
  exact rule10801 (meaning t m 2027) (meaning t m 2138) (meaning t m 2774) (meaning t m 4185) (meaning t m 4244) (meaning t m 4555) source

theorem rule10802 (p2027 p2608 p2761 p2839 p3105 p3946 p4191 p4395 p5021 : Prop) (h : (¬ p3946) ∨ (¬ p2608) ∨ (¬ p5021) ∨ (¬ p2839) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p4395) ∨ (¬ p3105) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4395) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial10802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory2314 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule10802 (meaning t m 2027) (meaning t m 2608) (meaning t m 2761) (meaning t m 2839) (meaning t m 3105) (meaning t m 3946) (meaning t m 4191) (meaning t m 4395) (meaning t m 5021) source

theorem rule10804 (p2027 p3286 p3414 p4278 p4653 p4660 : Prop) (h : p2027 ∨ (¬ p4653) ∨ (¬ p3414) ∨ (¬ p4278) ∨ (¬ p3286) ∨ (¬ p4660)) : (p2027) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p4278) ∨ (¬ p4653) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial10804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4653)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory2316 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 7) (m.theta 7 9)
  exact rule10804 (meaning t m 2027) (meaning t m 3286) (meaning t m 3414) (meaning t m 4278) (meaning t m 4653) (meaning t m 4660) source

theorem rule10806 (p2027 p2810 p3609 p4118 p4373 p5011 : Prop) (h : p2027 ∨ (¬ p3609) ∨ (¬ p4373) ∨ (¬ p5011) ∨ (¬ p2810) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4373) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial10806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4373)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory2318 t (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule10806 (meaning t m 2027) (meaning t m 2810) (meaning t m 3609) (meaning t m 4118) (meaning t m 4373) (meaning t m 5011) source

theorem rule10807 (p2027 p2383 p2962 p3556 p3989 p4555 : Prop) (h : (¬ p2383) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p3989) ∨ (¬ p2962)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2319 t (m.theta 0 5) (m.theta 0 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule10807 (meaning t m 2027) (meaning t m 2383) (meaning t m 2962) (meaning t m 3556) (meaning t m 3989) (meaning t m 4555) source

theorem rule10809 (p2027 p2761 p3945 p4133 p4347 p4444 : Prop) (h : (¬ p3945) ∨ (¬ p4133) ∨ (¬ p2761) ∨ (¬ p4444) ∨ (¬ p4347) ∨ p2027) : (p2027) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial10809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory2321 t (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10809 (meaning t m 2027) (meaning t m 2761) (meaning t m 3945) (meaning t m 4133) (meaning t m 4347) (meaning t m 4444) source

theorem rule10810 (p2027 p2459 p2881 p3955 p4347 p4559 : Prop) (h : (¬ p2881) ∨ (¬ p4559) ∨ (¬ p3955) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3955) ∨ (¬ p4347) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory2322 t (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule10810 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3955) (meaning t m 4347) (meaning t m 4559) source

theorem rule10811 (p2027 p2553 p2881 p3956 p4138 p4559 : Prop) (h : (¬ p2881) ∨ (¬ p4138) ∨ (¬ p3956) ∨ (¬ p2553) ∨ (¬ p4559) ∨ p2027) : (p2027) ∨ (¬ p2553) ∨ (¬ p2881) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory2323 t (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule10811 (meaning t m 2027) (meaning t m 2553) (meaning t m 2881) (meaning t m 3956) (meaning t m 4138) (meaning t m 4559) source

theorem rule10812 (p2027 p2881 p3399 p3542 p3860 p4911 : Prop) (h : (¬ p4911) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p3399) ∨ (¬ p2881) ∨ (¬ p3542)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p4911) := by
  classical
  tauto

theorem initial10812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4911)) := by
  have source := ElevenTheory.theory2324 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 5 7) (m.theta 7 8)
  exact rule10812 (meaning t m 2027) (meaning t m 2881) (meaning t m 3399) (meaning t m 3542) (meaning t m 3860) (meaning t m 4911) source

theorem rule10813 (p2027 p2177 p2295 p3581 p3644 p4976 : Prop) (h : p2027 ∨ (¬ p4976) ∨ (¬ p3581) ∨ (¬ p2295) ∨ (¬ p2177) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial10813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory2325 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10813 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 3581) (meaning t m 3644) (meaning t m 4976) source

theorem rule10814 (p2027 p2295 p2579 p2588 p2659 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2579) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2659) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial10814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory2326 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule10814 (meaning t m 2027) (meaning t m 2295) (meaning t m 2579) (meaning t m 2588) (meaning t m 2659) (meaning t m 3019) source

theorem rule10815 (p2027 p2252 p2750 p3093 p3319 p3414 p3553 p3954 p4330 p4348 : Prop) (h : (¬ p4330) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p3319) ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3414)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial10815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory2327 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule10815 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 3093) (meaning t m 3319) (meaning t m 3414) (meaning t m 3553) (meaning t m 3954) (meaning t m 4330) (meaning t m 4348) source

theorem rule10816 (p2027 p2230 p3238 p3402 p3591 p4079 p4756 : Prop) (h : (¬ p4756) ∨ (¬ p3402) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p4079) ∨ (¬ p3591) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756) := by
  classical
  tauto

theorem initial10816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4756)) := by
  have source := ElevenTheory.theory2328 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5)
  exact rule10816 (meaning t m 2027) (meaning t m 2230) (meaning t m 3238) (meaning t m 3402) (meaning t m 3591) (meaning t m 4079) (meaning t m 4756) source

theorem rule10819 (p2027 p2797 p3567 p4110 p4315 p4356 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p4356) ∨ (¬ p4110) ∨ (¬ p4315) ∨ (¬ p3567)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4110) ∨ (¬ p4315) ∨ (¬ p4356) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial10819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2331 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule10819 (meaning t m 2027) (meaning t m 2797) (meaning t m 3567) (meaning t m 4110) (meaning t m 4315) (meaning t m 4356) (meaning t m 4705) source

theorem rule10821 (p2027 p2881 p2901 p2954 p3551 p4984 : Prop) (h : (¬ p4984) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2881) ∨ (¬ p2954)) : (p2027) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2954) ∨ (¬ p3551) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial10821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory2333 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule10821 (meaning t m 2027) (meaning t m 2881) (meaning t m 2901) (meaning t m 2954) (meaning t m 3551) (meaning t m 4984) source

theorem rule10822 (p2027 p3323 p3461 p3746 p4425 p4976 : Prop) (h : (¬ p3461) ∨ (¬ p4976) ∨ (¬ p4425) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p3746)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial10822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory2334 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule10822 (meaning t m 2027) (meaning t m 3323) (meaning t m 3461) (meaning t m 3746) (meaning t m 4425) (meaning t m 4976) source

theorem rule10823 (p2027 p2685 p2954 p3556 p4315 p4333 : Prop) (h : (¬ p3556) ∨ (¬ p4333) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p4315) ∨ (¬ p2954)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2954) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial10823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory2335 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule10823 (meaning t m 2027) (meaning t m 2685) (meaning t m 2954) (meaning t m 3556) (meaning t m 4315) (meaning t m 4333) source

theorem rule10825 (p2027 p2901 p3237 p3680 p4192 p4425 p4705 : Prop) (h : p2027 ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4425) ∨ (¬ p4705) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4192) ∨ (¬ p4425) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial10825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2337 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule10825 (meaning t m 2027) (meaning t m 2901) (meaning t m 3237) (meaning t m 3680) (meaning t m 4192) (meaning t m 4425) (meaning t m 4705) source

theorem rule10826 (p2027 p3506 p4322 p4705 p4948 p5038 : Prop) (h : (¬ p4948) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p4705) ∨ (¬ p3506) ∨ (¬ p5038)) : (p2027) ∨ (¬ p3506) ∨ (¬ p4322) ∨ (¬ p4705) ∨ (¬ p4948) ∨ (¬ p5038) := by
  classical
  tauto

theorem initial10826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4705)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5038)) := by
  have source := ElevenTheory.theory2338 t (m.theta 3 5) (m.theta 3 9) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule10826 (meaning t m 2027) (meaning t m 3506) (meaning t m 4322) (meaning t m 4705) (meaning t m 4948) (meaning t m 5038) source

theorem rule10827 (p2027 p2138 p2774 p4110 p4185 p4885 : Prop) (h : (¬ p2138) ∨ (¬ p4110) ∨ (¬ p4185) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4885)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p4110) ∨ (¬ p4185) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial10827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory2339 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6)
  exact rule10827 (meaning t m 2027) (meaning t m 2138) (meaning t m 2774) (meaning t m 4110) (meaning t m 4185) (meaning t m 4885) source

theorem rule10829 (p2027 p2187 p2284 p4275 p4320 p4405 : Prop) (h : (¬ p2187) ∨ (¬ p4320) ∨ (¬ p4275) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4405)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2341 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule10829 (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 4275) (meaning t m 4320) (meaning t m 4405) source

theorem rule10830 (p2027 p2109 p2264 p2707 p3960 p4242 p4779 : Prop) (h : (¬ p3960) ∨ (¬ p2707) ∨ (¬ p4242) ∨ (¬ p2109) ∨ p2027 ∨ (¬ p4779) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2109) ∨ (¬ p2264) ∨ (¬ p2707) ∨ (¬ p3960) ∨ (¬ p4242) ∨ (¬ p4779) := by
  classical
  tauto

theorem initial10830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2109)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4779)) := by
  have source := ElevenTheory.theory2342 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 7) (m.theta 7 8)
  exact rule10830 (meaning t m 2027) (meaning t m 2109) (meaning t m 2264) (meaning t m 2707) (meaning t m 3960) (meaning t m 4242) (meaning t m 4779) source

theorem rule10831 (p2027 p2110 p3055 p3998 p4364 p4749 p5612 : Prop) (h : (¬ p4364) ∨ (¬ p4749) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2110) ∨ (¬ p5612) ∨ (¬ p3998)) : (p2027) ∨ (¬ p2110) ∨ (¬ p3055) ∨ (¬ p3998) ∨ (¬ p4364) ∨ (¬ p4749) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial10831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2110)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory2343 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 8 10)
  exact rule10831 (meaning t m 2027) (meaning t m 2110) (meaning t m 3055) (meaning t m 3998) (meaning t m 4364) (meaning t m 4749) (meaning t m 5612) source

theorem rule10832 (p2027 p2737 p3483 p3953 p4026 p4842 : Prop) (h : (¬ p3953) ∨ (¬ p2737) ∨ (¬ p3483) ∨ (¬ p4026) ∨ p2027 ∨ (¬ p4842)) : (p2027) ∨ (¬ p2737) ∨ (¬ p3483) ∨ (¬ p3953) ∨ (¬ p4026) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial10832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2344 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 9)
  exact rule10832 (meaning t m 2027) (meaning t m 2737) (meaning t m 3483) (meaning t m 3953) (meaning t m 4026) (meaning t m 4842) source

theorem rule10834 (p2264 p3553 : Prop) (h : (¬ p3553) ∨ (¬ p2264)) : (¬ p2264) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial10834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory2346 (m.theta 3 7) (m.theta 7 8)
  exact rule10834 (meaning t m 2264) (meaning t m 3553) source

theorem rule10835 (p2027 p3256 p3568 p4341 p4347 p4405 : Prop) (h : (¬ p3256) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p4341) ∨ (¬ p4405)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3568) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2347 t (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule10835 (meaning t m 2027) (meaning t m 3256) (meaning t m 3568) (meaning t m 4341) (meaning t m 4347) (meaning t m 4405) source

theorem rule10836 (p2027 p2274 p3093 p4366 p4427 p4514 : Prop) (h : (¬ p3093) ∨ (¬ p4427) ∨ (¬ p2274) ∨ (¬ p4514) ∨ p2027 ∨ (¬ p4366)) : (p2027) ∨ (¬ p2274) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial10836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory2348 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7)
  exact rule10836 (meaning t m 2027) (meaning t m 2274) (meaning t m 3093) (meaning t m 4366) (meaning t m 4427) (meaning t m 4514) source

theorem rule10838 (p2027 p2532 p2534 p3105 p3694 p4158 : Prop) (h : (¬ p2532) ∨ (¬ p4158) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p2534) ∨ p2027) : (p2027) ∨ (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3105) ∨ (¬ p3694) ∨ (¬ p4158) := by
  classical
  tauto

theorem initial10838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4158)) := by
  have source := ElevenTheory.theory2350 t (m.theta 2 5) (m.theta 4 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule10838 (meaning t m 2027) (meaning t m 2532) (meaning t m 2534) (meaning t m 3105) (meaning t m 3694) (meaning t m 4158) source

theorem rule10839 (p2027 p2252 p2579 p2630 p2655 p2745 p3016 : Prop) (h : (¬ p3016) ∨ (¬ p2655) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2745)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2745) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial10839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory2351 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule10839 (meaning t m 2027) (meaning t m 2252) (meaning t m 2579) (meaning t m 2630) (meaning t m 2655) (meaning t m 2745) (meaning t m 3016) source

theorem rule10840 (p2027 p2579 p2696 p3422 p3905 p4749 : Prop) (h : (¬ p3905) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4749) ∨ (¬ p3422) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3422) ∨ (¬ p3905) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial10840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2352 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule10840 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 3422) (meaning t m 3905) (meaning t m 4749) source

theorem rule10842 (p2027 p2470 p3367 p4242 p4730 p5369 : Prop) (h : p2027 ∨ (¬ p3367) ∨ (¬ p4730) ∨ (¬ p4242) ∨ (¬ p2470) ∨ (¬ p5369)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4730) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial10842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4730)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory2354 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8)
  exact rule10842 (meaning t m 2027) (meaning t m 2470) (meaning t m 3367) (meaning t m 4242) (meaning t m 4730) (meaning t m 5369) source

theorem rule10843 (p2027 p2470 p2528 p4340 p4730 p5368 : Prop) (h : (¬ p5368) ∨ (¬ p2470) ∨ (¬ p4730) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p4340) ∨ (¬ p4730) ∨ (¬ p5368) := by
  classical
  tauto

theorem initial10843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4730)) ∨ (¬ (meaning t m 5368)) := by
  have source := ElevenTheory.theory2355 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule10843 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 4340) (meaning t m 4730) (meaning t m 5368) source

theorem rule10844 (p2027 p2589 p2659 p2810 p3136 p4241 : Prop) (h : (¬ p2810) ∨ (¬ p4241) ∨ (¬ p3136) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial10844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory2356 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule10844 (meaning t m 2027) (meaning t m 2589) (meaning t m 2659) (meaning t m 2810) (meaning t m 3136) (meaning t m 4241) source

theorem rule10845 (p2027 p2860 p3367 p4173 p4874 p4881 : Prop) (h : (¬ p4881) ∨ (¬ p2860) ∨ (¬ p3367) ∨ (¬ p4874) ∨ (¬ p4173) ∨ p2027) : (p2027) ∨ (¬ p2860) ∨ (¬ p3367) ∨ (¬ p4173) ∨ (¬ p4874) ∨ (¬ p4881) := by
  classical
  tauto

theorem initial10845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 4881)) := by
  have source := ElevenTheory.theory2357 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule10845 (meaning t m 2027) (meaning t m 2860) (meaning t m 3367) (meaning t m 4173) (meaning t m 4874) (meaning t m 4881) source

theorem rule10847 (p2027 p2373 p3146 p3661 p4118 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p2373) ∨ (¬ p3661) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory2359 t (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule10847 (meaning t m 2027) (meaning t m 2373) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 4702) source

theorem rule10848 (p2027 p2088 p3156 p3949 p4208 p4532 : Prop) (h : p2027 ∨ (¬ p4532) ∨ (¬ p4208) ∨ (¬ p2088) ∨ (¬ p3949) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3949) ∨ (¬ p4208) ∨ (¬ p4532) := by
  classical
  tauto

theorem initial10848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4532)) := by
  have source := ElevenTheory.theory2360 t (m.theta 0 8) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule10848 (meaning t m 2027) (meaning t m 2088) (meaning t m 3156) (meaning t m 3949) (meaning t m 4208) (meaning t m 4532) source

theorem rule10849 (p2027 p3073 p3497 p3692 p4496 p4960 : Prop) (h : (¬ p4496) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4960) ∨ (¬ p3073) ∨ (¬ p3497)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4496) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory2361 t (m.theta 1 5) (m.theta 1 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule10849 (meaning t m 2027) (meaning t m 3073) (meaning t m 3497) (meaning t m 3692) (meaning t m 4496) (meaning t m 4960) source

theorem rule10851 (p2027 p2122 p2177 p2311 p2782 p3551 : Prop) (h : p2027 ∨ (¬ p2782) ∨ (¬ p2311) ∨ (¬ p2177) ∨ (¬ p2122) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2782) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial10851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2782)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory2363 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule10851 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2311) (meaning t m 2782) (meaning t m 3551) source

theorem rule10852 (p2027 p2528 p3497 p4261 p4355 p4446 p4702 : Prop) (h : (¬ p4261) ∨ (¬ p4446) ∨ (¬ p4702) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p4355) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p4261) ∨ (¬ p4355) ∨ (¬ p4446) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory2364 t (m.theta 1 8) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule10852 (meaning t m 2027) (meaning t m 2528) (meaning t m 3497) (meaning t m 4261) (meaning t m 4355) (meaning t m 4446) (meaning t m 4702) source

theorem rule10853 (p2027 p2972 p3680 p4314 p4960 p5284 : Prop) (h : (¬ p2972) ∨ (¬ p4314) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p4960)) : (p2027) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4314) ∨ (¬ p4960) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial10853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4314)) ∨ (¬ (meaning t m 4960)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2365 t (m.theta 1 5) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule10853 (meaning t m 2027) (meaning t m 2972) (meaning t m 3680) (meaning t m 4314) (meaning t m 4960) (meaning t m 5284) source

theorem rule10854 (p2027 p3707 p4208 p4322 p4942 p4960 : Prop) (h : (¬ p4960) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p4942) ∨ (¬ p4208) ∨ (¬ p3707)) : (p2027) ∨ (¬ p3707) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4942) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4942)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory2366 t (m.theta 1 5) (m.theta 1 9) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule10854 (meaning t m 2027) (meaning t m 3707) (meaning t m 4208) (meaning t m 4322) (meaning t m 4942) (meaning t m 4960) source

theorem rule10856 (p2027 p2498 p3319 p3422 p4037 p4194 p4753 : Prop) (h : (¬ p3319) ∨ (¬ p2498) ∨ (¬ p4037) ∨ (¬ p4194) ∨ p2027 ∨ (¬ p3422) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2498) ∨ (¬ p3319) ∨ (¬ p3422) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial10856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2368 t (m.theta 1 6) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule10856 (meaning t m 2027) (meaning t m 2498) (meaning t m 3319) (meaning t m 3422) (meaning t m 4037) (meaning t m 4194) (meaning t m 4753) source

theorem rule10857 (p2027 p2470 p2579 p2588 p4157 p4405 : Prop) (h : (¬ p2470) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4157) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2369 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule10857 (meaning t m 2027) (meaning t m 2470) (meaning t m 2579) (meaning t m 2588) (meaning t m 4157) (meaning t m 4405) source

theorem rule10858 (p2027 p2098 p2753 p3688 p3822 p4326 p4405 : Prop) (h : p2027 ∨ (¬ p2753) ∨ (¬ p2098) ∨ (¬ p4405) ∨ (¬ p3822) ∨ (¬ p4326) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2753) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4326) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2370 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8)
  exact rule10858 (meaning t m 2027) (meaning t m 2098) (meaning t m 2753) (meaning t m 3688) (meaning t m 3822) (meaning t m 4326) (meaning t m 4405) source

theorem rule10860 (p2027 p2241 p2387 p3027 p3931 p4347 p4444 p4826 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p3027) ∨ (¬ p3931) ∨ p2027 ∨ (¬ p2387) ∨ (¬ p4826) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial10860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory2372 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule10860 (meaning t m 2027) (meaning t m 2241) (meaning t m 2387) (meaning t m 3027) (meaning t m 3931) (meaning t m 4347) (meaning t m 4444) (meaning t m 4826) (meaning t m 5021) source

theorem rule10863 (p2027 p2210 p2427 p4366 p4629 p4909 : Prop) (h : (¬ p4629) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p4366) ∨ (¬ p2210) ∨ (¬ p4909)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2427) ∨ (¬ p4366) ∨ (¬ p4629) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial10863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4629)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory2375 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7)
  exact rule10863 (meaning t m 2027) (meaning t m 2210) (meaning t m 2427) (meaning t m 4366) (meaning t m 4629) (meaning t m 4909) source

theorem rule10864 (p2449 p3947 : Prop) (h : (¬ p3947) ∨ (¬ p2449)) : (¬ p2449) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial10864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory2376 (m.theta 3 7) (m.theta 7 9)
  exact rule10864 (meaning t m 2449) (meaning t m 3947) source

theorem rule10866 (p2774 p2780 : Prop) (h : (¬ p2780) ∨ (¬ p2774)) : (¬ p2774) ∨ (¬ p2780) := by
  classical
  tauto

theorem initial10866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2780)) := by
  have source := ElevenTheory.theory2378 (m.theta 0 2) (m.theta 2 6)
  exact rule10866 (meaning t m 2774) (meaning t m 2780) source

theorem rule10867 (p2027 p2383 p2779 p3917 p3979 p4171 p5122 : Prop) (h : (¬ p4171) ∨ (¬ p2779) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p3979) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2779) ∨ (¬ p3917) ∨ (¬ p3979) ∨ (¬ p4171) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial10867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory2379 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 8 9)
  exact rule10867 (meaning t m 2027) (meaning t m 2383) (meaning t m 2779) (meaning t m 3917) (meaning t m 3979) (meaning t m 4171) (meaning t m 5122) source

theorem rule10868 (p2027 p2132 p2440 p3055 p4210 p4418 p4753 : Prop) (h : (¬ p2132) ∨ (¬ p4210) ∨ (¬ p4418) ∨ (¬ p3055) ∨ (¬ p4753) ∨ (¬ p2440) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2440) ∨ (¬ p3055) ∨ (¬ p4210) ∨ (¬ p4418) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial10868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2380 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5)
  exact rule10868 (meaning t m 2027) (meaning t m 2132) (meaning t m 2440) (meaning t m 3055) (meaning t m 4210) (meaning t m 4418) (meaning t m 4753) source

theorem rule10869 (p2027 p2241 p2727 p3591 p4319 p4972 : Prop) (h : (¬ p3591) ∨ (¬ p4319) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p2727) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3591) ∨ (¬ p4319) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial10869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory2381 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6)
  exact rule10869 (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 3591) (meaning t m 4319) (meaning t m 4972) source

theorem rule10871 (p2027 p2936 p3449 p3644 p4366 p5307 : Prop) (h : (¬ p5307) ∨ (¬ p4366) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2936)) : (p2027) ∨ (¬ p2936) ∨ (¬ p3449) ∨ (¬ p3644) ∨ (¬ p4366) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial10871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2936)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory2383 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 4 7) (m.theta 7 8)
  exact rule10871 (meaning t m 2027) (meaning t m 2936) (meaning t m 3449) (meaning t m 3644) (meaning t m 4366) (meaning t m 5307) source

theorem rule10873 (p2027 p2619 p3644 p4244 p4277 p4312 p4378 : Prop) (h : (¬ p4244) ∨ (¬ p4378) ∨ (¬ p2619) ∨ (¬ p3644) ∨ (¬ p4277) ∨ (¬ p4312) ∨ p2027) : (p2027) ∨ (¬ p2619) ∨ (¬ p3644) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4312) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial10873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory2385 t (m.theta 2 5) (m.theta 3 8) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule10873 (meaning t m 2027) (meaning t m 2619) (meaning t m 3644) (meaning t m 4244) (meaning t m 4277) (meaning t m 4312) (meaning t m 4378) source

theorem rule10874 (p2027 p2470 p3146 p3346 p4158 p4440 : Prop) (h : (¬ p4158) ∨ (¬ p3346) ∨ (¬ p3146) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p4440)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3146) ∨ (¬ p3346) ∨ (¬ p4158) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial10874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory2386 t (m.theta 0 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule10874 (meaning t m 2027) (meaning t m 2470) (meaning t m 3146) (meaning t m 3346) (meaning t m 4158) (meaning t m 4440) source

theorem rule10875 (p2027 p2476 p2534 p2659 p3256 p4121 : Prop) (h : (¬ p2476) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3256) ∨ (¬ p4121)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2659) ∨ (¬ p3256) ∨ (¬ p4121) := by
  classical
  tauto

theorem initial10875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4121)) := by
  have source := ElevenTheory.theory2387 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule10875 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2659) (meaning t m 3256) (meaning t m 4121) source

theorem rule10877 (p2027 p2881 p3309 p3923 p3960 p4113 p4559 : Prop) (h : (¬ p4113) ∨ (¬ p3309) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p3960) ∨ (¬ p4559) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p3960) ∨ (¬ p4113) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory2389 t (m.theta 0 8) (m.theta 1 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule10877 (meaning t m 2027) (meaning t m 2881) (meaning t m 3309) (meaning t m 3923) (meaning t m 3960) (meaning t m 4113) (meaning t m 4559) source

theorem rule10878 (p2027 p2307 p2387 p2881 p4138 p4559 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p2881) ∨ (¬ p2387) ∨ (¬ p4138) ∨ (¬ p4559)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2881) ∨ (¬ p4138) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory2390 t (m.theta 0 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule10878 (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2881) (meaning t m 4138) (meaning t m 4559) source

theorem rule10879 (p2027 p2088 p2482 p2656 p2992 p4261 p4262 p4704 : Prop) (h : (¬ p4262) ∨ (¬ p4704) ∨ (¬ p2992) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p2482) ∨ (¬ p2088) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2482) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2391 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 5) (m.theta 8 9)
  exact rule10879 (meaning t m 2027) (meaning t m 2088) (meaning t m 2482) (meaning t m 2656) (meaning t m 2992) (meaning t m 4261) (meaning t m 4262) (meaning t m 4704) source

theorem rule10881 (p2027 p2241 p2685 p2745 p3032 p4366 : Prop) (h : (¬ p2685) ∨ (¬ p3032) ∨ (¬ p2241) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2745)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3032) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial10881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory2393 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7)
  exact rule10881 (meaning t m 2027) (meaning t m 2241) (meaning t m 2685) (meaning t m 2745) (meaning t m 3032) (meaning t m 4366) source

theorem rule10882 (p2027 p2299 p3115 p4042 p4320 p4335 p4559 : Prop) (h : (¬ p4335) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p4042) ∨ (¬ p2299) ∨ (¬ p3115) ∨ (¬ p4559)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3115) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4335) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial10882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4335)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory2394 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8)
  exact rule10882 (meaning t m 2027) (meaning t m 2299) (meaning t m 3115) (meaning t m 4042) (meaning t m 4320) (meaning t m 4335) (meaning t m 4559) source

theorem rule10883 (p2027 p2192 p2608 p3369 p3646 p4377 : Prop) (h : (¬ p4377) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p2192) ∨ (¬ p3369)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial10883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory2395 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6)
  exact rule10883 (meaning t m 2027) (meaning t m 2192) (meaning t m 2608) (meaning t m 3369) (meaning t m 3646) (meaning t m 4377) source

theorem rule10884 (p2027 p2589 p2659 p2901 p3413 p4235 : Prop) (h : p2027 ∨ (¬ p4235) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p2659) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial10884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory2396 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule10884 (meaning t m 2027) (meaning t m 2589) (meaning t m 2659) (meaning t m 2901) (meaning t m 3413) (meaning t m 4235) source

theorem rule10885 (p2027 p2319 p2727 p3031 p3516 p3567 p3817 p4972 : Prop) (h : (¬ p3031) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p2727) ∨ (¬ p2319) ∨ (¬ p4972) ∨ (¬ p3817) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2727) ∨ (¬ p3031) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p3817) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial10885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory2397 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 6) (m.theta 7 9)
  exact rule10885 (meaning t m 2027) (meaning t m 2319) (meaning t m 2727) (meaning t m 3031) (meaning t m 3516) (meaning t m 3567) (meaning t m 3817) (meaning t m 4972) source

theorem rule10886 (p2027 p2449 p2651 p3821 p4650 p4849 : Prop) (h : (¬ p3821) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4849) ∨ (¬ p4650)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p3821) ∨ (¬ p4650) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial10886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4650)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory2398 t (m.theta 0 3) (m.theta 0 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule10886 (meaning t m 2027) (meaning t m 2449) (meaning t m 2651) (meaning t m 3821) (meaning t m 4650) (meaning t m 4849) source

theorem rule10887 (p2027 p2307 p2727 p3549 p3567 p4245 p4972 : Prop) (h : (¬ p3567) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p4245) ∨ (¬ p3549) ∨ (¬ p2307) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2727) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial10887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4245)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory2399 t (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule10887 (meaning t m 2027) (meaning t m 2307) (meaning t m 2727) (meaning t m 3549) (meaning t m 3567) (meaning t m 4245) (meaning t m 4972) source

theorem rule10889 (p2027 p2373 p2542 p3742 p4001 p4904 : Prop) (h : p2027 ∨ (¬ p4904) ∨ (¬ p3742) ∨ (¬ p2373) ∨ (¬ p4001) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial10889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory2401 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8)
  exact rule10889 (meaning t m 2027) (meaning t m 2373) (meaning t m 2542) (meaning t m 3742) (meaning t m 4001) (meaning t m 4904) source

theorem rule10890 (p2027 p2651 p2963 p3422 p4389 p4753 : Prop) (h : (¬ p2651) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4753) ∨ (¬ p3422) ∨ (¬ p4389)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p3422) ∨ (¬ p4389) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial10890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2402 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule10890 (meaning t m 2027) (meaning t m 2651) (meaning t m 2963) (meaning t m 3422) (meaning t m 4389) (meaning t m 4753) source

theorem rule10891 (p2027 p2264 p3146 p3947 p4445 p4905 : Prop) (h : p2027 ∨ (¬ p4905) ∨ (¬ p4445) ∨ (¬ p3947) ∨ (¬ p2264) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10891 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory2403 t (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10891 (meaning t m 2027) (meaning t m 2264) (meaning t m 3146) (meaning t m 3947) (meaning t m 4445) (meaning t m 4905) source

theorem rule10892 (p2027 p2498 p3016 p3379 p3591 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p3016) ∨ (¬ p3591) ∨ (¬ p3379) ∨ (¬ p2498) ∨ p2027) : (p2027) ∨ (¬ p2498) ∨ (¬ p3016) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2404 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6)
  exact rule10892 (meaning t m 2027) (meaning t m 2498) (meaning t m 3016) (meaning t m 3379) (meaning t m 3591) (meaning t m 4811) source

theorem rule10893 (p2027 p2307 p2578 p3016 p3549 p4202 p4512 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p2307) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p3549) ∨ (¬ p3016) ∨ (¬ p2578) ∨ p2027) : (p2027) ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2405 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 5) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule10893 (meaning t m 2027) (meaning t m 2307) (meaning t m 2578) (meaning t m 3016) (meaning t m 3549) (meaning t m 4202) (meaning t m 4512) (meaning t m 4811) source

theorem rule10894 (p3136 p4315 : Prop) (h : (¬ p4315) ∨ (¬ p3136)) : (¬ p3136) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial10894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory2406 (m.theta 2 3) (m.theta 3 5)
  exact rule10894 (meaning t m 3136) (meaning t m 4315) source

theorem rule10895 (p2027 p2177 p2307 p2459 p2781 p3365 p4208 p4315 p5059 : Prop) (h : (¬ p4315) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2781) ∨ (¬ p2459) ∨ (¬ p5059) ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p4208)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p4208) ∨ (¬ p4315) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial10895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory2407 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule10895 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2459) (meaning t m 2781) (meaning t m 3365) (meaning t m 4208) (meaning t m 4315) (meaning t m 5059) source

theorem rule10899 (p2027 p2579 p2662 p2745 p3422 p3475 p4111 : Prop) (h : (¬ p3475) ∨ (¬ p2579) ∨ (¬ p2745) ∨ p2027 ∨ (¬ p3422) ∨ (¬ p2662) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial10899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory2411 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule10899 (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 2745) (meaning t m 3422) (meaning t m 3475) (meaning t m 4111) source

theorem rule10900 (p2027 p2668 p3093 p3922 p4275 p4366 p4405 p4909 : Prop) (h : (¬ p4909) ∨ (¬ p4366) ∨ (¬ p3922) ∨ (¬ p2668) ∨ (¬ p4405) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p3093)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3093) ∨ (¬ p3922) ∨ (¬ p4275) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial10900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory2412 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule10900 (meaning t m 2027) (meaning t m 2668) (meaning t m 3093) (meaning t m 3922) (meaning t m 4275) (meaning t m 4366) (meaning t m 4405) (meaning t m 4909) source

theorem rule10903 (p2027 p2246 p2331 p2668 p2751 p4358 p4841 : Prop) (h : p2027 ∨ (¬ p4841) ∨ (¬ p2246) ∨ (¬ p4358) ∨ (¬ p2668) ∨ (¬ p2751) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2751) ∨ (¬ p4358) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial10903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory2415 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8)
  exact rule10903 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2668) (meaning t m 2751) (meaning t m 4358) (meaning t m 4841) source

theorem rule10905 (p2797 p4195 : Prop) (h : (¬ p4195) ∨ (¬ p2797)) : (¬ p2797) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial10905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory2417 (m.theta 2 3) (m.theta 3 6)
  exact rule10905 (meaning t m 2797) (meaning t m 4195) source

theorem rule10907 (p2027 p2579 p3389 p4710 p5472 p5514 : Prop) (h : (¬ p5472) ∨ (¬ p4710) ∨ p2027 ∨ (¬ p5514) ∨ (¬ p2579) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p5472) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial10907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5472)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory2419 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10) (m.theta 6 7)
  exact rule10907 (meaning t m 2027) (meaning t m 2579) (meaning t m 3389) (meaning t m 4710) (meaning t m 5472) (meaning t m 5514) source

theorem rule10909 (p2027 p3527 p3551 p3585 p3687 p3959 p5086 : Prop) (h : (¬ p3959) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3527) ∨ (¬ p5086) ∨ (¬ p3687) ∨ (¬ p3551)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3585) ∨ (¬ p3687) ∨ (¬ p3959) ∨ (¬ p5086) := by
  classical
  tauto

theorem initial10909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 5086)) := by
  have source := ElevenTheory.theory2421 t (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule10909 (meaning t m 2027) (meaning t m 3527) (meaning t m 3551) (meaning t m 3585) (meaning t m 3687) (meaning t m 3959) (meaning t m 5086) source

theorem rule10910 (p2027 p2807 p3246 p3292 p4280 p4656 : Prop) (h : (¬ p4656) ∨ p2027 ∨ (¬ p3292) ∨ (¬ p3246) ∨ (¬ p2807) ∨ (¬ p4280)) : (p2027) ∨ (¬ p2807) ∨ (¬ p3246) ∨ (¬ p3292) ∨ (¬ p4280) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial10910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory2422 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 9) (m.theta 5 7) (m.theta 7 9)
  exact rule10910 (meaning t m 2027) (meaning t m 2807) (meaning t m 3246) (meaning t m 3292) (meaning t m 4280) (meaning t m 4656) source

theorem rule10912 (p2027 p2264 p2427 p4031 p4120 p4132 p4362 : Prop) (h : (¬ p2264) ∨ (¬ p4031) ∨ p2027 ∨ (¬ p4132) ∨ (¬ p4362) ∨ (¬ p2427) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p4031) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4362) := by
  classical
  tauto

theorem initial10912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4362)) := by
  have source := ElevenTheory.theory2424 t (m.theta 0 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule10912 (meaning t m 2027) (meaning t m 2264) (meaning t m 2427) (meaning t m 4031) (meaning t m 4120) (meaning t m 4132) (meaning t m 4362) source

theorem rule10914 (p2027 p3644 p3998 p4590 p5203 p5558 : Prop) (h : (¬ p5203) ∨ (¬ p4590) ∨ (¬ p5558) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p3998)) : (p2027) ∨ (¬ p3644) ∨ (¬ p3998) ∨ (¬ p4590) ∨ (¬ p5203) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial10914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 5203)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory2426 t (m.theta 0 7) (m.theta 0 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10)
  exact rule10914 (meaning t m 2027) (meaning t m 3644) (meaning t m 3998) (meaning t m 4590) (meaning t m 5203) (meaning t m 5558) source

theorem rule10915 (p2027 p2441 p2449 p3580 p4256 p4278 p4608 : Prop) (h : p2027 ∨ (¬ p4608) ∨ (¬ p3580) ∨ (¬ p2449) ∨ (¬ p2441) ∨ (¬ p4256) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4256) ∨ (¬ p4278) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial10915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory2427 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 7 9)
  exact rule10915 (meaning t m 2027) (meaning t m 2441) (meaning t m 2449) (meaning t m 3580) (meaning t m 4256) (meaning t m 4278) (meaning t m 4608) source

theorem rule10916 (p2027 p3527 p3551 p3959 p4235 p4344 p4431 p4632 : Prop) (h : (¬ p4344) ∨ (¬ p3959) ∨ (¬ p3551) ∨ (¬ p4632) ∨ (¬ p4431) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3527)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3959) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial10916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3959)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2428 t (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule10916 (meaning t m 2027) (meaning t m 3527) (meaning t m 3551) (meaning t m 3959) (meaning t m 4235) (meaning t m 4344) (meaning t m 4431) (meaning t m 4632) source

theorem rule10917 (p2027 p2230 p2870 p2933 p3540 p4885 p4909 : Prop) (h : (¬ p3540) ∨ (¬ p4885) ∨ (¬ p4909) ∨ (¬ p2933) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p4885) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial10917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4885)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory2429 t (m.theta 0 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule10917 (meaning t m 2027) (meaning t m 2230) (meaning t m 2870) (meaning t m 2933) (meaning t m 3540) (meaning t m 4885) (meaning t m 4909) source

theorem rule10918 (p2027 p2751 p3707 p4035 p4759 p5153 p5284 : Prop) (h : (¬ p3707) ∨ (¬ p4759) ∨ (¬ p5153) ∨ p2027 ∨ (¬ p4035) ∨ (¬ p5284) ∨ (¬ p2751)) : (p2027) ∨ (¬ p2751) ∨ (¬ p3707) ∨ (¬ p4035) ∨ (¬ p4759) ∨ (¬ p5153) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial10918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 5153)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2430 t (m.theta 1 3) (m.theta 1 6) (m.theta 1 9) (m.theta 2 3) (m.theta 3 9) (m.theta 9 10)
  exact rule10918 (meaning t m 2027) (meaning t m 2751) (meaning t m 3707) (meaning t m 4035) (meaning t m 4759) (meaning t m 5153) (meaning t m 5284) source

theorem rule10919 (p2027 p2579 p3389 p3822 p4710 p5222 : Prop) (h : (¬ p3389) ∨ (¬ p4710) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p5222) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3822) ∨ (¬ p4710) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial10919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory2431 t (m.theta 0 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule10919 (meaning t m 2027) (meaning t m 2579) (meaning t m 3389) (meaning t m 3822) (meaning t m 4710) (meaning t m 5222) source

theorem rule10920 (p2027 p2177 p3969 p4260 p4905 p5557 : Prop) (h : (¬ p2177) ∨ (¬ p4905) ∨ (¬ p4260) ∨ (¬ p5557) ∨ (¬ p3969) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p3969) ∨ (¬ p4260) ∨ (¬ p4905) ∨ (¬ p5557) := by
  classical
  tauto

theorem initial10920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5557)) := by
  have source := ElevenTheory.theory2432 t (m.theta 5 8) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule10920 (meaning t m 2027) (meaning t m 2177) (meaning t m 3969) (meaning t m 4260) (meaning t m 4905) (meaning t m 5557) source

theorem rule10921 (p2662 p3363 p4343 : Prop) (h : p3363 ∨ (¬ p4343) ∨ (¬ p2662)) : (¬ p2662) ∨ (p3363) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial10921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2662)) ∨ (meaning t m 3363) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory2433 (m.theta 0 4) (m.theta 2 4) (m.theta 3 4)
  exact rule10921 (meaning t m 2662) (meaning t m 3363) (meaning t m 4343) source

theorem rule10926 (p2027 p2230 p3115 p3346 p4705 p4947 : Prop) (h : (¬ p4947) ∨ (¬ p2230) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p3346) ∨ (¬ p4705)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3115) ∨ (¬ p3346) ∨ (¬ p4705) ∨ (¬ p4947) := by
  classical
  tauto

theorem initial10926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4705)) ∨ (¬ (meaning t m 4947)) := by
  have source := ElevenTheory.theory2438 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9)
  exact rule10926 (meaning t m 2027) (meaning t m 2230) (meaning t m 3115) (meaning t m 3346) (meaning t m 4705) (meaning t m 4947) source

theorem rule10927 (p2027 p2952 p3166 p4311 p4320 p4904 : Prop) (h : (¬ p3166) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p4904) ∨ (¬ p4320) ∨ (¬ p4311)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4320) ∨ (¬ p4904) := by
  classical
  tauto

theorem initial10927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4904)) := by
  have source := ElevenTheory.theory2439 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8)
  exact rule10927 (meaning t m 2027) (meaning t m 2952) (meaning t m 3166) (meaning t m 4311) (meaning t m 4320) (meaning t m 4904) source

theorem rule10928 (p2027 p2191 p2220 p2542 p4109 p4202 p4811 : Prop) (h : (¬ p4202) ∨ (¬ p2542) ∨ (¬ p4811) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2191) ∨ (¬ p4109)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2440 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8)
  exact rule10928 (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 2542) (meaning t m 4109) (meaning t m 4202) (meaning t m 4811) source

theorem rule10929 (p2027 p2579 p2655 p2807 p3016 p4652 : Prop) (h : p2027 ∨ (¬ p3016) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4652)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p3016) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial10929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2441 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6)
  exact rule10929 (meaning t m 2027) (meaning t m 2579) (meaning t m 2655) (meaning t m 2807) (meaning t m 3016) (meaning t m 4652) source

theorem rule10930 (p3256 p4118 : Prop) (h : (¬ p4118) ∨ (¬ p3256)) : (¬ p3256) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial10930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory2442 (m.theta 3 8) (m.theta 8 9)
  exact rule10930 (meaning t m 3256) (meaning t m 4118) source

theorem rule10931 (p2027 p2122 p2177 p2252 p2589 p2655 p2750 p2829 p3146 p4118 p4346 p4607 p4905 : Prop) (h : (¬ p2655) ∨ (¬ p4905) ∨ (¬ p2252) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4607) ∨ (¬ p2122) ∨ (¬ p2829) ∨ (¬ p4118) ∨ (¬ p4346) ∨ (¬ p2589) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2252) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory2443 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule10931 (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2252) (meaning t m 2589) (meaning t m 2655) (meaning t m 2750) (meaning t m 2829) (meaning t m 3146) (meaning t m 4118) (meaning t m 4346) (meaning t m 4607) (meaning t m 4905) source

theorem rule10933 (p2656 p2662 : Prop) (h : p2662 ∨ p2656) : (p2656) ∨ (p2662) := by
  classical
  tauto

theorem initial10933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2656) ∨ (meaning t m 2662) := by
  have source := ElevenTheory.theory2445 (m.theta 0 4) (m.theta 3 4)
  exact rule10933 (meaning t m 2656) (meaning t m 2662) source

theorem rule10934 (p2027 p2518 p2563 p4173 p4202 p4610 : Prop) (h : p2027 ∨ (¬ p4202) ∨ (¬ p4610) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p2518)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2563) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial10934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory2446 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule10934 (meaning t m 2027) (meaning t m 2518) (meaning t m 2563) (meaning t m 4173) (meaning t m 4202) (meaning t m 4610) source

theorem rule10936 (p2027 p2406 p2589 p2662 p4154 p4281 p4972 : Prop) (h : (¬ p2406) ∨ (¬ p4281) ∨ (¬ p4972) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p2662)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p4154) ∨ (¬ p4281) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial10936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory2448 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule10936 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2662) (meaning t m 4154) (meaning t m 4281) (meaning t m 4972) source

theorem rule10937 (p2027 p2241 p2745 p3136 p3412 p3555 : Prop) (h : (¬ p2241) ∨ (¬ p3412) ∨ (¬ p2745) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p3555)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2745) ∨ (¬ p3136) ∨ (¬ p3412) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial10937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory2449 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5)
  exact rule10937 (meaning t m 2027) (meaning t m 2241) (meaning t m 2745) (meaning t m 3136) (meaning t m 3412) (meaning t m 3555) source

theorem rule10938 (p2027 p3136 p3745 p4195 p4272 p5449 : Prop) (h : (¬ p5449) ∨ (¬ p4195) ∨ (¬ p3745) ∨ p2027 ∨ (¬ p4272) ∨ (¬ p3136)) : (p2027) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4272) ∨ (¬ p5449) := by
  classical
  tauto

theorem initial10938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 5449)) := by
  have source := ElevenTheory.theory2450 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 10) (m.theta 5 6)
  exact rule10938 (meaning t m 2027) (meaning t m 3136) (meaning t m 3745) (meaning t m 4195) (meaning t m 4272) (meaning t m 5449) source

theorem rule10939 (p2027 p2363 p2383 p2781 p3055 p3266 p3684 p5405 p5433 : Prop) (h : (¬ p3684) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p5405) ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p5433) ∨ (¬ p2383) ∨ (¬ p2781)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3684) ∨ (¬ p5405) ∨ (¬ p5433) := by
  classical
  tauto

theorem initial10939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5433)) := by
  have source := ElevenTheory.theory2451 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 10) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule10939 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2781) (meaning t m 3055) (meaning t m 3266) (meaning t m 3684) (meaning t m 5405) (meaning t m 5433) source

theorem rule10940 (p2027 p2498 p3379 p3422 p3591 p5214 : Prop) (h : (¬ p5214) ∨ (¬ p2498) ∨ (¬ p3422) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3591)) : (p2027) ∨ (¬ p2498) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3591) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial10940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2452 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6)
  exact rule10940 (meaning t m 2027) (meaning t m 2498) (meaning t m 3379) (meaning t m 3422) (meaning t m 3591) (meaning t m 5214) source

theorem rule10941 (p2027 p2850 p3096 p3584 p3727 p5449 : Prop) (h : p2027 ∨ (¬ p3584) ∨ (¬ p3727) ∨ (¬ p3096) ∨ (¬ p2850) ∨ (¬ p5449)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3584) ∨ (¬ p3727) ∨ (¬ p5449) := by
  classical
  tauto

theorem initial10941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 5449)) := by
  have source := ElevenTheory.theory2453 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 10) (m.theta 5 6)
  exact rule10941 (meaning t m 2027) (meaning t m 2850) (meaning t m 3096) (meaning t m 3584) (meaning t m 3727) (meaning t m 5449) source

theorem rule10942 (p2027 p2307 p2396 p2761 p2781 p3365 p4315 p5405 p5740 : Prop) (h : (¬ p2761) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p5740) ∨ (¬ p5405) ∨ (¬ p3365) ∨ (¬ p2307) ∨ (¬ p2781) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2781) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p5405) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial10942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory2454 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule10942 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2761) (meaning t m 2781) (meaning t m 3365) (meaning t m 4315) (meaning t m 5405) (meaning t m 5740) source

theorem rule10943 (p2027 p2383 p2781 p3055 p3461 p3684 p3990 p4444 p4948 p5059 : Prop) (h : (¬ p4444) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p5059) ∨ (¬ p3990) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3461) ∨ (¬ p3684) ∨ (¬ p3990) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial10943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2781)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory2455 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule10943 (meaning t m 2027) (meaning t m 2383) (meaning t m 2781) (meaning t m 3055) (meaning t m 3461) (meaning t m 3684) (meaning t m 3990) (meaning t m 4444) (meaning t m 4948) (meaning t m 5059) source

theorem rule10945 (p2027 p2850 p3379 p3555 p4034 p5214 : Prop) (h : p2027 ∨ (¬ p3555) ∨ (¬ p5214) ∨ (¬ p4034) ∨ (¬ p2850) ∨ (¬ p3379)) : (p2027) ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial10945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2457 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5)
  exact rule10945 (meaning t m 2027) (meaning t m 2850) (meaning t m 3379) (meaning t m 3555) (meaning t m 4034) (meaning t m 5214) source

theorem rule10947 (p2027 p2406 p2901 p2928 p4001 p4705 : Prop) (h : (¬ p4001) ∨ (¬ p2928) ∨ (¬ p2406) ∨ (¬ p4705) ∨ (¬ p2901) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p2901) ∨ (¬ p2928) ∨ (¬ p4001) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial10947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2459 t (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule10947 (meaning t m 2027) (meaning t m 2406) (meaning t m 2901) (meaning t m 2928) (meaning t m 4001) (meaning t m 4705) source

theorem rule10948 (p2819 p4358 : Prop) (h : (¬ p4358) ∨ (¬ p2819)) : (¬ p2819) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial10948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory2460 (m.theta 2 6) (m.theta 6 8)
  exact rule10948 (meaning t m 2819) (meaning t m 4358) source

theorem rule10949 (p2027 p2210 p2563 p3591 p3957 p4629 : Prop) (h : (¬ p4629) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2563) ∨ (¬ p3957)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2563) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial10949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory2461 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6)
  exact rule10949 (meaning t m 2027) (meaning t m 2210) (meaning t m 2563) (meaning t m 3591) (meaning t m 3957) (meaning t m 4629) source

theorem rule10950 (p2027 p2284 p2307 p3549 p3743 p4512 p4957 : Prop) (h : (¬ p3743) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4957) ∨ (¬ p2307) ∨ (¬ p4512) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4512) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial10950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory2462 t (m.theta 0 6) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule10950 (meaning t m 2027) (meaning t m 2284) (meaning t m 2307) (meaning t m 3549) (meaning t m 3743) (meaning t m 4512) (meaning t m 4957) source

theorem rule10951 (p2027 p2138 p2774 p3952 p4185 p5053 : Prop) (h : (¬ p4185) ∨ p2027 ∨ (¬ p5053) ∨ (¬ p3952) ∨ (¬ p2774) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial10951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory2463 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6)
  exact rule10951 (meaning t m 2027) (meaning t m 2138) (meaning t m 2774) (meaning t m 3952) (meaning t m 4185) (meaning t m 5053) source

theorem rule10952 (p2027 p2553 p2573 p3822 p4730 p5220 : Prop) (h : (¬ p2553) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p4730) ∨ (¬ p3822) ∨ (¬ p5220)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3822) ∨ (¬ p4730) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial10952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4730)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory2464 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule10952 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 3822) (meaning t m 4730) (meaning t m 5220) source

theorem rule10953 (p2027 p3367 p3389 p3688 p3689 p4106 p4730 : Prop) (h : (¬ p4730) ∨ (¬ p3688) ∨ (¬ p3689) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p4106)) : (p2027) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3688) ∨ (¬ p3689) ∨ (¬ p4106) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial10953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory2465 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 4 7)
  exact rule10953 (meaning t m 2027) (meaning t m 3367) (meaning t m 3389) (meaning t m 3688) (meaning t m 3689) (meaning t m 4106) (meaning t m 4730) source

theorem rule10956 (p2027 p2743 p3361 p3367 p3414 p3683 p4650 : Prop) (h : (¬ p2743) ∨ (¬ p3683) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3361) ∨ p2027 ∨ (¬ p4650)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3367) ∨ (¬ p3414) ∨ (¬ p3683) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial10956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory2468 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7)
  exact rule10956 (meaning t m 2027) (meaning t m 2743) (meaning t m 3361) (meaning t m 3367) (meaning t m 3414) (meaning t m 3683) (meaning t m 4650) source

theorem rule10957 (p2027 p2717 p3551 p3587 p4283 p4320 p5053 : Prop) (h : (¬ p4283) ∨ (¬ p3551) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p2717) ∨ (¬ p3587) ∨ (¬ p5053)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3587) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial10957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory2469 t (m.theta 0 7) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule10957 (meaning t m 2027) (meaning t m 2717) (meaning t m 3551) (meaning t m 3587) (meaning t m 4283) (meaning t m 4320) (meaning t m 5053) source

theorem rule10958 (p2027 p2098 p2299 p3425 p4477 p4804 : Prop) (h : p2027 ∨ (¬ p4804) ∨ (¬ p4477) ∨ (¬ p3425) ∨ (¬ p2098) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p4477) ∨ (¬ p4804) := by
  classical
  tauto

theorem initial10958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 4804)) := by
  have source := ElevenTheory.theory2470 t (m.theta 0 2) (m.theta 2 7) (m.theta 2 8) (m.theta 6 7) (m.theta 7 8)
  exact rule10958 (meaning t m 2027) (meaning t m 2098) (meaning t m 2299) (meaning t m 3425) (meaning t m 4477) (meaning t m 4804) source

theorem rule10959 (p2027 p2299 p2319 p2341 p4026 p4620 p5016 : Prop) (h : (¬ p5016) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2319) ∨ (¬ p4620) ∨ (¬ p4026) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p4026) ∨ (¬ p4620) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial10959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory2471 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule10959 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 4026) (meaning t m 4620) (meaning t m 5016) source

theorem rule10960 (p2027 p3497 p3741 p3875 p4149 p4702 p5568 : Prop) (h : (¬ p4702) ∨ (¬ p3741) ∨ (¬ p5568) ∨ (¬ p3875) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p4149)) : (p2027) ∨ (¬ p3497) ∨ (¬ p3741) ∨ (¬ p3875) ∨ (¬ p4149) ∨ (¬ p4702) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial10960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4702)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory2472 t (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule10960 (meaning t m 2027) (meaning t m 3497) (meaning t m 3741) (meaning t m 3875) (meaning t m 4149) (meaning t m 4702) (meaning t m 5568) source

theorem rule10961 (p2027 p2911 p3570 p3741 p4204 p4948 p5043 : Prop) (h : (¬ p4204) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p5043) ∨ p2027 ∨ (¬ p4948) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3741) ∨ (¬ p4204) ∨ (¬ p4948) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial10961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory2473 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule10961 (meaning t m 2027) (meaning t m 2911) (meaning t m 3570) (meaning t m 3741) (meaning t m 4204) (meaning t m 4948) (meaning t m 5043) source

theorem rule10963 (p2027 p2743 p3073 p4340 p4968 p5316 : Prop) (h : (¬ p2743) ∨ p2027 ∨ (¬ p4968) ∨ (¬ p4340) ∨ (¬ p3073) ∨ (¬ p5316)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3073) ∨ (¬ p4340) ∨ (¬ p4968) ∨ (¬ p5316) := by
  classical
  tauto

theorem initial10963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4968)) ∨ (¬ (meaning t m 5316)) := by
  have source := ElevenTheory.theory2475 t (m.theta 1 2) (m.theta 1 8) (m.theta 2 3) (m.theta 2 8) (m.theta 8 9)
  exact rule10963 (meaning t m 2027) (meaning t m 2743) (meaning t m 3073) (meaning t m 4340) (meaning t m 4968) (meaning t m 5316) source

theorem rule10964 (p3609 p4340 : Prop) (h : (¬ p4340) ∨ (¬ p3609)) : (¬ p3609) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial10964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory2476 (m.theta 2 8) (m.theta 8 9)
  exact rule10964 (meaning t m 3609) (meaning t m 4340) source

theorem rule10965 (p2027 p3097 p3631 p4107 p4452 p4518 : Prop) (h : (¬ p4107) ∨ (¬ p3097) ∨ (¬ p4452) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p4518)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3631) ∨ (¬ p4107) ∨ (¬ p4452) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial10965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory2477 t (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule10965 (meaning t m 2027) (meaning t m 3097) (meaning t m 3631) (meaning t m 4107) (meaning t m 4452) (meaning t m 4518) source

theorem rule10966 (p2027 p2247 p3662 p3952 p4356 p5017 : Prop) (h : (¬ p5017) ∨ (¬ p3952) ∨ (¬ p2247) ∨ (¬ p4356) ∨ p2027 ∨ (¬ p3662)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4356) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial10966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory2478 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6)
  exact rule10966 (meaning t m 2027) (meaning t m 2247) (meaning t m 3662) (meaning t m 3952) (meaning t m 4356) (meaning t m 5017) source

theorem rule10967 (p2027 p2307 p3791 p3923 p4138 p5016 p5564 : Prop) (h : (¬ p3923) ∨ (¬ p3791) ∨ (¬ p5564) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4138) ∨ (¬ p5016)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3791) ∨ (¬ p3923) ∨ (¬ p4138) ∨ (¬ p5016) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial10967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5016)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2479 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule10967 (meaning t m 2027) (meaning t m 2307) (meaning t m 3791) (meaning t m 3923) (meaning t m 4138) (meaning t m 5016) (meaning t m 5564) source

theorem rule10968 (p2470 p2476 : Prop) (h : (¬ p2476) ∨ (¬ p2470)) : (¬ p2470) ∨ (¬ p2476) := by
  classical
  tauto

theorem initial10968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2476)) := by
  have source := ElevenTheory.theory2480 (m.theta 0 4) (m.theta 4 8)
  exact rule10968 (meaning t m 2470) (meaning t m 2476) source

theorem rule10969 (p2027 p2972 p4154 p4208 p4365 p4700 p4972 : Prop) (h : (¬ p4365) ∨ (¬ p4154) ∨ (¬ p4972) ∨ p2027 ∨ (¬ p2972) ∨ (¬ p4208) ∨ (¬ p4700)) : (p2027) ∨ (¬ p2972) ∨ (¬ p4154) ∨ (¬ p4208) ∨ (¬ p4365) ∨ (¬ p4700) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial10969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory2481 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9)
  exact rule10969 (meaning t m 2027) (meaning t m 2972) (meaning t m 4154) (meaning t m 4208) (meaning t m 4365) (meaning t m 4700) (meaning t m 4972) source

theorem rule10970 (p2027 p2952 p3166 p3694 p4311 p4906 : Prop) (h : (¬ p3694) ∨ (¬ p4906) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4311)) : (p2027) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3694) ∨ (¬ p4311) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial10970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2482 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule10970 (meaning t m 2027) (meaning t m 2952) (meaning t m 3166) (meaning t m 3694) (meaning t m 4311) (meaning t m 4906) source

theorem rule10971 (p2027 p3599 p3688 p3744 p4401 p5269 : Prop) (h : (¬ p5269) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p3599) ∨ (¬ p4401)) : (p2027) ∨ (¬ p3599) ∨ (¬ p3688) ∨ (¬ p3744) ∨ (¬ p4401) ∨ (¬ p5269) := by
  classical
  tauto

theorem initial10971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 5269)) := by
  have source := ElevenTheory.theory2483 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 9) (m.theta 5 6) (m.theta 6 9)
  exact rule10971 (meaning t m 2027) (meaning t m 3599) (meaning t m 3688) (meaning t m 3744) (meaning t m 4401) (meaning t m 5269) source

theorem rule10975 (p2027 p2737 p2780 p3471 p4400 p4424 p4842 : Prop) (h : (¬ p2737) ∨ p2027 ∨ (¬ p2780) ∨ (¬ p4842) ∨ (¬ p4400) ∨ (¬ p3471) ∨ (¬ p4424)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p4400) ∨ (¬ p4424) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial10975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2487 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 6) (m.theta 2 7)
  exact rule10975 (meaning t m 2027) (meaning t m 2737) (meaning t m 2780) (meaning t m 3471) (meaning t m 4400) (meaning t m 4424) (meaning t m 4842) source

theorem rule10976 (p2027 p2137 p2307 p2737 p2962 p3549 p3953 p5049 : Prop) (h : (¬ p2737) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p2307) ∨ (¬ p3953) ∨ (¬ p2137) ∨ (¬ p2962) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial10976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory2488 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 5) (m.theta 6 7)
  exact rule10976 (meaning t m 2027) (meaning t m 2137) (meaning t m 2307) (meaning t m 2737) (meaning t m 2962) (meaning t m 3549) (meaning t m 3953) (meaning t m 5049) source

theorem rule10977 (p2027 p3367 p4379 p4425 p5159 p5391 p5682 : Prop) (h : (¬ p4425) ∨ (¬ p3367) ∨ (¬ p5391) ∨ (¬ p5159) ∨ (¬ p4379) ∨ (¬ p5682) ∨ p2027) : (p2027) ∨ (¬ p3367) ∨ (¬ p4379) ∨ (¬ p4425) ∨ (¬ p5159) ∨ (¬ p5391) ∨ (¬ p5682) := by
  classical
  tauto

theorem initial10977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5159)) ∨ (¬ (meaning t m 5391)) ∨ (¬ (meaning t m 5682)) := by
  have source := ElevenTheory.theory2489 t (m.theta 1 2) (m.theta 2 10) (m.theta 2 4) (m.theta 2 9) (m.theta 4 9) (m.theta 9 10)
  exact rule10977 (meaning t m 2027) (meaning t m 3367) (meaning t m 4379) (meaning t m 4425) (meaning t m 5159) (meaning t m 5391) (meaning t m 5682) source

theorem rule10978 (p2027 p2307 p2497 p2542 p2962 p3549 p4109 p4811 : Prop) (h : (¬ p2497) ∨ (¬ p3549) ∨ (¬ p2962) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4811) ∨ (¬ p2307) ∨ (¬ p4109)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2542) ∨ (¬ p2962) ∨ (¬ p3549) ∨ (¬ p4109) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10978 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2490 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 6 7)
  exact rule10978 (meaning t m 2027) (meaning t m 2307) (meaning t m 2497) (meaning t m 2542) (meaning t m 2962) (meaning t m 3549) (meaning t m 4109) (meaning t m 4811) source

theorem rule10979 (p2027 p2192 p2553 p3096 p4033 p4363 p4620 : Prop) (h : (¬ p3096) ∨ (¬ p4620) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p4033) ∨ (¬ p4363) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2553) ∨ (¬ p3096) ∨ (¬ p4033) ∨ (¬ p4363) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial10979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory2491 t (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule10979 (meaning t m 2027) (meaning t m 2192) (meaning t m 2553) (meaning t m 3096) (meaning t m 4033) (meaning t m 4363) (meaning t m 4620) source

theorem rule10980 (p2027 p2476 p2659 p4009 p4121 p4286 : Prop) (h : (¬ p2476) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p4286) ∨ (¬ p4121) ∨ (¬ p4009)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2659) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial10980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory2492 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 10)
  exact rule10980 (meaning t m 2027) (meaning t m 2476) (meaning t m 2659) (meaning t m 4009) (meaning t m 4121) (meaning t m 4286) source

theorem rule10981 (p2027 p3083 p3359 p4149 p4440 p5122 : Prop) (h : (¬ p3359) ∨ (¬ p4440) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p3083) ∨ (¬ p5122)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3359) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial10981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory2493 t (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 10) (m.theta 8 9)
  exact rule10981 (meaning t m 2027) (meaning t m 3083) (meaning t m 3359) (meaning t m 4149) (meaning t m 4440) (meaning t m 5122) source

theorem rule10982 (p2027 p3276 p3744 p4191 p4422 p4718 : Prop) (h : (¬ p4422) ∨ (¬ p4191) ∨ (¬ p3276) ∨ (¬ p4718) ∨ (¬ p3744) ∨ p2027) : (p2027) ∨ (¬ p3276) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4422)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory2494 t (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule10982 (meaning t m 2027) (meaning t m 3276) (meaning t m 3744) (meaning t m 4191) (meaning t m 4422) (meaning t m 4718) source

theorem rule10984 (p2027 p2417 p2493 p2926 p3741 p3817 p4717 : Prop) (h : (¬ p2493) ∨ (¬ p4717) ∨ (¬ p2926) ∨ (¬ p3741) ∨ (¬ p3817) ∨ p2027 ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3741) ∨ (¬ p3817) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2496 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule10984 (meaning t m 2027) (meaning t m 2417) (meaning t m 2493) (meaning t m 2926) (meaning t m 3741) (meaning t m 3817) (meaning t m 4717) source

theorem rule10985 (p2027 p2313 p2553 p3073 p3449 p3692 p3956 p4433 p5021 : Prop) (h : p2027 ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p5021) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p4433)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2553) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial10985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory2497 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule10985 (meaning t m 2027) (meaning t m 2313) (meaning t m 2553) (meaning t m 3073) (meaning t m 3449) (meaning t m 3692) (meaning t m 3956) (meaning t m 4433) (meaning t m 5021) source

theorem rule10986 (p2027 p2459 p3579 p3868 p3919 p4118 p5564 : Prop) (h : (¬ p5564) ∨ (¬ p3919) ∨ (¬ p3579) ∨ (¬ p4118) ∨ (¬ p2459) ∨ (¬ p3868) ∨ p2027) : (p2027) ∨ (¬ p2459) ∨ (¬ p3579) ∨ (¬ p3868) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial10986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2498 t (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule10986 (meaning t m 2027) (meaning t m 2459) (meaning t m 3579) (meaning t m 3868) (meaning t m 3919) (meaning t m 4118) (meaning t m 5564) source

theorem rule10987 (p3083 p4256 : Prop) (h : (¬ p4256) ∨ (¬ p3083)) : (¬ p3083) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial10987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory2499 (m.theta 3 4) (m.theta 4 8)
  exact rule10987 (meaning t m 3083) (meaning t m 4256) source

theorem rule10988 (p2027 p2187 p3093 p3365 p3366 p3555 p3568 p4195 p4377 p4405 p4516 : Prop) (h : (¬ p3568) ∨ (¬ p2187) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p3555) ∨ (¬ p3093) ∨ (¬ p4516)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3555) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4377) ∨ (¬ p4405) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial10988 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory2500 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule10988 (meaning t m 2027) (meaning t m 2187) (meaning t m 3093) (meaning t m 3365) (meaning t m 3366) (meaning t m 3555) (meaning t m 3568) (meaning t m 4195) (meaning t m 4377) (meaning t m 4405) (meaning t m 4516) source

theorem rule10989 (p2027 p3365 p3366 p3399 p3555 p3631 p3877 p3950 p4118 p4377 : Prop) (h : (¬ p3877) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p3366) ∨ (¬ p4377) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3555) ∨ (¬ p3950) ∨ p2027) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial10989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory2501 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10989 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3555) (meaning t m 3631) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4377) source

theorem rule10990 (p2027 p2156 p3125 p3365 p3366 p3370 p3461 p3877 p4377 p5123 p5600 : Prop) (h : (¬ p2156) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3370) ∨ (¬ p5123) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3366) ∨ (¬ p4377) ∨ p2027 ∨ (¬ p5600)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3461) ∨ (¬ p3877) ∨ (¬ p4377) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial10990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory2502 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule10990 (meaning t m 2027) (meaning t m 2156) (meaning t m 3125) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 3461) (meaning t m 3877) (meaning t m 4377) (meaning t m 5123) (meaning t m 5600) source

theorem rule10991 (p2027 p3641 p4149 p4440 p5122 p5160 : Prop) (h : (¬ p5160) ∨ (¬ p4440) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p4149) ∨ (¬ p3641)) : (p2027) ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p4440) ∨ (¬ p5122) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial10991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2503 t (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 10) (m.theta 8 9)
  exact rule10991 (meaning t m 2027) (meaning t m 3641) (meaning t m 4149) (meaning t m 4440) (meaning t m 5122) (meaning t m 5160) source

theorem rule10992 (p2027 p2139 p2761 p3051 p3246 p3365 p3877 p5123 p5600 : Prop) (h : (¬ p3246) ∨ (¬ p3877) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p5600) ∨ (¬ p3365) ∨ (¬ p5123) ∨ (¬ p2139) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p5123) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial10992 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory2504 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule10992 (meaning t m 2027) (meaning t m 2139) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 3365) (meaning t m 3877) (meaning t m 5123) (meaning t m 5600) source

theorem rule10993 (p2027 p2139 p2156 p2274 p2396 p3365 p3877 p3950 p4118 : Prop) (h : (¬ p3877) ∨ (¬ p4118) ∨ (¬ p2139) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p3365) ∨ (¬ p2396) ∨ (¬ p2274) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial10993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory2505 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule10993 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2274) (meaning t m 2396) (meaning t m 3365) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) source

theorem rule10994 (p2027 p2307 p2962 p3097 p3125 p3365 p3366 p3370 p3877 p3950 p4118 p4377 p4623 : Prop) (h : (¬ p3366) ∨ (¬ p4623) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4118) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3125) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4377) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial10994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory2506 t (m.theta 0 2) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9)
  exact rule10994 (meaning t m 2027) (meaning t m 2307) (meaning t m 2962) (meaning t m 3097) (meaning t m 3125) (meaning t m 3365) (meaning t m 3366) (meaning t m 3370) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4377) (meaning t m 4623) source

theorem rule10995 (p2027 p2138 p2696 p2839 p3585 p4749 : Prop) (h : (¬ p2138) ∨ (¬ p4749) ∨ (¬ p2839) ∨ (¬ p2696) ∨ (¬ p3585) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial10995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2507 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule10995 (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2839) (meaning t m 3585) (meaning t m 4749) source

theorem rule10996 (p2027 p2493 p3051 p3486 p4109 p4202 p4717 : Prop) (h : (¬ p3486) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4717) ∨ (¬ p4202)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2508 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule10996 (meaning t m 2027) (meaning t m 2493) (meaning t m 3051) (meaning t m 3486) (meaning t m 4109) (meaning t m 4202) (meaning t m 4717) source

theorem rule10997 (p2027 p2475 p2518 p3574 p3989 p4113 p4116 p4718 : Prop) (h : (¬ p4116) ∨ (¬ p2518) ∨ (¬ p2475) ∨ (¬ p4113) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p4718)) : (p2027) ∨ (¬ p2475) ∨ (¬ p2518) ∨ (¬ p3574) ∨ (¬ p3989) ∨ (¬ p4113) ∨ (¬ p4116) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory2509 t (m.theta 0 8) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule10997 (meaning t m 2027) (meaning t m 2475) (meaning t m 2518) (meaning t m 3574) (meaning t m 3989) (meaning t m 4113) (meaning t m 4116) (meaning t m 4718) source

theorem rule10998 (p2027 p2143 p2829 p3556 p3583 p4185 p4555 : Prop) (h : (¬ p2829) ∨ (¬ p4185) ∨ (¬ p3583) ∨ (¬ p3556) ∨ (¬ p4555) ∨ (¬ p2143) ∨ p2027) : (p2027) ∨ (¬ p2143) ∨ (¬ p2829) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2510 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7)
  exact rule10998 (meaning t m 2027) (meaning t m 2143) (meaning t m 2829) (meaning t m 3556) (meaning t m 3583) (meaning t m 4185) (meaning t m 4555) source

theorem rule10999 (p2027 p3093 p3483 p3834 p4867 p5148 : Prop) (h : (¬ p3093) ∨ (¬ p5148) ∨ (¬ p4867) ∨ (¬ p3834) ∨ p2027 ∨ (¬ p3483)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3483) ∨ (¬ p3834) ∨ (¬ p4867) ∨ (¬ p5148) := by
  classical
  tauto

theorem initial10999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4867)) ∨ (¬ (meaning t m 5148)) := by
  have source := ElevenTheory.theory2511 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 2 6) (m.theta 6 9)
  exact rule10999 (meaning t m 2027) (meaning t m 3093) (meaning t m 3483) (meaning t m 3834) (meaning t m 4867) (meaning t m 5148) source

theorem rule11001 (p2027 p2166 p2481 p2542 p3696 p4256 p4632 : Prop) (h : (¬ p2481) ∨ (¬ p3696) ∨ (¬ p4632) ∨ p2027 ∨ (¬ p4256) ∨ (¬ p2542) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2481) ∨ (¬ p2542) ∨ (¬ p3696) ∨ (¬ p4256) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial11001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2513 t (m.theta 0 8) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8)
  exact rule11001 (meaning t m 2027) (meaning t m 2166) (meaning t m 2481) (meaning t m 2542) (meaning t m 3696) (meaning t m 4256) (meaning t m 4632) source

theorem rule11003 (p2027 p2470 p2579 p3989 p4157 p4718 : Prop) (h : (¬ p4157) ∨ (¬ p3989) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p4718) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3989) ∨ (¬ p4157) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial11003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory2515 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule11003 (meaning t m 2027) (meaning t m 2470) (meaning t m 2579) (meaning t m 3989) (meaning t m 4157) (meaning t m 4718) source

theorem rule11004 (p2027 p2187 p2247 p2307 p3097 p4111 p4256 p4384 p5017 : Prop) (h : p2027 ∨ (¬ p5017) ∨ (¬ p3097) ∨ (¬ p2307) ∨ (¬ p2187) ∨ (¬ p4384) ∨ (¬ p4256) ∨ (¬ p4111) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial11004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory2516 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule11004 (meaning t m 2027) (meaning t m 2187) (meaning t m 2247) (meaning t m 2307) (meaning t m 3097) (meaning t m 4111) (meaning t m 4256) (meaning t m 4384) (meaning t m 5017) source

theorem rule11005 (p2027 p2247 p2307 p2459 p2881 p3359 p4111 p4275 p4697 p5017 : Prop) (h : (¬ p2247) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3359) ∨ (¬ p5017) ∨ (¬ p4275) ∨ (¬ p2881) ∨ (¬ p2459) ∨ (¬ p4697)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4275) ∨ (¬ p4697) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial11005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory2517 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11005 (meaning t m 2027) (meaning t m 2247) (meaning t m 2307) (meaning t m 2459) (meaning t m 2881) (meaning t m 3359) (meaning t m 4111) (meaning t m 4275) (meaning t m 4697) (meaning t m 5017) source

theorem rule11006 (p2027 p3551 p3641 p3876 p4404 p5199 : Prop) (h : (¬ p3876) ∨ (¬ p3641) ∨ (¬ p4404) ∨ (¬ p3551) ∨ (¬ p5199) ∨ p2027) : (p2027) ∨ (¬ p3551) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4404) ∨ (¬ p5199) := by
  classical
  tauto

theorem initial11006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 5199)) := by
  have source := ElevenTheory.theory2518 t (m.theta 0 7) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule11006 (meaning t m 2027) (meaning t m 3551) (meaning t m 3641) (meaning t m 3876) (meaning t m 4404) (meaning t m 5199) source

theorem rule11010 (p2027 p3256 p3692 p3880 p4237 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p4237) ∨ (¬ p3256) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4237) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4237)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2522 t (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule11010 (meaning t m 2027) (meaning t m 3256) (meaning t m 3692) (meaning t m 3880) (meaning t m 4237) (meaning t m 4705) source

theorem rule11011 (p2027 p2247 p3449 p4111 p4288 p5011 : Prop) (h : (¬ p4111) ∨ (¬ p4288) ∨ (¬ p2247) ∨ (¬ p5011) ∨ p2027 ∨ (¬ p3449)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4111) ∨ (¬ p4288) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial11011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory2523 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 8)
  exact rule11011 (meaning t m 2027) (meaning t m 2247) (meaning t m 3449) (meaning t m 4111) (meaning t m 4288) (meaning t m 5011) source

theorem rule11012 (p2027 p2247 p2751 p3037 p3399 p3572 : Prop) (h : (¬ p3399) ∨ (¬ p3037) ∨ (¬ p2751) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial11012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory2524 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7)
  exact rule11012 (meaning t m 2027) (meaning t m 2247) (meaning t m 2751) (meaning t m 3037) (meaning t m 3399) (meaning t m 3572) source

theorem rule11013 (p2027 p3830 p3860 p4347 p4352 p4998 : Prop) (h : (¬ p3830) ∨ (¬ p4352) ∨ (¬ p4998) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p4347)) : (p2027) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4347) ∨ (¬ p4352) ∨ (¬ p4998) := by
  classical
  tauto

theorem initial11013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4352)) ∨ (¬ (meaning t m 4998)) := by
  have source := ElevenTheory.theory2525 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 6 8) (m.theta 8 9)
  exact rule11013 (meaning t m 2027) (meaning t m 3830) (meaning t m 3860) (meaning t m 4347) (meaning t m 4352) (meaning t m 4998) source

theorem rule11014 (p2027 p3399 p3591 p4427 p4435 p5472 : Prop) (h : p4427 ∨ (¬ p4435) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p5472)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3591) ∨ (p4427) ∨ (¬ p4435) ∨ (¬ p5472) := by
  classical
  tauto

theorem initial11014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3591)) ∨ (meaning t m 4427) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 5472)) := by
  have source := ElevenTheory.theory2526 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 10) (m.theta 6 7)
  exact rule11014 (meaning t m 2027) (meaning t m 3399) (meaning t m 3591) (meaning t m 4427) (meaning t m 4435) (meaning t m 5472) source

theorem rule11015 (p2027 p3246 p3399 p3834 p4911 p5358 : Prop) (h : (¬ p4911) ∨ (¬ p5358) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3246) ∨ (¬ p3834)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4911) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial11015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4911)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory2527 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 5 7) (m.theta 7 9)
  exact rule11015 (meaning t m 2027) (meaning t m 3246) (meaning t m 3399) (meaning t m 3834) (meaning t m 4911) (meaning t m 5358) source

theorem rule11016 (p2027 p2982 p3440 p3680 p4321 p4492 p4629 : Prop) (h : (¬ p4629) ∨ (¬ p4492) ∨ p2027 ∨ (¬ p4321) ∨ (¬ p3680) ∨ (¬ p2982) ∨ (¬ p3440)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3440) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4492) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial11016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory2528 t (m.theta 1 5) (m.theta 1 8) (m.theta 1 9) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule11016 (meaning t m 2027) (meaning t m 2982) (meaning t m 3440) (meaning t m 3680) (meaning t m 4321) (meaning t m 4492) (meaning t m 4629) source

theorem rule11017 (p2027 p2187 p2192 p3486 p4275 p4405 : Prop) (h : (¬ p2192) ∨ (¬ p2187) ∨ (¬ p3486) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p4405)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p3486) ∨ (¬ p4275) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial11017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2529 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule11017 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 3486) (meaning t m 4275) (meaning t m 4405) source

theorem rule11018 (p2027 p3549 p3707 p4349 p4405 p4417 p5153 p5284 : Prop) (h : p2027 ∨ (¬ p4417) ∨ (¬ p3707) ∨ (¬ p5153) ∨ (¬ p4349) ∨ (¬ p3549) ∨ (¬ p4405) ∨ (¬ p5284)) : (p2027) ∨ (¬ p3549) ∨ (¬ p3707) ∨ (¬ p4349) ∨ (¬ p4405) ∨ (¬ p4417) ∨ (¬ p5153) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 5153)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2530 t (m.theta 1 6) (m.theta 1 9) (m.theta 3 8) (m.theta 3 9) (m.theta 6 7) (m.theta 6 8) (m.theta 9 10)
  exact rule11018 (meaning t m 2027) (meaning t m 3549) (meaning t m 3707) (meaning t m 4349) (meaning t m 4405) (meaning t m 4417) (meaning t m 5153) (meaning t m 5284) source

theorem rule11021 (p2027 p2860 p3246 p4136 p4324 p4555 : Prop) (h : (¬ p4555) ∨ (¬ p4136) ∨ (¬ p3246) ∨ (¬ p2860) ∨ (¬ p4324) ∨ p2027) : (p2027) ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p4136) ∨ (¬ p4324) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2533 t (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule11021 (meaning t m 2027) (meaning t m 2860) (meaning t m 3246) (meaning t m 4136) (meaning t m 4324) (meaning t m 4555) source

theorem rule11022 (p2027 p2542 p3276 p4949 p5170 p5284 : Prop) (h : (¬ p2542) ∨ (¬ p4949) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p5170) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2542) ∨ (¬ p3276) ∨ (¬ p4949) ∨ (¬ p5170) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4949)) ∨ (¬ (meaning t m 5170)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2534 t (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule11022 (meaning t m 2027) (meaning t m 2542) (meaning t m 3276) (meaning t m 4949) (meaning t m 5170) (meaning t m 5284) source

theorem rule11023 (p2786 p3873 p5015 : Prop) (h : (¬ p5015) ∨ p3873 ∨ (¬ p2786)) : (¬ p2786) ∨ (p3873) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial11023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2786)) ∨ (meaning t m 3873) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory2535 (m.theta 0 1) (m.theta 0 2) (m.theta 0 6)
  exact rule11023 (meaning t m 2786) (meaning t m 3873) (meaning t m 5015) source

theorem rule11024 (p2027 p2534 p2608 p2753 p2774 p3551 p3914 p4404 p4444 p5210 p5250 : Prop) (h : (¬ p2753) ∨ (¬ p2608) ∨ (¬ p2774) ∨ (¬ p3914) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4404) ∨ (¬ p5250) ∨ (¬ p4444) ∨ (¬ p5210)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3551) ∨ (¬ p3914) ∨ (¬ p4404) ∨ (¬ p4444) ∨ (¬ p5210) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial11024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3914)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5210)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory2536 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 4 8) (m.theta 6 10) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule11024 (meaning t m 2027) (meaning t m 2534) (meaning t m 2608) (meaning t m 2753) (meaning t m 2774) (meaning t m 3551) (meaning t m 3914) (meaning t m 4404) (meaning t m 4444) (meaning t m 5210) (meaning t m 5250) source

theorem rule11026 (p2027 p2459 p2881 p3051 p3585 p3954 p4521 p4697 p5160 : Prop) (h : (¬ p2459) ∨ (¬ p4521) ∨ (¬ p5160) ∨ (¬ p3051) ∨ (¬ p4697) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3954) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4697) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial11026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2538 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11026 (meaning t m 2027) (meaning t m 2459) (meaning t m 2881) (meaning t m 3051) (meaning t m 3585) (meaning t m 3954) (meaning t m 4521) (meaning t m 4697) (meaning t m 5160) source

theorem rule11027 (p2027 p2187 p2307 p2962 p3097 p3585 p3874 p3954 p4384 p4521 : Prop) (h : (¬ p3585) ∨ (¬ p3874) ∨ (¬ p4384) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p4521) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4384) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial11027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory2539 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule11027 (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2962) (meaning t m 3097) (meaning t m 3585) (meaning t m 3874) (meaning t m 3954) (meaning t m 4384) (meaning t m 4521) source

theorem rule11030 (p2027 p2190 p3744 p3955 p3969 p4620 p5580 : Prop) (h : (¬ p4620) ∨ (¬ p3955) ∨ (¬ p5580) ∨ (¬ p2190) ∨ (¬ p3744) ∨ (¬ p3969) ∨ p2027) : (p2027) ∨ (¬ p2190) ∨ (¬ p3744) ∨ (¬ p3955) ∨ (¬ p3969) ∨ (¬ p4620) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial11030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory2542 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule11030 (meaning t m 2027) (meaning t m 2190) (meaning t m 3744) (meaning t m 3955) (meaning t m 3969) (meaning t m 4620) (meaning t m 5580) source

theorem rule11031 (p2027 p2459 p2668 p3917 p4133 p4171 p4328 : Prop) (h : (¬ p4133) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4171) ∨ (¬ p4328) ∨ (¬ p3917) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2668) ∨ (¬ p3917) ∨ (¬ p4133) ∨ (¬ p4171) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial11031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory2543 t (m.theta 2 6) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11031 (meaning t m 2027) (meaning t m 2459) (meaning t m 2668) (meaning t m 3917) (meaning t m 4133) (meaning t m 4171) (meaning t m 4328) source

theorem rule11032 (p2027 p2295 p3093 p3834 p3922 p4620 p5148 : Prop) (h : (¬ p3834) ∨ (¬ p3922) ∨ (¬ p3093) ∨ (¬ p5148) ∨ (¬ p2295) ∨ (¬ p4620) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3922) ∨ (¬ p4620) ∨ (¬ p5148) := by
  classical
  tauto

theorem initial11032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 5148)) := by
  have source := ElevenTheory.theory2544 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule11032 (meaning t m 2027) (meaning t m 2295) (meaning t m 3093) (meaning t m 3834) (meaning t m 3922) (meaning t m 4620) (meaning t m 5148) source

theorem rule11033 (p2027 p2307 p2373 p3696 p4033 p4197 p4620 p4948 : Prop) (h : p2027 ∨ (¬ p4197) ∨ (¬ p2307) ∨ (¬ p4620) ∨ (¬ p4948) ∨ (¬ p3696) ∨ (¬ p2373) ∨ (¬ p4033)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p3696) ∨ (¬ p4033) ∨ (¬ p4197) ∨ (¬ p4620) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory2545 t (m.theta 0 6) (m.theta 0 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule11033 (meaning t m 2027) (meaning t m 2307) (meaning t m 2373) (meaning t m 3696) (meaning t m 4033) (meaning t m 4197) (meaning t m 4620) (meaning t m 4948) source

theorem rule11034 (p2027 p2145 p2696 p3506 p3556 p3570 p3755 p5123 p5558 : Prop) (h : (¬ p3755) ∨ (¬ p5558) ∨ (¬ p5123) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p3570) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3506) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3755) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial11034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory2546 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11034 (meaning t m 2027) (meaning t m 2145) (meaning t m 2696) (meaning t m 3506) (meaning t m 3556) (meaning t m 3570) (meaning t m 3755) (meaning t m 5123) (meaning t m 5558) source

theorem rule11035 (p3487 p3683 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p3683) ∨ p3487) : (p3487) ∨ (¬ p3683) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial11035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3487) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory2547 (m.theta 1 4) (m.theta 2 4) (m.theta 3 4)
  exact rule11035 (meaning t m 3487) (meaning t m 3683) (meaning t m 4030) source

theorem rule11038 (p2027 p2307 p2786 p3365 p3822 p4845 : Prop) (h : (¬ p4845) ∨ p2027 ∨ (¬ p2786) ∨ (¬ p2307) ∨ (¬ p3822) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p3822) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory2550 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule11038 (meaning t m 2027) (meaning t m 2307) (meaning t m 2786) (meaning t m 3365) (meaning t m 3822) (meaning t m 4845) source

theorem rule11039 (p2027 p2110 p3365 p3998 p4968 p5612 : Prop) (h : (¬ p4968) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p5612) ∨ (¬ p3998) ∨ (¬ p2110)) : (p2027) ∨ (¬ p2110) ∨ (¬ p3365) ∨ (¬ p3998) ∨ (¬ p4968) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial11039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2110)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4968)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory2551 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 3) (m.theta 2 8) (m.theta 8 10)
  exact rule11039 (meaning t m 2027) (meaning t m 2110) (meaning t m 3365) (meaning t m 3998) (meaning t m 4968) (meaning t m 5612) source

theorem rule11040 (p2027 p3365 p3527 p3546 p3659 p3819 p4782 : Prop) (h : (¬ p4782) ∨ (¬ p3546) ∨ (¬ p3819) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3527)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial11040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory2552 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule11040 (meaning t m 2027) (meaning t m 3365) (meaning t m 3527) (meaning t m 3546) (meaning t m 3659) (meaning t m 3819) (meaning t m 4782) source

theorem rule11042 (p3819 p4104 p4117 : Prop) (h : (¬ p4104) ∨ (¬ p4117) ∨ p3819) : (p3819) ∨ (¬ p4104) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial11042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3819) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory2554 (m.theta 0 2) (m.theta 0 3) (m.theta 0 7)
  exact rule11042 (meaning t m 3819) (meaning t m 4104) (meaning t m 4117) source

end SunPrize.SMT
