import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory033
import SunPrize.Certificate.Theory034
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule21790 (p2027 p2437 p2481 p2717 p3960 p4256 p5087 : Prop) (h : (¬ p2717) ∨ (¬ p4256) ∨ (¬ p3960) ∨ (¬ p2481) ∨ (¬ p2437) ∨ (¬ p5087) ∨ p2027) : (p2027) ∨ (¬ p2437) ∨ (¬ p2481) ∨ (¬ p2717) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p5087) := by
  classical
  tauto

theorem initial21790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 5087)) := by
  have source := ElevenTheory.theory11046 t (m.theta 0 8) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule21790 (meaning t m 2027) (meaning t m 2437) (meaning t m 2481) (meaning t m 2717) (meaning t m 3960) (meaning t m 4256) (meaning t m 5087) source

theorem rule21794 (p2027 p3325 p3553 p3979 p4570 p5558 : Prop) (h : (¬ p3325) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4570) ∨ (¬ p3979) ∨ (¬ p5558)) : (p2027) ∨ (¬ p3325) ∨ (¬ p3553) ∨ (¬ p3979) ∨ (¬ p4570) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial21794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory11050 t (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule21794 (meaning t m 2027) (meaning t m 3325) (meaning t m 3553) (meaning t m 3979) (meaning t m 4570) (meaning t m 5558) source

theorem rule21795 (p2027 p2191 p2248 p2417 p2437 p2651 p3555 p3692 p3950 : Prop) (h : (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p3555) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial21795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory11051 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21795 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3555) (meaning t m 3692) (meaning t m 3950) source

theorem rule21796 (p2027 p2440 p3016 p4203 p4235 p4555 : Prop) (h : (¬ p4555) ∨ (¬ p3016) ∨ (¬ p2440) ∨ (¬ p4203) ∨ p2027 ∨ (¬ p4235)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial21796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory11052 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule21796 (meaning t m 2027) (meaning t m 2440) (meaning t m 3016) (meaning t m 4203) (meaning t m 4235) (meaning t m 4555) source

theorem rule21798 (p1998 p2027 p2589 p2842 p2850 p2911 p3389 : Prop) (h : p2027 ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p2850) ∨ p2842 ∨ (¬ p3389) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2589) ∨ (p2842) ∨ (¬ p2850) ∨ (¬ p2911) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial21798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory11054 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule21798 (meaning t m 1998) (meaning t m 2027) (meaning t m 2589) (meaning t m 2842) (meaning t m 2850) (meaning t m 2911) (meaning t m 3389) source

theorem rule21799 (p2027 p2307 p2586 p3016 p3742 p3921 : Prop) (h : (¬ p3921) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3742) ∨ (¬ p3016) ∨ (¬ p2586)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial21799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory11055 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule21799 (meaning t m 2027) (meaning t m 2307) (meaning t m 2586) (meaning t m 3016) (meaning t m 3742) (meaning t m 3921) source

theorem rule21800 (p2027 p2248 p2417 p2437 p2651 p3950 p3954 p4242 p4340 : Prop) (h : (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3954) ∨ (¬ p2651) ∨ (¬ p4242) ∨ (¬ p4340) ∨ p2027 ∨ (¬ p3950)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial21800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory11056 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21800 (meaning t m 2027) (meaning t m 2248) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3950) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) source

theorem rule21801 (p2027 p2248 p2901 p2946 p3246 p3950 p3954 p4242 p4340 : Prop) (h : (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p2248) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2901) ∨ (¬ p4242) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial21801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory11057 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21801 (meaning t m 2027) (meaning t m 2248) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3950) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) source

theorem rule21802 (p2027 p2187 p2248 p2284 p2946 p3688 p3822 p3954 p4405 : Prop) (h : (¬ p2248) ∨ (¬ p2284) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4405) ∨ (¬ p3822) ∨ (¬ p3688) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial21802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory11058 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule21802 (meaning t m 2027) (meaning t m 2187) (meaning t m 2248) (meaning t m 2284) (meaning t m 2946) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) (meaning t m 4405) source

theorem rule21803 (p2027 p2248 p2449 p2761 p2807 p3954 p4242 p5123 p5612 : Prop) (h : (¬ p4242) ∨ (¬ p2248) ∨ (¬ p3954) ∨ (¬ p2449) ∨ (¬ p5612) ∨ (¬ p2807) ∨ (¬ p2761) ∨ (¬ p5123) ∨ p2027) : (p2027) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial21803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory11059 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule21803 (meaning t m 2027) (meaning t m 2248) (meaning t m 2449) (meaning t m 2761) (meaning t m 2807) (meaning t m 3954) (meaning t m 4242) (meaning t m 5123) (meaning t m 5612) source

theorem rule21804 (p2027 p2665 p3389 p3868 p4112 p4391 : Prop) (h : p2027 ∨ (¬ p3389) ∨ (¬ p3868) ∨ (¬ p2665) ∨ (¬ p4391) ∨ (¬ p4112)) : (p2027) ∨ (¬ p2665) ∨ (¬ p3389) ∨ (¬ p3868) ∨ (¬ p4112) ∨ (¬ p4391) := by
  classical
  tauto

theorem initial21804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4391)) := by
  have source := ElevenTheory.theory11060 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 10)
  exact rule21804 (meaning t m 2027) (meaning t m 2665) (meaning t m 3389) (meaning t m 3868) (meaning t m 4112) (meaning t m 4391) source

theorem rule21808 (p2000 p2027 p2169 p2363 p2589 p3692 p3988 p4110 : Prop) (h : (¬ p2000) ∨ p2169 ∨ (¬ p3692) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p3988) ∨ (¬ p2589)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial21808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory11064 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21808 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2589) (meaning t m 3692) (meaning t m 3988) (meaning t m 4110) source

theorem rule21809 (p2027 p2132 p2352 p2753 p2870 p3246 p3923 p4137 p4625 p4870 : Prop) (h : (¬ p4137) ∨ (¬ p2753) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p2870) ∨ (¬ p2132) ∨ (¬ p4870) ∨ (¬ p2352) ∨ (¬ p3923)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2352) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3923) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial21809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory11065 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule21809 (meaning t m 2027) (meaning t m 2132) (meaning t m 2352) (meaning t m 2753) (meaning t m 2870) (meaning t m 3246) (meaning t m 3923) (meaning t m 4137) (meaning t m 4625) (meaning t m 4870) source

theorem rule21810 (p2246 p3286 p3848 : Prop) (h : (¬ p3286) ∨ (¬ p2246) ∨ (¬ p3848)) : (¬ p2246) ∨ (¬ p3286) ∨ (¬ p3848) := by
  classical
  tauto

theorem initial21810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3848)) := by
  have source := ElevenTheory.theory11066 (m.theta 0 3) (m.theta 1 3) (m.theta 3 9)
  exact rule21810 (meaning t m 2246) (meaning t m 3286) (meaning t m 3848) source

theorem rule21812 (p2027 p2470 p2630 p2665 p3877 p4437 : Prop) (h : (¬ p2630) ∨ (¬ p4437) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2665)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3877) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial21812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory11068 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule21812 (meaning t m 2027) (meaning t m 2470) (meaning t m 2630) (meaning t m 2665) (meaning t m 3877) (meaning t m 4437) source

theorem rule21815 (p3005 p3136 p3661 : Prop) (h : (¬ p3005) ∨ (¬ p3661) ∨ p3136) : (¬ p3005) ∨ (p3136) ∨ (¬ p3661) := by
  classical
  tauto

theorem initial21815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3005)) ∨ (meaning t m 3136) ∨ (¬ (meaning t m 3661)) := by
  have source := ElevenTheory.theory11071 (m.theta 2 3) (m.theta 3 5) (m.theta 3 8)
  exact rule21815 (meaning t m 3005) (meaning t m 3136) (meaning t m 3661) source

theorem rule21816 (p2027 p2139 p3051 p3055 p3156 p3584 p3956 p4320 p4433 : Prop) (h : p2027 ∨ (¬ p4320) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p3156) ∨ (¬ p3055) ∨ (¬ p3051) ∨ (¬ p4433) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2139) ∨ (¬ p3051) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4320) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial21816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory11072 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule21816 (meaning t m 2027) (meaning t m 2139) (meaning t m 3051) (meaning t m 3055) (meaning t m 3156) (meaning t m 3584) (meaning t m 3956) (meaning t m 4320) (meaning t m 4433) source

theorem rule21818 (p2027 p2255 p2958 p2996 p3516 p3947 p4988 : Prop) (h : (¬ p2255) ∨ (¬ p2958) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p4988) ∨ (¬ p3947) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p2996) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial21818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory11074 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9)
  exact rule21818 (meaning t m 2027) (meaning t m 2255) (meaning t m 2958) (meaning t m 2996) (meaning t m 3516) (meaning t m 3947) (meaning t m 4988) source

theorem rule21819 (p2104 p3366 p4379 p5338 : Prop) (h : (¬ p2104) ∨ (¬ p5338) ∨ (¬ p3366) ∨ p4379) : (¬ p2104) ∨ (¬ p3366) ∨ (p4379) ∨ (¬ p5338) := by
  classical
  tauto

theorem initial21819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3366)) ∨ (meaning t m 4379) ∨ (¬ (meaning t m 5338)) := by
  have source := ElevenTheory.theory11075 (m.theta 0 2) (m.theta 1 2) (m.theta 2 8) (m.theta 2 9)
  exact rule21819 (meaning t m 2104) (meaning t m 3366) (meaning t m 4379) (meaning t m 5338) source

theorem rule21823 (p1980 p2027 p2323 p2641 p2946 p3115 p3368 p4363 : Prop) (h : (¬ p4363) ∨ (¬ p3368) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p1980) ∨ (¬ p3115) ∨ p2323) : (¬ p1980) ∨ (p2027) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3368) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial21823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory11079 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9)
  exact rule21823 (meaning t m 1980) (meaning t m 2027) (meaning t m 2323) (meaning t m 2641) (meaning t m 2946) (meaning t m 3115) (meaning t m 3368) (meaning t m 4363) source

theorem rule21826 (p2957 p3370 p4282 : Prop) (h : (¬ p2957) ∨ p4282 ∨ (¬ p3370)) : (¬ p2957) ∨ (¬ p3370) ∨ (p4282) := by
  classical
  tauto

theorem initial21826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3370)) ∨ (meaning t m 4282) := by
  have source := ElevenTheory.theory11082 (m.theta 0 5) (m.theta 1 5) (m.theta 3 5)
  exact rule21826 (meaning t m 2957) (meaning t m 3370) (meaning t m 4282) source

theorem rule21839 (p2299 p3791 p5556 : Prop) (h : (¬ p3791) ∨ (¬ p2299) ∨ (¬ p5556)) : (¬ p2299) ∨ (¬ p3791) ∨ (¬ p5556) := by
  classical
  tauto

theorem initial21839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 5556)) := by
  have source := ElevenTheory.theory11095 (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule21839 (meaning t m 2299) (meaning t m 3791) (meaning t m 5556) source

theorem rule21845 (p2027 p2122 p2313 p2373 p2406 p3379 p4358 p4433 p5021 : Prop) (h : (¬ p3379) ∨ (¬ p2122) ∨ (¬ p4358) ∨ (¬ p5021) ∨ (¬ p2313) ∨ (¬ p4433) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2373)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4433) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial21845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory11101 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21845 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2373) (meaning t m 2406) (meaning t m 3379) (meaning t m 4358) (meaning t m 4433) (meaning t m 5021) source

theorem rule21851 (p2027 p2255 p2331 p2476 p2534 p2662 p3063 p3979 p4111 p4319 p5122 : Prop) (h : (¬ p2476) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p2662) ∨ (¬ p2331) ∨ (¬ p2255) ∨ (¬ p2534) ∨ (¬ p3979)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2331) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p3063) ∨ (¬ p3979) ∨ (¬ p4111) ∨ (¬ p4319) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial21851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory11107 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21851 (meaning t m 2027) (meaning t m 2255) (meaning t m 2331) (meaning t m 2476) (meaning t m 2534) (meaning t m 2662) (meaning t m 3063) (meaning t m 3979) (meaning t m 4111) (meaning t m 4319) (meaning t m 5122) source

theorem rule21852 (p1977 p2027 p2169 p2363 p2957 p3646 p3662 p3692 p3988 : Prop) (h : (¬ p1977) ∨ p2169 ∨ p2027 ∨ (¬ p2957) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p3662) ∨ (¬ p3646)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p3988) := by
  classical
  tauto

theorem initial21852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) := by
  have source := ElevenTheory.theory11108 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule21852 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2957) (meaning t m 3646) (meaning t m 3662) (meaning t m 3692) (meaning t m 3988) source

theorem rule21856 (p2253 p2663 p4079 : Prop) (h : (¬ p2663) ∨ (¬ p2253) ∨ p4079) : (¬ p2253) ∨ (¬ p2663) ∨ (p4079) := by
  classical
  tauto

theorem initial21856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2663)) ∨ (meaning t m 4079) := by
  have source := ElevenTheory.theory11112 (m.theta 0 1) (m.theta 0 3) (m.theta 0 4)
  exact rule21856 (meaning t m 2253) (meaning t m 2663) (meaning t m 4079) source

theorem rule21857 (p2006 p2027 p2764 p3051 p4032 p4244 p4381 p4382 : Prop) (h : (¬ p4244) ∨ p2027 ∨ (¬ p2006) ∨ p2764 ∨ (¬ p3051) ∨ (¬ p4382) ∨ (¬ p4032) ∨ (¬ p4381)) : (¬ p2006) ∨ (p2027) ∨ (p2764) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4244) ∨ (¬ p4381) ∨ (¬ p4382) := by
  classical
  tauto

theorem initial21857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4382)) := by
  have source := ElevenTheory.theory11113 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21857 (meaning t m 2006) (meaning t m 2027) (meaning t m 2764) (meaning t m 3051) (meaning t m 4032) (meaning t m 4244) (meaning t m 4381) (meaning t m 4382) source

theorem rule21858 (p1994 p2027 p2331 p2406 p2440 p2611 p4117 p4154 p4281 : Prop) (h : (¬ p4154) ∨ (¬ p2331) ∨ p2611 ∨ p2027 ∨ (¬ p4117) ∨ (¬ p4281) ∨ (¬ p2440) ∨ (¬ p1994) ∨ (¬ p2406)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2611) ∨ (¬ p4117) ∨ (¬ p4154) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial21858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory11114 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule21858 (meaning t m 1994) (meaning t m 2027) (meaning t m 2331) (meaning t m 2406) (meaning t m 2440) (meaning t m 2611) (meaning t m 4117) (meaning t m 4154) (meaning t m 4281) source

theorem rule21867 (p1984 p2027 p2098 p2114 p2363 p2780 p2829 p3238 p3452 p4326 p4948 p5059 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p5059) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p2363) ∨ (¬ p4948) ∨ (¬ p2829) ∨ p2114 ∨ (¬ p2780) ∨ (¬ p4326) ∨ (¬ p2098)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2098) ∨ (p2114) ∨ (¬ p2363) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4326) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial21867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory11123 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 6) (m.theta 2 8) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule21867 (meaning t m 1984) (meaning t m 2027) (meaning t m 2098) (meaning t m 2114) (meaning t m 2363) (meaning t m 2780) (meaning t m 2829) (meaning t m 3238) (meaning t m 3452) (meaning t m 4326) (meaning t m 4948) (meaning t m 5059) source

theorem rule21871 (p2027 p2248 p2295 p2331 p2396 p3950 p3954 p4242 p4340 : Prop) (h : (¬ p4340) ∨ (¬ p2295) ∨ (¬ p3954) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4242) ∨ (¬ p3950) ∨ (¬ p2396) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial21871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory11127 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 8) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule21871 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 3950) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) source

theorem rule21872 (p2027 p2104 p2248 p2274 p2284 p2946 p3537 p3588 p3873 p4477 : Prop) (h : (¬ p2946) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p2104) ∨ (¬ p2284) ∨ (¬ p3537) ∨ (¬ p4477) ∨ (¬ p2274) ∨ (¬ p3873) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial21872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory11128 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule21872 (meaning t m 2027) (meaning t m 2104) (meaning t m 2248) (meaning t m 2274) (meaning t m 2284) (meaning t m 2946) (meaning t m 3537) (meaning t m 3588) (meaning t m 3873) (meaning t m 4477) source

theorem rule21873 (p2027 p2191 p2248 p2651 p3276 p3343 p3555 p5123 p5568 : Prop) (h : p2027 ∨ (¬ p2191) ∨ (¬ p3343) ∨ (¬ p2248) ∨ (¬ p3276) ∨ (¬ p2651) ∨ (¬ p5568) ∨ (¬ p5123) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3555) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial21873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory11129 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule21873 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2651) (meaning t m 3276) (meaning t m 3343) (meaning t m 3555) (meaning t m 5123) (meaning t m 5568) source

theorem rule21874 (p2027 p2191 p2248 p2573 p2663 p3343 p3555 p3574 p3692 p4332 : Prop) (h : (¬ p4332) ∨ (¬ p3555) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2663) ∨ (¬ p3343) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p3574) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3343) ∨ (¬ p3555) ∨ (¬ p3574) ∨ (¬ p3692) ∨ (¬ p4332) := by
  classical
  tauto

theorem initial21874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4332)) := by
  have source := ElevenTheory.theory11130 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule21874 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2573) (meaning t m 2663) (meaning t m 3343) (meaning t m 3555) (meaning t m 3574) (meaning t m 3692) (meaning t m 4332) source

theorem rule21875 (p2027 p2191 p2248 p2331 p2668 p3555 p3692 p3979 p5122 : Prop) (h : (¬ p2331) ∨ (¬ p2191) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p3979) ∨ (¬ p3555) ∨ (¬ p5122) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3979) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial21875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory11131 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule21875 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2331) (meaning t m 2668) (meaning t m 3555) (meaning t m 3692) (meaning t m 3979) (meaning t m 5122) source

theorem rule21877 (p2498 p4761 p4973 : Prop) (h : (¬ p2498) ∨ (¬ p4973) ∨ p4761) : (¬ p2498) ∨ (p4761) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial21877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (meaning t m 4761) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory11133 t (m.theta 1 6) (m.theta 3 6) (m.theta 4 6)
  exact rule21877 (meaning t m 2498) (meaning t m 4761) (meaning t m 4973) source

theorem rule21878 (p2027 p2248 p2295 p2331 p2396 p3585 p3954 p4641 p5160 : Prop) (h : p2027 ∨ (¬ p2331) ∨ (¬ p4641) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2248) ∨ (¬ p3954) ∨ (¬ p5160) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4641) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial21878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory11134 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 3 6) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule21878 (meaning t m 2027) (meaning t m 2248) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 3585) (meaning t m 3954) (meaning t m 4641) (meaning t m 5160) source

theorem rule21882 (p2027 p2241 p2748 p3688 p3954 p4842 : Prop) (h : (¬ p2241) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p2748) ∨ (¬ p4842)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial21882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory11138 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6)
  exact rule21882 (meaning t m 2027) (meaning t m 2241) (meaning t m 2748) (meaning t m 3688) (meaning t m 3954) (meaning t m 4842) source

theorem rule21883 (p2027 p2177 p2254 p2630 p2657 p3093 p3309 p3877 p4041 : Prop) (h : p2027 ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p3877) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p4041)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3877) ∨ (¬ p4041) := by
  classical
  tauto

theorem initial21883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) := by
  have source := ElevenTheory.theory11139 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21883 (meaning t m 2027) (meaning t m 2177) (meaning t m 2254) (meaning t m 2630) (meaning t m 2657) (meaning t m 3093) (meaning t m 3309) (meaning t m 3877) (meaning t m 4041) source

theorem rule21884 (p2000 p2027 p2437 p2766 p3540 p4256 p4348 p4383 : Prop) (h : (¬ p2000) ∨ (¬ p4256) ∨ (¬ p3540) ∨ (¬ p4348) ∨ p2766 ∨ p2027 ∨ (¬ p2437) ∨ (¬ p4383)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2437) ∨ (p2766) ∨ (¬ p3540) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial21884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory11140 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21884 (meaning t m 2000) (meaning t m 2027) (meaning t m 2437) (meaning t m 2766) (meaning t m 3540) (meaning t m 4256) (meaning t m 4348) (meaning t m 4383) source

theorem rule21885 (p1983 p2027 p2202 p2254 p2396 p2563 p2657 p3054 p3399 p3683 p3758 p4075 p4260 : Prop) (h : (¬ p2563) ∨ (¬ p3399) ∨ (¬ p4075) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2396) ∨ p2202 ∨ (¬ p2657) ∨ (¬ p2254) ∨ (¬ p3054) ∨ (¬ p3758) ∨ (¬ p3683) ∨ (¬ p4260)) : (¬ p1983) ∨ (p2027) ∨ (p2202) ∨ (¬ p2254) ∨ (¬ p2396) ∨ (¬ p2563) ∨ (¬ p2657) ∨ (¬ p3054) ∨ (¬ p3399) ∨ (¬ p3683) ∨ (¬ p3758) ∨ (¬ p4075) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial21885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory11141 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9)
  exact rule21885 (meaning t m 1983) (meaning t m 2027) (meaning t m 2202) (meaning t m 2254) (meaning t m 2396) (meaning t m 2563) (meaning t m 2657) (meaning t m 3054) (meaning t m 3399) (meaning t m 3683) (meaning t m 3758) (meaning t m 4075) (meaning t m 4260) source

theorem rule21886 (p3745 p4328 p4428 : Prop) (h : (¬ p4328) ∨ (¬ p4428) ∨ p3745) : (p3745) ∨ (¬ p4328) ∨ (¬ p4428) := by
  classical
  tauto

theorem initial21886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3745) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4428)) := by
  have source := ElevenTheory.theory11142 (m.theta 2 6) (m.theta 3 6) (m.theta 5 6)
  exact rule21886 (meaning t m 3745) (meaning t m 4328) (meaning t m 4428) source

theorem rule21887 (p2577 p2655 p3983 : Prop) (h : (¬ p2577) ∨ (¬ p2655) ∨ p3983) : (¬ p2577) ∨ (¬ p2655) ∨ (p3983) := by
  classical
  tauto

theorem initial21887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2655)) ∨ (meaning t m 3983) := by
  have source := ElevenTheory.theory11143 (m.theta 0 3) (m.theta 0 4) (m.theta 0 6)
  exact rule21887 (meaning t m 2577) (meaning t m 2655) (meaning t m 3983) source

theorem rule21888 (p2001 p2027 p2156 p2166 p2542 p2545 p4109 p4173 : Prop) (h : (¬ p2001) ∨ (¬ p2156) ∨ p2545 ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p4173) ∨ (¬ p2542)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2166) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p4109) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial21888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory11144 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule21888 (meaning t m 2001) (meaning t m 2027) (meaning t m 2156) (meaning t m 2166) (meaning t m 2542) (meaning t m 2545) (meaning t m 4109) (meaning t m 4173) source

theorem rule21890 (p1975 p2027 p2230 p2274 p2764 p3172 p3362 p3660 p3888 p4118 p4393 p4444 p4789 : Prop) (h : (¬ p3362) ∨ (¬ p3888) ∨ (¬ p2230) ∨ (¬ p3172) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2764 ∨ (¬ p4789) ∨ (¬ p4444) ∨ (¬ p4118) ∨ (¬ p4393) ∨ (¬ p3660)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (p2764) ∨ (¬ p3172) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4118) ∨ (¬ p4393) ∨ (¬ p4444) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial21890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory11146 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7) (m.theta 8 9) (m.theta 9 10)
  exact rule21890 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2764) (meaning t m 3172) (meaning t m 3362) (meaning t m 3660) (meaning t m 3888) (meaning t m 4118) (meaning t m 4393) (meaning t m 4444) (meaning t m 4789) source

theorem rule21893 (p2315 p4275 p4986 : Prop) (h : (¬ p2315) ∨ (¬ p4275) ∨ p4986) : (¬ p2315) ∨ (¬ p4275) ∨ (p4986) := by
  classical
  tauto

theorem initial21893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 4275)) ∨ (meaning t m 4986) := by
  have source := ElevenTheory.theory11149 t (m.theta 0 7) (m.theta 5 7) (m.theta 6 7)
  exact rule21893 (meaning t m 2315) (meaning t m 4275) (meaning t m 4986) source

theorem rule21894 (p2246 p2996 p3414 : Prop) (h : (¬ p2996) ∨ (¬ p2246) ∨ p3414) : (¬ p2246) ∨ (¬ p2996) ∨ (p3414) := by
  classical
  tauto

theorem initial21894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 3414) := by
  have source := ElevenTheory.theory11150 (m.theta 0 3) (m.theta 1 3) (m.theta 3 7)
  exact rule21894 (meaning t m 2246) (meaning t m 2996) (meaning t m 3414) source

theorem rule21896 (p2027 p2210 p2254 p2891 p2963 p3246 p3324 p3950 p4347 : Prop) (h : (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3950) ∨ (¬ p2891) ∨ (¬ p3324) ∨ (¬ p3246) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3950) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory11152 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21896 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2891) (meaning t m 2963) (meaning t m 3246) (meaning t m 3324) (meaning t m 3950) (meaning t m 4347) source

theorem rule21897 (p2027 p2507 p3591 p3830 p4137 p5152 : Prop) (h : (¬ p3591) ∨ (¬ p4137) ∨ (¬ p5152) ∨ (¬ p3830) ∨ (¬ p2507) ∨ p2027) : (p2027) ∨ (¬ p2507) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4137) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial21897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory11153 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 4 6) (m.theta 6 9)
  exact rule21897 (meaning t m 2027) (meaning t m 2507) (meaning t m 3591) (meaning t m 3830) (meaning t m 4137) (meaning t m 5152) source

theorem rule21898 (p2027 p2210 p2254 p2797 p2881 p2891 p2963 p3877 p4041 : Prop) (h : (¬ p2254) ∨ (¬ p2891) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2797) ∨ (¬ p2210) ∨ (¬ p3877) ∨ (¬ p4041)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2797) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p2963) ∨ (¬ p3877) ∨ (¬ p4041) := by
  classical
  tauto

theorem initial21898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) := by
  have source := ElevenTheory.theory11154 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule21898 (meaning t m 2027) (meaning t m 2210) (meaning t m 2254) (meaning t m 2797) (meaning t m 2881) (meaning t m 2891) (meaning t m 2963) (meaning t m 3877) (meaning t m 4041) source

theorem rule21899 (p2027 p2146 p2156 p2274 p3822 p4193 : Prop) (h : (¬ p2156) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p2146)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p3822) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial21899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory11155 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7)
  exact rule21899 (meaning t m 2027) (meaning t m 2146) (meaning t m 2156) (meaning t m 2274) (meaning t m 3822) (meaning t m 4193) source

theorem rule21900 (p2027 p2191 p2192 p2274 p4501 p4506 : Prop) (h : (¬ p4501) ∨ (¬ p2274) ∨ (¬ p4506) ∨ (¬ p2191) ∨ (¬ p2192) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p4501) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial21900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory11156 t (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21900 (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2274) (meaning t m 4501) (meaning t m 4506) source

theorem rule21901 (p2027 p2166 p2241 p3369 p4120 p4448 : Prop) (h : p2027 ∨ (¬ p2241) ∨ (¬ p4448) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p2166)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2241) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p4448) := by
  classical
  tauto

theorem initial21901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4448)) := by
  have source := ElevenTheory.theory11157 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 5 8)
  exact rule21901 (meaning t m 2027) (meaning t m 2166) (meaning t m 2241) (meaning t m 3369) (meaning t m 4120) (meaning t m 4448) source

theorem rule21902 (p2027 p2264 p2299 p2313 p4156 p4581 : Prop) (h : (¬ p2299) ∨ (¬ p2264) ∨ (¬ p2313) ∨ (¬ p4156) ∨ (¬ p4581) ∨ p2027) : (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p4156) ∨ (¬ p4581) := by
  classical
  tauto

theorem initial21902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4581)) := by
  have source := ElevenTheory.theory11158 t (m.theta 0 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule21902 (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 2313) (meaning t m 4156) (meaning t m 4581) source

theorem rule21903 (p2027 p2299 p2319 p2341 p3097 p4489 : Prop) (h : p2027 ∨ (¬ p4489) ∨ (¬ p3097) ∨ (¬ p2341) ∨ (¬ p2299) ∨ (¬ p2319)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3097) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial21903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory11159 t (m.theta 0 6) (m.theta 0 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule21903 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 3097) (meaning t m 4489) source

theorem rule21904 (p2027 p2383 p2563 p3880 p4489 p4506 : Prop) (h : (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4489) ∨ p2027 ∨ (¬ p4506)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4489) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial21904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4489)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory11160 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule21904 (meaning t m 2027) (meaning t m 2383) (meaning t m 2563) (meaning t m 3880) (meaning t m 4489) (meaning t m 4506) source

theorem rule21905 (p1998 p2462 p4348 p4669 : Prop) (h : (¬ p1998) ∨ p4669 ∨ (¬ p4348) ∨ p2462) : (¬ p1998) ∨ (p2462) ∨ (¬ p4348) ∨ (p4669) := by
  classical
  tauto

theorem initial21905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 4348)) ∨ (meaning t m 4669) := by
  have source := ElevenTheory.theory11161 t (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule21905 (meaning t m 1998) (meaning t m 2462) (meaning t m 4348) (meaning t m 4669) source

theorem rule21906 (p2027 p2476 p2553 p2573 p4432 p4501 : Prop) (h : p2027 ∨ (¬ p4501) ∨ (¬ p4432) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p4432) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial21906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11162 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21906 (meaning t m 2027) (meaning t m 2476) (meaning t m 2553) (meaning t m 2573) (meaning t m 4432) (meaning t m 4501) source

theorem rule21907 (p2027 p2220 p2542 p3054 p3694 p4109 p4750 : Prop) (h : (¬ p4750) ∨ (¬ p2542) ∨ (¬ p3054) ∨ (¬ p4109) ∨ (¬ p2220) ∨ (¬ p3694) ∨ p2027) : (p2027) ∨ (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3054) ∨ (¬ p3694) ∨ (¬ p4109) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial21907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11163 t (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8)
  exact rule21907 (meaning t m 2027) (meaning t m 2220) (meaning t m 2542) (meaning t m 3054) (meaning t m 3694) (meaning t m 4109) (meaning t m 4750) source

theorem rule21908 (p2027 p2177 p2459 p3692 p4119 p4556 : Prop) (h : (¬ p4119) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial21908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory11164 t (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21908 (meaning t m 2027) (meaning t m 2177) (meaning t m 2459) (meaning t m 3692) (meaning t m 4119) (meaning t m 4556) source

theorem rule21909 (p2027 p2144 p2156 p3583 p3758 p4737 : Prop) (h : (¬ p2144) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p2156) ∨ (¬ p4737) ∨ p2027) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3583) ∨ (¬ p3758) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial21909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11165 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6)
  exact rule21909 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 3583) (meaning t m 3758) (meaning t m 4737) source

theorem rule21910 (p2027 p2563 p2839 p3688 p4428 p4882 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4882) ∨ (¬ p2839) ∨ (¬ p4428) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2839) ∨ (¬ p3688) ∨ (¬ p4428) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial21910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11166 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 6)
  exact rule21910 (meaning t m 2027) (meaning t m 2563) (meaning t m 2839) (meaning t m 3688) (meaning t m 4428) (meaning t m 4882) source

theorem rule21911 (p2027 p2144 p3051 p3583 p4244 p4737 : Prop) (h : (¬ p4737) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p3051) ∨ (¬ p2144)) : (p2027) ∨ (¬ p2144) ∨ (¬ p3051) ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial21911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11167 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7)
  exact rule21911 (meaning t m 2027) (meaning t m 2144) (meaning t m 3051) (meaning t m 3583) (meaning t m 4244) (meaning t m 4737) source

theorem rule21912 (p2027 p2881 p2891 p3659 p4136 p4878 : Prop) (h : (¬ p2891) ∨ p2027 ∨ (¬ p4136) ∨ (¬ p4878) ∨ (¬ p2881) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial21912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory11168 t (m.theta 1 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule21912 (meaning t m 2027) (meaning t m 2881) (meaning t m 2891) (meaning t m 3659) (meaning t m 4136) (meaning t m 4878) source

theorem rule21913 (p2027 p2284 p3359 p3413 p4110 p4949 : Prop) (h : (¬ p4110) ∨ (¬ p3413) ∨ (¬ p3359) ∨ (¬ p4949) ∨ (¬ p2284) ∨ p2027) : (p2027) ∨ (¬ p2284) ∨ (¬ p3359) ∨ (¬ p3413) ∨ (¬ p4110) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial21913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory11169 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule21913 (meaning t m 2027) (meaning t m 2284) (meaning t m 3359) (meaning t m 3413) (meaning t m 4110) (meaning t m 4949) source

theorem rule21916 (p2027 p2253 p2750 p2946 p3662 p3954 : Prop) (h : p2027 ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial21916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory11172 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5)
  exact rule21916 (meaning t m 2027) (meaning t m 2253) (meaning t m 2750) (meaning t m 2946) (meaning t m 3662) (meaning t m 3954) source

theorem rule21917 (p2027 p2542 p2651 p2963 p4389 p4715 : Prop) (h : (¬ p2651) ∨ (¬ p2542) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p4389)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (¬ p4389) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial21917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory11173 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule21917 (meaning t m 2027) (meaning t m 2542) (meaning t m 2651) (meaning t m 2963) (meaning t m 4389) (meaning t m 4715) source

theorem rule21920 (p2027 p2946 p2963 p3115 p3745 p5046 : Prop) (h : (¬ p3115) ∨ (¬ p3745) ∨ (¬ p2963) ∨ (¬ p2946) ∨ (¬ p5046) ∨ p2027) : (p2027) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3115) ∨ (¬ p3745) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial21920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11176 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9)
  exact rule21920 (meaning t m 2027) (meaning t m 2946) (meaning t m 2963) (meaning t m 3115) (meaning t m 3745) (meaning t m 5046) source

theorem rule21921 (p2027 p2253 p2946 p3365 p4315 p4736 : Prop) (h : (¬ p2946) ∨ (¬ p4736) ∨ (¬ p2253) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p3365) ∨ (¬ p4315) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial21921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11177 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5)
  exact rule21921 (meaning t m 2027) (meaning t m 2253) (meaning t m 2946) (meaning t m 3365) (meaning t m 4315) (meaning t m 4736) source

theorem rule21922 (p2027 p2630 p2696 p2741 p4111 p4737 : Prop) (h : p2027 ∨ (¬ p4737) ∨ (¬ p2741) ∨ (¬ p2696) ∨ (¬ p4111) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial21922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11178 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule21922 (meaning t m 2027) (meaning t m 2630) (meaning t m 2696) (meaning t m 2741) (meaning t m 4111) (meaning t m 4737) source

theorem rule21924 (p2027 p2299 p2528 p3875 p4348 p4712 : Prop) (h : (¬ p2299) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p3875) ∨ (¬ p2528) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2528) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial21924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11180 t (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule21924 (meaning t m 2027) (meaning t m 2299) (meaning t m 2528) (meaning t m 3875) (meaning t m 4348) (meaning t m 4712) source

theorem rule21925 (p2027 p2138 p3212 p4172 p4385 p4736 : Prop) (h : (¬ p2138) ∨ (¬ p3212) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p4172) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3212) ∨ (¬ p4172) ∨ (¬ p4385) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial21925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11181 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 5 9)
  exact rule21925 (meaning t m 2027) (meaning t m 2138) (meaning t m 3212) (meaning t m 4172) (meaning t m 4385) (meaning t m 4736) source

theorem rule21926 (p2027 p3222 p3238 p4110 p4952 p5046 : Prop) (h : (¬ p3238) ∨ (¬ p4110) ∨ (¬ p5046) ∨ p2027 ∨ (¬ p3222) ∨ (¬ p4952)) : (p2027) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p4110) ∨ (¬ p4952) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial21926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4952)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11182 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9)
  exact rule21926 (meaning t m 2027) (meaning t m 3222) (meaning t m 3238) (meaning t m 4110) (meaning t m 4952) (meaning t m 5046) source

theorem rule21927 (p2027 p2651 p3170 p3256 p3857 p5008 : Prop) (h : (¬ p2651) ∨ (¬ p5008) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p3170)) : (p2027) ∨ (¬ p2651) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial21927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11183 t (m.theta 0 3) (m.theta 0 8) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule21927 (meaning t m 2027) (meaning t m 2651) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) (meaning t m 5008) source

theorem rule21930 (p2027 p2088 p2110 p2476 p2534 p4729 : Prop) (h : (¬ p2476) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2110) ∨ (¬ p2088) ∨ (¬ p4729)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2110) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial21930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2110)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory11186 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 8) (m.theta 4 8) (m.theta 8 9)
  exact rule21930 (meaning t m 2027) (meaning t m 2088) (meaning t m 2110) (meaning t m 2476) (meaning t m 2534) (meaning t m 4729) source

theorem rule21931 (p2027 p2138 p2651 p2810 p4117 p5049 : Prop) (h : (¬ p2810) ∨ (¬ p5049) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial21931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory11187 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4)
  exact rule21931 (meaning t m 2027) (meaning t m 2138) (meaning t m 2651) (meaning t m 2810) (meaning t m 4117) (meaning t m 5049) source

theorem rule21932 (p1986 p2545 p2810 p4752 : Prop) (h : p4752 ∨ p2545 ∨ (¬ p1986) ∨ (¬ p2810)) : (¬ p1986) ∨ (p2545) ∨ (¬ p2810) ∨ (p4752) := by
  classical
  tauto

theorem initial21932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 4752) := by
  have source := ElevenTheory.theory11188 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule21932 (meaning t m 1986) (meaning t m 2545) (meaning t m 2810) (meaning t m 4752) source

theorem rule21933 (p2027 p2598 p2748 p3365 p3662 p3683 p4701 : Prop) (h : p2027 ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p2748) ∨ (¬ p2598) ∨ (¬ p4701) ∨ (¬ p3683)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p3683) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial21933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11189 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5)
  exact rule21933 (meaning t m 2027) (meaning t m 2598) (meaning t m 2748) (meaning t m 3365) (meaning t m 3662) (meaning t m 3683) (meaning t m 4701) source

theorem rule21934 (p2210 p2245 p2946 p4282 : Prop) (h : (¬ p2210) ∨ (¬ p2245) ∨ (¬ p4282) ∨ p2946) : (¬ p2210) ∨ (¬ p2245) ∨ (p2946) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial21934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2245)) ∨ (meaning t m 2946) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory11190 (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 5)
  exact rule21934 (meaning t m 2210) (meaning t m 2245) (meaning t m 2946) (meaning t m 4282) source

theorem rule21936 (p2027 p2743 p3379 p3954 p4030 p4752 : Prop) (h : (¬ p2743) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4030) ∨ (¬ p3954) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial21936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory11192 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4)
  exact rule21936 (meaning t m 2027) (meaning t m 2743) (meaning t m 3379) (meaning t m 3954) (meaning t m 4030) (meaning t m 4752) source

theorem rule21937 (p2027 p2417 p2761 p4025 p4191 p4712 : Prop) (h : (¬ p4025) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p2761) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial21937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11193 t (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule21937 (meaning t m 2027) (meaning t m 2417) (meaning t m 2761) (meaning t m 4025) (meaning t m 4191) (meaning t m 4712) source

theorem rule21938 (p2027 p2341 p2928 p3644 p5194 p5201 : Prop) (h : p2027 ∨ (¬ p5194) ∨ (¬ p2928) ∨ (¬ p5201) ∨ (¬ p2341) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2928) ∨ (¬ p3644) ∨ (¬ p5194) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial21938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 5194)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory11194 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8)
  exact rule21938 (meaning t m 2027) (meaning t m 2341) (meaning t m 2928) (meaning t m 3644) (meaning t m 5194) (meaning t m 5201) source

theorem rule21939 (p2027 p2901 p2992 p3745 p4154 p4558 : Prop) (h : (¬ p2992) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p4558) ∨ (¬ p2901) ∨ (¬ p3745)) : (p2027) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial21939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11195 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule21939 (meaning t m 2027) (meaning t m 2901) (meaning t m 2992) (meaning t m 3745) (meaning t m 4154) (meaning t m 4558) source

theorem rule21941 (p2027 p2341 p3570 p4235 p4539 p4988 : Prop) (h : (¬ p4539) ∨ (¬ p4988) ∨ (¬ p4235) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4539) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial21941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4539)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory11197 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule21941 (meaning t m 2027) (meaning t m 2341) (meaning t m 3570) (meaning t m 4235) (meaning t m 4539) (meaning t m 4988) source

theorem rule21942 (p2027 p2299 p2319 p2341 p3568 p4584 : Prop) (h : (¬ p4584) ∨ p2027 ∨ (¬ p2319) ∨ (¬ p2299) ∨ (¬ p3568) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3568) ∨ (¬ p4584) := by
  classical
  tauto

theorem initial21942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4584)) := by
  have source := ElevenTheory.theory11198 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule21942 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 3568) (meaning t m 4584) source

theorem rule21943 (p2027 p2437 p2598 p3425 p4106 p4750 : Prop) (h : (¬ p3425) ∨ (¬ p4750) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p4106) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2598) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial21943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11199 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7)
  exact rule21943 (meaning t m 2027) (meaning t m 2437) (meaning t m 2598) (meaning t m 3425) (meaning t m 4106) (meaning t m 4750) source

theorem rule21944 (p2027 p2132 p2247 p2860 p3125 p4118 p4330 p4360 p4733 : Prop) (h : (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4330) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2132) ∨ (¬ p3125) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4360) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial21944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11200 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule21944 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2860) (meaning t m 3125) (meaning t m 4118) (meaning t m 4330) (meaning t m 4360) (meaning t m 4733) source

theorem rule21945 (p2027 p2630 p2748 p3256 p4261 p4262 p5008 : Prop) (h : (¬ p4262) ∨ (¬ p2748) ∨ (¬ p3256) ∨ (¬ p5008) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p4261)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p3256) ∨ (¬ p4261) ∨ (¬ p4262) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial21945 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11201 t (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule21945 (meaning t m 2027) (meaning t m 2630) (meaning t m 2748) (meaning t m 3256) (meaning t m 4261) (meaning t m 4262) (meaning t m 5008) source

theorem rule21946 (p2027 p2156 p2630 p3370 p3412 p3758 p4392 p4701 : Prop) (h : (¬ p2156) ∨ (¬ p2630) ∨ (¬ p3370) ∨ (¬ p4392) ∨ (¬ p4701) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p3412)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2630) ∨ (¬ p3370) ∨ (¬ p3412) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial21946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11202 t (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule21946 (meaning t m 2027) (meaning t m 2156) (meaning t m 2630) (meaning t m 3370) (meaning t m 3412) (meaning t m 3758) (meaning t m 4392) (meaning t m 4701) source

theorem rule21949 (p2027 p2255 p2542 p2651 p3238 p3402 : Prop) (h : (¬ p2542) ∨ p2027 ∨ (¬ p3402) ∨ (¬ p2651) ∨ (¬ p3238) ∨ (¬ p2255)) : (p2027) ∨ (¬ p2255) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3238) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial21949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory11205 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule21949 (meaning t m 2027) (meaning t m 2255) (meaning t m 2542) (meaning t m 2651) (meaning t m 3238) (meaning t m 3402) source

theorem rule21950 (p2027 p2132 p2860 p2928 p3125 p3452 p4278 p4621 p4733 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4621) ∨ (¬ p3125) ∨ (¬ p4733) ∨ (¬ p4278) ∨ (¬ p2860)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p2928) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial21950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11206 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule21950 (meaning t m 2027) (meaning t m 2132) (meaning t m 2860) (meaning t m 2928) (meaning t m 3125) (meaning t m 3452) (meaning t m 4278) (meaning t m 4621) (meaning t m 4733) source

theorem rule21951 (p2027 p2284 p2651 p2950 p3646 p4701 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p3646) ∨ (¬ p2950) ∨ (¬ p2284) ∨ (¬ p4701)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2651) ∨ (¬ p2950) ∨ (¬ p3646) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial21951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11207 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule21951 (meaning t m 2027) (meaning t m 2284) (meaning t m 2651) (meaning t m 2950) (meaning t m 3646) (meaning t m 4701) source

theorem rule21952 (p2027 p2651 p2922 p3414 p3740 p4814 : Prop) (h : (¬ p2651) ∨ (¬ p4814) ∨ (¬ p2922) ∨ (¬ p3414) ∨ (¬ p3740) ∨ p2027) : (p2027) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial21952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory11208 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule21952 (meaning t m 2027) (meaning t m 2651) (meaning t m 2922) (meaning t m 3414) (meaning t m 3740) (meaning t m 4814) source

theorem rule21953 (p2027 p2274 p2284 p3497 p4501 p4506 : Prop) (h : (¬ p4506) ∨ (¬ p2284) ∨ (¬ p4501) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p4501) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial21953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory11209 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21953 (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 3497) (meaning t m 4501) (meaning t m 4506) source

theorem rule21954 (p2027 p3286 p3414 p3740 p4107 p4660 p4712 : Prop) (h : (¬ p4107) ∨ (¬ p3740) ∨ (¬ p3414) ∨ (¬ p3286) ∨ (¬ p4660) ∨ p2027 ∨ (¬ p4712)) : (p2027) ∨ (¬ p3286) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4107) ∨ (¬ p4660) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial21954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4660)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11210 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule21954 (meaning t m 2027) (meaning t m 3286) (meaning t m 3414) (meaning t m 3740) (meaning t m 4107) (meaning t m 4660) (meaning t m 4712) source

theorem rule21955 (p2027 p2274 p2417 p3744 p4396 p4712 : Prop) (h : (¬ p2274) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p4396) ∨ (¬ p4712)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2417) ∨ (¬ p3744) ∨ (¬ p4396) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial21955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11211 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule21955 (meaning t m 2027) (meaning t m 2274) (meaning t m 2417) (meaning t m 3744) (meaning t m 4396) (meaning t m 4712) source

theorem rule21956 (p2027 p2299 p2518 p2928 p4404 p4712 : Prop) (h : (¬ p4404) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4712) ∨ (¬ p2518) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4404) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial21956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11212 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule21956 (meaning t m 2027) (meaning t m 2299) (meaning t m 2518) (meaning t m 2928) (meaning t m 4404) (meaning t m 4712) source

theorem rule21957 (p2027 p2247 p2751 p2810 p3379 p3487 : Prop) (h : (¬ p2810) ∨ (¬ p2751) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3487)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p3379) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial21957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory11213 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4)
  exact rule21957 (meaning t m 2027) (meaning t m 2247) (meaning t m 2751) (meaning t m 2810) (meaning t m 3379) (meaning t m 3487) source

theorem rule21958 (p2027 p2122 p2829 p4242 p4501 p4857 : Prop) (h : (¬ p4857) ∨ (¬ p4242) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p4501)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2829) ∨ (¬ p4242) ∨ (¬ p4501) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial21958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory11214 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8)
  exact rule21958 (meaning t m 2027) (meaning t m 2122) (meaning t m 2829) (meaning t m 4242) (meaning t m 4501) (meaning t m 4857) source

theorem rule21959 (p2027 p2685 p2737 p3414 p4236 p4734 : Prop) (h : (¬ p2737) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p4236)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p3414) ∨ (¬ p4236) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial21959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11215 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7)
  exact rule21959 (meaning t m 2027) (meaning t m 2685) (meaning t m 2737) (meaning t m 3414) (meaning t m 4236) (meaning t m 4734) source

theorem rule21960 (p2027 p2146 p2319 p2341 p2962 p3570 p4244 : Prop) (h : (¬ p2962) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p2319) ∨ (¬ p3570) ∨ (¬ p2341) ∨ (¬ p2146)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2962) ∨ (¬ p3570) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial21960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory11216 t (m.theta 0 5) (m.theta 0 6) (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule21960 (meaning t m 2027) (meaning t m 2146) (meaning t m 2319) (meaning t m 2341) (meaning t m 2962) (meaning t m 3570) (meaning t m 4244) source

theorem rule21961 (p2027 p2341 p2926 p3365 p3548 p3819 p4030 p4752 : Prop) (h : (¬ p3819) ∨ (¬ p4030) ∨ (¬ p2926) ∨ (¬ p4752) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2926) ∨ (¬ p3365) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p4030) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial21961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory11217 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 7 8)
  exact rule21961 (meaning t m 2027) (meaning t m 2341) (meaning t m 2926) (meaning t m 3365) (meaning t m 3548) (meaning t m 3819) (meaning t m 4030) (meaning t m 4752) source

theorem rule21963 (p2027 p2341 p3545 p3548 p3954 p4796 : Prop) (h : (¬ p2341) ∨ (¬ p3548) ∨ (¬ p4796) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3545)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p3954) ∨ (¬ p4796) := by
  classical
  tauto

theorem initial21963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4796)) := by
  have source := ElevenTheory.theory11219 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 7 8)
  exact rule21963 (meaning t m 2027) (meaning t m 2341) (meaning t m 3545) (meaning t m 3548) (meaning t m 3954) (meaning t m 4796) source

theorem rule21967 (p2027 p2187 p2459 p3744 p4133 p4171 : Prop) (h : p2027 ∨ (¬ p4133) ∨ (¬ p2187) ∨ (¬ p3744) ∨ (¬ p2459) ∨ (¬ p4171)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p3744) ∨ (¬ p4133) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial21967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory11223 t (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule21967 (meaning t m 2027) (meaning t m 2187) (meaning t m 2459) (meaning t m 3744) (meaning t m 4133) (meaning t m 4171) source

theorem rule21968 (p2027 p2588 p3246 p3872 p3958 p4107 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p3958) ∨ (¬ p4107) ∨ (¬ p3246) ∨ (¬ p3872)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3246) ∨ (¬ p3872) ∨ (¬ p3958) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial21968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory11224 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule21968 (meaning t m 2027) (meaning t m 2588) (meaning t m 3246) (meaning t m 3872) (meaning t m 3958) (meaning t m 4107) source

theorem rule21969 (p2005 p2202 p2563 p3958 : Prop) (h : p2202 ∨ p3958 ∨ (¬ p2005) ∨ (¬ p2563)) : (¬ p2005) ∨ (p2202) ∨ (¬ p2563) ∨ (p3958) := by
  classical
  tauto

theorem initial21969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3958) := by
  have source := ElevenTheory.theory11225 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule21969 (meaning t m 2005) (meaning t m 2202) (meaning t m 2563) (meaning t m 3958) source

theorem rule21970 (p2027 p2230 p3055 p3684 p4079 p4736 : Prop) (h : p2027 ∨ (¬ p4736) ∨ (¬ p3684) ∨ (¬ p3055) ∨ (¬ p4079) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4079) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial21970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11226 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5)
  exact rule21970 (meaning t m 2027) (meaning t m 2230) (meaning t m 3055) (meaning t m 3684) (meaning t m 4079) (meaning t m 4736) source

theorem rule21973 (p2331 p2811 p4195 : Prop) (h : (¬ p2811) ∨ (¬ p2331) ∨ (¬ p4195)) : (¬ p2331) ∨ (¬ p2811) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial21973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory11229 (m.theta 0 3) (m.theta 2 3) (m.theta 3 6)
  exact rule21973 (meaning t m 2331) (meaning t m 2811) (meaning t m 4195) source

theorem rule21975 (p2341 p2470 p4383 p5201 : Prop) (h : (¬ p4383) ∨ (¬ p5201) ∨ (¬ p2341) ∨ p2470) : (¬ p2341) ∨ (p2470) ∨ (¬ p4383) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial21975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (meaning t m 2470) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory11231 (m.theta 0 4) (m.theta 0 7) (m.theta 4 8) (m.theta 7 8)
  exact rule21975 (meaning t m 2341) (meaning t m 2470) (meaning t m 4383) (meaning t m 5201) source

theorem rule21979 (p2027 p2499 p2573 p2922 p2952 p3136 p3572 p4079 p4236 p4653 p4736 : Prop) (h : (¬ p2499) ∨ (¬ p4736) ∨ (¬ p2922) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4236) ∨ (¬ p3136) ∨ (¬ p4653) ∨ (¬ p4079) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3572) ∨ (¬ p4079) ∨ (¬ p4236) ∨ (¬ p4653) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial21979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4653)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11235 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule21979 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2922) (meaning t m 2952) (meaning t m 3136) (meaning t m 3572) (meaning t m 4079) (meaning t m 4236) (meaning t m 4653) (meaning t m 4736) source

theorem rule21980 (p2027 p2298 p2307 p2641 p2996 p4584 : Prop) (h : (¬ p2298) ∨ (¬ p4584) ∨ (¬ p2996) ∨ (¬ p2641) ∨ (¬ p2307) ∨ p2027) : (p2027) ∨ (¬ p2298) ∨ (¬ p2307) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p4584) := by
  classical
  tauto

theorem initial21980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 4584)) := by
  have source := ElevenTheory.theory11236 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule21980 (meaning t m 2027) (meaning t m 2298) (meaning t m 2307) (meaning t m 2641) (meaning t m 2996) (meaning t m 4584) source

theorem rule21982 (p2027 p2499 p2598 p3422 p4257 p4737 : Prop) (h : p2027 ∨ (¬ p2499) ∨ (¬ p3422) ∨ (¬ p4737) ∨ (¬ p2598) ∨ (¬ p4257)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p4257) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial21982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11238 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule21982 (meaning t m 2027) (meaning t m 2499) (meaning t m 2598) (meaning t m 3422) (meaning t m 4257) (meaning t m 4737) source

theorem rule21983 (p2027 p2598 p2608 p3452 p3590 p4737 : Prop) (h : (¬ p4737) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p3452) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial21983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11239 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule21983 (meaning t m 2027) (meaning t m 2598) (meaning t m 2608) (meaning t m 3452) (meaning t m 3590) (meaning t m 4737) source

theorem rule21984 (p2027 p2657 p2743 p2839 p3361 p4704 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p3361) ∨ (¬ p2839) ∨ (¬ p4704) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2743)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3361) ∨ (¬ p4704) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial21984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory11240 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule21984 (meaning t m 2027) (meaning t m 2657) (meaning t m 2743) (meaning t m 2839) (meaning t m 3361) (meaning t m 4704) (meaning t m 5051) source

theorem rule21985 (p2027 p2132 p2870 p3486 p4737 p4874 : Prop) (h : p2027 ∨ (¬ p4874) ∨ (¬ p3486) ∨ (¬ p2132) ∨ (¬ p4737) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3486) ∨ (¬ p4737) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial21985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory11241 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule21985 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 3486) (meaning t m 4737) (meaning t m 4874) source

theorem rule21987 (p2027 p2230 p3238 p3954 p4079 p5216 : Prop) (h : (¬ p3954) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2230) ∨ (¬ p4079) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial21987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory11243 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5)
  exact rule21987 (meaning t m 2027) (meaning t m 2230) (meaning t m 3238) (meaning t m 3954) (meaning t m 4079) (meaning t m 5216) source

theorem rule21989 (p2027 p2573 p2589 p3758 p4203 p4882 : Prop) (h : p2027 ∨ (¬ p4203) ∨ (¬ p4882) ∨ (¬ p3758) ∨ (¬ p2589) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3758) ∨ (¬ p4203) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial21989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11245 t (m.theta 0 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule21989 (meaning t m 2027) (meaning t m 2573) (meaning t m 2589) (meaning t m 3758) (meaning t m 4203) (meaning t m 4882) source

theorem rule21991 (p2027 p2807 p2963 p3549 p3552 p4024 p4843 : Prop) (h : (¬ p4024) ∨ p2027 ∨ (¬ p4843) ∨ (¬ p2807) ∨ (¬ p3549) ∨ (¬ p2963) ∨ (¬ p3552)) : (p2027) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3552) ∨ (¬ p4024) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial21991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory11247 t (m.theta 0 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule21991 (meaning t m 2027) (meaning t m 2807) (meaning t m 2963) (meaning t m 3549) (meaning t m 3552) (meaning t m 4024) (meaning t m 4843) source

theorem rule21994 (p1998 p2027 p2254 p2598 p2707 p2717 p2766 p2963 p3324 p3585 p3589 p4347 : Prop) (h : (¬ p1998) ∨ (¬ p3589) ∨ (¬ p2717) ∨ (¬ p3585) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2254) ∨ p2766 ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3324) ∨ (¬ p2963)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (p2766) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial21994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory11250 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule21994 (meaning t m 1998) (meaning t m 2027) (meaning t m 2254) (meaning t m 2598) (meaning t m 2707) (meaning t m 2717) (meaning t m 2766) (meaning t m 2963) (meaning t m 3324) (meaning t m 3585) (meaning t m 3589) (meaning t m 4347) source

theorem rule21998 (p2027 p2284 p3413 p3742 p4110 p4644 : Prop) (h : (¬ p2284) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4644) ∨ (¬ p3413)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3413) ∨ (¬ p3742) ∨ (¬ p4110) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial21998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory11254 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule21998 (meaning t m 2027) (meaning t m 2284) (meaning t m 3413) (meaning t m 3742) (meaning t m 4110) (meaning t m 4644) source

theorem rule21999 (p2027 p2598 p3452 p3585 p3589 p4376 : Prop) (h : (¬ p3589) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2598) ∨ (¬ p4376) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3452) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial21999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory11255 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule21999 (meaning t m 2027) (meaning t m 2598) (meaning t m 3452) (meaning t m 3585) (meaning t m 3589) (meaning t m 4376) source

theorem rule22001 (p2027 p2341 p3588 p3659 p3819 p4737 : Prop) (h : (¬ p3819) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p2341) ∨ (¬ p3659) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3819) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11257 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 7 8)
  exact rule22001 (meaning t m 2027) (meaning t m 2341) (meaning t m 3588) (meaning t m 3659) (meaning t m 3819) (meaning t m 4737) source

theorem rule22002 (p2027 p2437 p2911 p3659 p3686 p4750 : Prop) (h : p2027 ∨ (¬ p4750) ∨ (¬ p3659) ∨ (¬ p2911) ∨ (¬ p2437) ∨ (¬ p3686)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11258 t (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule22002 (meaning t m 2027) (meaning t m 2437) (meaning t m 2911) (meaning t m 3659) (meaning t m 3686) (meaning t m 4750) source

theorem rule22003 (p2027 p2922 p3238 p3569 p4244 p4882 : Prop) (h : p2027 ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p4244) ∨ (¬ p3569) ∨ (¬ p4882)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p4244) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial22003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory11259 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule22003 (meaning t m 2027) (meaning t m 2922) (meaning t m 3238) (meaning t m 3569) (meaning t m 4244) (meaning t m 4882) source

theorem rule22004 (p2027 p2254 p2608 p2829 p2952 p3483 p3690 p4320 p4621 : Prop) (h : (¬ p2254) ∨ (¬ p4320) ∨ (¬ p2829) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3483) ∨ (¬ p2952) ∨ (¬ p3690) ∨ (¬ p4621)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3483) ∨ (¬ p3690) ∨ (¬ p4320) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial22004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory11260 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule22004 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2829) (meaning t m 2952) (meaning t m 3483) (meaning t m 3690) (meaning t m 4320) (meaning t m 4621) source

theorem rule22005 (p2027 p3189 p3662 p3952 p4311 p4509 : Prop) (h : (¬ p4509) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p3662) ∨ (¬ p4311) ∨ (¬ p3189)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4311) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial22005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4311)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory11261 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8)
  exact rule22005 (meaning t m 2027) (meaning t m 3189) (meaning t m 3662) (meaning t m 3952) (meaning t m 4311) (meaning t m 4509) source

theorem rule22006 (p2027 p2651 p2737 p3585 p4343 p4790 : Prop) (h : (¬ p4343) ∨ (¬ p2651) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p4790) ∨ (¬ p2737)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial22006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory11262 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule22006 (meaning t m 2027) (meaning t m 2651) (meaning t m 2737) (meaning t m 3585) (meaning t m 4343) (meaning t m 4790) source

theorem rule22007 (p2027 p2341 p3540 p3644 p4172 p4988 p5193 : Prop) (h : (¬ p3644) ∨ (¬ p4172) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p2341) ∨ (¬ p4988)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4172) ∨ (¬ p4988) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial22007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4988)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory11263 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule22007 (meaning t m 2027) (meaning t m 2341) (meaning t m 3540) (meaning t m 3644) (meaning t m 4172) (meaning t m 4988) (meaning t m 5193) source

theorem rule22010 (p2011 p2148 p3212 p4138 p4503 : Prop) (h : (¬ p3212) ∨ p2148 ∨ (¬ p2011) ∨ (¬ p4138) ∨ p4503) : (¬ p2011) ∨ (p2148) ∨ (¬ p3212) ∨ (¬ p4138) ∨ (p4503) := by
  classical
  tauto

theorem initial22010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4138)) ∨ (meaning t m 4503) := by
  have source := ElevenTheory.theory11266 t (m.theta 0 5) (m.theta 5 9) (m.theta 6 8) (m.theta 7 8)
  exact rule22010 (meaning t m 2011) (meaning t m 2148) (meaning t m 3212) (meaning t m 4138) (meaning t m 4503) source

theorem rule22011 (p2027 p2749 p3189 p3583 p3877 p5049 : Prop) (h : (¬ p3189) ∨ (¬ p2749) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p3583) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2749) ∨ (¬ p3189) ∨ (¬ p3583) ∨ (¬ p3877) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial22011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory11267 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 8)
  exact rule22011 (meaning t m 2027) (meaning t m 2749) (meaning t m 3189) (meaning t m 3583) (meaning t m 3877) (meaning t m 5049) source

theorem rule22012 (p2027 p3362 p3389 p3585 p3876 p4737 : Prop) (h : (¬ p3876) ∨ (¬ p3362) ∨ (¬ p3585) ∨ (¬ p4737) ∨ (¬ p3389) ∨ p2027) : (p2027) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11268 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7)
  exact rule22012 (meaning t m 2027) (meaning t m 3362) (meaning t m 3389) (meaning t m 3585) (meaning t m 3876) (meaning t m 4737) source

theorem rule22013 (p2027 p2307 p2387 p2396 p4138 p4668 : Prop) (h : p2027 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p4138) ∨ (¬ p2396) ∨ (¬ p4668)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2396) ∨ (¬ p4138) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial22013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory11269 t (m.theta 0 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule22013 (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2396) (meaning t m 4138) (meaning t m 4668) source

theorem rule22014 (p2027 p2143 p2707 p3583 p3646 p4344 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p4344) ∨ (¬ p3646) ∨ (¬ p2707) ∨ (¬ p2143) ∨ p2027 ∨ (¬ p3583)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2707) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p4344) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11270 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22014 (meaning t m 2027) (meaning t m 2143) (meaning t m 2707) (meaning t m 3583) (meaning t m 3646) (meaning t m 4344) (meaning t m 4558) source

theorem rule22015 (p2027 p3399 p3555 p3571 p4173 p4558 : Prop) (h : (¬ p3571) ∨ (¬ p4173) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3555)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4173) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11271 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22015 (meaning t m 2027) (meaning t m 3399) (meaning t m 3555) (meaning t m 3571) (meaning t m 4173) (meaning t m 4558) source

theorem rule22018 (p2027 p2295 p2396 p3689 p4324 p4843 : Prop) (h : (¬ p4324) ∨ (¬ p3689) ∨ (¬ p4843) ∨ (¬ p2396) ∨ (¬ p2295) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2396) ∨ (¬ p3689) ∨ (¬ p4324) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial22018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory11274 t (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9)
  exact rule22018 (meaning t m 2027) (meaning t m 2295) (meaning t m 2396) (meaning t m 3689) (meaning t m 4324) (meaning t m 4843) source

theorem rule22022 (p3362 p3873 p4108 : Prop) (h : p3873 ∨ (¬ p3362) ∨ (¬ p4108)) : (¬ p3362) ∨ (p3873) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial22022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3362)) ∨ (meaning t m 3873) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory11278 (m.theta 0 1) (m.theta 0 2) (m.theta 0 4)
  exact rule22022 (meaning t m 3362) (meaning t m 3873) (meaning t m 4108) source

theorem rule22023 (p2027 p2177 p2870 p3694 p4132 p4556 : Prop) (h : (¬ p2870) ∨ (¬ p4556) ∨ p2027 ∨ (¬ p4132) ∨ (¬ p2177) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial22023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory11279 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule22023 (meaning t m 2027) (meaning t m 2177) (meaning t m 2870) (meaning t m 3694) (meaning t m 4132) (meaning t m 4556) source

theorem rule22025 (p1981 p2027 p2230 p2352 p2493 p2699 p3238 p4079 : Prop) (h : (¬ p4079) ∨ p2699 ∨ (¬ p2493) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p1981) ∨ (¬ p2352)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (p2699) ∨ (¬ p3238) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial22025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory11281 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule22025 (meaning t m 1981) (meaning t m 2027) (meaning t m 2230) (meaning t m 2352) (meaning t m 2493) (meaning t m 2699) (meaning t m 3238) (meaning t m 4079) source

theorem rule22028 (p2027 p2518 p2528 p3365 p3379 p4037 p4195 p4604 p4736 : Prop) (h : (¬ p2518) ∨ (¬ p3379) ∨ (¬ p4604) ∨ (¬ p2528) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p4037) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11284 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule22028 (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 3365) (meaning t m 3379) (meaning t m 4037) (meaning t m 4195) (meaning t m 4604) (meaning t m 4736) source

theorem rule22029 (p2027 p3323 p3497 p3744 p4336 p4507 : Prop) (h : (¬ p3744) ∨ p2027 ∨ (¬ p4507) ∨ (¬ p4336) ∨ (¬ p3497) ∨ (¬ p3323)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3497) ∨ (¬ p3744) ∨ (¬ p4336) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial22029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory11285 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 9)
  exact rule22029 (meaning t m 2027) (meaning t m 3323) (meaning t m 3497) (meaning t m 3744) (meaning t m 4336) (meaning t m 4507) source

theorem rule22030 (p2027 p2192 p3125 p3556 p3645 p4275 p4624 : Prop) (h : (¬ p3125) ∨ (¬ p3645) ∨ (¬ p4624) ∨ (¬ p4275) ∨ (¬ p3556) ∨ (¬ p2192) ∨ p2027) : (p2027) ∨ (¬ p2192) ∨ (¬ p3125) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4275) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial22030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory11286 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9)
  exact rule22030 (meaning t m 2027) (meaning t m 2192) (meaning t m 3125) (meaning t m 3556) (meaning t m 3645) (meaning t m 4275) (meaning t m 4624) source

theorem rule22033 (p2027 p2138 p2518 p2528 p3379 p3744 p3758 p4604 p4736 : Prop) (h : (¬ p4604) ∨ (¬ p2138) ∨ (¬ p2528) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p4736) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3744)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11289 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22033 (meaning t m 2027) (meaning t m 2138) (meaning t m 2518) (meaning t m 2528) (meaning t m 3379) (meaning t m 3744) (meaning t m 3758) (meaning t m 4604) (meaning t m 4736) source

theorem rule22034 (p1976 p2027 p2766 p2952 p3136 p3692 p3877 p4236 p4312 : Prop) (h : p2766 ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p3692) ∨ (¬ p2952) ∨ (¬ p4236) ∨ (¬ p4312) ∨ (¬ p3877)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3692) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4312) := by
  classical
  tauto

theorem initial22034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4312)) := by
  have source := ElevenTheory.theory11290 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule22034 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 2952) (meaning t m 3136) (meaning t m 3692) (meaning t m 3877) (meaning t m 4236) (meaning t m 4312) source

theorem rule22035 (p1984 p2873 p3369 p3555 p4524 : Prop) (h : (¬ p1984) ∨ (¬ p3555) ∨ p2873 ∨ p4524 ∨ (¬ p3369)) : (¬ p1984) ∨ (p2873) ∨ (¬ p3369) ∨ (¬ p3555) ∨ (p4524) := by
  classical
  tauto

theorem initial22035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3555)) ∨ (meaning t m 4524) := by
  have source := ElevenTheory.theory11291 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5)
  exact rule22035 (meaning t m 1984) (meaning t m 2873) (meaning t m 3369) (meaning t m 3555) (meaning t m 4524) source

theorem rule22036 (p2027 p2518 p2528 p3365 p3379 p3572 p3947 p4669 p4736 : Prop) (h : (¬ p3572) ∨ (¬ p2528) ∨ (¬ p4669) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p4736) ∨ (¬ p3365) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11292 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22036 (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 3365) (meaning t m 3379) (meaning t m 3572) (meaning t m 3947) (meaning t m 4669) (meaning t m 4736) source

theorem rule22037 (p2027 p2156 p2590 p3125 p4137 p4539 : Prop) (h : p2027 ∨ (¬ p4539) ∨ (¬ p2156) ∨ (¬ p2590) ∨ (¬ p4137) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p4137) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial22037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory11293 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule22037 (meaning t m 2027) (meaning t m 2156) (meaning t m 2590) (meaning t m 3125) (meaning t m 4137) (meaning t m 4539) source

theorem rule22038 (p2027 p2493 p3365 p3379 p3564 p3877 p4118 p4330 p4736 : Prop) (h : (¬ p3877) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3365) ∨ (¬ p4736) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3365) ∨ (¬ p3379) ∨ (¬ p3564) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11294 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22038 (meaning t m 2027) (meaning t m 2493) (meaning t m 3365) (meaning t m 3379) (meaning t m 3564) (meaning t m 3877) (meaning t m 4118) (meaning t m 4330) (meaning t m 4736) source

theorem rule22039 (p2027 p2341 p3548 p3571 p3646 p4558 p4988 : Prop) (h : (¬ p4988) ∨ (¬ p3548) ∨ (¬ p3571) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p4558)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3548) ∨ (¬ p3571) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial22039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory11295 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule22039 (meaning t m 2027) (meaning t m 2341) (meaning t m 3548) (meaning t m 3571) (meaning t m 3646) (meaning t m 4558) (meaning t m 4988) source

theorem rule22040 (p2027 p2156 p3238 p4110 p4399 p5194 : Prop) (h : (¬ p4399) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3238) ∨ (¬ p2156) ∨ (¬ p5194)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3238) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11296 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6)
  exact rule22040 (meaning t m 2027) (meaning t m 2156) (meaning t m 3238) (meaning t m 4110) (meaning t m 4399) (meaning t m 5194) source

theorem rule22041 (p2027 p2230 p2829 p3238 p3759 p4257 p5224 : Prop) (h : (¬ p5224) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p4257) ∨ (¬ p3759) ∨ (¬ p3238) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2829) ∨ (¬ p3238) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p5224) := by
  classical
  tauto

theorem initial22041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5224)) := by
  have source := ElevenTheory.theory11297 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5)
  exact rule22041 (meaning t m 2027) (meaning t m 2230) (meaning t m 2829) (meaning t m 3238) (meaning t m 3759) (meaning t m 4257) (meaning t m 5224) source

theorem rule22043 (p2027 p2230 p2630 p2656 p2745 p3238 p3402 : Prop) (h : (¬ p2656) ∨ (¬ p3402) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p2630) ∨ (¬ p2745)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3238) ∨ (¬ p3402) := by
  classical
  tauto

theorem initial22043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) := by
  have source := ElevenTheory.theory11299 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule22043 (meaning t m 2027) (meaning t m 2230) (meaning t m 2630) (meaning t m 2656) (meaning t m 2745) (meaning t m 3238) (meaning t m 3402) source

theorem rule22045 (p2027 p2230 p2579 p2982 p3096 p5046 : Prop) (h : (¬ p2982) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3096) ∨ (¬ p5046)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2982) ∨ (¬ p3096) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11301 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 9)
  exact rule22045 (meaning t m 2027) (meaning t m 2230) (meaning t m 2579) (meaning t m 2982) (meaning t m 3096) (meaning t m 5046) source

theorem rule22050 (p2027 p2911 p2926 p3389 p3548 p5194 : Prop) (h : (¬ p2926) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p5194) ∨ (¬ p3389) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3389) ∨ (¬ p3548) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11306 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule22050 (meaning t m 2027) (meaning t m 2911) (meaning t m 2926) (meaning t m 3389) (meaning t m 3548) (meaning t m 5194) source

theorem rule22053 (p2027 p2761 p3222 p3807 p4638 p5127 : Prop) (h : (¬ p4638) ∨ (¬ p2761) ∨ (¬ p5127) ∨ p2027 ∨ (¬ p3807) ∨ (¬ p3222)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3222) ∨ (¬ p3807) ∨ (¬ p4638) ∨ (¬ p5127) := by
  classical
  tauto

theorem initial22053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3807)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 5127)) := by
  have source := ElevenTheory.theory11309 t (m.theta 1 4) (m.theta 4 10) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule22053 (meaning t m 2027) (meaning t m 2761) (meaning t m 3222) (meaning t m 3807) (meaning t m 4638) (meaning t m 5127) source

theorem rule22054 (p1988 p2027 p2230 p2699 p3222 p3238 p3276 p4079 : Prop) (h : (¬ p3222) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p4079) ∨ p2027 ∨ p2699 ∨ (¬ p1988) ∨ (¬ p3276)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2699) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3276) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial22054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory11310 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule22054 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2699) (meaning t m 3222) (meaning t m 3238) (meaning t m 3276) (meaning t m 4079) source

theorem rule22057 (p2027 p2922 p3238 p3556 p3569 p4533 : Prop) (h : (¬ p3569) ∨ (¬ p4533) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2922) ∨ (¬ p3238)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3556) ∨ (¬ p3569) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial22057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory11313 t (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule22057 (meaning t m 2027) (meaning t m 2922) (meaning t m 3238) (meaning t m 3556) (meaning t m 3569) (meaning t m 4533) source

theorem rule22058 (p2027 p2383 p2786 p3055 p3822 p3955 p5224 : Prop) (h : (¬ p2786) ∨ (¬ p3822) ∨ (¬ p5224) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3955)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3055) ∨ (¬ p3822) ∨ (¬ p3955) ∨ (¬ p5224) := by
  classical
  tauto

theorem initial22058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 5224)) := by
  have source := ElevenTheory.theory11314 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule22058 (meaning t m 2027) (meaning t m 2383) (meaning t m 2786) (meaning t m 3055) (meaning t m 3822) (meaning t m 3955) (meaning t m 5224) source

theorem rule22059 (p2027 p2437 p2440 p3569 p3646 p4031 p4558 : Prop) (h : (¬ p2437) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p4031) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p3569)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p3569) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11315 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule22059 (meaning t m 2027) (meaning t m 2437) (meaning t m 2440) (meaning t m 3569) (meaning t m 3646) (meaning t m 4031) (meaning t m 4558) source

theorem rule22060 (p1983 p2027 p2230 p2417 p2699 p2922 p3238 p4079 : Prop) (h : (¬ p1983) ∨ p2699 ∨ (¬ p4079) ∨ (¬ p2417) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2922)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2417) ∨ (p2699) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial22060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory11316 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule22060 (meaning t m 1983) (meaning t m 2027) (meaning t m 2230) (meaning t m 2417) (meaning t m 2699) (meaning t m 2922) (meaning t m 3238) (meaning t m 4079) source

theorem rule22062 (p2027 p2396 p3707 p4322 p4402 p4556 p5358 : Prop) (h : (¬ p4402) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p3707) ∨ (¬ p4556) ∨ (¬ p5358)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4556) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial22062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory11318 t (m.theta 1 9) (m.theta 5 7) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule22062 (meaning t m 2027) (meaning t m 2396) (meaning t m 3707) (meaning t m 4322) (meaning t m 4402) (meaning t m 4556) (meaning t m 5358) source

theorem rule22063 (p2027 p2241 p2780 p2992 p3115 p3822 p4107 p4395 p4736 : Prop) (h : (¬ p2241) ∨ (¬ p4395) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2992) ∨ (¬ p4736) ∨ (¬ p2780) ∨ (¬ p3822)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2780) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11319 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule22063 (meaning t m 2027) (meaning t m 2241) (meaning t m 2780) (meaning t m 2992) (meaning t m 3115) (meaning t m 3822) (meaning t m 4107) (meaning t m 4395) (meaning t m 4736) source

theorem rule22064 (p4107 p4324 p4471 : Prop) (h : (¬ p4107) ∨ (¬ p4471) ∨ p4324) : (¬ p4107) ∨ (p4324) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial22064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4107)) ∨ (meaning t m 4324) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory11320 (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule22064 (meaning t m 4107) (meaning t m 4324) (meaning t m 4471) source

theorem rule22066 (p2027 p2191 p2230 p2373 p4202 p5194 : Prop) (h : p2027 ∨ (¬ p5194) ∨ (¬ p2191) ∨ (¬ p4202) ∨ (¬ p2373) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p4202) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11322 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule22066 (meaning t m 2027) (meaning t m 2191) (meaning t m 2230) (meaning t m 2373) (meaning t m 4202) (meaning t m 5194) source

theorem rule22067 (p2027 p2911 p3389 p3548 p3554 p4202 p5194 : Prop) (h : (¬ p5194) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4202)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4202) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11323 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8)
  exact rule22067 (meaning t m 2027) (meaning t m 2911) (meaning t m 3389) (meaning t m 3548) (meaning t m 3554) (meaning t m 4202) (meaning t m 5194) source

theorem rule22070 (p1977 p2027 p2542 p2997 p3096 p3097 p3238 p3402 p3574 : Prop) (h : (¬ p3238) ∨ (¬ p2542) ∨ (¬ p3097) ∨ (¬ p1977) ∨ (¬ p3402) ∨ (¬ p3574) ∨ p2997 ∨ p2027 ∨ (¬ p3096)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2542) ∨ (p2997) ∨ (¬ p3096) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial22070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory11326 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule22070 (meaning t m 1977) (meaning t m 2027) (meaning t m 2542) (meaning t m 2997) (meaning t m 3096) (meaning t m 3097) (meaning t m 3238) (meaning t m 3402) (meaning t m 3574) source

theorem rule22073 (p2027 p2743 p3166 p3877 p4117 p4737 : Prop) (h : (¬ p4117) ∨ (¬ p3877) ∨ (¬ p2743) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3166)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3166) ∨ (¬ p3877) ∨ (¬ p4117) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial22073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory11329 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8)
  exact rule22073 (meaning t m 2027) (meaning t m 2743) (meaning t m 3166) (meaning t m 3877) (meaning t m 4117) (meaning t m 4737) source

theorem rule22074 (p2027 p2743 p3172 p3361 p3367 p3683 p5008 : Prop) (h : (¬ p3361) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p5008)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial22074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11330 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8)
  exact rule22074 (meaning t m 2027) (meaning t m 2743) (meaning t m 3172) (meaning t m 3361) (meaning t m 3367) (meaning t m 3683) (meaning t m 5008) source

theorem rule22075 (p2027 p2657 p2807 p3579 p3876 p4750 : Prop) (h : (¬ p3579) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p4750) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3579) ∨ (¬ p3876) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial22075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory11331 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule22075 (meaning t m 2027) (meaning t m 2657) (meaning t m 2807) (meaning t m 3579) (meaning t m 3876) (meaning t m 4750) source

theorem rule22076 (p2027 p2363 p2383 p2788 p4078 p4340 : Prop) (h : p2027 ∨ (¬ p2788) ∨ (¬ p2383) ∨ (¬ p4078) ∨ (¬ p2363) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2788) ∨ (¬ p4078) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial22076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2788)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory11332 t (m.theta 0 6) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule22076 (meaning t m 2027) (meaning t m 2363) (meaning t m 2383) (meaning t m 2788) (meaning t m 4078) (meaning t m 4340) source

theorem rule22077 (p2027 p2901 p3125 p4037 p4153 p4558 : Prop) (h : (¬ p3125) ∨ (¬ p4153) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4153) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11333 t (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule22077 (meaning t m 2027) (meaning t m 2901) (meaning t m 3125) (meaning t m 4037) (meaning t m 4153) (meaning t m 4558) source

theorem rule22078 (p2027 p2241 p2534 p2641 p3055 p3323 p3874 p4330 p4736 : Prop) (h : (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2241) ∨ (¬ p3874) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p4736) ∨ (¬ p4330) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3874) ∨ (¬ p4330) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11334 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule22078 (meaning t m 2027) (meaning t m 2241) (meaning t m 2534) (meaning t m 2641) (meaning t m 3055) (meaning t m 3323) (meaning t m 3874) (meaning t m 4330) (meaning t m 4736) source

theorem rule22079 (p2027 p2341 p2901 p3497 p3575 p4132 p4647 : Prop) (h : (¬ p3575) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4132) ∨ (¬ p4647) ∨ (¬ p2901) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3575) ∨ (¬ p4132) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial22079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory11335 t (m.theta 0 7) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule22079 (meaning t m 2027) (meaning t m 2341) (meaning t m 2901) (meaning t m 3497) (meaning t m 3575) (meaning t m 4132) (meaning t m 4647) source

theorem rule22082 (p2027 p2579 p2662 p3422 p3475 p3877 p5008 : Prop) (h : p2027 ∨ (¬ p3422) ∨ (¬ p2579) ∨ (¬ p5008) ∨ (¬ p3475) ∨ (¬ p3877) ∨ (¬ p2662)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2662) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3877) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial22082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory11338 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 6)
  exact rule22082 (meaning t m 2027) (meaning t m 2579) (meaning t m 2662) (meaning t m 3422) (meaning t m 3475) (meaning t m 3877) (meaning t m 5008) source

theorem rule22084 (p2027 p2241 p2589 p3189 p3256 p3744 p3905 p4110 p4604 p4736 : Prop) (h : (¬ p3744) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p2241) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3744) ∨ (¬ p3905) ∨ (¬ p4110) ∨ (¬ p4604) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11340 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule22084 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3189) (meaning t m 3256) (meaning t m 3744) (meaning t m 3905) (meaning t m 4110) (meaning t m 4604) (meaning t m 4736) source

theorem rule22085 (p2027 p2542 p2589 p2630 p2655 p4787 : Prop) (h : (¬ p2542) ∨ (¬ p4787) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p2655)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial22085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory11341 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule22085 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2630) (meaning t m 2655) (meaning t m 4787) source

theorem rule22086 (p2027 p2901 p3952 p3989 p4140 p4501 : Prop) (h : (¬ p4140) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p3989) ∨ (¬ p4501)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4140) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11342 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule22086 (meaning t m 2027) (meaning t m 2901) (meaning t m 3952) (meaning t m 3989) (meaning t m 4140) (meaning t m 4501) source

theorem rule22087 (p2220 p2341 p4132 p4988 : Prop) (h : (¬ p4132) ∨ (¬ p2341) ∨ (¬ p4988) ∨ p2220) : (p2220) ∨ (¬ p2341) ∨ (¬ p4132) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial22087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2220) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory11343 (m.theta 0 5) (m.theta 0 7) (m.theta 5 8) (m.theta 7 8)
  exact rule22087 (meaning t m 2220) (meaning t m 2341) (meaning t m 4132) (meaning t m 4988) source

theorem rule22089 (p2027 p2331 p2630 p2952 p4195 p4701 : Prop) (h : p2027 ∨ (¬ p4701) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p2952) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2630) ∨ (¬ p2952) ∨ (¬ p4195) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11345 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule22089 (meaning t m 2027) (meaning t m 2331) (meaning t m 2630) (meaning t m 2952) (meaning t m 4195) (meaning t m 4701) source

theorem rule22090 (p2027 p2598 p3201 p3540 p4108 p4733 : Prop) (h : (¬ p3201) ∨ (¬ p4733) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p4108)) : (p2027) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p4108) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial22090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory11346 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 7)
  exact rule22090 (meaning t m 2027) (meaning t m 2598) (meaning t m 3201) (meaning t m 3540) (meaning t m 4108) (meaning t m 4733) source

theorem rule22092 (p2027 p2274 p2363 p3692 p3988 p4501 : Prop) (h : (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p2274) ∨ (¬ p4501) ∨ p2027) : (p2027) ∨ (¬ p2274) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11348 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule22092 (meaning t m 2027) (meaning t m 2274) (meaning t m 2363) (meaning t m 3692) (meaning t m 3988) (meaning t m 4501) source

theorem rule22093 (p2027 p2459 p2911 p3692 p3955 p4441 p4712 : Prop) (h : (¬ p4712) ∨ (¬ p3955) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4441)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3692) ∨ (¬ p3955) ∨ (¬ p4441) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial22093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11349 t (m.theta 4 7) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22093 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3692) (meaning t m 3955) (meaning t m 4441) (meaning t m 4712) source

theorem rule22095 (p2027 p2132 p2780 p3105 p4428 p5046 : Prop) (h : (¬ p4428) ∨ p2027 ∨ (¬ p5046) ∨ (¬ p2780) ∨ (¬ p2132) ∨ (¬ p3105)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2780) ∨ (¬ p3105) ∨ (¬ p4428) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11351 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 9)
  exact rule22095 (meaning t m 2027) (meaning t m 2132) (meaning t m 2780) (meaning t m 3105) (meaning t m 4428) (meaning t m 5046) source

theorem rule22096 (p2027 p2341 p3365 p3548 p3631 p4037 p4172 p4195 p4625 p4736 p4988 : Prop) (h : (¬ p4736) ∨ (¬ p3631) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p4172) ∨ (¬ p4988) ∨ (¬ p3548) ∨ (¬ p3365) ∨ (¬ p4625)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3365) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4037) ∨ (¬ p4172) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p4736) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial22096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory11352 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule22096 (meaning t m 2027) (meaning t m 2341) (meaning t m 3365) (meaning t m 3548) (meaning t m 3631) (meaning t m 4037) (meaning t m 4172) (meaning t m 4195) (meaning t m 4625) (meaning t m 4736) (meaning t m 4988) source

theorem rule22097 (p2027 p2307 p2563 p4235 p4275 p4489 : Prop) (h : (¬ p4275) ∨ (¬ p4489) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p2563) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4489) := by
  classical
  tauto

theorem initial22097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4489)) := by
  have source := ElevenTheory.theory11353 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule22097 (meaning t m 2027) (meaning t m 2307) (meaning t m 2563) (meaning t m 4235) (meaning t m 4275) (meaning t m 4489) source

theorem rule22098 (p2027 p2299 p2363 p4348 p4501 : Prop) (h : (¬ p4348) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4501) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2363) ∨ (¬ p4348) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial22098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory11354 t (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule22098 (meaning t m 2027) (meaning t m 2299) (meaning t m 2363) (meaning t m 4348) (meaning t m 4501) source

theorem rule22102 (p2027 p2241 p2295 p2641 p3055 p3684 p4235 p4559 p4736 : Prop) (h : (¬ p2641) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2295) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p3684) ∨ (¬ p4736)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11358 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7)
  exact rule22102 (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2641) (meaning t m 3055) (meaning t m 3684) (meaning t m 4235) (meaning t m 4559) (meaning t m 4736) source

theorem rule22105 (p2027 p2850 p2982 p3742 p3872 p4001 p4343 p5046 : Prop) (h : (¬ p4343) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p4001) ∨ (¬ p2982) ∨ (¬ p5046) ∨ (¬ p3872) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3742) ∨ (¬ p3872) ∨ (¬ p4001) ∨ (¬ p4343) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial22105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory11361 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule22105 (meaning t m 2027) (meaning t m 2850) (meaning t m 2982) (meaning t m 3742) (meaning t m 3872) (meaning t m 4001) (meaning t m 4343) (meaning t m 5046) source

theorem rule22107 (p2027 p2870 p2911 p3694 p4132 p4647 : Prop) (h : (¬ p2870) ∨ (¬ p2911) ∨ (¬ p4132) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p4647)) : (p2027) ∨ (¬ p2870) ∨ (¬ p2911) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial22107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory11363 t (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule22107 (meaning t m 2027) (meaning t m 2870) (meaning t m 2911) (meaning t m 3694) (meaning t m 4132) (meaning t m 4647) source

theorem rule22109 (p1994 p2323 p2651 p4417 p4771 : Prop) (h : (¬ p2651) ∨ p2323 ∨ (¬ p1994) ∨ p4771 ∨ (¬ p4417)) : (¬ p1994) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p4417) ∨ (p4771) := by
  classical
  tauto

theorem initial22109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 4417)) ∨ (meaning t m 4771) := by
  have source := ElevenTheory.theory11365 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 8)
  exact rule22109 (meaning t m 1994) (meaning t m 2323) (meaning t m 2651) (meaning t m 4417) (meaning t m 4771) source

theorem rule22111 (p2027 p2901 p3125 p4026 p4282 p4512 p4558 : Prop) (h : (¬ p4282) ∨ p2027 ∨ (¬ p4026) ∨ (¬ p3125) ∨ (¬ p4512) ∨ (¬ p2901) ∨ (¬ p4558)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4282) ∨ (¬ p4512) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial22111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory11367 t (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule22111 (meaning t m 2027) (meaning t m 2901) (meaning t m 3125) (meaning t m 4026) (meaning t m 4282) (meaning t m 4512) (meaning t m 4558) source

theorem rule22113 (p2027 p2156 p2960 p3136 p3745 p4195 : Prop) (h : p2027 ∨ (¬ p2960) ∨ (¬ p2156) ∨ (¬ p3745) ∨ (¬ p3136) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2960) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial22113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2960)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory11369 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule22113 (meaning t m 2027) (meaning t m 2156) (meaning t m 2960) (meaning t m 3136) (meaning t m 3745) (meaning t m 4195) source

theorem rule22114 (p2027 p3333 p3876 p4107 p4451 p4712 : Prop) (h : (¬ p4107) ∨ (¬ p4712) ∨ (¬ p3333) ∨ (¬ p4451) ∨ (¬ p3876) ∨ p2027) : (p2027) ∨ (¬ p3333) ∨ (¬ p3876) ∨ (¬ p4107) ∨ (¬ p4451) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial22114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory11370 t (m.theta 2 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9)
  exact rule22114 (meaning t m 2027) (meaning t m 3333) (meaning t m 3876) (meaning t m 4107) (meaning t m 4451) (meaning t m 4712) source

theorem rule22115 (p2027 p2619 p2839 p2928 p3055 p3146 p4030 p4278 p4669 p4734 : Prop) (h : (¬ p2928) ∨ (¬ p4278) ∨ (¬ p2839) ∨ (¬ p4669) ∨ (¬ p4734) ∨ (¬ p4030) ∨ (¬ p2619) ∨ (¬ p3055) ∨ (¬ p3146) ∨ p2027) : (p2027) ∨ (¬ p2619) ∨ (¬ p2839) ∨ (¬ p2928) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p4030) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial22115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory11371 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule22115 (meaning t m 2027) (meaning t m 2619) (meaning t m 2839) (meaning t m 2928) (meaning t m 3055) (meaning t m 3146) (meaning t m 4030) (meaning t m 4278) (meaning t m 4669) (meaning t m 4734) source

theorem rule22116 (p2027 p2246 p2663 p3389 p3662 p3742 p4701 : Prop) (h : (¬ p2246) ∨ (¬ p3742) ∨ (¬ p4701) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2663) ∨ (¬ p3389) ∨ (¬ p3662) ∨ (¬ p3742) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial22116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory11372 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule22116 (meaning t m 2027) (meaning t m 2246) (meaning t m 2663) (meaning t m 3389) (meaning t m 3662) (meaning t m 3742) (meaning t m 4701) source

theorem rule22118 (p2027 p2928 p3516 p4278 p5194 p5201 : Prop) (h : (¬ p5194) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2928) ∨ (¬ p3516) ∨ (¬ p5201)) : (p2027) ∨ (¬ p2928) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p5194) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial22118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5194)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory11374 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 4 7) (m.theta 7 9)
  exact rule22118 (meaning t m 2027) (meaning t m 2928) (meaning t m 3516) (meaning t m 4278) (meaning t m 5194) (meaning t m 5201) source

theorem rule22119 (p2027 p2177 p3093 p3309 p3365 p3572 p3947 p4666 p4736 : Prop) (h : (¬ p3093) ∨ (¬ p4736) ∨ (¬ p3365) ∨ (¬ p2177) ∨ (¬ p3309) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial22119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory11375 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule22119 (meaning t m 2027) (meaning t m 2177) (meaning t m 3093) (meaning t m 3309) (meaning t m 3365) (meaning t m 3572) (meaning t m 3947) (meaning t m 4666) (meaning t m 4736) source

theorem rule22121 (p2027 p2352 p3016 p4358 p4750 p5220 : Prop) (h : (¬ p4750) ∨ p2027 ∨ (¬ p5220) ∨ (¬ p3016) ∨ (¬ p4358) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3016) ∨ (¬ p4358) ∨ (¬ p4750) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial22121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory11377 t (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule22121 (meaning t m 2027) (meaning t m 2352) (meaning t m 3016) (meaning t m 4358) (meaning t m 4750) (meaning t m 5220) source

theorem rule22123 (p2027 p2088 p3923 p4114 p4347 p5022 : Prop) (h : p2027 ∨ (¬ p4114) ∨ (¬ p2088) ∨ (¬ p5022) ∨ (¬ p3923) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3923) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p5022) := by
  classical
  tauto

theorem initial22123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5022)) := by
  have source := ElevenTheory.theory11379 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule22123 (meaning t m 2027) (meaning t m 2088) (meaning t m 3923) (meaning t m 4114) (meaning t m 4347) (meaning t m 5022) source

theorem rule22124 (p2027 p2307 p2810 p3063 p3365 p3549 p4256 p4384 p4736 p5020 : Prop) (h : (¬ p4384) ∨ (¬ p2810) ∨ (¬ p3063) ∨ (¬ p4256) ∨ (¬ p3549) ∨ (¬ p2307) ∨ (¬ p5020) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3365)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2810) ∨ (¬ p3063) ∨ (¬ p3365) ∨ (¬ p3549) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p4736) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial22124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory11380 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule22124 (meaning t m 2027) (meaning t m 2307) (meaning t m 2810) (meaning t m 3063) (meaning t m 3365) (meaning t m 3549) (meaning t m 4256) (meaning t m 4384) (meaning t m 4736) (meaning t m 5020) source

theorem rule22125 (p2027 p2230 p3238 p4079 p4257 p4366 p4793 : Prop) (h : (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4793) ∨ (¬ p3238) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4366)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4366) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial22125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory11381 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5)
  exact rule22125 (meaning t m 2027) (meaning t m 2230) (meaning t m 3238) (meaning t m 4079) (meaning t m 4257) (meaning t m 4366) (meaning t m 4793) source

theorem rule22126 (p2027 p2230 p2427 p3486 p4202 p5194 : Prop) (h : (¬ p3486) ∨ (¬ p4202) ∨ (¬ p2230) ∨ (¬ p5194) ∨ (¬ p2427) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3486) ∨ (¬ p4202) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial22126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory11382 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule22126 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 3486) (meaning t m 4202) (meaning t m 5194) source

end SunPrize.SMT
