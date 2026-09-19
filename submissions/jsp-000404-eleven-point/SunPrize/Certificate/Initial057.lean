import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory041
import SunPrize.Certificate.Theory042
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule24617 (p2027 p2829 p3426 p3434 p3821 p3905 p4734 p5197 : Prop) (h : (¬ p3905) ∨ (¬ p3434) ∨ (¬ p5197) ∨ (¬ p4734) ∨ (¬ p2829) ∨ (¬ p3821) ∨ (¬ p3426) ∨ p2027) : (p2027) ∨ (¬ p2829) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3821) ∨ (¬ p3905) ∨ (¬ p4734) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial24617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory13873 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 7 9)
  exact rule24617 (meaning t m 2027) (meaning t m 2829) (meaning t m 3426) (meaning t m 3434) (meaning t m 3821) (meaning t m 3905) (meaning t m 4734) (meaning t m 5197) source

theorem rule24618 (p2027 p2098 p2247 p3497 p3609 p3662 p4134 p4347 p4733 : Prop) (h : (¬ p4347) ∨ (¬ p2247) ∨ (¬ p2098) ∨ (¬ p4733) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4134) ∨ p2027 ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p3497) ∨ (¬ p3609) ∨ (¬ p3662) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13874 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24618 (meaning t m 2027) (meaning t m 2098) (meaning t m 2247) (meaning t m 3497) (meaning t m 3609) (meaning t m 3662) (meaning t m 4134) (meaning t m 4347) (meaning t m 4733) source

theorem rule24619 (p2027 p3027 p3097 p3552 p4154 p4560 : Prop) (h : (¬ p4560) ∨ (¬ p3027) ∨ (¬ p4154) ∨ (¬ p3552) ∨ p2027 ∨ (¬ p3097)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4154) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial24619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13875 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule24619 (meaning t m 2027) (meaning t m 3027) (meaning t m 3097) (meaning t m 3552) (meaning t m 4154) (meaning t m 4560) source

theorem rule24621 (p3857 p3960 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3960) ∨ p3857) : (p3857) ∨ (¬ p3960) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial24621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3857) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory13877 (m.theta 0 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24621 (meaning t m 3857) (meaning t m 3960) (meaning t m 4348) source

theorem rule24622 (p2027 p2427 p2590 p3737 p4558 p5514 : Prop) (h : (¬ p2590) ∨ (¬ p2427) ∨ (¬ p4558) ∨ (¬ p3737) ∨ p2027 ∨ (¬ p5514)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2590) ∨ (¬ p3737) ∨ (¬ p4558) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial24622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory13878 t (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10)
  exact rule24622 (meaning t m 2027) (meaning t m 2427) (meaning t m 2590) (meaning t m 3737) (meaning t m 4558) (meaning t m 5514) source

theorem rule24623 (p2027 p2427 p3237 p3680 p4334 p4425 p4558 : Prop) (h : (¬ p2427) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p4425) ∨ (¬ p3237) ∨ (¬ p4334) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3237) ∨ (¬ p3680) ∨ (¬ p4334) ∨ (¬ p4425) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4334)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13879 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule24623 (meaning t m 2027) (meaning t m 2427) (meaning t m 3237) (meaning t m 3680) (meaning t m 4334) (meaning t m 4425) (meaning t m 4558) source

theorem rule24625 (p2027 p3083 p3550 p3742 p4157 p5503 p5559 : Prop) (h : p2027 ∨ (¬ p5559) ∨ (¬ p3742) ∨ (¬ p3083) ∨ (¬ p5503) ∨ (¬ p4157) ∨ (¬ p3550)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3550) ∨ (¬ p3742) ∨ (¬ p4157) ∨ (¬ p5503) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial24625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory13881 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule24625 (meaning t m 2027) (meaning t m 3083) (meaning t m 3550) (meaning t m 3742) (meaning t m 4157) (meaning t m 5503) (meaning t m 5559) source

theorem rule24626 (p2027 p2104 p2248 p2427 p2542 p2651 p3537 p3588 p3873 p4898 : Prop) (h : (¬ p4898) ∨ (¬ p3873) ∨ (¬ p2104) ∨ (¬ p3588) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3537) ∨ (¬ p2542) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial24626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory13882 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule24626 (meaning t m 2027) (meaning t m 2104) (meaning t m 2248) (meaning t m 2427) (meaning t m 2542) (meaning t m 2651) (meaning t m 3537) (meaning t m 3588) (meaning t m 3873) (meaning t m 4898) source

theorem rule24630 (p2027 p2156 p2177 p2245 p2274 p2657 p2727 p4041 p4360 p4521 : Prop) (h : (¬ p2245) ∨ (¬ p2727) ∨ (¬ p2657) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4041) ∨ (¬ p4521) ∨ (¬ p2274) ∨ (¬ p4360) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2274) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial24630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory13886 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule24630 (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2245) (meaning t m 2274) (meaning t m 2657) (meaning t m 2727) (meaning t m 4041) (meaning t m 4360) (meaning t m 4521) source

theorem rule24631 (p2177 p2396 p3657 : Prop) (h : (¬ p3657) ∨ (¬ p2396) ∨ p2177) : (p2177) ∨ (¬ p2396) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial24631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2177) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory13887 (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24631 (meaning t m 2177) (meaning t m 2396) (meaning t m 3657) source

theorem rule24632 (p2027 p3171 p3189 p4113 p4154 p4358 p4843 : Prop) (h : (¬ p4358) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p3171) ∨ (¬ p4113) ∨ (¬ p4154) ∨ (¬ p4843)) : (p2027) ∨ (¬ p3171) ∨ (¬ p3189) ∨ (¬ p4113) ∨ (¬ p4154) ∨ (¬ p4358) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial24632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory13888 t (m.theta 0 8) (m.theta 1 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule24632 (meaning t m 2027) (meaning t m 3171) (meaning t m 3189) (meaning t m 4113) (meaning t m 4154) (meaning t m 4358) (meaning t m 4843) source

theorem rule24633 (p2027 p2295 p2696 p2797 p2911 p3548 p4366 p4712 p4733 : Prop) (h : (¬ p2797) ∨ (¬ p2295) ∨ (¬ p4712) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2696) ∨ (¬ p4733) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4712) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13889 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24633 (meaning t m 2027) (meaning t m 2295) (meaning t m 2696) (meaning t m 2797) (meaning t m 2911) (meaning t m 3548) (meaning t m 4366) (meaning t m 4712) (meaning t m 4733) source

theorem rule24634 (p2027 p2509 p2534 p2696 p2797 p3323 p3452 p4330 p4733 : Prop) (h : (¬ p3452) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p2696) ∨ (¬ p4733) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p4330) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13890 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24634 (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2696) (meaning t m 2797) (meaning t m 3323) (meaning t m 3452) (meaning t m 4330) (meaning t m 4733) source

theorem rule24636 (p2518 p3083 p4116 : Prop) (h : (¬ p2518) ∨ (¬ p4116) ∨ p3083) : (¬ p2518) ∨ (p3083) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial24636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2518)) ∨ (meaning t m 3083) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory13892 (m.theta 1 4) (m.theta 3 4) (m.theta 4 8)
  exact rule24636 (meaning t m 2518) (meaning t m 3083) (meaning t m 4116) source

theorem rule24637 (p3879 p4882 p4906 : Prop) (h : (¬ p3879) ∨ (¬ p4882) ∨ p4906) : (¬ p3879) ∨ (¬ p4882) ∨ (p4906) := by
  classical
  tauto

theorem initial24637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4882)) ∨ (meaning t m 4906) := by
  have source := ElevenTheory.theory13893 t (m.theta 2 5) (m.theta 3 5) (m.theta 4 5)
  exact rule24637 (meaning t m 3879) (meaning t m 4882) (meaning t m 4906) source

theorem rule24640 (p2027 p2230 p2656 p2727 p4154 p4389 p4715 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p4715) ∨ (¬ p4154) ∨ (¬ p2727) ∨ (¬ p4389) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4154) ∨ (¬ p4389) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial24640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory13896 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule24640 (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 2727) (meaning t m 4154) (meaning t m 4389) (meaning t m 4715) source

theorem rule24641 (p2027 p2143 p2499 p2934 p3631 p3695 p3821 p4715 p4984 : Prop) (h : (¬ p4984) ∨ (¬ p2934) ∨ (¬ p2143) ∨ (¬ p2499) ∨ (¬ p3695) ∨ (¬ p4715) ∨ p2027 ∨ (¬ p3821) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2499) ∨ (¬ p2934) ∨ (¬ p3631) ∨ (¬ p3695) ∨ (¬ p3821) ∨ (¬ p4715) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial24641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory13897 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 7 9)
  exact rule24641 (meaning t m 2027) (meaning t m 2143) (meaning t m 2499) (meaning t m 2934) (meaning t m 3631) (meaning t m 3695) (meaning t m 3821) (meaning t m 4715) (meaning t m 4984) source

theorem rule24642 (p3359 p4045 p4256 : Prop) (h : (¬ p4045) ∨ (¬ p4256) ∨ p3359) : (p3359) ∨ (¬ p4045) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial24642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3359) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory13898 (m.theta 3 4) (m.theta 4 8) (m.theta 4 9)
  exact rule24642 (meaning t m 3359) (meaning t m 4045) (meaning t m 4256) source

theorem rule24643 (p4042 p4132 : Prop) (h : p4042 ∨ p4132) : (p4042) ∨ (p4132) := by
  classical
  tauto

theorem initial24643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4042) ∨ (meaning t m 4132) := by
  have source := ElevenTheory.theory13899 (m.theta 5 8) (m.theta 7 8)
  exact rule24643 (meaning t m 4042) (meaning t m 4132) source

theorem rule24644 (p2027 p2122 p2241 p2750 p2753 p2774 p3791 p3834 p4321 p4826 : Prop) (h : (¬ p4826) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p4321) ∨ (¬ p3834) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p2753) ∨ (¬ p3791) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3791) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13900 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule24644 (meaning t m 2027) (meaning t m 2122) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3791) (meaning t m 3834) (meaning t m 4321) (meaning t m 4826) source

theorem rule24645 (p2027 p2619 p3550 p4244 p4441 p5559 p5660 : Prop) (h : (¬ p5559) ∨ (¬ p4441) ∨ (¬ p3550) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p5660) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3550) ∨ (¬ p4244) ∨ (¬ p4441) ∨ (¬ p5559) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial24645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 5559)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory13901 t (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule24645 (meaning t m 2027) (meaning t m 2619) (meaning t m 3550) (meaning t m 4244) (meaning t m 4441) (meaning t m 5559) (meaning t m 5660) source

theorem rule24647 (p2027 p2274 p2449 p4026 p4361 p4396 p4516 : Prop) (h : (¬ p4361) ∨ (¬ p4396) ∨ (¬ p2274) ∨ (¬ p4026) ∨ (¬ p4516) ∨ p2027 ∨ (¬ p2449)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2449) ∨ (¬ p4026) ∨ (¬ p4361) ∨ (¬ p4396) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial24647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory13903 t (m.theta 1 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule24647 (meaning t m 2027) (meaning t m 2274) (meaning t m 2449) (meaning t m 4026) (meaning t m 4361) (meaning t m 4396) (meaning t m 4516) source

theorem rule24648 (p2027 p2417 p2437 p3359 p3950 p4440 : Prop) (h : (¬ p4440) ∨ (¬ p2437) ∨ (¬ p3359) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3359) ∨ (¬ p3950) ∨ (¬ p4440) := by
  classical
  tauto

theorem initial24648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4440)) := by
  have source := ElevenTheory.theory13904 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9)
  exact rule24648 (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 3359) (meaning t m 3950) (meaning t m 4440) source

theorem rule24649 (p2027 p2619 p3051 p3880 p4244 p4539 : Prop) (h : p2027 ∨ (¬ p4244) ∨ (¬ p3051) ∨ (¬ p2619) ∨ (¬ p4539) ∨ (¬ p3880)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3880) ∨ (¬ p4244) ∨ (¬ p4539) := by
  classical
  tauto

theorem initial24649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4539)) := by
  have source := ElevenTheory.theory13905 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule24649 (meaning t m 2027) (meaning t m 2619) (meaning t m 3051) (meaning t m 3880) (meaning t m 4244) (meaning t m 4539) source

theorem rule24650 (p2027 p2668 p3979 p4197 p4581 p5590 : Prop) (h : (¬ p4581) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p3979) ∨ (¬ p5590) ∨ (¬ p4197)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p4581) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial24650 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4581)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory13906 t (m.theta 0 6) (m.theta 0 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10)
  exact rule24650 (meaning t m 2027) (meaning t m 2668) (meaning t m 3979) (meaning t m 4197) (meaning t m 4581) (meaning t m 5590) source

theorem rule24651 (p2027 p2241 p2748 p3585 p3954 p4749 : Prop) (h : p2027 ∨ (¬ p3954) ∨ (¬ p2748) ∨ (¬ p4749) ∨ (¬ p3585) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial24651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory13907 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4)
  exact rule24651 (meaning t m 2027) (meaning t m 2241) (meaning t m 2748) (meaning t m 3585) (meaning t m 3954) (meaning t m 4749) source

theorem rule24653 (p2027 p2104 p2230 p2427 p4129 p4340 p4419 p4444 p4826 : Prop) (h : (¬ p4129) ∨ (¬ p4826) ∨ (¬ p4444) ∨ (¬ p4340) ∨ (¬ p2427) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p4419) ∨ p2027) : (p2027) ∨ (¬ p2104) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p4129) ∨ (¬ p4340) ∨ (¬ p4419) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13909 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24653 (meaning t m 2027) (meaning t m 2104) (meaning t m 2230) (meaning t m 2427) (meaning t m 4129) (meaning t m 4340) (meaning t m 4419) (meaning t m 4444) (meaning t m 4826) source

theorem rule24654 (p2027 p3005 p3989 p4195 p4417 p4560 : Prop) (h : (¬ p4195) ∨ (¬ p4417) ∨ (¬ p3005) ∨ (¬ p4560) ∨ p2027 ∨ (¬ p3989)) : (p2027) ∨ (¬ p3005) ∨ (¬ p3989) ∨ (¬ p4195) ∨ (¬ p4417) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial24654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13910 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 5 6) (m.theta 6 8)
  exact rule24654 (meaning t m 2027) (meaning t m 3005) (meaning t m 3989) (meaning t m 4195) (meaning t m 4417) (meaning t m 4560) source

theorem rule24655 (p1998 p2027 p2668 p2997 p3568 p3979 p5558 : Prop) (h : (¬ p5558) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p1998) ∨ (¬ p2668) ∨ p2997 ∨ (¬ p3979)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial24655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory13911 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule24655 (meaning t m 1998) (meaning t m 2027) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 3979) (meaning t m 5558) source

theorem rule24657 (p2027 p3093 p3323 p3834 p4024 p4843 p5148 : Prop) (h : p2027 ∨ (¬ p3093) ∨ (¬ p3323) ∨ (¬ p4024) ∨ (¬ p5148) ∨ (¬ p4843) ∨ (¬ p3834)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3323) ∨ (¬ p3834) ∨ (¬ p4024) ∨ (¬ p4843) ∨ (¬ p5148) := by
  classical
  tauto

theorem initial24657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4843)) ∨ (¬ (meaning t m 5148)) := by
  have source := ElevenTheory.theory13913 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule24657 (meaning t m 2027) (meaning t m 3093) (meaning t m 3323) (meaning t m 3834) (meaning t m 4024) (meaning t m 4843) (meaning t m 5148) source

theorem rule24658 (p1987 p2611 p2696 p5117 p5123 : Prop) (h : (¬ p1987) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p5117) ∨ p5123) : (¬ p1987) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p5117) ∨ (p5123) := by
  classical
  tauto

theorem initial24658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 5117)) ∨ (meaning t m 5123) := by
  have source := ElevenTheory.theory13914 t (m.theta 0 2) (m.theta 2 3) (m.theta 8 10) (m.theta 9 10)
  exact rule24658 (meaning t m 1987) (meaning t m 2611) (meaning t m 2696) (meaning t m 5117) (meaning t m 5123) source

theorem rule24660 (p2027 p3232 p3452 p3830 p5160 p5217 : Prop) (h : (¬ p3830) ∨ (¬ p5217) ∨ (¬ p3232) ∨ (¬ p5160) ∨ (¬ p3452) ∨ p2027) : (p2027) ∨ (¬ p3232) ∨ (¬ p3452) ∨ (¬ p3830) ∨ (¬ p5160) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial24660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory13916 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 2 4) (m.theta 4 9)
  exact rule24660 (meaning t m 2027) (meaning t m 3232) (meaning t m 3452) (meaning t m 3830) (meaning t m 5160) (meaning t m 5217) source

theorem rule24662 (p2027 p3233 p3707 p4425 p5160 p5217 : Prop) (h : (¬ p3707) ∨ (¬ p3233) ∨ (¬ p5160) ∨ (¬ p5217) ∨ p2027 ∨ (¬ p4425)) : (p2027) ∨ (¬ p3233) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p5160) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial24662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory13918 t (m.theta 1 4) (m.theta 1 9) (m.theta 2 4) (m.theta 4 9) (m.theta 9 10)
  exact rule24662 (meaning t m 2027) (meaning t m 3233) (meaning t m 3707) (meaning t m 4425) (meaning t m 5160) (meaning t m 5217) source

theorem rule24663 (p2027 p2088 p2484 p3641 p4440 p5160 : Prop) (h : (¬ p3641) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p2484) ∨ (¬ p4440) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2484) ∨ (¬ p3641) ∨ (¬ p4440) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial24663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2484)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory13919 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule24663 (meaning t m 2027) (meaning t m 2088) (meaning t m 2484) (meaning t m 3641) (meaning t m 4440) (meaning t m 5160) source

theorem rule24664 (p2027 p2230 p2870 p2963 p3362 p3698 p4037 p4129 p4191 p4789 p4826 : Prop) (h : (¬ p4037) ∨ (¬ p4789) ∨ (¬ p4191) ∨ (¬ p3362) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p2230) ∨ (¬ p2870) ∨ (¬ p4826) ∨ (¬ p3698) ∨ (¬ p4129)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2870) ∨ (¬ p2963) ∨ (¬ p3362) ∨ (¬ p3698) ∨ (¬ p4037) ∨ (¬ p4129) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13920 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule24664 (meaning t m 2027) (meaning t m 2230) (meaning t m 2870) (meaning t m 2963) (meaning t m 3362) (meaning t m 3698) (meaning t m 4037) (meaning t m 4129) (meaning t m 4191) (meaning t m 4789) (meaning t m 4826) source

theorem rule24666 (p2027 p2247 p2761 p3434 p3471 p4154 p4733 p5254 p5717 : Prop) (h : (¬ p4154) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p2761) ∨ (¬ p5254) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4733) ∨ (¬ p5717)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4154) ∨ (¬ p4733) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial24666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory13922 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule24666 (meaning t m 2027) (meaning t m 2247) (meaning t m 2761) (meaning t m 3434) (meaning t m 3471) (meaning t m 4154) (meaning t m 4733) (meaning t m 5254) (meaning t m 5717) source

theorem rule24667 (p2027 p2588 p2685 p3552 p4195 p4976 : Prop) (h : (¬ p2588) ∨ (¬ p3552) ∨ p2027 ∨ (¬ p4976) ∨ (¬ p4195) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2588) ∨ (¬ p2685) ∨ (¬ p3552) ∨ (¬ p4195) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial24667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory13923 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7)
  exact rule24667 (meaning t m 2027) (meaning t m 2588) (meaning t m 2685) (meaning t m 3552) (meaning t m 4195) (meaning t m 4976) source

theorem rule24669 (p2027 p2727 p3016 p4154 p4976 : Prop) (h : (¬ p4154) ∨ (¬ p2727) ∨ (¬ p4976) ∨ p2027 ∨ (¬ p3016)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p4154) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial24669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory13925 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule24669 (meaning t m 2027) (meaning t m 2727) (meaning t m 3016) (meaning t m 4154) (meaning t m 4976) source

theorem rule24670 (p2027 p2352 p2598 p3422 p3486 p3555 p3570 p4133 p4733 : Prop) (h : (¬ p3555) ∨ (¬ p4733) ∨ (¬ p2598) ∨ (¬ p3570) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2352) ∨ (¬ p4133)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13926 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8)
  exact rule24670 (meaning t m 2027) (meaning t m 2352) (meaning t m 2598) (meaning t m 3422) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4133) (meaning t m 4733) source

theorem rule24672 (p2027 p2313 p2373 p2598 p2850 p3309 p3923 p4433 p4733 p5015 : Prop) (h : (¬ p4433) ∨ (¬ p5015) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4733) ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3923) ∨ (¬ p2313) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4433) ∨ (¬ p4733) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial24672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4433)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory13928 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule24672 (meaning t m 2027) (meaning t m 2313) (meaning t m 2373) (meaning t m 2598) (meaning t m 2850) (meaning t m 3309) (meaning t m 3923) (meaning t m 4433) (meaning t m 4733) (meaning t m 5015) source

theorem rule24673 (p2027 p2230 p2299 p2528 p3549 p3591 p3692 p4355 p4902 p5190 : Prop) (h : (¬ p2230) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3591) ∨ (¬ p4902) ∨ (¬ p3549) ∨ (¬ p4355) ∨ (¬ p3692) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2528) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3692) ∨ (¬ p4355) ∨ (¬ p4902) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial24673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13929 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule24673 (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2528) (meaning t m 3549) (meaning t m 3591) (meaning t m 3692) (meaning t m 4355) (meaning t m 4902) (meaning t m 5190) source

theorem rule24674 (p2027 p2363 p2668 p3692 p3988 p4560 : Prop) (h : (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4560) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial24674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory13930 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule24674 (meaning t m 2027) (meaning t m 2363) (meaning t m 2668) (meaning t m 3692) (meaning t m 3988) (meaning t m 4560) source

theorem rule24675 (p2027 p2417 p2598 p3201 p3555 p3744 p4173 p4625 p4733 : Prop) (h : (¬ p3555) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p3744) ∨ (¬ p4733) ∨ (¬ p3201) ∨ (¬ p4173) ∨ (¬ p2417) ∨ (¬ p4625)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4625) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13931 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule24675 (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 3201) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4625) (meaning t m 4733) source

theorem rule24676 (p2027 p3309 p3568 p4111 p4759 p4975 : Prop) (h : (¬ p3568) ∨ (¬ p4759) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p4975) ∨ (¬ p3309)) : (p2027) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4111) ∨ (¬ p4759) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial24676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory13932 t (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule24676 (meaning t m 2027) (meaning t m 3309) (meaning t m 3568) (meaning t m 4111) (meaning t m 4759) (meaning t m 4975) source

theorem rule24678 (p2027 p2774 p2819 p3555 p3979 p4322 p4363 p4733 p5119 : Prop) (h : (¬ p3555) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p3979) ∨ (¬ p2819) ∨ (¬ p5119) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3555) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4733) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial24678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory13934 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule24678 (meaning t m 2027) (meaning t m 2774) (meaning t m 2819) (meaning t m 3555) (meaning t m 3979) (meaning t m 4322) (meaning t m 4363) (meaning t m 4733) (meaning t m 5119) source

theorem rule24679 (p2027 p2191 p2528 p2598 p3555 p3641 p4733 p5118 p5568 : Prop) (h : (¬ p3641) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p4733) ∨ (¬ p2528) ∨ (¬ p3555) ∨ (¬ p5568) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p3555) ∨ (¬ p3641) ∨ (¬ p4733) ∨ (¬ p5118) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13935 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule24679 (meaning t m 2027) (meaning t m 2191) (meaning t m 2528) (meaning t m 2598) (meaning t m 3555) (meaning t m 3641) (meaning t m 4733) (meaning t m 5118) (meaning t m 5568) source

theorem rule24681 (p2027 p2247 p2299 p2717 p3471 p3662 p4320 p4559 p4733 : Prop) (h : (¬ p4320) ∨ (¬ p3662) ∨ (¬ p4559) ∨ (¬ p2299) ∨ (¬ p4733) ∨ (¬ p3471) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p2717)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3662) ∨ (¬ p4320) ∨ (¬ p4559) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13937 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24681 (meaning t m 2027) (meaning t m 2247) (meaning t m 2299) (meaning t m 2717) (meaning t m 3471) (meaning t m 3662) (meaning t m 4320) (meaning t m 4559) (meaning t m 4733) source

theorem rule24682 (p2027 p2245 p2299 p2717 p2952 p2992 p2996 p3471 p4361 p4733 : Prop) (h : (¬ p3471) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2299) ∨ (¬ p2245) ∨ (¬ p4733) ∨ (¬ p2717) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p4361)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2299) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3471) ∨ (¬ p4361) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13938 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24682 (meaning t m 2027) (meaning t m 2245) (meaning t m 2299) (meaning t m 2717) (meaning t m 2952) (meaning t m 2992) (meaning t m 2996) (meaning t m 3471) (meaning t m 4361) (meaning t m 4733) source

theorem rule24683 (p2027 p2573 p2881 p3201 p3362 p3548 p3584 p4277 p4366 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p4277) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3584) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3201) ∨ (¬ p2881) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2881) ∨ (¬ p3201) ∨ (¬ p3362) ∨ (¬ p3548) ∨ (¬ p3584) ∨ (¬ p4277) ∨ (¬ p4366) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13939 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule24683 (meaning t m 2027) (meaning t m 2573) (meaning t m 2881) (meaning t m 3201) (meaning t m 3362) (meaning t m 3548) (meaning t m 3584) (meaning t m 4277) (meaning t m 4366) (meaning t m 4733) source

theorem rule24685 (p2819 p3641 p4375 p4432 : Prop) (h : (¬ p2819) ∨ (¬ p4375) ∨ (¬ p4432) ∨ p3641) : (¬ p2819) ∨ (p3641) ∨ (¬ p4375) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial24685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (meaning t m 3641) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory13941 (m.theta 2 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 8)
  exact rule24685 (meaning t m 2819) (meaning t m 3641) (meaning t m 4375) (meaning t m 4432) source

theorem rule24687 (p2027 p2707 p3583 p3952 p4316 p4344 p4558 : Prop) (h : (¬ p4316) ∨ (¬ p3952) ∨ (¬ p4558) ∨ (¬ p4344) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4316) ∨ (¬ p4344) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13943 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule24687 (meaning t m 2027) (meaning t m 2707) (meaning t m 3583) (meaning t m 3952) (meaning t m 4316) (meaning t m 4344) (meaning t m 4558) source

theorem rule24688 (p1986 p3584 p3586 p5225 : Prop) (h : p3586 ∨ (¬ p1986) ∨ p5225 ∨ (¬ p3584)) : (¬ p1986) ∨ (¬ p3584) ∨ (p3586) ∨ (p5225) := by
  classical
  tauto

theorem initial24688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 3586) ∨ (meaning t m 5225) := by
  have source := ElevenTheory.theory13944 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule24688 (meaning t m 1986) (meaning t m 3584) (meaning t m 3586) (meaning t m 5225) source

theorem rule24689 (p2027 p2295 p3422 p3876 p3921 p4976 : Prop) (h : (¬ p3921) ∨ (¬ p3876) ∨ (¬ p3422) ∨ (¬ p2295) ∨ (¬ p4976) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial24689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory13945 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule24689 (meaning t m 2027) (meaning t m 2295) (meaning t m 3422) (meaning t m 3876) (meaning t m 3921) (meaning t m 4976) source

theorem rule24690 (p1988 p2027 p2761 p3128 p3471 p3516 p3591 p3737 p3744 p4066 p4325 p4435 p4733 : Prop) (h : (¬ p4066) ∨ (¬ p3591) ∨ (¬ p4435) ∨ p3128 ∨ (¬ p1988) ∨ (¬ p3516) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p3737) ∨ (¬ p4325) ∨ (¬ p2761) ∨ (¬ p3744)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2761) ∨ (p3128) ∨ (¬ p3471) ∨ (¬ p3516) ∨ (¬ p3591) ∨ (¬ p3737) ∨ (¬ p3744) ∨ (¬ p4066) ∨ (¬ p4325) ∨ (¬ p4435) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4435)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13946 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 1 6) (m.theta 2 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 10) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule24690 (meaning t m 1988) (meaning t m 2027) (meaning t m 2761) (meaning t m 3128) (meaning t m 3471) (meaning t m 3516) (meaning t m 3591) (meaning t m 3737) (meaning t m 3744) (meaning t m 4066) (meaning t m 4325) (meaning t m 4435) (meaning t m 4733) source

theorem rule24692 (p3519 p4730 p5217 : Prop) (h : (¬ p3519) ∨ (¬ p5217) ∨ p4730) : (¬ p3519) ∨ (p4730) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial24692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3519)) ∨ (meaning t m 4730) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory13948 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4)
  exact rule24692 (meaning t m 3519) (meaning t m 4730) (meaning t m 5217) source

theorem rule24693 (p2140 p2954 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p2140) ∨ p2954) : (¬ p2140) ∨ (p2954) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial24693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2140)) ∨ (meaning t m 2954) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory13949 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 5)
  exact rule24693 (meaning t m 2140) (meaning t m 2954) (meaning t m 5051) source

theorem rule24695 (p2027 p2459 p2619 p3949 p4385 p4902 : Prop) (h : (¬ p3949) ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p4385)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p3949) ∨ (¬ p4385) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial24695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory13951 t (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule24695 (meaning t m 2027) (meaning t m 2459) (meaning t m 2619) (meaning t m 3949) (meaning t m 4385) (meaning t m 4902) source

theorem rule24696 (p2003 p2169 p2363 p3946 p4330 : Prop) (h : (¬ p2003) ∨ (¬ p2363) ∨ p4330 ∨ (¬ p3946) ∨ p2169) : (¬ p2003) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3946) ∨ (p4330) := by
  classical
  tauto

theorem initial24696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3946)) ∨ (meaning t m 4330) := by
  have source := ElevenTheory.theory13952 t (m.theta 0 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24696 (meaning t m 2003) (meaning t m 2169) (meaning t m 2363) (meaning t m 3946) (meaning t m 4330) source

theorem rule24698 (p2027 p2598 p2952 p3201 p3868 p4208 p4322 p4789 p4826 : Prop) (h : (¬ p3201) ∨ (¬ p4826) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p4789) ∨ (¬ p4322) ∨ (¬ p3868) ∨ (¬ p4208) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2952) ∨ (¬ p3201) ∨ (¬ p3868) ∨ (¬ p4208) ∨ (¬ p4322) ∨ (¬ p4789) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13954 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 9) (m.theta 7 10) (m.theta 9 10)
  exact rule24698 (meaning t m 2027) (meaning t m 2598) (meaning t m 2952) (meaning t m 3201) (meaning t m 3868) (meaning t m 4208) (meaning t m 4322) (meaning t m 4789) (meaning t m 4826) source

theorem rule24699 (p2027 p3641 p3876 p4404 p5503 p5559 : Prop) (h : p2027 ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p5503) ∨ (¬ p4404) ∨ (¬ p5559)) : (p2027) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4404) ∨ (¬ p5503) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial24699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory13955 t (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 10) (m.theta 7 8)
  exact rule24699 (meaning t m 2027) (meaning t m 3641) (meaning t m 3876) (meaning t m 4404) (meaning t m 5503) (meaning t m 5559) source

theorem rule24700 (p2027 p2504 p3093 p3452 p3584 p5217 : Prop) (h : (¬ p3093) ∨ (¬ p3452) ∨ (¬ p5217) ∨ (¬ p2504) ∨ (¬ p3584) ∨ p2027) : (p2027) ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3584) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial24700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory13956 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6)
  exact rule24700 (meaning t m 2027) (meaning t m 2504) (meaning t m 3093) (meaning t m 3452) (meaning t m 3584) (meaning t m 5217) source

theorem rule24701 (p2027 p2191 p2220 p3954 p4172 p4877 : Prop) (h : (¬ p3954) ∨ (¬ p4877) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p4172) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p3954) ∨ (¬ p4172) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory13957 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 8)
  exact rule24701 (meaning t m 2027) (meaning t m 2191) (meaning t m 2220) (meaning t m 3954) (meaning t m 4172) (meaning t m 4877) source

theorem rule24702 (p2027 p3032 p3449 p4366 p4391 p5307 p5559 : Prop) (h : (¬ p4366) ∨ (¬ p4391) ∨ p2027 ∨ (¬ p5559) ∨ (¬ p3032) ∨ (¬ p5307) ∨ (¬ p3449)) : (p2027) ∨ (¬ p3032) ∨ (¬ p3449) ∨ (¬ p4366) ∨ (¬ p4391) ∨ (¬ p5307) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial24702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 5307)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory13958 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 3 7) (m.theta 7 10) (m.theta 7 8)
  exact rule24702 (meaning t m 2027) (meaning t m 3032) (meaning t m 3449) (meaning t m 4366) (meaning t m 4391) (meaning t m 5307) (meaning t m 5559) source

theorem rule24703 (p1998 p2027 p2396 p2911 p2997 p3201 p4636 p5160 : Prop) (h : p2997 ∨ (¬ p2396) ∨ (¬ p1998) ∨ (¬ p3201) ∨ (¬ p2911) ∨ (¬ p4636) ∨ p2027 ∨ (¬ p5160)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2911) ∨ (p2997) ∨ (¬ p3201) ∨ (¬ p4636) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial24703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory13959 t (m.theta 2 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24703 (meaning t m 1998) (meaning t m 2027) (meaning t m 2396) (meaning t m 2911) (meaning t m 2997) (meaning t m 3201) (meaning t m 4636) (meaning t m 5160) source

theorem rule24704 (p2027 p2138 p2553 p2573 p3791 p4322 p4385 p4419 p4826 : Prop) (h : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3791) ∨ p2027 ∨ (¬ p4419) ∨ (¬ p4385) ∨ (¬ p2138) ∨ (¬ p4322) ∨ (¬ p4826)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3791) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4419) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory13960 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule24704 (meaning t m 2027) (meaning t m 2138) (meaning t m 2553) (meaning t m 2573) (meaning t m 3791) (meaning t m 4322) (meaning t m 4385) (meaning t m 4419) (meaning t m 4826) source

theorem rule24706 (p2027 p2264 p2995 p3551 p3952 p4283 p4558 : Prop) (h : (¬ p3551) ∨ (¬ p4283) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4558) ∨ (¬ p2264) ∨ (¬ p2995)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p3952) ∨ (¬ p4283) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13962 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule24706 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3551) (meaning t m 3952) (meaning t m 4283) (meaning t m 4558) source

theorem rule24707 (p1991 p2287 p2668 p3172 p4771 : Prop) (h : (¬ p1991) ∨ p4771 ∨ (¬ p2668) ∨ p2287 ∨ (¬ p3172)) : (¬ p1991) ∨ (p2287) ∨ (¬ p2668) ∨ (¬ p3172) ∨ (p4771) := by
  classical
  tauto

theorem initial24707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3172)) ∨ (meaning t m 4771) := by
  have source := ElevenTheory.theory13963 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8)
  exact rule24707 (meaning t m 1991) (meaning t m 2287) (meaning t m 2668) (meaning t m 3172) (meaning t m 4771) source

theorem rule24709 (p2027 p3694 p4181 p4496 p4878 p5568 : Prop) (h : (¬ p4878) ∨ (¬ p4496) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p3694) ∨ (¬ p4181)) : (p2027) ∨ (¬ p3694) ∨ (¬ p4181) ∨ (¬ p4496) ∨ (¬ p4878) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4878)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory13965 t (m.theta 1 5) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10)
  exact rule24709 (meaning t m 2027) (meaning t m 3694) (meaning t m 4181) (meaning t m 4496) (meaning t m 4878) (meaning t m 5568) source

theorem rule24710 (p2027 p3449 p3555 p3694 p4446 p4878 : Prop) (h : (¬ p4878) ∨ (¬ p3694) ∨ p2027 ∨ (¬ p4446) ∨ (¬ p3449) ∨ (¬ p3555)) : (p2027) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3694) ∨ (¬ p4446) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial24710 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory13966 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8)
  exact rule24710 (meaning t m 2027) (meaning t m 3449) (meaning t m 3555) (meaning t m 3694) (meaning t m 4446) (meaning t m 4878) source

theorem rule24711 (p2027 p3032 p3553 p3830 p4366 p4668 p5362 : Prop) (h : p2027 ∨ (¬ p3032) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p5362) ∨ (¬ p4668) ∨ (¬ p3830)) : (p2027) ∨ (¬ p3032) ∨ (¬ p3553) ∨ (¬ p3830) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial24711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory13967 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24711 (meaning t m 2027) (meaning t m 3032) (meaning t m 3553) (meaning t m 3830) (meaning t m 4366) (meaning t m 4668) (meaning t m 5362) source

theorem rule24714 (p1978 p2027 p2284 p2299 p2633 p3646 p4275 p4320 : Prop) (h : (¬ p1978) ∨ (¬ p2284) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4275) ∨ (¬ p2299) ∨ p2027 ∨ p2633) : (¬ p1978) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3646) ∨ (¬ p4275) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial24714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory13970 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24714 (meaning t m 1978) (meaning t m 2027) (meaning t m 2284) (meaning t m 2299) (meaning t m 2633) (meaning t m 3646) (meaning t m 4275) (meaning t m 4320) source

theorem rule24715 (p2027 p2247 p2352 p2363 p2573 p2996 p3947 p4669 p5190 : Prop) (h : (¬ p3947) ∨ (¬ p2352) ∨ (¬ p2996) ∨ (¬ p2573) ∨ (¬ p2363) ∨ (¬ p4669) ∨ (¬ p2247) ∨ (¬ p5190) ∨ p2027) : (p2027) ∨ (¬ p2247) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial24715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory13971 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24715 (meaning t m 2027) (meaning t m 2247) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2996) (meaning t m 3947) (meaning t m 4669) (meaning t m 5190) source

theorem rule24716 (p2027 p2132 p2247 p2619 p2996 p3146 p3947 p4669 p4733 : Prop) (h : (¬ p4733) ∨ (¬ p2132) ∨ (¬ p4669) ∨ (¬ p2247) ∨ (¬ p3947) ∨ (¬ p2996) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p3146)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p2996) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4669) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial24716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory13972 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24716 (meaning t m 2027) (meaning t m 2132) (meaning t m 2247) (meaning t m 2619) (meaning t m 2996) (meaning t m 3146) (meaning t m 3947) (meaning t m 4669) (meaning t m 4733) source

theorem rule24717 (p2027 p2253 p2651 p2750 p3954 p4111 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p3954) ∨ (¬ p2750) ∨ (¬ p2253)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial24717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory13973 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4)
  exact rule24717 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2750) (meaning t m 3954) (meaning t m 4111) source

theorem rule24719 (p2027 p2745 p2870 p4111 p4313 p4320 p4700 : Prop) (h : (¬ p4111) ∨ (¬ p2745) ∨ (¬ p4700) ∨ (¬ p4320) ∨ (¬ p4313) ∨ p2027 ∨ (¬ p2870)) : (p2027) ∨ (¬ p2745) ∨ (¬ p2870) ∨ (¬ p4111) ∨ (¬ p4313) ∨ (¬ p4320) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial24719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory13975 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule24719 (meaning t m 2027) (meaning t m 2745) (meaning t m 2870) (meaning t m 4111) (meaning t m 4313) (meaning t m 4320) (meaning t m 4700) source

theorem rule24720 (p1988 p2027 p2396 p2699 p2761 p3093 p3309 : Prop) (h : (¬ p1988) ∨ p2699 ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3309) ∨ (¬ p3093) ∨ (¬ p2396)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2396) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p3093) ∨ (¬ p3309) := by
  classical
  tauto

theorem initial24720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) := by
  have source := ElevenTheory.theory13976 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule24720 (meaning t m 1988) (meaning t m 2027) (meaning t m 2396) (meaning t m 2699) (meaning t m 2761) (meaning t m 3093) (meaning t m 3309) source

theorem rule24722 (p1987 p2611 p2696 p2744 p2749 : Prop) (h : (¬ p2696) ∨ p2611 ∨ (¬ p1987) ∨ p2744 ∨ (¬ p2749)) : (¬ p1987) ∨ (p2611) ∨ (¬ p2696) ∨ (p2744) ∨ (¬ p2749) := by
  classical
  tauto

theorem initial24722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2744) ∨ (¬ (meaning t m 2749)) := by
  have source := ElevenTheory.theory13978 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3)
  exact rule24722 (meaning t m 1987) (meaning t m 2611) (meaning t m 2696) (meaning t m 2744) (meaning t m 2749) source

theorem rule24723 (p2027 p2741 p2797 p3367 p4154 p4752 : Prop) (h : p2027 ∨ (¬ p3367) ∨ (¬ p4752) ∨ (¬ p2797) ∨ (¬ p2741) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2741) ∨ (¬ p2797) ∨ (¬ p3367) ∨ (¬ p4154) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial24723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory13979 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule24723 (meaning t m 2027) (meaning t m 2741) (meaning t m 2797) (meaning t m 3367) (meaning t m 4154) (meaning t m 4752) source

theorem rule24724 (p2027 p2341 p3486 p3570 p4525 p4988 : Prop) (h : (¬ p4988) ∨ (¬ p3570) ∨ (¬ p3486) ∨ (¬ p4525) ∨ p2027 ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3486) ∨ (¬ p3570) ∨ (¬ p4525) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial24724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4525)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory13980 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8)
  exact rule24724 (meaning t m 2027) (meaning t m 2341) (meaning t m 3486) (meaning t m 3570) (meaning t m 4525) (meaning t m 4988) source

theorem rule24727 (p1995 p2027 p2459 p2499 p2633 p3956 p4347 : Prop) (h : p2027 ∨ (¬ p2499) ∨ p2633 ∨ (¬ p3956) ∨ (¬ p2459) ∨ (¬ p1995) ∨ (¬ p4347)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (p2633) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial24727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory13983 t (m.theta 1 4) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24727 (meaning t m 1995) (meaning t m 2027) (meaning t m 2459) (meaning t m 2499) (meaning t m 2633) (meaning t m 3956) (meaning t m 4347) source

theorem rule24731 (p2027 p2737 p3005 p3583 p4316 p5065 : Prop) (h : (¬ p3005) ∨ (¬ p2737) ∨ (¬ p4316) ∨ (¬ p3583) ∨ (¬ p5065) ∨ p2027) : (p2027) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p5065) := by
  classical
  tauto

theorem initial24731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 5065)) := by
  have source := ElevenTheory.theory13987 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 8)
  exact rule24731 (meaning t m 2027) (meaning t m 2737) (meaning t m 3005) (meaning t m 3583) (meaning t m 4316) (meaning t m 5065) source

theorem rule24732 (p1992 p2027 p2098 p2341 p3360 p3425 p3659 p4242 : Prop) (h : p2027 ∨ p3360 ∨ (¬ p2341) ∨ (¬ p4242) ∨ (¬ p1992) ∨ (¬ p3659) ∨ (¬ p2098) ∨ (¬ p3425)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2341) ∨ (p3360) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial24732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory13988 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8)
  exact rule24732 (meaning t m 1992) (meaning t m 2027) (meaning t m 2098) (meaning t m 2341) (meaning t m 3360) (meaning t m 3425) (meaning t m 3659) (meaning t m 4242) source

theorem rule24733 (p1982 p2027 p2352 p2363 p2493 p2699 p3379 : Prop) (h : (¬ p3379) ∨ p2027 ∨ p2699 ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p2352) ∨ (¬ p2493)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2493) ∨ (p2699) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial24733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory13989 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule24733 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2493) (meaning t m 2699) (meaning t m 3379) source

theorem rule24734 (p2027 p2307 p2499 p2584 p2588 p5194 : Prop) (h : p2027 ∨ (¬ p2588) ∨ (¬ p2307) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p5194)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2499) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p5194) := by
  classical
  tauto

theorem initial24734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 5194)) := by
  have source := ElevenTheory.theory13990 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7)
  exact rule24734 (meaning t m 2027) (meaning t m 2307) (meaning t m 2499) (meaning t m 2584) (meaning t m 2588) (meaning t m 5194) source

theorem rule24736 (p2027 p2312 p2341 p3319 p3548 p4105 p4624 : Prop) (h : (¬ p4624) ∨ (¬ p3319) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p4105) ∨ (¬ p2341) ∨ (¬ p2312)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3319) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial24736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory13992 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule24736 (meaning t m 2027) (meaning t m 2312) (meaning t m 2341) (meaning t m 3319) (meaning t m 3548) (meaning t m 4105) (meaning t m 4624) source

theorem rule24737 (p2027 p2922 p3379 p3556 p3569 p4524 : Prop) (h : p2027 ∨ (¬ p2922) ∨ (¬ p4524) ∨ (¬ p3569) ∨ (¬ p3379) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3556) ∨ (¬ p3569) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial24737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory13993 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 7) (m.theta 5 7)
  exact rule24737 (meaning t m 2027) (meaning t m 2922) (meaning t m 3379) (meaning t m 3556) (meaning t m 3569) (meaning t m 4524) source

theorem rule24739 (p2027 p2307 p2584 p2588 p2665 p3574 : Prop) (h : p2027 ∨ (¬ p2665) ∨ (¬ p2588) ∨ (¬ p3574) ∨ (¬ p2584) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2665) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial24739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory13995 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule24739 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 2665) (meaning t m 3574) source

theorem rule24740 (p2027 p2230 p2579 p2901 p3096 p3879 p4558 : Prop) (h : (¬ p3879) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3096) ∨ (¬ p4558) ∨ (¬ p2579) ∨ (¬ p2901)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2901) ∨ (¬ p3096) ∨ (¬ p3879) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial24740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory13996 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule24740 (meaning t m 2027) (meaning t m 2230) (meaning t m 2579) (meaning t m 2901) (meaning t m 3096) (meaning t m 3879) (meaning t m 4558) source

theorem rule24742 (p2001 p2027 p2156 p2254 p2534 p2619 p2657 p2766 p3125 p3917 p4172 p4193 p4256 : Prop) (h : (¬ p4172) ∨ (¬ p2001) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2619) ∨ (¬ p4256) ∨ p2766 ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p3125) ∨ (¬ p4193) ∨ (¬ p2156) ∨ (¬ p3917)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2254) ∨ (¬ p2534) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3125) ∨ (¬ p3917) ∨ (¬ p4172) ∨ (¬ p4193) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial24742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory13998 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 2 5) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24742 (meaning t m 2001) (meaning t m 2027) (meaning t m 2156) (meaning t m 2254) (meaning t m 2534) (meaning t m 2619) (meaning t m 2657) (meaning t m 2766) (meaning t m 3125) (meaning t m 3917) (meaning t m 4172) (meaning t m 4193) (meaning t m 4256) source

theorem rule24744 (p2498 p3063 p3956 : Prop) (h : (¬ p2498) ∨ (¬ p3063) ∨ (¬ p3956)) : (¬ p2498) ∨ (¬ p3063) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial24744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory14000 (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule24744 (meaning t m 2498) (meaning t m 3063) (meaning t m 3956) source

theorem rule24747 (p2027 p2584 p2590 p3540 p3654 p4137 p4644 : Prop) (h : (¬ p3654) ∨ (¬ p2590) ∨ (¬ p4644) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2584) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2584) ∨ (¬ p2590) ∨ (¬ p3540) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial24747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory14003 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule24747 (meaning t m 2027) (meaning t m 2584) (meaning t m 2590) (meaning t m 3540) (meaning t m 3654) (meaning t m 4137) (meaning t m 4644) source

theorem rule24753 (p2001 p2027 p2148 p2156 p2274 p2373 p2588 p2590 : Prop) (h : (¬ p2001) ∨ p2148 ∨ (¬ p2156) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p2590) ∨ (¬ p2588) ∨ (¬ p2274)) : (¬ p2001) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) := by
  classical
  tauto

theorem initial24753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) := by
  have source := ElevenTheory.theory14009 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule24753 (meaning t m 2001) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2274) (meaning t m 2373) (meaning t m 2588) (meaning t m 2590) source

theorem rule24763 (p2027 p2584 p2589 p3654 p4137 p4717 : Prop) (h : (¬ p3654) ∨ (¬ p4137) ∨ (¬ p2589) ∨ (¬ p2584) ∨ (¬ p4717) ∨ p2027) : (p2027) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial24763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory14019 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule24763 (meaning t m 2027) (meaning t m 2584) (meaning t m 2589) (meaning t m 3654) (meaning t m 4137) (meaning t m 4717) source

theorem rule24766 (p1994 p2027 p2247 p2688 p2922 p3379 p3742 : Prop) (h : p2688 ∨ (¬ p3742) ∨ (¬ p1994) ∨ (¬ p2922) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2247)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial24766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory14022 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 7)
  exact rule24766 (meaning t m 1994) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 2922) (meaning t m 3379) (meaning t m 3742) source

theorem rule24767 (p2008 p2027 p2622 p2743 p3055 p3367 p3471 : Prop) (h : (¬ p2008) ∨ p2622 ∨ (¬ p3055) ∨ p2027 ∨ (¬ p3471) ∨ (¬ p3367) ∨ (¬ p2743)) : (¬ p2008) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial24767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory14023 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7)
  exact rule24767 (meaning t m 2008) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3055) (meaning t m 3367) (meaning t m 3471) source

theorem rule24772 (p3773 p4321 p4374 : Prop) (h : (¬ p3773) ∨ (¬ p4374) ∨ p4321) : (¬ p3773) ∨ (p4321) ∨ (¬ p4374) := by
  classical
  tauto

theorem initial24772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3773)) ∨ (meaning t m 4321) ∨ (¬ (meaning t m 4374)) := by
  have source := ElevenTheory.theory14028 (m.theta 0 9) (m.theta 1 9) (m.theta 9 10)
  exact rule24772 (meaning t m 3773) (meaning t m 4321) (meaning t m 4374) source

theorem rule24773 (p2027 p2241 p2459 p2727 p3343 p3556 p3692 p4045 p4119 p4420 p4524 : Prop) (h : (¬ p4045) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3556) ∨ (¬ p3343) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3692) ∨ (¬ p2459) ∨ (¬ p4119) ∨ (¬ p4420)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4045) ∨ (¬ p4119) ∨ (¬ p4420) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial24773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14029 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24773 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 2727) (meaning t m 3343) (meaning t m 3556) (meaning t m 3692) (meaning t m 4045) (meaning t m 4119) (meaning t m 4420) (meaning t m 4524) source

theorem rule24776 (p3355 p3759 p5160 : Prop) (h : (¬ p3759) ∨ (¬ p3355) ∨ (¬ p5160)) : (¬ p3355) ∨ (¬ p3759) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial24776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory14032 (m.theta 0 4) (m.theta 2 4) (m.theta 4 9)
  exact rule24776 (meaning t m 3355) (meaning t m 3759) (meaning t m 5160) source

theorem rule24794 (p1990 p2027 p2233 p2406 p2470 p2509 p2563 : Prop) (h : (¬ p2509) ∨ p2027 ∨ (¬ p2563) ∨ p2233 ∨ (¬ p2406) ∨ (¬ p1990) ∨ (¬ p2470)) : (¬ p1990) ∨ (p2027) ∨ (p2233) ∨ (¬ p2406) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2563) := by
  classical
  tauto

theorem initial24794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2563)) := by
  have source := ElevenTheory.theory14050 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule24794 (meaning t m 1990) (meaning t m 2027) (meaning t m 2233) (meaning t m 2406) (meaning t m 2470) (meaning t m 2509) (meaning t m 2563) source

theorem rule24796 (p2584 p4108 p5015 : Prop) (h : (¬ p5015) ∨ (¬ p2584) ∨ p4108) : (¬ p2584) ∨ (p4108) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial24796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2584)) ∨ (meaning t m 4108) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory14052 (m.theta 0 1) (m.theta 0 4) (m.theta 0 6)
  exact rule24796 (meaning t m 2584) (meaning t m 4108) (meaning t m 5015) source

theorem rule24797 (p1977 p2027 p2298 p2331 p2462 p3414 p4107 p4154 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4107) ∨ p2462 ∨ (¬ p2331) ∨ (¬ p2298) ∨ (¬ p4154)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (p2462) ∨ (¬ p3414) ∨ (¬ p4107) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial24797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory14053 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule24797 (meaning t m 1977) (meaning t m 2027) (meaning t m 2298) (meaning t m 2331) (meaning t m 2462) (meaning t m 3414) (meaning t m 4107) (meaning t m 4154) source

theorem rule24804 (p2027 p2156 p2187 p2363 p3585 p3954 p4521 p4697 p5160 : Prop) (h : (¬ p2363) ∨ (¬ p2187) ∨ (¬ p3585) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4697) ∨ (¬ p5160) ∨ (¬ p4521)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p4521) ∨ (¬ p4697) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial24804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory14060 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule24804 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3585) (meaning t m 3954) (meaning t m 4521) (meaning t m 4697) (meaning t m 5160) source

theorem rule24806 (p2027 p3425 p3516 p3873 p4324 p5207 : Prop) (h : (¬ p5207) ∨ (¬ p3425) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p3873) ∨ (¬ p3516)) : (p2027) ∨ (¬ p3425) ∨ (¬ p3516) ∨ (¬ p3873) ∨ (¬ p4324) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial24806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory14062 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 7) (m.theta 2 7) (m.theta 7 9)
  exact rule24806 (meaning t m 2027) (meaning t m 3425) (meaning t m 3516) (meaning t m 3873) (meaning t m 4324) (meaning t m 5207) source

theorem rule24807 (p2027 p2299 p2341 p2396 p3238 p3452 p3951 p4948 p5207 : Prop) (h : (¬ p2341) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3452) ∨ (¬ p5207) ∨ (¬ p3238) ∨ (¬ p3951) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3951) ∨ (¬ p4948) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial24807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory14063 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule24807 (meaning t m 2027) (meaning t m 2299) (meaning t m 2341) (meaning t m 2396) (meaning t m 3238) (meaning t m 3452) (meaning t m 3951) (meaning t m 4948) (meaning t m 5207) source

theorem rule24810 (p2027 p2253 p2651 p3591 p4111 p4756 : Prop) (h : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p4756) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3591) ∨ (¬ p4111) ∨ (¬ p4756) := by
  classical
  tauto

theorem initial24810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4756)) := by
  have source := ElevenTheory.theory14066 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4)
  exact rule24810 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 3591) (meaning t m 4111) (meaning t m 4756) source

theorem rule24812 (p2027 p2707 p3540 p3585 p3658 p4727 : Prop) (h : (¬ p3585) ∨ (¬ p4727) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p3658) ∨ (¬ p2707)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial24812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory14068 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule24812 (meaning t m 2027) (meaning t m 2707) (meaning t m 3540) (meaning t m 3585) (meaning t m 3658) (meaning t m 4727) source

theorem rule24814 (p2027 p2253 p2651 p3555 p4111 p4448 : Prop) (h : p2027 ∨ (¬ p2253) ∨ (¬ p3555) ∨ (¬ p4111) ∨ (¬ p2651) ∨ (¬ p4448)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3555) ∨ (¬ p4111) ∨ (¬ p4448) := by
  classical
  tauto

theorem initial24814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4448)) := by
  have source := ElevenTheory.theory14070 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4)
  exact rule24814 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 3555) (meaning t m 4111) (meaning t m 4448) source

theorem rule24816 (p2027 p2331 p2737 p2750 p2811 p4154 : Prop) (h : p2027 ∨ (¬ p4154) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2750) ∨ (¬ p2811) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial24816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory14072 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule24816 (meaning t m 2027) (meaning t m 2331) (meaning t m 2737) (meaning t m 2750) (meaning t m 2811) (meaning t m 4154) source

theorem rule24818 (p1988 p2027 p2253 p2651 p2699 p3506 p3842 p4111 : Prop) (h : p2027 ∨ (¬ p1988) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3842) ∨ (¬ p4111) ∨ p2699 ∨ (¬ p3506)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (p2699) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial24818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory14074 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule24818 (meaning t m 1988) (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2699) (meaning t m 3506) (meaning t m 3842) (meaning t m 4111) source

theorem rule24819 (p2253 p3873 p4117 : Prop) (h : (¬ p3873) ∨ (¬ p2253) ∨ p4117) : (¬ p2253) ∨ (¬ p3873) ∨ (p4117) := by
  classical
  tauto

theorem initial24819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 3873)) ∨ (meaning t m 4117) := by
  have source := ElevenTheory.theory14075 (m.theta 0 1) (m.theta 0 2) (m.theta 0 3)
  exact rule24819 (meaning t m 2253) (meaning t m 3873) (meaning t m 4117) source

theorem rule24820 (p2027 p3461 p3564 p4204 p4322 p4402 p4718 : Prop) (h : p2027 ∨ (¬ p4204) ∨ (¬ p3564) ∨ (¬ p3461) ∨ (¬ p4718) ∨ (¬ p4402) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4204) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial24820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory14076 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule24820 (meaning t m 2027) (meaning t m 3461) (meaning t m 3564) (meaning t m 4204) (meaning t m 4322) (meaning t m 4402) (meaning t m 4718) source

theorem rule24828 (p2027 p2192 p2255 p2946 p3125 p3266 p3297 p3412 p3773 p3848 p4330 : Prop) (h : p2027 ∨ (¬ p3125) ∨ (¬ p2192) ∨ (¬ p3412) ∨ (¬ p3773) ∨ (¬ p2946) ∨ (¬ p2255) ∨ (¬ p4330) ∨ (¬ p3297) ∨ (¬ p3848) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3297) ∨ (¬ p3412) ∨ (¬ p3773) ∨ (¬ p3848) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial24828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory14084 t (m.theta 0 3) (m.theta 0 9) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 9) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24828 (meaning t m 2027) (meaning t m 2192) (meaning t m 2255) (meaning t m 2946) (meaning t m 3125) (meaning t m 3266) (meaning t m 3297) (meaning t m 3412) (meaning t m 3773) (meaning t m 3848) (meaning t m 4330) source

theorem rule24829 (p1999 p2027 p2210 p2699 p2972 p3680 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p1999) ∨ p2027 ∨ (¬ p2972) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p3680)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2972) ∨ (¬ p3680) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial24829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory14085 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule24829 (meaning t m 1999) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2972) (meaning t m 3680) (meaning t m 4191) source

theorem rule24836 (p1997 p2027 p2247 p2499 p2542 p2573 p2688 p3487 p4079 : Prop) (h : (¬ p3487) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2542) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p4079)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2499) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (p2688) ∨ (¬ p3487) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial24836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory14092 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule24836 (meaning t m 1997) (meaning t m 2027) (meaning t m 2247) (meaning t m 2499) (meaning t m 2542) (meaning t m 2573) (meaning t m 2688) (meaning t m 3487) (meaning t m 4079) source

theorem rule24838 (p4524 p4984 p5210 : Prop) (h : (¬ p4984) ∨ (¬ p4524) ∨ p5210) : (¬ p4524) ∨ (¬ p4984) ∨ (p5210) := by
  classical
  tauto

theorem initial24838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4984)) ∨ (meaning t m 5210) := by
  have source := ElevenTheory.theory14094 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 7)
  exact rule24838 (meaning t m 4524) (meaning t m 4984) (meaning t m 5210) source

theorem rule24840 (p1982 p2027 p2253 p2651 p2699 p3189 p3256 p4111 : Prop) (h : p2699 ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4111) ∨ (¬ p1982) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p3256)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial24840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory14096 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule24840 (meaning t m 1982) (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2699) (meaning t m 3189) (meaning t m 3256) (meaning t m 4111) source

theorem rule24842 (p2012 p2027 p2253 p2651 p2699 p3707 p3833 p4111 p4425 : Prop) (h : p2027 ∨ (¬ p4111) ∨ p2699 ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4425) ∨ (¬ p3833) ∨ (¬ p2012) ∨ (¬ p3707)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (p2699) ∨ (¬ p3707) ∨ (¬ p3833) ∨ (¬ p4111) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial24842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3833)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory14098 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 9) (m.theta 9 10)
  exact rule24842 (meaning t m 2012) (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2699) (meaning t m 3707) (meaning t m 3833) (meaning t m 4111) (meaning t m 4425) source

theorem rule24843 (p2027 p2253 p2459 p2651 p3189 p3556 p3692 p4111 p4119 p4524 p4550 : Prop) (h : (¬ p4550) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3556) ∨ (¬ p3189) ∨ (¬ p4111) ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4119) ∨ (¬ p3692) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3189) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p4111) ∨ (¬ p4119) ∨ (¬ p4524) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial24843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory14099 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule24843 (meaning t m 2027) (meaning t m 2253) (meaning t m 2459) (meaning t m 2651) (meaning t m 3189) (meaning t m 3556) (meaning t m 3692) (meaning t m 4111) (meaning t m 4119) (meaning t m 4524) (meaning t m 4550) source

theorem rule24850 (p2027 p2177 p3146 p3919 p4132 p4261 p4288 p4570 : Prop) (h : (¬ p4288) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3919) ∨ (¬ p4132) ∨ (¬ p4570) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p3919) ∨ (¬ p4132) ∨ (¬ p4261) ∨ (¬ p4288) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial24850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory14106 t (m.theta 1 8) (m.theta 3 7) (m.theta 3 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule24850 (meaning t m 2027) (meaning t m 2177) (meaning t m 3146) (meaning t m 3919) (meaning t m 4132) (meaning t m 4261) (meaning t m 4288) (meaning t m 4570) source

theorem rule24851 (p2027 p2177 p2253 p2651 p3027 p3556 p3570 p4111 p4524 p4570 : Prop) (h : p2027 ∨ (¬ p4570) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111) ∨ (¬ p2253) ∨ (¬ p2177) ∨ (¬ p4524) ∨ (¬ p3570) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4111) ∨ (¬ p4524) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial24851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory14107 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24851 (meaning t m 2027) (meaning t m 2177) (meaning t m 2253) (meaning t m 2651) (meaning t m 3027) (meaning t m 3556) (meaning t m 3570) (meaning t m 4111) (meaning t m 4524) (meaning t m 4570) source

theorem rule24853 (p2027 p2253 p2651 p2860 p3027 p3646 p4111 p4244 p4280 p4524 : Prop) (h : (¬ p3027) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2253) ∨ p2027 ∨ (¬ p4280) ∨ (¬ p2860) ∨ (¬ p4524) ∨ (¬ p3646) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2860) ∨ (¬ p3027) ∨ (¬ p3646) ∨ (¬ p4111) ∨ (¬ p4244) ∨ (¬ p4280) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial24853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14109 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7)
  exact rule24853 (meaning t m 2027) (meaning t m 2253) (meaning t m 2651) (meaning t m 2860) (meaning t m 3027) (meaning t m 3646) (meaning t m 4111) (meaning t m 4244) (meaning t m 4280) (meaning t m 4524) source

theorem rule24857 (p2027 p2299 p2588 p2881 p3872 p3958 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p3958) ∨ (¬ p2299) ∨ (¬ p3872) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2881) ∨ (¬ p3872) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial24857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory14113 t (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule24857 (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 2881) (meaning t m 3872) (meaning t m 3958) source

theorem rule24862 (p2027 p2253 p2299 p2651 p3097 p3189 p3646 p4111 p4524 p4550 : Prop) (h : (¬ p3097) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3646) ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4550) ∨ (¬ p4111) ∨ (¬ p3189) ∨ (¬ p2299)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2299) ∨ (¬ p2651) ∨ (¬ p3097) ∨ (¬ p3189) ∨ (¬ p3646) ∨ (¬ p4111) ∨ (¬ p4524) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial24862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory14118 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule24862 (meaning t m 2027) (meaning t m 2253) (meaning t m 2299) (meaning t m 2651) (meaning t m 3097) (meaning t m 3189) (meaning t m 3646) (meaning t m 4111) (meaning t m 4524) (meaning t m 4550) source

theorem rule24866 (p2027 p2881 p3027 p4280 p4360 p4548 : Prop) (h : (¬ p2881) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p4280) ∨ (¬ p4548) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2881) ∨ (¬ p3027) ∨ (¬ p4280) ∨ (¬ p4360) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial24866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory14122 t (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule24866 (meaning t m 2027) (meaning t m 2881) (meaning t m 3027) (meaning t m 4280) (meaning t m 4360) (meaning t m 4548) source

theorem rule24868 (p2027 p2253 p2528 p2651 p3083 p3097 p3646 p4107 p4524 p4669 : Prop) (h : (¬ p3097) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3646) ∨ (¬ p2253) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial24868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory14124 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule24868 (meaning t m 2027) (meaning t m 2253) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3097) (meaning t m 3646) (meaning t m 4107) (meaning t m 4524) (meaning t m 4669) source

theorem rule24871 (p2027 p2427 p2992 p2996 p3699 p4702 : Prop) (h : (¬ p4702) ∨ p2027 ∨ (¬ p3699) ∨ (¬ p2427) ∨ (¬ p2992) ∨ (¬ p2996)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3699) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial24871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory14127 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7)
  exact rule24871 (meaning t m 2027) (meaning t m 2427) (meaning t m 2992) (meaning t m 2996) (meaning t m 3699) (meaning t m 4702) source

theorem rule24873 (p2027 p2274 p2298 p2331 p3414 p4564 : Prop) (h : (¬ p3414) ∨ (¬ p2274) ∨ (¬ p4564) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2298)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial24873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14129 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule24873 (meaning t m 2027) (meaning t m 2274) (meaning t m 2298) (meaning t m 2331) (meaning t m 3414) (meaning t m 4564) source

theorem rule24874 (p2027 p2299 p2608 p3097 p3367 p3641 p3646 p4420 p4524 : Prop) (h : (¬ p3367) ∨ (¬ p2608) ∨ (¬ p4420) ∨ p2027 ∨ (¬ p4524) ∨ (¬ p3646) ∨ (¬ p2299) ∨ (¬ p3097) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2608) ∨ (¬ p3097) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p4420) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial24874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory14130 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule24874 (meaning t m 2027) (meaning t m 2299) (meaning t m 2608) (meaning t m 3097) (meaning t m 3367) (meaning t m 3641) (meaning t m 3646) (meaning t m 4420) (meaning t m 4524) source

theorem rule24875 (p2027 p2274 p2298 p2641 p2996 p3958 p3984 : Prop) (h : p2027 ∨ (¬ p2298) ∨ (¬ p2996) ∨ (¬ p2274) ∨ (¬ p3984) ∨ (¬ p3958) ∨ (¬ p2641)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2298) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3958) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial24875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory14131 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule24875 (meaning t m 2027) (meaning t m 2274) (meaning t m 2298) (meaning t m 2641) (meaning t m 2996) (meaning t m 3958) (meaning t m 3984) source

theorem rule24877 (p2027 p2307 p2962 p3097 p3370 p3758 p4878 : Prop) (h : (¬ p4878) ∨ (¬ p2962) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3370) ∨ (¬ p3097) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3370) ∨ (¬ p3758) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial24877 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory14133 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule24877 (meaning t m 2027) (meaning t m 2307) (meaning t m 2962) (meaning t m 3097) (meaning t m 3370) (meaning t m 3758) (meaning t m 4878) source

theorem rule24878 (p2177 p2318 p3960 p3961 : Prop) (h : (¬ p2318) ∨ (¬ p3961) ∨ (¬ p3960) ∨ (¬ p2177)) : (¬ p2177) ∨ (¬ p2318) ∨ (¬ p3960) ∨ (¬ p3961) := by
  classical
  tauto

theorem initial24878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 3961)) := by
  have source := ElevenTheory.theory14134 (m.theta 0 7) (m.theta 0 8) (m.theta 6 7) (m.theta 7 8)
  exact rule24878 (meaning t m 2177) (meaning t m 2318) (meaning t m 3960) (meaning t m 3961) source

theorem rule24879 (p2027 p2295 p2313 p2651 p3983 p4972 : Prop) (h : (¬ p2295) ∨ (¬ p4972) ∨ p2027 ∨ (¬ p3983) ∨ (¬ p2651) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p3983) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial24879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory14135 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule24879 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2651) (meaning t m 3983) (meaning t m 4972) source

theorem rule24880 (p2027 p2313 p2577 p2743 p3309 p3363 p4752 p4869 : Prop) (h : (¬ p3363) ∨ (¬ p4752) ∨ (¬ p4869) ∨ (¬ p2313) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p2577)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2743) ∨ (¬ p3309) ∨ (¬ p3363) ∨ (¬ p4752) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial24880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory14136 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 6 7)
  exact rule24880 (meaning t m 2027) (meaning t m 2313) (meaning t m 2577) (meaning t m 2743) (meaning t m 3309) (meaning t m 3363) (meaning t m 4752) (meaning t m 4869) source

theorem rule24882 (p2027 p2313 p2427 p4110 p4140 p4486 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p4486) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4140)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2427) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial24882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory14138 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule24882 (meaning t m 2027) (meaning t m 2313) (meaning t m 2427) (meaning t m 4110) (meaning t m 4140) (meaning t m 4486) source

theorem rule24883 (p2264 p3644 p3740 : Prop) (h : (¬ p3644) ∨ (¬ p3740) ∨ (¬ p2264)) : (¬ p2264) ∨ (¬ p3644) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial24883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory14139 (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule24883 (meaning t m 2264) (meaning t m 3644) (meaning t m 3740) source

theorem rule24885 (p2027 p2249 p2295 p2313 p2641 p3983 : Prop) (h : (¬ p2313) ∨ (¬ p3983) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2641) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial24885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory14141 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7)
  exact rule24885 (meaning t m 2027) (meaning t m 2249) (meaning t m 2295) (meaning t m 2313) (meaning t m 2641) (meaning t m 3983) source

theorem rule24887 (p2027 p2387 p2598 p2742 p2778 p3063 p4752 p4759 : Prop) (h : (¬ p2778) ∨ (¬ p4752) ∨ (¬ p4759) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2387) ∨ (¬ p2742) ∨ (¬ p3063)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2598) ∨ (¬ p2742) ∨ (¬ p2778) ∨ (¬ p3063) ∨ (¬ p4752) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial24887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory14143 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 6 8)
  exact rule24887 (meaning t m 2027) (meaning t m 2387) (meaning t m 2598) (meaning t m 2742) (meaning t m 2778) (meaning t m 3063) (meaning t m 4752) (meaning t m 4759) source

theorem rule24889 (p2027 p2249 p3038 p3414 p3527 p3553 : Prop) (h : (¬ p3414) ∨ (¬ p3038) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2249) ∨ (¬ p3038) ∨ (¬ p3414) ∨ (¬ p3527) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial24889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory14145 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8)
  exact rule24889 (meaning t m 2027) (meaning t m 2249) (meaning t m 3038) (meaning t m 3414) (meaning t m 3527) (meaning t m 3553) source

theorem rule24892 (p2027 p2307 p3172 p3568 p3987 p4153 p5062 : Prop) (h : p2027 ∨ (¬ p3987) ∨ (¬ p5062) ∨ (¬ p3172) ∨ (¬ p2307) ∨ (¬ p4153) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2307) ∨ (¬ p3172) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4153) ∨ (¬ p5062) := by
  classical
  tauto

theorem initial24892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 5062)) := by
  have source := ElevenTheory.theory14148 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule24892 (meaning t m 2027) (meaning t m 2307) (meaning t m 3172) (meaning t m 3568) (meaning t m 3987) (meaning t m 4153) (meaning t m 5062) source

theorem rule24894 (p2027 p2598 p2797 p2963 p4236 p4752 : Prop) (h : (¬ p2598) ∨ p2027 ∨ (¬ p4752) ∨ (¬ p4236) ∨ (¬ p2963) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p4236) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial24894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14150 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule24894 (meaning t m 2027) (meaning t m 2598) (meaning t m 2797) (meaning t m 2963) (meaning t m 4236) (meaning t m 4752) source

theorem rule24895 (p2027 p2249 p2655 p2992 p3115 p3904 p4032 : Prop) (h : (¬ p2249) ∨ (¬ p4032) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p3904) ∨ (¬ p3115) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2655) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3904) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial24895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory14151 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9)
  exact rule24895 (meaning t m 2027) (meaning t m 2249) (meaning t m 2655) (meaning t m 2992) (meaning t m 3115) (meaning t m 3904) (meaning t m 4032) source

theorem rule24897 (p2027 p2249 p2655 p2901 p2992 p3556 p3904 : Prop) (h : (¬ p2655) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p2249) ∨ (¬ p2992) ∨ p2027) : (p2027) ∨ (¬ p2249) ∨ (¬ p2655) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3556) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial24897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory14153 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7)
  exact rule24897 (meaning t m 2027) (meaning t m 2249) (meaning t m 2655) (meaning t m 2901) (meaning t m 2992) (meaning t m 3556) (meaning t m 3904) source

theorem rule24898 (p2027 p2249 p2963 p3309 p3568 p4759 : Prop) (h : (¬ p3568) ∨ p2027 ∨ (¬ p4759) ∨ (¬ p2249) ∨ (¬ p2963) ∨ (¬ p3309)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2963) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial24898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory14154 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule24898 (meaning t m 2027) (meaning t m 2249) (meaning t m 2963) (meaning t m 3309) (meaning t m 3568) (meaning t m 4759) source

theorem rule24899 (p1994 p2027 p2630 p3166 p3292 p3871 p3877 : Prop) (h : p3871 ∨ (¬ p3292) ∨ (¬ p2630) ∨ (¬ p3877) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3166)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (p3871) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial24899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3292)) ∨ (meaning t m 3871) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory14155 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 3 9)
  exact rule24899 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 3166) (meaning t m 3292) (meaning t m 3871) (meaning t m 3877) source

theorem rule24902 (p2027 p2341 p2449 p2499 p3452 p3553 p4137 p4625 p5207 : Prop) (h : (¬ p5207) ∨ p2027 ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p2341) ∨ (¬ p2449) ∨ (¬ p3553) ∨ (¬ p4137) ∨ (¬ p4625)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2449) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3553) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial24902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory14158 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule24902 (meaning t m 2027) (meaning t m 2341) (meaning t m 2449) (meaning t m 2499) (meaning t m 3452) (meaning t m 3553) (meaning t m 4137) (meaning t m 4625) (meaning t m 5207) source

theorem rule24907 (p2027 p2192 p2249 p2952 p3952 p4365 : Prop) (h : (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4365) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p2249)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2249) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial24907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory14163 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule24907 (meaning t m 2027) (meaning t m 2192) (meaning t m 2249) (meaning t m 2952) (meaning t m 3952) (meaning t m 4365) source

theorem rule24908 (p2027 p2383 p2528 p3693 p3946 p4134 p4171 : Prop) (h : (¬ p2528) ∨ (¬ p2383) ∨ (¬ p4134) ∨ (¬ p3693) ∨ (¬ p4171) ∨ p2027 ∨ (¬ p3946)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2528) ∨ (¬ p3693) ∨ (¬ p3946) ∨ (¬ p4134) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial24908 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory14164 t (m.theta 0 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule24908 (meaning t m 2027) (meaning t m 2383) (meaning t m 2528) (meaning t m 3693) (meaning t m 3946) (meaning t m 4134) (meaning t m 4171) source

theorem rule24911 (p2027 p2249 p2406 p2440 p2657 p4281 : Prop) (h : (¬ p2249) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2657) ∨ (¬ p2440) ∨ (¬ p4281)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial24911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory14167 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule24911 (meaning t m 2027) (meaning t m 2249) (meaning t m 2406) (meaning t m 2440) (meaning t m 2657) (meaning t m 4281) source

theorem rule24912 (p2027 p2192 p2589 p3948 p4110 p5191 : Prop) (h : (¬ p4110) ∨ (¬ p3948) ∨ (¬ p5191) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p2589)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2589) ∨ (¬ p3948) ∨ (¬ p4110) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial24912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory14168 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule24912 (meaning t m 2027) (meaning t m 2192) (meaning t m 2589) (meaning t m 3948) (meaning t m 4110) (meaning t m 5191) source

theorem rule24913 (p3193 p3343 p3487 : Prop) (h : (¬ p3487) ∨ (¬ p3193) ∨ (¬ p3343)) : (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3487) := by
  classical
  tauto

theorem initial24913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3487)) := by
  have source := ElevenTheory.theory14169 (m.theta 1 4) (m.theta 3 4) (m.theta 4 9)
  exact rule24913 (meaning t m 3193) (meaning t m 3343) (meaning t m 3487) source

theorem rule24914 (p2027 p2249 p2499 p2657 p3189 p3487 p3506 p4137 p4444 p4604 p5111 : Prop) (h : (¬ p3487) ∨ (¬ p5111) ∨ (¬ p2499) ∨ (¬ p2249) ∨ (¬ p3506) ∨ (¬ p2657) ∨ (¬ p4604) ∨ (¬ p4444) ∨ (¬ p4137) ∨ (¬ p3189) ∨ p2027) : (p2027) ∨ (¬ p2249) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3189) ∨ (¬ p3487) ∨ (¬ p3506) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial24914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory14170 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24914 (meaning t m 2027) (meaning t m 2249) (meaning t m 2499) (meaning t m 2657) (meaning t m 3189) (meaning t m 3487) (meaning t m 3506) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) (meaning t m 5111) source

theorem rule24916 (p2027 p2341 p2499 p3246 p3452 p3570 p4137 p4443 p4604 p5207 : Prop) (h : (¬ p2341) ∨ (¬ p3570) ∨ (¬ p2499) ∨ (¬ p4137) ∨ (¬ p5207) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p4443) ∨ (¬ p4604) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2499) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p3570) ∨ (¬ p4137) ∨ (¬ p4443) ∨ (¬ p4604) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial24916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory14172 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24916 (meaning t m 2027) (meaning t m 2341) (meaning t m 2499) (meaning t m 3246) (meaning t m 3452) (meaning t m 3570) (meaning t m 4137) (meaning t m 4443) (meaning t m 4604) (meaning t m 5207) source

theorem rule24920 (p2027 p2192 p3125 p4037 p4153 p4960 : Prop) (h : (¬ p3125) ∨ (¬ p4037) ∨ (¬ p2192) ∨ (¬ p4960) ∨ (¬ p4153) ∨ p2027) : (p2027) ∨ (¬ p2192) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4153) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial24920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory14176 t (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule24920 (meaning t m 2027) (meaning t m 2192) (meaning t m 3125) (meaning t m 4037) (meaning t m 4153) (meaning t m 4960) source

theorem rule24922 (p2027 p2264 p3941 p3961 p4851 p5590 : Prop) (h : (¬ p4851) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p5590) ∨ (¬ p3961) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3941) ∨ (¬ p3961) ∨ (¬ p4851) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial24922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4851)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory14178 t (m.theta 0 7) (m.theta 0 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10)
  exact rule24922 (meaning t m 2027) (meaning t m 2264) (meaning t m 3941) (meaning t m 3961) (meaning t m 4851) (meaning t m 5590) source

theorem rule24923 (p2027 p2311 p2427 p2881 p3551 p4198 p4533 : Prop) (h : p2027 ∨ (¬ p2311) ∨ (¬ p4533) ∨ (¬ p3551) ∨ (¬ p4198) ∨ (¬ p2427) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p4198) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial24923 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory14179 t (m.theta 0 5) (m.theta 0 6) (m.theta 0 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule24923 (meaning t m 2027) (meaning t m 2311) (meaning t m 2427) (meaning t m 2881) (meaning t m 3551) (meaning t m 4198) (meaning t m 4533) source

theorem rule24924 (p3644 p3920 p3956 p4138 : Prop) (h : (¬ p3920) ∨ (¬ p4138) ∨ (¬ p3956) ∨ p3644) : (p3644) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial24924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3644) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory14180 (m.theta 4 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule24924 (meaning t m 3644) (meaning t m 3920) (meaning t m 3956) (meaning t m 4138) source

theorem rule24926 (p2027 p2136 p2598 p2619 p4120 p4313 p4752 : Prop) (h : p2027 ∨ (¬ p4120) ∨ (¬ p2619) ∨ (¬ p2136) ∨ (¬ p4313) ∨ (¬ p4752) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2598) ∨ (¬ p2619) ∨ (¬ p4120) ∨ (¬ p4313) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial24926 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14182 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 5 8)
  exact rule24926 (meaning t m 2027) (meaning t m 2136) (meaning t m 2598) (meaning t m 2619) (meaning t m 4120) (meaning t m 4313) (meaning t m 4752) source

theorem rule24928 (p1990 p2027 p2169 p2220 p2284 p2313 p2598 p2778 p2811 p2958 p3309 p3497 p3923 p4752 : Prop) (h : (¬ p2284) ∨ (¬ p1990) ∨ (¬ p3497) ∨ p2169 ∨ (¬ p2313) ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p2811) ∨ (¬ p3923) ∨ (¬ p2598) ∨ (¬ p4752) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p2778)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2778) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3309) ∨ (¬ p3497) ∨ (¬ p3923) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial24928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14184 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule24928 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2220) (meaning t m 2284) (meaning t m 2313) (meaning t m 2598) (meaning t m 2778) (meaning t m 2811) (meaning t m 2958) (meaning t m 3309) (meaning t m 3497) (meaning t m 3923) (meaning t m 4752) source

theorem rule24933 (p2307 p3325 p3743 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p3743) ∨ (¬ p2307) ∨ (¬ p3325)) : (¬ p2307) ∨ (¬ p3325) ∨ (¬ p3743) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial24933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory14189 (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule24933 (meaning t m 2307) (meaning t m 3325) (meaning t m 3743) (meaning t m 3989) source

theorem rule24935 (p2156 p3370 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p3370) ∨ (¬ p2156)) : (¬ p2156) ∨ (¬ p3370) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial24935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory14191 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6)
  exact rule24935 (meaning t m 2156) (meaning t m 3370) (meaning t m 4173) source

theorem rule24938 (p2027 p2264 p2928 p3580 p3644 p4811 : Prop) (h : (¬ p4811) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p3644) ∨ (¬ p3580) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2928) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial24938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory14194 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule24938 (meaning t m 2027) (meaning t m 2264) (meaning t m 2928) (meaning t m 3580) (meaning t m 3644) (meaning t m 4811) source

theorem rule24942 (p1987 p2027 p2323 p3027 p3166 p3572 p4360 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p4360) ∨ (¬ p3572) ∨ (¬ p3027) ∨ (¬ p1987) ∨ (¬ p3166)) : (¬ p1987) ∨ (p2027) ∨ (p2323) ∨ (¬ p3027) ∨ (¬ p3166) ∨ (¬ p3572) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial24942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory14198 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8)
  exact rule24942 (meaning t m 1987) (meaning t m 2027) (meaning t m 2323) (meaning t m 3027) (meaning t m 3166) (meaning t m 3572) (meaning t m 4360) source

theorem rule24946 (p2027 p2499 p2761 p3452 p3516 p4137 p4444 p4604 p5207 : Prop) (h : (¬ p4604) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p5207) ∨ (¬ p4444) ∨ (¬ p3452) ∨ (¬ p2499) ∨ (¬ p3516)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3452) ∨ (¬ p3516) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5207) := by
  classical
  tauto

theorem initial24946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5207)) := by
  have source := ElevenTheory.theory14202 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24946 (meaning t m 2027) (meaning t m 2499) (meaning t m 2761) (meaning t m 3452) (meaning t m 3516) (meaning t m 4137) (meaning t m 4444) (meaning t m 4604) (meaning t m 5207) source

theorem rule24947 (p1988 p2027 p2202 p2427 p2459 p2881 p3266 : Prop) (h : (¬ p2459) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p1988) ∨ p2202 ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial24947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory14203 t (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule24947 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2459) (meaning t m 2881) (meaning t m 3266) source

theorem rule24953 (p2727 p4121 p4360 : Prop) (h : (¬ p4360) ∨ (¬ p2727) ∨ (¬ p4121)) : (¬ p2727) ∨ (¬ p4121) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial24953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory14209 (m.theta 1 3) (m.theta 3 4) (m.theta 3 8)
  exact rule24953 (meaning t m 2727) (meaning t m 4121) (meaning t m 4360) source

theorem rule24954 (p2027 p2247 p2761 p3516 p4037 p4154 p4444 p4521 p4604 p4988 : Prop) (h : (¬ p4154) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p4037) ∨ (¬ p3516) ∨ (¬ p4444) ∨ (¬ p2761) ∨ (¬ p4521) ∨ (¬ p4988)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4444) ∨ (¬ p4521) ∨ (¬ p4604) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial24954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory14210 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24954 (meaning t m 2027) (meaning t m 2247) (meaning t m 2761) (meaning t m 3516) (meaning t m 4037) (meaning t m 4154) (meaning t m 4444) (meaning t m 4521) (meaning t m 4604) (meaning t m 4988) source

theorem rule24956 (p1997 p2027 p2114 p2542 p2598 p2737 p3365 p3683 : Prop) (h : p2027 ∨ (¬ p3683) ∨ (¬ p1997) ∨ (¬ p2542) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3365) ∨ p2114) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2542) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3683) := by
  classical
  tauto

theorem initial24956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3683)) := by
  have source := ElevenTheory.theory14212 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule24956 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2542) (meaning t m 2598) (meaning t m 2737) (meaning t m 3365) (meaning t m 3683) source

theorem rule24958 (p2027 p2589 p3347 p3399 p3631 p3692 p3880 p3950 p3954 p5216 : Prop) (h : (¬ p3950) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3692) ∨ (¬ p5216) ∨ (¬ p3399)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14214 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24958 (meaning t m 2027) (meaning t m 2589) (meaning t m 3347) (meaning t m 3399) (meaning t m 3631) (meaning t m 3692) (meaning t m 3880) (meaning t m 3950) (meaning t m 3954) (meaning t m 5216) source

theorem rule24959 (p2027 p3204 p3266 p3399 p3631 p3946 p3950 p3954 p4191 p4870 : Prop) (h : (¬ p3204) ∨ (¬ p3946) ∨ (¬ p4870) ∨ (¬ p3954) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3950) ∨ (¬ p3266) ∨ (¬ p4191)) : (p2027) ∨ (¬ p3204) ∨ (¬ p3266) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3946) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4191) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial24959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory14215 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule24959 (meaning t m 2027) (meaning t m 3204) (meaning t m 3266) (meaning t m 3399) (meaning t m 3631) (meaning t m 3946) (meaning t m 3950) (meaning t m 3954) (meaning t m 4191) (meaning t m 4870) source

theorem rule24960 (p1991 p2027 p2177 p2274 p2765 p3414 p3553 : Prop) (h : (¬ p1991) ∨ (¬ p3553) ∨ (¬ p2274) ∨ p2027 ∨ p2765 ∨ (¬ p2177) ∨ (¬ p3414)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial24960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory14216 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule24960 (meaning t m 1991) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2765) (meaning t m 3414) (meaning t m 3553) source

theorem rule24963 (p2027 p2743 p2922 p3363 p3540 p3541 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p3541) ∨ (¬ p3363) ∨ (¬ p2922) ∨ (¬ p3540) ∨ p2027 ∨ (¬ p2743)) : (p2027) ∨ (¬ p2743) ∨ (¬ p2922) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3541) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial24963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory14219 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 7)
  exact rule24963 (meaning t m 2027) (meaning t m 2743) (meaning t m 2922) (meaning t m 3363) (meaning t m 3540) (meaning t m 3541) (meaning t m 4752) source

theorem rule24965 (p2027 p2192 p2751 p3952 p4315 p4365 : Prop) (h : (¬ p3952) ∨ (¬ p2751) ∨ (¬ p2192) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p4365)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2751) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial24965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory14221 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule24965 (meaning t m 2027) (meaning t m 2192) (meaning t m 2751) (meaning t m 3952) (meaning t m 4315) (meaning t m 4365) source

theorem rule24969 (p1983 p2027 p2110 p2138 p3246 p3474 p3998 p4119 p5568 : Prop) (h : p3474 ∨ (¬ p2110) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p2138) ∨ (¬ p1983) ∨ (¬ p3246) ∨ (¬ p4119) ∨ (¬ p3998)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2110) ∨ (¬ p2138) ∨ (¬ p3246) ∨ (p3474) ∨ (¬ p3998) ∨ (¬ p4119) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial24969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2110)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3246)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory14225 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10)
  exact rule24969 (meaning t m 1983) (meaning t m 2027) (meaning t m 2110) (meaning t m 2138) (meaning t m 3246) (meaning t m 3474) (meaning t m 3998) (meaning t m 4119) (meaning t m 5568) source

theorem rule24971 (p2027 p2579 p3347 p3399 p3631 p3950 p3954 p3956 p4347 p5216 : Prop) (h : (¬ p2579) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p5216) ∨ (¬ p3954) ∨ (¬ p3347) ∨ (¬ p3950) ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial24971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory14227 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24971 (meaning t m 2027) (meaning t m 2579) (meaning t m 3347) (meaning t m 3399) (meaning t m 3631) (meaning t m 3950) (meaning t m 3954) (meaning t m 3956) (meaning t m 4347) (meaning t m 5216) source

theorem rule24972 (p2027 p2274 p2573 p3540 p3921 p3958 : Prop) (h : (¬ p3921) ∨ (¬ p3540) ∨ (¬ p3958) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial24972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory14228 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule24972 (meaning t m 2027) (meaning t m 2274) (meaning t m 2573) (meaning t m 3540) (meaning t m 3921) (meaning t m 3958) source

theorem rule24973 (p2027 p3399 p3631 p3645 p3646 p3950 p3954 p3989 p4347 p4877 : Prop) (h : (¬ p3399) ∨ (¬ p3646) ∨ (¬ p3631) ∨ (¬ p3645) ∨ (¬ p4877) ∨ (¬ p3954) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3950)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p3989) ∨ (¬ p4347) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial24973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory14229 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule24973 (meaning t m 2027) (meaning t m 3399) (meaning t m 3631) (meaning t m 3645) (meaning t m 3646) (meaning t m 3950) (meaning t m 3954) (meaning t m 3989) (meaning t m 4347) (meaning t m 4877) source

theorem rule24974 (p2027 p2241 p2373 p2449 p3027 p3951 p4120 p4524 p4948 : Prop) (h : (¬ p3951) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p4524) ∨ (¬ p2373) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2373) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3951) ∨ (¬ p4120) ∨ (¬ p4524) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial24974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory14230 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 7 9)
  exact rule24974 (meaning t m 2027) (meaning t m 2241) (meaning t m 2373) (meaning t m 2449) (meaning t m 3027) (meaning t m 3951) (meaning t m 4120) (meaning t m 4524) (meaning t m 4948) source

theorem rule24975 (p2027 p2241 p3027 p3692 p3931 p4120 p4444 p4524 p4826 : Prop) (h : (¬ p4120) ∨ (¬ p3931) ∨ (¬ p4826) ∨ (¬ p3692) ∨ (¬ p3027) ∨ (¬ p4524) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4444)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3692) ∨ (¬ p3931) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4524) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial24975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory14231 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule24975 (meaning t m 2027) (meaning t m 2241) (meaning t m 3027) (meaning t m 3692) (meaning t m 3931) (meaning t m 4120) (meaning t m 4444) (meaning t m 4524) (meaning t m 4826) source

theorem rule24982 (p1999 p2027 p2169 p2553 p3319 p3549 p3956 : Prop) (h : (¬ p3549) ∨ (¬ p1999) ∨ (¬ p3319) ∨ (¬ p3956) ∨ p2027 ∨ p2169 ∨ (¬ p2553)) : (¬ p1999) ∨ (p2027) ∨ (p2169) ∨ (¬ p2553) ∨ (¬ p3319) ∨ (¬ p3549) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial24982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory14238 t (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule24982 (meaning t m 1999) (meaning t m 2027) (meaning t m 2169) (meaning t m 2553) (meaning t m 3319) (meaning t m 3549) (meaning t m 3956) source

theorem rule24987 (p2187 p3125 p3322 : Prop) (h : (¬ p3322) ∨ (¬ p3125) ∨ p2187) : (p2187) ∨ (¬ p3125) ∨ (¬ p3322) := by
  classical
  tauto

theorem initial24987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2187) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3322)) := by
  have source := ElevenTheory.theory14243 (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule24987 (meaning t m 2187) (meaning t m 3125) (meaning t m 3322) source

theorem rule24998 (p1990 p3128 p4137 p4718 : Prop) (h : (¬ p1990) ∨ p3128 ∨ (¬ p4137) ∨ p4718) : (¬ p1990) ∨ (p3128) ∨ (¬ p4137) ∨ (p4718) := by
  classical
  tauto

theorem initial24998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4137)) ∨ (meaning t m 4718) := by
  have source := ElevenTheory.theory14254 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule24998 (meaning t m 1990) (meaning t m 3128) (meaning t m 4137) (meaning t m 4718) source

theorem rule24999 (p3575 p4372 p5503 : Prop) (h : (¬ p3575) ∨ (¬ p5503) ∨ p4372) : (¬ p3575) ∨ (p4372) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial24999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3575)) ∨ (meaning t m 4372) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory14255 (m.theta 0 7) (m.theta 4 7) (m.theta 7 10)
  exact rule24999 (meaning t m 3575) (meaning t m 4372) (meaning t m 5503) source

theorem rule25001 (p2027 p2493 p2579 p2608 p4108 p4376 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p4108)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial25001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory14257 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 6)
  exact rule25001 (meaning t m 2027) (meaning t m 2493) (meaning t m 2579) (meaning t m 2608) (meaning t m 4108) (meaning t m 4376) source

theorem rule25003 (p1991 p2027 p2657 p3527 p3623 p3644 p3742 : Prop) (h : (¬ p3742) ∨ (¬ p1991) ∨ (¬ p3644) ∨ (¬ p2657) ∨ p2027 ∨ p3623 ∨ (¬ p3527)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (¬ p3527) ∨ (p3623) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial25003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3527)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory14259 t (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule25003 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 3527) (meaning t m 3623) (meaning t m 3644) (meaning t m 3742) source

theorem rule25006 (p2274 p3549 p4516 : Prop) (h : (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4516)) : (¬ p2274) ∨ (¬ p3549) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial25006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory14262 (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule25006 (meaning t m 2274) (meaning t m 3549) (meaning t m 4516) source

theorem rule25008 (p2027 p2249 p2951 p2963 p2992 p3276 p3355 p3904 p3922 p3923 p5123 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p3355) ∨ (¬ p3904) ∨ (¬ p2992) ∨ (¬ p2951) ∨ (¬ p3276) ∨ (¬ p3922) ∨ p2027 ∨ (¬ p2249) ∨ (¬ p5123) ∨ (¬ p3923) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3904) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory14264 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25008 (meaning t m 2027) (meaning t m 2249) (meaning t m 2951) (meaning t m 2963) (meaning t m 2992) (meaning t m 3276) (meaning t m 3355) (meaning t m 3904) (meaning t m 3922) (meaning t m 3923) (meaning t m 5123) (meaning t m 5580) source

theorem rule25009 (p2027 p2220 p2249 p2951 p2963 p2992 p3922 p3969 p4026 p4191 p5119 : Prop) (h : p2027 ∨ (¬ p4026) ∨ (¬ p2963) ∨ (¬ p4191) ∨ (¬ p3922) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p2220) ∨ (¬ p3969) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2249) ∨ (¬ p2951) ∨ (¬ p2963) ∨ (¬ p2992) ∨ (¬ p3922) ∨ (¬ p3969) ∨ (¬ p4026) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial25009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory14265 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule25009 (meaning t m 2027) (meaning t m 2220) (meaning t m 2249) (meaning t m 2951) (meaning t m 2963) (meaning t m 2992) (meaning t m 3922) (meaning t m 3969) (meaning t m 4026) (meaning t m 4191) (meaning t m 5119) source

theorem rule25014 (p2010 p2027 p2449 p2545 p2657 p2807 p4278 : Prop) (h : p2027 ∨ (¬ p2010) ∨ p2545 ∨ (¬ p2449) ∨ (¬ p4278) ∨ (¬ p2657) ∨ (¬ p2807)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2449) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial25014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory14270 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule25014 (meaning t m 2010) (meaning t m 2027) (meaning t m 2449) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 4278) source

theorem rule25015 (p1981 p2027 p2233 p2307 p2510 p2528 p2584 p2588 p4347 : Prop) (h : (¬ p2588) ∨ p2233 ∨ (¬ p1981) ∨ (¬ p2584) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2510) ∨ (¬ p2528)) : (¬ p1981) ∨ (p2027) ∨ (p2233) ∨ (¬ p2307) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial25015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory14271 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule25015 (meaning t m 1981) (meaning t m 2027) (meaning t m 2233) (meaning t m 2307) (meaning t m 2510) (meaning t m 2528) (meaning t m 2584) (meaning t m 2588) (meaning t m 4347) source

theorem rule25016 (p2027 p3136 p3343 p3364 p4704 p5160 : Prop) (h : (¬ p4704) ∨ (¬ p3364) ∨ (¬ p3343) ∨ p2027 ∨ (¬ p5160) ∨ (¬ p3136)) : (p2027) ∨ (¬ p3136) ∨ (¬ p3343) ∨ (¬ p3364) ∨ (¬ p4704) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial25016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory14272 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 9)
  exact rule25016 (meaning t m 2027) (meaning t m 3136) (meaning t m 3343) (meaning t m 3364) (meaning t m 4704) (meaning t m 5160) source

theorem rule25017 (p2027 p2177 p2274 p3546 p3551 p3922 p4105 p4564 : Prop) (h : (¬ p3922) ∨ p2027 ∨ (¬ p3546) ∨ (¬ p4105) ∨ (¬ p2274) ∨ (¬ p4564) ∨ (¬ p2177) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3546) ∨ (¬ p3551) ∨ (¬ p3922) ∨ (¬ p4105) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial25017 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory14273 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule25017 (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 3546) (meaning t m 3551) (meaning t m 3922) (meaning t m 4105) (meaning t m 4564) source

theorem rule25018 (p2027 p2657 p2727 p3039 p3266 p3286 p3817 p4191 p4450 p4623 p4952 p5175 : Prop) (h : (¬ p3286) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4450) ∨ (¬ p4952) ∨ (¬ p3039) ∨ (¬ p4191) ∨ (¬ p3266) ∨ (¬ p5175) ∨ (¬ p4623) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3039) ∨ (¬ p3266) ∨ (¬ p3286) ∨ (¬ p3817) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p4623) ∨ (¬ p4952) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial25018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3039)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4623)) ∨ (¬ (meaning t m 4952)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory14274 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule25018 (meaning t m 2027) (meaning t m 2657) (meaning t m 2727) (meaning t m 3039) (meaning t m 3266) (meaning t m 3286) (meaning t m 3817) (meaning t m 4191) (meaning t m 4450) (meaning t m 4623) (meaning t m 4952) (meaning t m 5175) source

theorem rule25020 (p2027 p2249 p2891 p2952 p4320 p4365 : Prop) (h : (¬ p2952) ∨ (¬ p2891) ∨ (¬ p2249) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p4365)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2891) ∨ (¬ p2952) ∨ (¬ p4320) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial25020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory14276 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule25020 (meaning t m 2027) (meaning t m 2249) (meaning t m 2891) (meaning t m 2952) (meaning t m 4320) (meaning t m 4365) source

theorem rule25025 (p2027 p2249 p2449 p3027 p3821 p4849 : Prop) (h : (¬ p4849) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p2249)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3821) ∨ (¬ p4849) := by
  classical
  tauto

theorem initial25025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4849)) := by
  have source := ElevenTheory.theory14281 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9)
  exact rule25025 (meaning t m 2027) (meaning t m 2249) (meaning t m 2449) (meaning t m 3027) (meaning t m 3821) (meaning t m 4849) source

theorem rule25026 (p2027 p2274 p3422 p3876 p3921 p3958 : Prop) (h : (¬ p3422) ∨ (¬ p3958) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3921) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2274) ∨ (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3921) ∨ (¬ p3958) := by
  classical
  tauto

theorem initial25026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 3958)) := by
  have source := ElevenTheory.theory14282 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7)
  exact rule25026 (meaning t m 2027) (meaning t m 2274) (meaning t m 3422) (meaning t m 3876) (meaning t m 3921) (meaning t m 3958) source

theorem rule25027 (p2027 p2274 p2396 p3581 p3958 p4278 : Prop) (h : (¬ p3958) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3581) ∨ (¬ p2396) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3581) ∨ (¬ p3958) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial25027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory14283 t (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule25027 (meaning t m 2027) (meaning t m 2274) (meaning t m 2396) (meaning t m 3581) (meaning t m 3958) (meaning t m 4278) source

theorem rule25032 (p3958 p4390 p4889 : Prop) (h : (¬ p3958) ∨ (¬ p4390) ∨ p4889) : (¬ p3958) ∨ (¬ p4390) ∨ (p4889) := by
  classical
  tauto

theorem initial25032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4390)) ∨ (meaning t m 4889) := by
  have source := ElevenTheory.theory14288 t (m.theta 2 6) (m.theta 4 6) (m.theta 5 6)
  exact rule25032 (meaning t m 3958) (meaning t m 4390) (meaning t m 4889) source

theorem rule25034 (p2027 p2191 p2249 p2417 p2656 p2727 p2952 p3389 p3692 p3950 p4282 : Prop) (h : (¬ p2727) ∨ (¬ p3389) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2417) ∨ (¬ p2249) ∨ (¬ p3950) ∨ (¬ p2656) ∨ (¬ p4282) ∨ (¬ p2191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2249) ∨ (¬ p2417) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3389) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial25034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory14290 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25034 (meaning t m 2027) (meaning t m 2191) (meaning t m 2249) (meaning t m 2417) (meaning t m 2656) (meaning t m 2727) (meaning t m 2952) (meaning t m 3389) (meaning t m 3692) (meaning t m 3950) (meaning t m 4282) source

theorem rule25035 (p2027 p2249 p2417 p2656 p2727 p2952 p3389 p3497 p3692 p3950 : Prop) (h : (¬ p2727) ∨ (¬ p3389) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p2417) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p3950) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2417) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3389) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950) := by
  classical
  tauto

theorem initial25035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) := by
  have source := ElevenTheory.theory14291 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25035 (meaning t m 2027) (meaning t m 2249) (meaning t m 2417) (meaning t m 2656) (meaning t m 2727) (meaning t m 2952) (meaning t m 3389) (meaning t m 3497) (meaning t m 3692) (meaning t m 3950) source

theorem rule25038 (p2132 p2598 p3582 : Prop) (h : (¬ p3582) ∨ (¬ p2598) ∨ p2132) : (p2132) ∨ (¬ p2598) ∨ (¬ p3582) := by
  classical
  tauto

theorem initial25038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2132) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3582)) := by
  have source := ElevenTheory.theory14294 (m.theta 0 2) (m.theta 2 4) (m.theta 2 5)
  exact rule25038 (meaning t m 2132) (meaning t m 2598) (meaning t m 3582) source

end SunPrize.SMT
