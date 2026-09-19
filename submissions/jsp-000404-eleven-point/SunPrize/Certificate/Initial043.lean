import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory027
import SunPrize.Certificate.Theory028
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule19519 (p2001 p2027 p2114 p2619 p3830 p3954 p4385 p4387 : Prop) (h : (¬ p4387) ∨ p2114 ∨ (¬ p3830) ∨ (¬ p2619) ∨ (¬ p2001) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p3954)) : (¬ p2001) ∨ (p2027) ∨ (p2114) ∨ (¬ p2619) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p4387) := by
  classical
  tauto

theorem initial19519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4387)) := by
  have source := ElevenTheory.theory8775 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 5) (m.theta 5 8) (m.theta 5 9)
  exact rule19519 (meaning t m 2001) (meaning t m 2027) (meaning t m 2114) (meaning t m 2619) (meaning t m 3830) (meaning t m 3954) (meaning t m 4385) (meaning t m 4387) source

theorem rule19520 (p1988 p2027 p2122 p2396 p2611 p2761 p2774 : Prop) (h : (¬ p2774) ∨ p2611 ∨ (¬ p2122) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (p2611) ∨ (¬ p2761) ∨ (¬ p2774) := by
  classical
  tauto

theorem initial19520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2774)) := by
  have source := ElevenTheory.theory8776 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19520 (meaning t m 1988) (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2611) (meaning t m 2761) (meaning t m 2774) source

theorem rule19522 (p1984 p2027 p2766 p3266 p3817 p4366 p4381 : Prop) (h : (¬ p1984) ∨ (¬ p3266) ∨ p2027 ∨ p2766 ∨ (¬ p4366) ∨ (¬ p3817) ∨ (¬ p4381)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial19522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory8778 t (m.theta 0 1) (m.theta 1 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19522 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3817) (meaning t m 4366) (meaning t m 4381) source

theorem rule19524 (p1975 p2295 p3818 p4761 : Prop) (h : (¬ p1975) ∨ p3818 ∨ (¬ p2295) ∨ p4761) : (¬ p1975) ∨ (¬ p2295) ∨ (p3818) ∨ (p4761) := by
  classical
  tauto

theorem initial19524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 3818) ∨ (meaning t m 4761) := by
  have source := ElevenTheory.theory8780 t (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule19524 (meaning t m 1975) (meaning t m 2295) (meaning t m 3818) (meaning t m 4761) source

theorem rule19531 (p1998 p2027 p2114 p2177 p2274 p2839 p2860 : Prop) (h : (¬ p2274) ∨ (¬ p2177) ∨ p2114 ∨ p2027 ∨ (¬ p2839) ∨ (¬ p1998) ∨ (¬ p2860)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2839) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial19531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory8787 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19531 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 2274) (meaning t m 2839) (meaning t m 2860) source

theorem rule19532 (p1977 p2027 p2241 p2509 p2534 p2766 p3452 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p2509) ∨ (¬ p3452) ∨ (¬ p2534) ∨ (¬ p2241) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial19532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory8788 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9)
  exact rule19532 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2509) (meaning t m 2534) (meaning t m 2766) (meaning t m 3452) source

theorem rule19533 (p1975 p2027 p2287 p2299 p2341 p3027 p4066 p4154 : Prop) (h : (¬ p3027) ∨ p2027 ∨ p2287 ∨ (¬ p4066) ∨ (¬ p4154) ∨ (¬ p2341) ∨ (¬ p2299) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (p2287) ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial19533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory8789 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19533 (meaning t m 1975) (meaning t m 2027) (meaning t m 2287) (meaning t m 2299) (meaning t m 2341) (meaning t m 3027) (meaning t m 4066) (meaning t m 4154) source

theorem rule19534 (p1991 p2027 p2534 p2657 p2727 p2766 p4360 p4437 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p1991) ∨ (¬ p4437) ∨ (¬ p2727)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (p2766) ∨ (¬ p4360) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial19534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory8790 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule19534 (meaning t m 1991) (meaning t m 2027) (meaning t m 2534) (meaning t m 2657) (meaning t m 2727) (meaning t m 2766) (meaning t m 4360) (meaning t m 4437) source

theorem rule19536 (p1984 p2027 p2245 p2518 p2657 p2914 p3590 p3876 p4256 : Prop) (h : (¬ p1984) ∨ p2027 ∨ p2914 ∨ (¬ p2245) ∨ (¬ p3876) ∨ (¬ p3590) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (¬ p4256)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2245) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (p2914) ∨ (¬ p3590) ∨ (¬ p3876) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial19536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory8792 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule19536 (meaning t m 1984) (meaning t m 2027) (meaning t m 2245) (meaning t m 2518) (meaning t m 2657) (meaning t m 2914) (meaning t m 3590) (meaning t m 3876) (meaning t m 4256) source

theorem rule19537 (p2307 p3309 p5016 : Prop) (h : (¬ p2307) ∨ (¬ p5016) ∨ p3309) : (¬ p2307) ∨ (p3309) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial19537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (meaning t m 3309) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory8793 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule19537 (meaning t m 2307) (meaning t m 3309) (meaning t m 5016) source

theorem rule19538 (p1988 p2027 p2307 p2396 p2641 p2688 p2761 p3567 : Prop) (h : (¬ p3567) ∨ (¬ p2641) ∨ p2027 ∨ p2688 ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p2307) ∨ (¬ p2396)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2641) ∨ (p2688) ∨ (¬ p2761) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial19538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory8794 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19538 (meaning t m 1988) (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2641) (meaning t m 2688) (meaning t m 2761) (meaning t m 3567) source

theorem rule19539 (p1983 p2027 p2143 p2284 p2388 p2396 p2870 p3646 p4140 : Prop) (h : p2388 ∨ (¬ p3646) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2284) ∨ (¬ p2143) ∨ (¬ p2870) ∨ (¬ p4140)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2143) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p4140) := by
  classical
  tauto

theorem initial19539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4140)) := by
  have source := ElevenTheory.theory8795 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule19539 (meaning t m 1983) (meaning t m 2027) (meaning t m 2143) (meaning t m 2284) (meaning t m 2388) (meaning t m 2396) (meaning t m 2870) (meaning t m 3646) (meaning t m 4140) source

theorem rule19541 (p1991 p2027 p2766 p3172 p3692 p3969 p5600 : Prop) (h : (¬ p3692) ∨ (¬ p3969) ∨ (¬ p5600) ∨ p2027 ∨ (¬ p1991) ∨ p2766 ∨ (¬ p3172)) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial19541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory8797 t (m.theta 0 3) (m.theta 3 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19541 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 3172) (meaning t m 3692) (meaning t m 3969) (meaning t m 5600) source

theorem rule19542 (p1993 p2027 p2191 p2766 p2952 p3166 p3692 p4282 : Prop) (h : (¬ p2952) ∨ (¬ p1993) ∨ (¬ p3166) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p2191) ∨ p2766 ∨ (¬ p4282)) : (¬ p1993) ∨ (p2027) ∨ (¬ p2191) ∨ (p2766) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3692) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial19542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory8798 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule19542 (meaning t m 1993) (meaning t m 2027) (meaning t m 2191) (meaning t m 2766) (meaning t m 2952) (meaning t m 3166) (meaning t m 3692) (meaning t m 4282) source

theorem rule19544 (p2001 p2027 p2166 p2542 p2545 p3212 p4109 p4363 : Prop) (h : p2027 ∨ (¬ p4109) ∨ p2545 ∨ (¬ p2542) ∨ (¬ p2001) ∨ (¬ p2166) ∨ (¬ p4363) ∨ (¬ p3212)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3212) ∨ (¬ p4109) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial19544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory8800 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule19544 (meaning t m 2001) (meaning t m 2027) (meaning t m 2166) (meaning t m 2542) (meaning t m 2545) (meaning t m 3212) (meaning t m 4109) (meaning t m 4363) source

theorem rule19545 (p1975 p2027 p2299 p2765 p2870 p2881 p3758 : Prop) (h : (¬ p3758) ∨ (¬ p2870) ∨ (¬ p1975) ∨ p2765 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2299)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2765) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial19545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory8801 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19545 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2765) (meaning t m 2870) (meaning t m 2881) (meaning t m 3758) source

theorem rule19546 (p3426 p4426 p4781 : Prop) (h : p4781 ∨ (¬ p3426) ∨ (¬ p4426)) : (¬ p3426) ∨ (¬ p4426) ∨ (p4781) := by
  classical
  tauto

theorem initial19546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 4426)) ∨ (meaning t m 4781) := by
  have source := ElevenTheory.theory8802 (m.theta 2 3) (m.theta 2 6) (m.theta 2 7)
  exact rule19546 (meaning t m 3426) (meaning t m 4426) (meaning t m 4781) source

theorem rule19548 (p2004 p2027 p2462 p2761 p3399 p3834 p4321 : Prop) (h : (¬ p2004) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p2761) ∨ p2462) : (¬ p2004) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial19548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory8804 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19548 (meaning t m 2004) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3399) (meaning t m 3834) (meaning t m 4321) source

theorem rule19549 (p1975 p2027 p2274 p2388 p2860 p3115 p4385 : Prop) (h : (¬ p1975) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p4385) ∨ p2388 ∨ (¬ p3115)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2388) ∨ (¬ p2860) ∨ (¬ p3115) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial19549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory8805 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule19549 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2388) (meaning t m 2860) (meaning t m 3115) (meaning t m 4385) source

theorem rule19550 (p1977 p2027 p2241 p2417 p2914 p3817 p4366 : Prop) (h : p2914 ∨ (¬ p2241) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p1977) ∨ (¬ p3817) ∨ (¬ p4366)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2417) ∨ (p2914) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial19550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8806 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule19550 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2417) (meaning t m 2914) (meaning t m 3817) (meaning t m 4366) source

theorem rule19551 (p1975 p2027 p2299 p2344 p2717 p3426 p3654 p3917 : Prop) (h : p2027 ∨ p2344 ∨ (¬ p2717) ∨ (¬ p3917) ∨ (¬ p3654) ∨ (¬ p2299) ∨ (¬ p3426) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (p2344) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3654) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial19551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory8807 t (m.theta 0 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule19551 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2344) (meaning t m 2717) (meaning t m 3426) (meaning t m 3654) (meaning t m 3917) source

theorem rule19557 (p1975 p2307 p2782 p3586 : Prop) (h : (¬ p1975) ∨ p3586 ∨ (¬ p2307) ∨ p2782) : (¬ p1975) ∨ (¬ p2307) ∨ (p2782) ∨ (p3586) := by
  classical
  tauto

theorem initial19557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2782) ∨ (meaning t m 3586) := by
  have source := ElevenTheory.theory8813 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7)
  exact rule19557 (meaning t m 1975) (meaning t m 2307) (meaning t m 2782) (meaning t m 3586) source

theorem rule19558 (p1991 p2027 p2202 p2440 p2810 p3005 p3172 : Prop) (h : (¬ p2810) ∨ p2202 ∨ (¬ p2440) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p3172) ∨ (¬ p3005)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) := by
  classical
  tauto

theorem initial19558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) := by
  have source := ElevenTheory.theory8814 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5)
  exact rule19558 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2810) (meaning t m 3005) (meaning t m 3172) source

theorem rule19559 (p1998 p2545 p3083 p4438 : Prop) (h : (¬ p3083) ∨ (¬ p1998) ∨ p2545 ∨ p4438) : (¬ p1998) ∨ (p2545) ∨ (¬ p3083) ∨ (p4438) := by
  classical
  tauto

theorem initial19559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3083)) ∨ (meaning t m 4438) := by
  have source := ElevenTheory.theory8815 t (m.theta 3 4) (m.theta 4 8) (m.theta 7 8)
  exact rule19559 (meaning t m 1998) (meaning t m 2545) (meaning t m 3083) (meaning t m 4438) source

theorem rule19562 (p1985 p2027 p2156 p2542 p2545 p2891 p4109 p4173 : Prop) (h : (¬ p1985) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p4109) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p2156) ∨ (¬ p2891)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2891) ∨ (¬ p4109) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial19562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory8818 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule19562 (meaning t m 1985) (meaning t m 2027) (meaning t m 2156) (meaning t m 2542) (meaning t m 2545) (meaning t m 2891) (meaning t m 4109) (meaning t m 4173) source

theorem rule19563 (p2319 p3545 p5020 : Prop) (h : (¬ p2319) ∨ (¬ p5020) ∨ p3545) : (¬ p2319) ∨ (p3545) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial19563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2319)) ∨ (meaning t m 3545) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory8819 (m.theta 0 1) (m.theta 0 6) (m.theta 0 7)
  exact rule19563 (meaning t m 2319) (meaning t m 3545) (meaning t m 5020) source

theorem rule19564 (p2657 p3166 p3878 : Prop) (h : (¬ p3878) ∨ (¬ p2657) ∨ (¬ p3166)) : (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3878) := by
  classical
  tauto

theorem initial19564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3878)) := by
  have source := ElevenTheory.theory8820 (m.theta 0 3) (m.theta 3 4) (m.theta 3 8)
  exact rule19564 (meaning t m 2657) (meaning t m 3166) (meaning t m 3878) source

theorem rule19567 (p1998 p2027 p2202 p2440 p2475 p3083 p3998 p5558 : Prop) (h : (¬ p1998) ∨ p2027 ∨ p2202 ∨ (¬ p2475) ∨ (¬ p3998) ∨ (¬ p3083) ∨ (¬ p5558) ∨ (¬ p2440)) : (¬ p1998) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p3998) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial19567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory8823 t (m.theta 0 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10)
  exact rule19567 (meaning t m 1998) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2475) (meaning t m 3083) (meaning t m 3998) (meaning t m 5558) source

theorem rule19568 (p1998 p2027 p2144 p2611 p2870 p2881 p3212 p4385 : Prop) (h : p2611 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p4385) ∨ (¬ p2144)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2144) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3212) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial19568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory8824 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule19568 (meaning t m 1998) (meaning t m 2027) (meaning t m 2144) (meaning t m 2611) (meaning t m 2870) (meaning t m 2881) (meaning t m 3212) (meaning t m 4385) source

theorem rule19569 (p2000 p2027 p2579 p2766 p3266 p3322 p3956 p4191 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p4191) ∨ (¬ p2000) ∨ (¬ p3322) ∨ (¬ p3266) ∨ (¬ p2579) ∨ (¬ p3956)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2579) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3956) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial19569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory8825 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19569 (meaning t m 2000) (meaning t m 2027) (meaning t m 2579) (meaning t m 2766) (meaning t m 3266) (meaning t m 3322) (meaning t m 3956) (meaning t m 4191) source

theorem rule19570 (p2000 p2027 p2579 p2766 p3266 p4137 p4191 : Prop) (h : (¬ p2579) ∨ (¬ p4191) ∨ (¬ p3266) ∨ (¬ p2000) ∨ p2766 ∨ p2027 ∨ (¬ p4137)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2579) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial19570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory8826 t (m.theta 0 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19570 (meaning t m 2000) (meaning t m 2027) (meaning t m 2579) (meaning t m 2766) (meaning t m 3266) (meaning t m 4137) (meaning t m 4191) source

theorem rule19572 (p2020 p2027 p2144 p2611 p2619 p3051 p3969 p4244 : Prop) (h : (¬ p2144) ∨ p2611 ∨ (¬ p2619) ∨ (¬ p4244) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p2020) ∨ (¬ p3969)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2144) ∨ (p2611) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3969) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial19572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory8828 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 10)
  exact rule19572 (meaning t m 2020) (meaning t m 2027) (meaning t m 2144) (meaning t m 2611) (meaning t m 2619) (meaning t m 3051) (meaning t m 3969) (meaning t m 4244) source

theorem rule19575 (p1984 p2027 p2534 p2766 p3860 p4149 p5693 : Prop) (h : (¬ p2534) ∨ p2766 ∨ (¬ p1984) ∨ (¬ p5693) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p4149)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial19575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory8831 t (m.theta 0 1) (m.theta 1 8) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19575 (meaning t m 1984) (meaning t m 2027) (meaning t m 2534) (meaning t m 2766) (meaning t m 3860) (meaning t m 4149) (meaning t m 5693) source

theorem rule19578 (p1988 p2027 p2761 p2873 p3399 p3555 p3631 : Prop) (h : p2873 ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2761) ∨ (p2873) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) := by
  classical
  tauto

theorem initial19578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3631)) := by
  have source := ElevenTheory.theory8834 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19578 (meaning t m 1988) (meaning t m 2027) (meaning t m 2761) (meaning t m 2873) (meaning t m 3399) (meaning t m 3555) (meaning t m 3631) source

theorem rule19580 (p1989 p2027 p2352 p2588 p2997 p3989 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p1989) ∨ p2027 ∨ p2997 ∨ (¬ p2588) ∨ (¬ p2352) ∨ (¬ p3989)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3989) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial19580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory8836 t (m.theta 1 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19580 (meaning t m 1989) (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 2997) (meaning t m 3989) (meaning t m 4173) source

theorem rule19582 (p1991 p2027 p2169 p2363 p2534 p2657 p4256 : Prop) (h : (¬ p2534) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p4256) ∨ p2169 ∨ (¬ p2363)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial19582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory8838 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19582 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 2657) (meaning t m 4256) source

theorem rule19583 (p1988 p2027 p2202 p2427 p2761 p2972 p3556 p3645 p4135 : Prop) (h : (¬ p2972) ∨ (¬ p2427) ∨ (¬ p3645) ∨ (¬ p4135) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p1988) ∨ (¬ p3556) ∨ p2202) : (¬ p1988) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2761) ∨ (¬ p2972) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4135) := by
  classical
  tauto

theorem initial19583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4135)) := by
  have source := ElevenTheory.theory8839 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19583 (meaning t m 1988) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 2761) (meaning t m 2972) (meaning t m 3556) (meaning t m 3645) (meaning t m 4135) source

theorem rule19585 (p1998 p2027 p2148 p2156 p2427 p2881 p4110 : Prop) (h : p2148 ∨ (¬ p1998) ∨ (¬ p2881) ∨ (¬ p4110) ∨ (¬ p2427) ∨ (¬ p2156) ∨ p2027) : (¬ p1998) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8841 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule19585 (meaning t m 1998) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2427) (meaning t m 2881) (meaning t m 4110) source

theorem rule19586 (p1976 p2027 p2685 p2766 p3414 p3877 p4118 p4236 : Prop) (h : (¬ p4118) ∨ p2766 ∨ (¬ p3877) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p2685) ∨ (¬ p3414)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2685) ∨ (p2766) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial19586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory8842 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 8 9)
  exact rule19586 (meaning t m 1976) (meaning t m 2027) (meaning t m 2685) (meaning t m 2766) (meaning t m 3414) (meaning t m 3877) (meaning t m 4118) (meaning t m 4236) source

theorem rule19588 (p2020 p2027 p2187 p2230 p2545 p2563 p2810 p3005 p3172 p3366 p3519 p3979 p4236 p4376 : Prop) (h : p2027 ∨ (¬ p2020) ∨ (¬ p3005) ∨ (¬ p2810) ∨ p2545 ∨ (¬ p3519) ∨ (¬ p2187) ∨ (¬ p4376) ∨ (¬ p3979) ∨ (¬ p2563) ∨ (¬ p2230) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p3172)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3979) ∨ (¬ p4236) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial19588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory8844 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10)
  exact rule19588 (meaning t m 2020) (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2545) (meaning t m 2563) (meaning t m 2810) (meaning t m 3005) (meaning t m 3172) (meaning t m 3366) (meaning t m 3519) (meaning t m 3979) (meaning t m 4236) (meaning t m 4376) source

theorem rule19589 (p1981 p2027 p2187 p2233 p2553 p2573 p3097 : Prop) (h : (¬ p2553) ∨ p2233 ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3097) ∨ (¬ p1981) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (p2233) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial19589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory8845 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19589 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2233) (meaning t m 2553) (meaning t m 2573) (meaning t m 3097) source

theorem rule19593 (p1992 p2027 p2545 p2608 p2810 p3755 p3834 p3847 : Prop) (h : (¬ p3834) ∨ (¬ p1992) ∨ (¬ p2810) ∨ p2545 ∨ p2027 ∨ (¬ p3755) ∨ (¬ p3847) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (p2545) ∨ (¬ p2608) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) := by
  classical
  tauto

theorem initial19593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) := by
  have source := ElevenTheory.theory8849 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9)
  exact rule19593 (meaning t m 1992) (meaning t m 2027) (meaning t m 2545) (meaning t m 2608) (meaning t m 2810) (meaning t m 3755) (meaning t m 3834) (meaning t m 3847) source

theorem rule19594 (p2020 p2027 p2148 p2156 p2373 p3969 p4110 : Prop) (h : p2148 ∨ (¬ p2020) ∨ (¬ p2156) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p2373)) : (¬ p2020) ∨ (p2027) ∨ (p2148) ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3969) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory8850 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule19594 (meaning t m 2020) (meaning t m 2027) (meaning t m 2148) (meaning t m 2156) (meaning t m 2373) (meaning t m 3969) (meaning t m 4110) source

theorem rule19595 (p1975 p2027 p2331 p2553 p2657 p2688 p2727 p3984 : Prop) (h : (¬ p3984) ∨ (¬ p2553) ∨ (¬ p2331) ∨ (¬ p1975) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2727) ∨ p2688) : (¬ p1975) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial19595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory8851 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19595 (meaning t m 1975) (meaning t m 2027) (meaning t m 2331) (meaning t m 2553) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3984) source

theorem rule19598 (p1977 p2027 p2241 p2284 p2388 p3555 p4173 : Prop) (h : (¬ p2284) ∨ (¬ p2241) ∨ (¬ p1977) ∨ p2027 ∨ p2388 ∨ (¬ p3555) ∨ (¬ p4173)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p3555) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial19598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory8854 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule19598 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2284) (meaning t m 2388) (meaning t m 3555) (meaning t m 4173) source

theorem rule19599 (p1977 p2027 p2241 p2766 p3412 p3497 p3555 p3692 : Prop) (h : (¬ p3555) ∨ (¬ p1977) ∨ p2766 ∨ (¬ p3412) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3497)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2766) ∨ (¬ p3412) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial19599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory8855 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule19599 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2766) (meaning t m 3412) (meaning t m 3497) (meaning t m 3555) (meaning t m 3692) source

theorem rule19602 (p1977 p2027 p2169 p2241 p2363 p3860 p4261 : Prop) (h : p2169 ∨ (¬ p2241) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p1977) ∨ (¬ p2363) ∨ (¬ p3860)) : (¬ p1977) ∨ (p2027) ∨ (p2169) ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial19602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory8858 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19602 (meaning t m 1977) (meaning t m 2027) (meaning t m 2169) (meaning t m 2241) (meaning t m 2363) (meaning t m 3860) (meaning t m 4261) source

theorem rule19603 (p2023 p2027 p2355 p3005 p3171 p3572 p3998 p5693 : Prop) (h : p2355 ∨ p2027 ∨ (¬ p5693) ∨ (¬ p2023) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p3005) ∨ (¬ p3572)) : (¬ p2023) ∨ (p2027) ∨ (p2355) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3572) ∨ (¬ p3998) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial19603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2023)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory8859 t (m.theta 0 8) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 8 10)
  exact rule19603 (meaning t m 2023) (meaning t m 2027) (meaning t m 2355) (meaning t m 3005) (meaning t m 3171) (meaning t m 3572) (meaning t m 3998) (meaning t m 5693) source

theorem rule19606 (p1998 p2027 p2417 p2881 p2997 p3365 p3389 p3568 p3690 p4195 p4419 : Prop) (h : (¬ p3690) ∨ (¬ p4419) ∨ p2997 ∨ (¬ p3365) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p1998) ∨ (¬ p4195) ∨ (¬ p2417)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2881) ∨ (p2997) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4195) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial19606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory8862 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19606 (meaning t m 1998) (meaning t m 2027) (meaning t m 2417) (meaning t m 2881) (meaning t m 2997) (meaning t m 3365) (meaning t m 3389) (meaning t m 3568) (meaning t m 3690) (meaning t m 4195) (meaning t m 4419) source

theorem rule19608 (p1991 p2027 p2766 p2963 p3266 p4037 p4191 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p4037) ∨ (¬ p1991) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p4191)) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial19608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory8864 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule19608 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 2963) (meaning t m 3266) (meaning t m 4037) (meaning t m 4191) source

theorem rule19609 (p1977 p2027 p2241 p2766 p3591 p3923 p4347 : Prop) (h : (¬ p3591) ∨ p2766 ∨ p2027 ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p1977) ∨ (¬ p2241)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2766) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial19609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory8865 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule19609 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2766) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) source

theorem rule19610 (p1977 p2027 p2241 p2764 p3860 p4261 p4444 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3860) ∨ p2764 ∨ (¬ p4444) ∨ (¬ p4261)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2241) ∨ (p2764) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial19610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory8866 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19610 (meaning t m 1977) (meaning t m 2027) (meaning t m 2241) (meaning t m 2764) (meaning t m 3860) (meaning t m 4261) (meaning t m 4444) source

theorem rule19613 (p2018 p2027 p2341 p2462 p3543 p3817 p3941 p5612 : Prop) (h : (¬ p3543) ∨ p2462 ∨ p2027 ∨ (¬ p2341) ∨ (¬ p3817) ∨ (¬ p3941) ∨ (¬ p2018) ∨ (¬ p5612)) : (¬ p2018) ∨ (p2027) ∨ (¬ p2341) ∨ (p2462) ∨ (¬ p3543) ∨ (¬ p3817) ∨ (¬ p3941) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial19613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory8869 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule19613 (meaning t m 2018) (meaning t m 2027) (meaning t m 2341) (meaning t m 2462) (meaning t m 3543) (meaning t m 3817) (meaning t m 3941) (meaning t m 5612) source

theorem rule19614 (p2001 p2027 p2148 p3212 p4019 p4385 p4744 p5568 : Prop) (h : p2148 ∨ (¬ p4019) ∨ (¬ p4744) ∨ p2027 ∨ (¬ p4385) ∨ (¬ p3212) ∨ (¬ p2001) ∨ (¬ p5568)) : (¬ p2001) ∨ (p2027) ∨ (p2148) ∨ (¬ p3212) ∨ (¬ p4019) ∨ (¬ p4385) ∨ (¬ p4744) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial19614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory8870 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10)
  exact rule19614 (meaning t m 2001) (meaning t m 2027) (meaning t m 2148) (meaning t m 3212) (meaning t m 4019) (meaning t m 4385) (meaning t m 4744) (meaning t m 5568) source

theorem rule19620 (p1990 p2027 p2545 p2563 p2850 p3343 p5160 : Prop) (h : p2027 ∨ p2545 ∨ (¬ p3343) ∨ (¬ p5160) ∨ (¬ p2850) ∨ (¬ p1990) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3343) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial19620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory8876 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule19620 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2563) (meaning t m 2850) (meaning t m 3343) (meaning t m 5160) source

theorem rule19623 (p2012 p2027 p2764 p2963 p3333 p3362 p3389 p3686 p3868 p4037 p4191 p4423 p4789 : Prop) (h : (¬ p3333) ∨ (¬ p3389) ∨ (¬ p2012) ∨ (¬ p3362) ∨ (¬ p2963) ∨ (¬ p4789) ∨ p2764 ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4037) ∨ (¬ p3868) ∨ (¬ p4423) ∨ (¬ p3686)) : (¬ p2012) ∨ (p2027) ∨ (p2764) ∨ (¬ p2963) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3686) ∨ (¬ p3868) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4423) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial19623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory8879 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 2 7) (m.theta 3 6) (m.theta 4 7) (m.theta 4 9) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule19623 (meaning t m 2012) (meaning t m 2027) (meaning t m 2764) (meaning t m 2963) (meaning t m 3333) (meaning t m 3362) (meaning t m 3389) (meaning t m 3686) (meaning t m 3868) (meaning t m 4037) (meaning t m 4191) (meaning t m 4423) (meaning t m 4789) source

theorem rule19624 (p1998 p2027 p2753 p2764 p2881 p3093 p3362 p3389 p3834 p3868 p4321 p4870 p5660 : Prop) (h : (¬ p3362) ∨ (¬ p3834) ∨ (¬ p3389) ∨ (¬ p3093) ∨ (¬ p1998) ∨ (¬ p4321) ∨ p2027 ∨ p2764 ∨ (¬ p3868) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p2881) ∨ (¬ p5660)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2753) ∨ (p2764) ∨ (¬ p2881) ∨ (¬ p3093) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3834) ∨ (¬ p3868) ∨ (¬ p4321) ∨ (¬ p4870) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial19624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory8880 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 6) (m.theta 1 9) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8) (m.theta 9 10)
  exact rule19624 (meaning t m 1998) (meaning t m 2027) (meaning t m 2753) (meaning t m 2764) (meaning t m 2881) (meaning t m 3093) (meaning t m 3362) (meaning t m 3389) (meaning t m 3834) (meaning t m 3868) (meaning t m 4321) (meaning t m 4870) (meaning t m 5660) source

theorem rule19628 (p2020 p2027 p2230 p2233 p2427 p2881 p3941 : Prop) (h : (¬ p2881) ∨ p2233 ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2020) ∨ (¬ p2230) ∨ (¬ p3941)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3941) := by
  classical
  tauto

theorem initial19628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3941)) := by
  have source := ElevenTheory.theory8884 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10)
  exact rule19628 (meaning t m 2020) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2427) (meaning t m 2881) (meaning t m 3941) source

theorem rule19629 (p1998 p2027 p2699 p2881 p3399 p4075 p5660 : Prop) (h : p2699 ∨ (¬ p4075) ∨ (¬ p3399) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p5660) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial19629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory8885 t (m.theta 0 1) (m.theta 1 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule19629 (meaning t m 1998) (meaning t m 2027) (meaning t m 2699) (meaning t m 2881) (meaning t m 3399) (meaning t m 4075) (meaning t m 5660) source

theorem rule19630 (p2005 p2027 p2287 p2295 p2313 p3654 p4137 : Prop) (h : p2027 ∨ p2287 ∨ (¬ p2295) ∨ (¬ p2005) ∨ (¬ p3654) ∨ (¬ p4137) ∨ (¬ p2313)) : (¬ p2005) ∨ (p2027) ∨ (p2287) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial19630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory8886 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule19630 (meaning t m 2005) (meaning t m 2027) (meaning t m 2287) (meaning t m 2295) (meaning t m 2313) (meaning t m 3654) (meaning t m 4137) source

theorem rule19633 (p1988 p2027 p2545 p2579 p3016 p3276 p3355 : Prop) (h : (¬ p3355) ∨ p2545 ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p1988) ∨ (¬ p3276)) : (¬ p1988) ∨ (p2027) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p3355) := by
  classical
  tauto

theorem initial19633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) := by
  have source := ElevenTheory.theory8889 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 9 10)
  exact rule19633 (meaning t m 1988) (meaning t m 2027) (meaning t m 2545) (meaning t m 2579) (meaning t m 3016) (meaning t m 3276) (meaning t m 3355) source

theorem rule19635 (p1984 p2027 p2633 p3554 p3555 p3570 p4129 p4442 : Prop) (h : (¬ p4442) ∨ (¬ p1984) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3554) ∨ (¬ p4129) ∨ (¬ p3570) ∨ p2633) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3554) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4129) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial19635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory8891 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 8)
  exact rule19635 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3554) (meaning t m 3555) (meaning t m 3570) (meaning t m 4129) (meaning t m 4442) source

theorem rule19636 (p2022 p2027 p3146 p3544 p3578 p4075 p4261 p4372 : Prop) (h : (¬ p3544) ∨ p3578 ∨ (¬ p3146) ∨ (¬ p2022) ∨ p2027 ∨ (¬ p4372) ∨ (¬ p4261) ∨ (¬ p4075)) : (¬ p2022) ∨ (p2027) ∨ (¬ p3146) ∨ (¬ p3544) ∨ (p3578) ∨ (¬ p4075) ∨ (¬ p4261) ∨ (¬ p4372) := by
  classical
  tauto

theorem initial19636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3544)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4372)) := by
  have source := ElevenTheory.theory8892 t (m.theta 0 7) (m.theta 1 7) (m.theta 1 8) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9)
  exact rule19636 (meaning t m 2022) (meaning t m 2027) (meaning t m 3146) (meaning t m 3544) (meaning t m 3578) (meaning t m 4075) (meaning t m 4261) (meaning t m 4372) source

theorem rule19638 (p1997 p2027 p2088 p2534 p2633 p2850 p3486 p3555 p3570 p3874 p5239 : Prop) (h : (¬ p1997) ∨ (¬ p3874) ∨ (¬ p2534) ∨ (¬ p3486) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2088) ∨ p2633 ∨ (¬ p5239) ∨ (¬ p3555)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2534) ∨ (p2633) ∨ (¬ p2850) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3874) ∨ (¬ p5239) := by
  classical
  tauto

theorem initial19638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 5239)) := by
  have source := ElevenTheory.theory8894 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19638 (meaning t m 1997) (meaning t m 2027) (meaning t m 2088) (meaning t m 2534) (meaning t m 2633) (meaning t m 2850) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 3874) (meaning t m 5239) source

theorem rule19639 (p1975 p2027 p2233 p2470 p2553 p3422 p3874 : Prop) (h : (¬ p3874) ∨ (¬ p3422) ∨ (¬ p2553) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p1975) ∨ p2233) : (¬ p1975) ∨ (p2027) ∨ (p2233) ∨ (¬ p2470) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial19639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory8895 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule19639 (meaning t m 1975) (meaning t m 2027) (meaning t m 2233) (meaning t m 2470) (meaning t m 2553) (meaning t m 3422) (meaning t m 3874) source

theorem rule19640 (p1988 p2027 p2088 p2103 p2842 p3266 p3537 p3585 : Prop) (h : (¬ p2103) ∨ (¬ p2088) ∨ (¬ p3585) ∨ p2027 ∨ p2842 ∨ (¬ p3537) ∨ (¬ p1988) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2103) ∨ (p2842) ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial19640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2103)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory8896 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19640 (meaning t m 1988) (meaning t m 2027) (meaning t m 2088) (meaning t m 2103) (meaning t m 2842) (meaning t m 3266) (meaning t m 3537) (meaning t m 3585) source

theorem rule19642 (p1991 p2027 p2633 p2996 p3292 p3553 p3842 : Prop) (h : p2633 ∨ (¬ p1991) ∨ (¬ p2996) ∨ (¬ p3292) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3842)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3292) ∨ (¬ p3553) ∨ (¬ p3842) := by
  classical
  tauto

theorem initial19642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3842)) := by
  have source := ElevenTheory.theory8898 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 8)
  exact rule19642 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 2996) (meaning t m 3292) (meaning t m 3553) (meaning t m 3842) source

theorem rule19643 (p1990 p2027 p2459 p2563 p2633 p3692 p3880 : Prop) (h : (¬ p2563) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3692) ∨ p2633 ∨ (¬ p3880)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial19643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory8899 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19643 (meaning t m 1990) (meaning t m 2027) (meaning t m 2459) (meaning t m 2563) (meaning t m 2633) (meaning t m 3692) (meaning t m 3880) source

theorem rule19645 (p2005 p2027 p2169 p2363 p2534 p3422 p3874 : Prop) (h : p2169 ∨ (¬ p3874) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p2005) ∨ (¬ p2363) ∨ (¬ p2534)) : (¬ p2005) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3422) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial19645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory8901 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule19645 (meaning t m 2005) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 3422) (meaning t m 3874) source

theorem rule19646 (p1997 p2027 p2850 p2881 p2938 p3644 p3876 : Prop) (h : (¬ p3876) ∨ p2027 ∨ p2938 ∨ (¬ p3644) ∨ (¬ p1997) ∨ (¬ p2850) ∨ (¬ p2881)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2850) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial19646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory8902 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19646 (meaning t m 1997) (meaning t m 2027) (meaning t m 2850) (meaning t m 2881) (meaning t m 2938) (meaning t m 3644) (meaning t m 3876) source

theorem rule19647 (p1982 p2459 p3498 p4438 : Prop) (h : p3498 ∨ (¬ p1982) ∨ (¬ p2459) ∨ p4438) : (¬ p1982) ∨ (¬ p2459) ∨ (p3498) ∨ (p4438) := by
  classical
  tauto

theorem initial19647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 3498) ∨ (meaning t m 4438) := by
  have source := ElevenTheory.theory8903 t (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19647 (meaning t m 1982) (meaning t m 2459) (meaning t m 3498) (meaning t m 4438) source

theorem rule19648 (p1979 p2027 p2881 p2938 p3136 p3543 p3548 p3572 p4155 : Prop) (h : (¬ p3543) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2881) ∨ p2938 ∨ (¬ p4155) ∨ (¬ p1979) ∨ (¬ p3136) ∨ (¬ p3572)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3136) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial19648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory8904 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19648 (meaning t m 1979) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3136) (meaning t m 3543) (meaning t m 3548) (meaning t m 3572) (meaning t m 4155) source

theorem rule19651 (p1982 p2027 p2459 p2688 p3027 p3171 p3998 p4044 p5558 : Prop) (h : (¬ p3171) ∨ p2027 ∨ (¬ p4044) ∨ (¬ p5558) ∨ p2688 ∨ (¬ p3998) ∨ (¬ p3027) ∨ (¬ p2459) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4044) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial19651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory8907 t (m.theta 0 8) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19651 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2688) (meaning t m 3027) (meaning t m 3171) (meaning t m 3998) (meaning t m 4044) (meaning t m 5558) source

theorem rule19653 (p2010 p2027 p2470 p2656 p2688 p2727 p3201 p3874 : Prop) (h : (¬ p2727) ∨ p2688 ∨ (¬ p2470) ∨ (¬ p3201) ∨ (¬ p2010) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p2656)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3201) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial19653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory8909 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule19653 (meaning t m 2010) (meaning t m 2027) (meaning t m 2470) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3201) (meaning t m 3874) source

theorem rule19656 (p1982 p2027 p2352 p2363 p2598 p2611 p3422 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p2352) ∨ p2611 ∨ (¬ p2363) ∨ (¬ p3422) ∨ (¬ p2598)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial19656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory8912 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule19656 (meaning t m 1982) (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2598) (meaning t m 2611) (meaning t m 3422) source

theorem rule19658 (p1991 p2952 p3474 p5053 : Prop) (h : p3474 ∨ (¬ p1991) ∨ p5053 ∨ (¬ p2952)) : (¬ p1991) ∨ (¬ p2952) ∨ (p3474) ∨ (p5053) := by
  classical
  tauto

theorem initial19658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 3474) ∨ (meaning t m 5053) := by
  have source := ElevenTheory.theory8914 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5)
  exact rule19658 (meaning t m 1991) (meaning t m 2952) (meaning t m 3474) (meaning t m 5053) source

theorem rule19659 (p1982 p2027 p2177 p2307 p2459 p2545 p2578 p3016 : Prop) (h : p2027 ∨ (¬ p2578) ∨ (¬ p2307) ∨ (¬ p2177) ∨ (¬ p1982) ∨ p2545 ∨ (¬ p2459) ∨ (¬ p3016)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (p2545) ∨ (¬ p2578) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial19659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory8915 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule19659 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2459) (meaning t m 2545) (meaning t m 2578) (meaning t m 3016) source

theorem rule19660 (p1984 p2027 p2187 p2247 p2765 p3324 p4154 : Prop) (h : (¬ p3324) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p1984) ∨ p2765 ∨ (¬ p2247) ∨ (¬ p2187)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2247) ∨ (p2765) ∨ (¬ p3324) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial19660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory8916 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19660 (meaning t m 1984) (meaning t m 2027) (meaning t m 2187) (meaning t m 2247) (meaning t m 2765) (meaning t m 3324) (meaning t m 4154) source

theorem rule19662 (p1996 p2287 p2295 p4570 : Prop) (h : (¬ p2295) ∨ (¬ p1996) ∨ p4570 ∨ p2287) : (¬ p1996) ∨ (p2287) ∨ (¬ p2295) ∨ (p4570) := by
  classical
  tauto

theorem initial19662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 4570) := by
  have source := ElevenTheory.theory8918 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule19662 (meaning t m 1996) (meaning t m 2287) (meaning t m 2295) (meaning t m 4570) source

theorem rule19663 (p1997 p2027 p2850 p3043 p3680 p4264 p4321 p5160 p5487 : Prop) (h : p2027 ∨ (¬ p4264) ∨ (¬ p5160) ∨ (¬ p4321) ∨ (¬ p2850) ∨ (¬ p1997) ∨ p3043 ∨ (¬ p3680) ∨ (¬ p5487)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2850) ∨ (p3043) ∨ (¬ p3680) ∨ (¬ p4264) ∨ (¬ p4321) ∨ (¬ p5160) ∨ (¬ p5487) := by
  classical
  tauto

theorem initial19663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4264)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5160)) ∨ (¬ (meaning t m 5487)) := by
  have source := ElevenTheory.theory8919 t (m.theta 0 9) (m.theta 1 9) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule19663 (meaning t m 1997) (meaning t m 2027) (meaning t m 2850) (meaning t m 3043) (meaning t m 3680) (meaning t m 4264) (meaning t m 4321) (meaning t m 5160) (meaning t m 5487) source

theorem rule19665 (p2387 p2779 p4358 : Prop) (h : (¬ p2779) ∨ (¬ p4358) ∨ p2387) : (p2387) ∨ (¬ p2779) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial19665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2387) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory8921 (m.theta 0 6) (m.theta 2 6) (m.theta 6 8)
  exact rule19665 (meaning t m 2387) (meaning t m 2779) (meaning t m 4358) source

theorem rule19666 (p1998 p2027 p2470 p2528 p2914 p3540 p4348 : Prop) (h : (¬ p1998) ∨ p2914 ∨ (¬ p2528) ∨ (¬ p3540) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2470)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (p2914) ∨ (¬ p3540) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19666 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8922 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19666 (meaning t m 1998) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2914) (meaning t m 3540) (meaning t m 4348) source

theorem rule19667 (p1982 p2027 p2373 p2873 p2891 p3146 p3556 p4031 : Prop) (h : p2873 ∨ (¬ p4031) ∨ (¬ p1982) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3556) ∨ (¬ p2891)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2373) ∨ (p2873) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3556) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial19667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory8923 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule19667 (meaning t m 1982) (meaning t m 2027) (meaning t m 2373) (meaning t m 2873) (meaning t m 2891) (meaning t m 3146) (meaning t m 3556) (meaning t m 4031) source

theorem rule19668 (p2641 p2992 p4336 : Prop) (h : (¬ p2992) ∨ (¬ p4336) ∨ p2641) : (p2641) ∨ (¬ p2992) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial19668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2641) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory8924 (m.theta 1 3) (m.theta 3 5) (m.theta 3 6)
  exact rule19668 (meaning t m 2641) (meaning t m 2992) (meaning t m 4336) source

theorem rule19669 (p1982 p2027 p2230 p2233 p2528 p3641 p3684 : Prop) (h : p2233 ∨ (¬ p2230) ∨ (¬ p1982) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p3684)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial19669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory8925 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule19669 (meaning t m 1982) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2528) (meaning t m 3641) (meaning t m 3684) source

theorem rule19671 (p1988 p2027 p2417 p2656 p2688 p2727 p2761 p3389 : Prop) (h : (¬ p3389) ∨ (¬ p1988) ∨ p2688 ∨ (¬ p2417) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2761) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial19671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory8927 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19671 (meaning t m 1988) (meaning t m 2027) (meaning t m 2417) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2761) (meaning t m 3389) source

theorem rule19672 (p2005 p2027 p3146 p3578 p4118 p4196 p4228 p5514 : Prop) (h : p3578 ∨ (¬ p4118) ∨ (¬ p3146) ∨ (¬ p4196) ∨ (¬ p5514) ∨ (¬ p4228) ∨ p2027 ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4228) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial19672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory8928 t (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 5 8) (m.theta 6 10) (m.theta 8 9)
  exact rule19672 (meaning t m 2005) (meaning t m 2027) (meaning t m 3146) (meaning t m 3578) (meaning t m 4118) (meaning t m 4196) (meaning t m 4228) (meaning t m 5514) source

theorem rule19673 (p1997 p2027 p2534 p2545 p2850 p3256 p3874 p4121 : Prop) (h : (¬ p4121) ∨ p2545 ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3874) ∨ (¬ p1997) ∨ (¬ p2534) ∨ (¬ p3256)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2534) ∨ (p2545) ∨ (¬ p2850) ∨ (¬ p3256) ∨ (¬ p3874) ∨ (¬ p4121) := by
  classical
  tauto

theorem initial19673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4121)) := by
  have source := ElevenTheory.theory8929 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9)
  exact rule19673 (meaning t m 1997) (meaning t m 2027) (meaning t m 2534) (meaning t m 2545) (meaning t m 2850) (meaning t m 3256) (meaning t m 3874) (meaning t m 4121) source

theorem rule19674 (p1997 p2027 p2764 p2870 p4235 p4322 p4385 : Prop) (h : p2027 ∨ p2764 ∨ (¬ p4385) ∨ (¬ p4235) ∨ (¬ p1997) ∨ (¬ p4322) ∨ (¬ p2870)) : (¬ p1997) ∨ (p2027) ∨ (p2764) ∨ (¬ p2870) ∨ (¬ p4235) ∨ (¬ p4322) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial19674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory8930 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule19674 (meaning t m 1997) (meaning t m 2027) (meaning t m 2764) (meaning t m 2870) (meaning t m 4235) (meaning t m 4322) (meaning t m 4385) source

theorem rule19677 (p1997 p2027 p2481 p2850 p3146 p3578 p3857 p3874 : Prop) (h : (¬ p3874) ∨ p3578 ∨ (¬ p2481) ∨ (¬ p1997) ∨ (¬ p3857) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p3146)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2481) ∨ (¬ p2850) ∨ (¬ p3146) ∨ (p3578) ∨ (¬ p3857) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial19677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory8933 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule19677 (meaning t m 1997) (meaning t m 2027) (meaning t m 2481) (meaning t m 2850) (meaning t m 3146) (meaning t m 3578) (meaning t m 3857) (meaning t m 3874) source

theorem rule19680 (p1999 p2027 p2230 p2611 p3125 p3362 p3660 p3888 p4393 : Prop) (h : (¬ p1999) ∨ p2611 ∨ p2027 ∨ (¬ p3125) ∨ (¬ p3660) ∨ (¬ p3362) ∨ (¬ p3888) ∨ (¬ p2230) ∨ (¬ p4393)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2230) ∨ (p2611) ∨ (¬ p3125) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial19680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory8936 t (m.theta 0 2) (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 9)
  exact rule19680 (meaning t m 1999) (meaning t m 2027) (meaning t m 2230) (meaning t m 2611) (meaning t m 3125) (meaning t m 3362) (meaning t m 3660) (meaning t m 3888) (meaning t m 4393) source

theorem rule19681 (p1997 p2027 p2573 p2656 p2688 p2727 p2850 p3584 : Prop) (h : (¬ p1997) ∨ (¬ p2656) ∨ p2027 ∨ (¬ p2727) ∨ p2688 ∨ (¬ p2850) ∨ (¬ p2573) ∨ (¬ p3584)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial19681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory8937 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule19681 (meaning t m 1997) (meaning t m 2027) (meaning t m 2573) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2850) (meaning t m 3584) source

theorem rule19683 (p2005 p2027 p2509 p2534 p2657 p2766 p3361 p3422 p3487 p3686 p4781 : Prop) (h : p2027 ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3487) ∨ (¬ p3361) ∨ p2766 ∨ (¬ p4781) ∨ (¬ p2509) ∨ (¬ p3686) ∨ (¬ p2005) ∨ (¬ p3422)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3361) ∨ (¬ p3422) ∨ (¬ p3487) ∨ (¬ p3686) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial19683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3686)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory8939 t (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule19683 (meaning t m 2005) (meaning t m 2027) (meaning t m 2509) (meaning t m 2534) (meaning t m 2657) (meaning t m 2766) (meaning t m 3361) (meaning t m 3422) (meaning t m 3487) (meaning t m 3686) (meaning t m 4781) source

theorem rule19687 (p1984 p2027 p2247 p2764 p2996 p3947 p4381 : Prop) (h : (¬ p1984) ∨ (¬ p3947) ∨ (¬ p2996) ∨ (¬ p4381) ∨ p2764 ∨ p2027 ∨ (¬ p2247)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2764) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial19687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory8943 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule19687 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2764) (meaning t m 2996) (meaning t m 3947) (meaning t m 4381) source

theorem rule19689 (p1983 p2027 p2210 p2409 p2891 p3246 p3452 : Prop) (h : (¬ p3452) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p2210) ∨ p2409 ∨ (¬ p1983) ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2210) ∨ (p2409) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial19689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory8945 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 7) (m.theta 7 9)
  exact rule19689 (meaning t m 1983) (meaning t m 2027) (meaning t m 2210) (meaning t m 2409) (meaning t m 2891) (meaning t m 3246) (meaning t m 3452) source

theorem rule19690 (p2005 p2027 p2114 p3063 p3093 p3954 p3956 : Prop) (h : (¬ p3956) ∨ p2114 ∨ (¬ p3063) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial19690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory8946 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule19690 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 3063) (meaning t m 3093) (meaning t m 3954) (meaning t m 3956) source

theorem rule19691 (p1975 p2027 p2202 p2299 p2911 p3238 p3389 p3519 : Prop) (h : p2027 ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p2299) ∨ p2202 ∨ (¬ p3238) ∨ (¬ p1975) ∨ (¬ p3519)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial19691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory8947 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19691 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2299) (meaning t m 2911) (meaning t m 3238) (meaning t m 3389) (meaning t m 3519) source

theorem rule19692 (p1998 p2027 p2177 p2409 p3093 p3309 p3452 : Prop) (h : (¬ p1998) ∨ p2409 ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3309) ∨ (¬ p3093)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2409) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial19692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory8948 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19692 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2409) (meaning t m 3093) (meaning t m 3309) (meaning t m 3452) source

theorem rule19693 (p1991 p2027 p2765 p3005 p3172 p3952 p4315 : Prop) (h : (¬ p3172) ∨ (¬ p1991) ∨ p2765 ∨ (¬ p3952) ∨ (¬ p3005) ∨ (¬ p4315) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (p2765) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3952) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial19693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory8949 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6)
  exact rule19693 (meaning t m 1991) (meaning t m 2027) (meaning t m 2765) (meaning t m 3005) (meaning t m 3172) (meaning t m 3952) (meaning t m 4315) source

theorem rule19694 (p1978 p2027 p2766 p2901 p3497 p3556 p3692 : Prop) (h : (¬ p3556) ∨ (¬ p1978) ∨ (¬ p3497) ∨ p2027 ∨ p2766 ∨ (¬ p2901) ∨ (¬ p3692)) : (¬ p1978) ∨ (p2027) ∨ (p2766) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial19694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory8950 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule19694 (meaning t m 1978) (meaning t m 2027) (meaning t m 2766) (meaning t m 2901) (meaning t m 3497) (meaning t m 3556) (meaning t m 3692) source

theorem rule19695 (p1998 p2027 p2409 p3073 p3449 p3452 p4348 : Prop) (h : p2027 ∨ p2409 ∨ (¬ p1998) ∨ (¬ p3452) ∨ (¬ p3449) ∨ (¬ p4348) ∨ (¬ p3073)) : (¬ p1998) ∨ (p2027) ∨ (p2409) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial19695 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory8951 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule19695 (meaning t m 1998) (meaning t m 2027) (meaning t m 2409) (meaning t m 3073) (meaning t m 3449) (meaning t m 3452) (meaning t m 4348) source

theorem rule19698 (p1997 p2027 p2573 p2766 p2850 p2952 p3362 p3497 p3564 p3692 p3917 p4789 p5220 : Prop) (h : p2027 ∨ (¬ p3362) ∨ (¬ p2573) ∨ (¬ p2850) ∨ (¬ p3692) ∨ (¬ p1997) ∨ (¬ p3497) ∨ p2766 ∨ (¬ p2952) ∨ (¬ p4789) ∨ (¬ p3564) ∨ (¬ p3917) ∨ (¬ p5220)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2573) ∨ (p2766) ∨ (¬ p2850) ∨ (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p3917) ∨ (¬ p4789) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial19698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory8954 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule19698 (meaning t m 1997) (meaning t m 2027) (meaning t m 2573) (meaning t m 2766) (meaning t m 2850) (meaning t m 2952) (meaning t m 3362) (meaning t m 3497) (meaning t m 3564) (meaning t m 3692) (meaning t m 3917) (meaning t m 4789) (meaning t m 5220) source

theorem rule19699 (p2007 p2027 p2573 p2964 p3346 p3584 p3641 : Prop) (h : p2964 ∨ (¬ p2007) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p3584) ∨ (¬ p3346) ∨ (¬ p2573)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2573) ∨ (p2964) ∨ (¬ p3346) ∨ (¬ p3584) ∨ (¬ p3641) := by
  classical
  tauto

theorem initial19699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3641)) := by
  have source := ElevenTheory.theory8955 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 4 9)
  exact rule19699 (meaning t m 2007) (meaning t m 2027) (meaning t m 2573) (meaning t m 2964) (meaning t m 3346) (meaning t m 3584) (meaning t m 3641) source

theorem rule19700 (p1997 p2027 p2114 p2850 p3449 p3874 p3954 p4687 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p3954) ∨ (¬ p1997) ∨ (¬ p3874) ∨ (¬ p2850) ∨ (¬ p4687) ∨ (¬ p3449)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2850) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687) := by
  classical
  tauto

theorem initial19700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4687)) := by
  have source := ElevenTheory.theory8956 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8)
  exact rule19700 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2850) (meaning t m 3449) (meaning t m 3874) (meaning t m 3954) (meaning t m 4687) source

theorem rule19702 (p1981 p2027 p2355 p2819 p3822 p3931 p4260 : Prop) (h : (¬ p3931) ∨ p2355 ∨ (¬ p4260) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p3822) ∨ (¬ p2819)) : (¬ p1981) ∨ (p2027) ∨ (p2355) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3931) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial19702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory8958 t (m.theta 2 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule19702 (meaning t m 1981) (meaning t m 2027) (meaning t m 2355) (meaning t m 2819) (meaning t m 3822) (meaning t m 3931) (meaning t m 4260) source

theorem rule19704 (p2022 p2027 p2765 p3156 p3952 p3961 p3969 p5590 : Prop) (h : (¬ p3952) ∨ (¬ p2022) ∨ (¬ p5590) ∨ p2027 ∨ (¬ p3961) ∨ (¬ p3969) ∨ p2765 ∨ (¬ p3156)) : (¬ p2022) ∨ (p2027) ∨ (p2765) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3961) ∨ (¬ p3969) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial19704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2022)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory8960 t (m.theta 0 7) (m.theta 0 8) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 10)
  exact rule19704 (meaning t m 2022) (meaning t m 2027) (meaning t m 2765) (meaning t m 3156) (meaning t m 3952) (meaning t m 3961) (meaning t m 3969) (meaning t m 5590) source

theorem rule19706 (p2005 p2027 p3063 p3093 p3623 p3956 p4366 : Prop) (h : (¬ p3063) ∨ p3623 ∨ p2027 ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p3956) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (p3623) ∨ (¬ p3956) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial19706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory8962 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 8)
  exact rule19706 (meaning t m 2005) (meaning t m 2027) (meaning t m 3063) (meaning t m 3093) (meaning t m 3623) (meaning t m 3956) (meaning t m 4366) source

theorem rule19707 (p1978 p2027 p2901 p2997 p3097 p3556 p3952 : Prop) (h : (¬ p1978) ∨ (¬ p3952) ∨ p2997 ∨ (¬ p3556) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2901)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2901) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3556) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial19707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory8963 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule19707 (meaning t m 1978) (meaning t m 2027) (meaning t m 2901) (meaning t m 2997) (meaning t m 3097) (meaning t m 3556) (meaning t m 3952) source

theorem rule19708 (p1975 p2027 p2264 p2299 p2545 p2797 p2810 p4156 : Prop) (h : p2545 ∨ (¬ p2810) ∨ (¬ p2299) ∨ (¬ p2797) ∨ (¬ p4156) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2264)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial19708 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory8964 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19708 (meaning t m 1975) (meaning t m 2027) (meaning t m 2264) (meaning t m 2299) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 4156) source

theorem rule19709 (p2004 p2409 p2922 p2930 : Prop) (h : p2409 ∨ (¬ p2922) ∨ (¬ p2004) ∨ p2930) : (¬ p2004) ∨ (p2409) ∨ (¬ p2922) ∨ (p2930) := by
  classical
  tauto

theorem initial19709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2922)) ∨ (meaning t m 2930) := by
  have source := ElevenTheory.theory8965 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 7)
  exact rule19709 (meaning t m 2004) (meaning t m 2409) (meaning t m 2922) (meaning t m 2930) source

theorem rule19711 (p2005 p2027 p2295 p2545 p2588 p2797 p2810 : Prop) (h : (¬ p2295) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2005) ∨ p2545 ∨ (¬ p2797)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2295) ∨ (p2545) ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p2810) := by
  classical
  tauto

theorem initial19711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) := by
  have source := ElevenTheory.theory8967 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19711 (meaning t m 2005) (meaning t m 2027) (meaning t m 2295) (meaning t m 2545) (meaning t m 2588) (meaning t m 2797) (meaning t m 2810) source

theorem rule19715 (p1976 p2027 p2764 p2952 p3136 p4035 p4040 p4236 p4322 : Prop) (h : (¬ p1976) ∨ (¬ p4040) ∨ (¬ p4236) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4035) ∨ (¬ p4322) ∨ p2764) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4035) ∨ (¬ p4040) ∨ (¬ p4236) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial19715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory8971 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule19715 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 2952) (meaning t m 3136) (meaning t m 4035) (meaning t m 4040) (meaning t m 4236) (meaning t m 4322) source

theorem rule19716 (p1976 p2027 p2104 p3146 p3982 p4340 p5568 : Prop) (h : (¬ p1976) ∨ (¬ p4340) ∨ (¬ p5568) ∨ (¬ p3146) ∨ p2027 ∨ p3982 ∨ (¬ p2104)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p3146) ∨ (p3982) ∨ (¬ p4340) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial19716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory8972 t (m.theta 0 2) (m.theta 2 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule19716 (meaning t m 1976) (meaning t m 2027) (meaning t m 2104) (meaning t m 3146) (meaning t m 3982) (meaning t m 4340) (meaning t m 5568) source

theorem rule19717 (p2417 p3564 p3581 p4623 : Prop) (h : (¬ p3564) ∨ (¬ p3581) ∨ (¬ p4623) ∨ p2417) : (p2417) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial19717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory8973 (m.theta 4 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9)
  exact rule19717 (meaning t m 2417) (meaning t m 3564) (meaning t m 3581) (meaning t m 4623) source

theorem rule19718 (p2010 p2027 p2287 p2499 p2922 p3323 p4137 : Prop) (h : p2287 ∨ (¬ p2010) ∨ (¬ p3323) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p4137) ∨ p2027) : (¬ p2010) ∨ (p2027) ∨ (p2287) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3323) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial19718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory8974 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule19718 (meaning t m 2010) (meaning t m 2027) (meaning t m 2287) (meaning t m 2499) (meaning t m 2922) (meaning t m 3323) (meaning t m 4137) source

theorem rule19719 (p1998 p2027 p2114 p2210 p2881 p2891 p3954 : Prop) (h : (¬ p2210) ∨ p2114 ∨ (¬ p3954) ∨ (¬ p2891) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8975 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8)
  exact rule19719 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2881) (meaning t m 2891) (meaning t m 3954) source

theorem rule19721 (p1987 p2027 p2737 p2764 p4242 p4340 p4444 : Prop) (h : p2764 ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4340) ∨ (¬ p4242) ∨ (¬ p1987) ∨ (¬ p4444)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2764) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial19721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory8977 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 8 9) (m.theta 9 10)
  exact rule19721 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2764) (meaning t m 4242) (meaning t m 4340) (meaning t m 4444) source

theorem rule19722 (p2005 p2233 p2470 p4595 : Prop) (h : (¬ p2470) ∨ p2233 ∨ (¬ p2005) ∨ p4595) : (¬ p2005) ∨ (p2233) ∨ (¬ p2470) ∨ (p4595) := by
  classical
  tauto

theorem initial19722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2470)) ∨ (meaning t m 4595) := by
  have source := ElevenTheory.theory8978 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule19722 (meaning t m 2005) (meaning t m 2233) (meaning t m 2470) (meaning t m 4595) source

theorem rule19726 (p1978 p2027 p2284 p2764 p3646 p4208 p4322 : Prop) (h : (¬ p4322) ∨ (¬ p1978) ∨ (¬ p2284) ∨ p2764 ∨ p2027 ∨ (¬ p4208) ∨ (¬ p3646)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2284) ∨ (p2764) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial19726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory8982 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule19726 (meaning t m 1978) (meaning t m 2027) (meaning t m 2284) (meaning t m 2764) (meaning t m 3646) (meaning t m 4208) (meaning t m 4322) source

theorem rule19728 (p4045 p4186 p4635 : Prop) (h : p4635 ∨ (¬ p4045) ∨ (¬ p4186)) : (¬ p4045) ∨ (¬ p4186) ∨ (p4635) := by
  classical
  tauto

theorem initial19728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4186)) ∨ (meaning t m 4635) := by
  have source := ElevenTheory.theory8984 (m.theta 4 7) (m.theta 4 8) (m.theta 4 9)
  exact rule19728 (meaning t m 4045) (meaning t m 4186) (meaning t m 4635) source

theorem rule19730 (p1982 p2027 p2114 p2166 p2210 p3146 p3954 : Prop) (h : (¬ p3954) ∨ p2027 ∨ p2114 ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p1982) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8986 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9)
  exact rule19730 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2166) (meaning t m 2210) (meaning t m 3146) (meaning t m 3954) source

theorem rule19731 (p2005 p2027 p2114 p3422 p3449 p3874 p3954 p4687 : Prop) (h : p2114 ∨ (¬ p4687) ∨ (¬ p3954) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p2005) ∨ (¬ p3422)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p3422) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687) := by
  classical
  tauto

theorem initial19731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4687)) := by
  have source := ElevenTheory.theory8987 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule19731 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 3422) (meaning t m 3449) (meaning t m 3874) (meaning t m 3954) (meaning t m 4687) source

theorem rule19732 (p2010 p2027 p2114 p2504 p3093 p3201 p3584 p3954 : Prop) (h : p2114 ∨ (¬ p2504) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2010) ∨ (¬ p3093) ∨ (¬ p3954)) : (¬ p2010) ∨ (p2027) ∨ (p2114) ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory8988 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule19732 (meaning t m 2010) (meaning t m 2027) (meaning t m 2114) (meaning t m 2504) (meaning t m 3093) (meaning t m 3201) (meaning t m 3584) (meaning t m 3954) source

theorem rule19733 (p1986 p2027 p2579 p2588 p2997 p3355 p5160 : Prop) (h : (¬ p1986) ∨ p2997 ∨ (¬ p5160) ∨ (¬ p2588) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p3355)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3355) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial19733 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory8989 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 7)
  exact rule19733 (meaning t m 1986) (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2997) (meaning t m 3355) (meaning t m 5160) source

theorem rule19737 (p1985 p2027 p2230 p2233 p2373 p2870 p3694 : Prop) (h : (¬ p1985) ∨ (¬ p2373) ∨ (¬ p2870) ∨ p2233 ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3694)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2373) ∨ (¬ p2870) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial19737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory8993 t (m.theta 0 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule19737 (meaning t m 1985) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2373) (meaning t m 2870) (meaning t m 3694) source

theorem rule19740 (p1990 p2027 p2299 p2633 p3323 p3568 p3744 : Prop) (h : p2027 ∨ p2633 ∨ (¬ p3568) ∨ (¬ p2299) ∨ (¬ p1990) ∨ (¬ p3744) ∨ (¬ p3323)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial19740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory8996 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule19740 (meaning t m 1990) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3323) (meaning t m 3568) (meaning t m 3744) source

theorem rule19742 (p1978 p2027 p2997 p3097 p3115 p3952 p4032 : Prop) (h : (¬ p3097) ∨ p2027 ∨ p2997 ∨ (¬ p1978) ∨ (¬ p4032) ∨ (¬ p3952) ∨ (¬ p3115)) : (¬ p1978) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial19742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory8998 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule19742 (meaning t m 1978) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3115) (meaning t m 3952) (meaning t m 4032) source

theorem rule19744 (p1991 p2027 p2633 p3246 p3414 p3570 p3947 : Prop) (h : (¬ p3947) ∨ (¬ p1991) ∨ (¬ p3570) ∨ p2027 ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3414)) : (¬ p1991) ∨ (p2027) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3414) ∨ (¬ p3570) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial19744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory9000 t (m.theta 0 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19744 (meaning t m 1991) (meaning t m 2027) (meaning t m 2633) (meaning t m 3246) (meaning t m 3414) (meaning t m 3570) (meaning t m 3947) source

theorem rule19745 (p2007 p2388 p3156 p4158 : Prop) (h : (¬ p3156) ∨ (¬ p2007) ∨ p2388 ∨ p4158) : (¬ p2007) ∨ (p2388) ∨ (¬ p3156) ∨ (p4158) := by
  classical
  tauto

theorem initial19745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3156)) ∨ (meaning t m 4158) := by
  have source := ElevenTheory.theory9001 t (m.theta 3 5) (m.theta 4 8) (m.theta 5 8)
  exact rule19745 (meaning t m 2007) (meaning t m 2388) (meaning t m 3156) (meaning t m 4158) source

theorem rule19746 (p2003 p2027 p2284 p2938 p3125 p3946 p4320 : Prop) (h : p2027 ∨ (¬ p2003) ∨ p2938 ∨ (¬ p3946) ∨ (¬ p4320) ∨ (¬ p3125) ∨ (¬ p2284)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2284) ∨ (p2938) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial19746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory9002 t (m.theta 0 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule19746 (meaning t m 2003) (meaning t m 2027) (meaning t m 2284) (meaning t m 2938) (meaning t m 3125) (meaning t m 3946) (meaning t m 4320) source

theorem rule19747 (p2449 p3740 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p2449) ∨ (¬ p3740)) : (¬ p2449) ∨ (¬ p3740) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial19747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory9003 (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule19747 (meaning t m 2449) (meaning t m 3740) (meaning t m 4278) source

theorem rule19748 (p2881 p3659 p4344 : Prop) (h : (¬ p2881) ∨ (¬ p3659) ∨ (¬ p4344)) : (¬ p2881) ∨ (¬ p3659) ∨ (¬ p4344) := by
  classical
  tauto

theorem initial19748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4344)) := by
  have source := ElevenTheory.theory9004 (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19748 (meaning t m 2881) (meaning t m 3659) (meaning t m 4344) source

theorem rule19749 (p2027 p2177 p2295 p3570 p4204 p4560 : Prop) (h : (¬ p2295) ∨ (¬ p2177) ∨ (¬ p4204) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4560)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial19749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory9005 t (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19749 (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 3570) (meaning t m 4204) (meaning t m 4560) source

theorem rule19752 (p2284 p3879 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p2284) ∨ (¬ p3879)) : (¬ p2284) ∨ (¬ p3879) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial19752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory9008 (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule19752 (meaning t m 2284) (meaning t m 3879) (meaning t m 4110) source

theorem rule19753 (p2295 p3324 p3325 : Prop) (h : (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3325)) : (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial19753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory9009 (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule19753 (meaning t m 2295) (meaning t m 3324) (meaning t m 3325) source

theorem rule19754 (p1984 p2247 p2255 p2323 : Prop) (h : (¬ p1984) ∨ p2255 ∨ (¬ p2247) ∨ p2323) : (¬ p1984) ∨ (¬ p2247) ∨ (p2255) ∨ (p2323) := by
  classical
  tauto

theorem initial19754 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2255) ∨ (meaning t m 2323) := by
  have source := ElevenTheory.theory9010 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule19754 (meaning t m 1984) (meaning t m 2247) (meaning t m 2255) (meaning t m 2323) source

theorem rule19755 (p2027 p2589 p2662 p2745 p2850 p3475 p4111 : Prop) (h : (¬ p2850) ∨ (¬ p2589) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3475)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial19755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory9011 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule19755 (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2745) (meaning t m 2850) (meaning t m 3475) (meaning t m 4111) source

theorem rule19758 (p2963 p3166 p4196 : Prop) (h : (¬ p3166) ∨ (¬ p2963) ∨ (¬ p4196)) : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial19758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory9014 (m.theta 0 3) (m.theta 3 6) (m.theta 3 8)
  exact rule19758 (meaning t m 2963) (meaning t m 3166) (meaning t m 4196) source

theorem rule19759 (p1991 p2233 p2657 p2665 : Prop) (h : p2233 ∨ (¬ p1991) ∨ (¬ p2657) ∨ p2665) : (¬ p1991) ∨ (p2233) ∨ (¬ p2657) ∨ (p2665) := by
  classical
  tauto

theorem initial19759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2665) := by
  have source := ElevenTheory.theory9015 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4)
  exact rule19759 (meaning t m 1991) (meaning t m 2233) (meaning t m 2657) (meaning t m 2665) source

theorem rule19760 (p2881 p3690 p3945 : Prop) (h : (¬ p2881) ∨ (¬ p3690) ∨ (¬ p3945)) : (¬ p2881) ∨ (¬ p3690) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial19760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory9016 (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule19760 (meaning t m 2881) (meaning t m 3690) (meaning t m 3945) source

theorem rule19762 (p3063 p3990 p4026 : Prop) (h : (¬ p3063) ∨ (¬ p4026) ∨ (¬ p3990)) : (¬ p3063) ∨ (¬ p3990) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial19762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory9018 (m.theta 1 6) (m.theta 6 8) (m.theta 6 9)
  exact rule19762 (meaning t m 3063) (meaning t m 3990) (meaning t m 4026) source

theorem rule19764 (p2003 p2313 p2321 p3360 : Prop) (h : (¬ p2313) ∨ p3360 ∨ (¬ p2003) ∨ p2321) : (¬ p2003) ∨ (¬ p2313) ∨ (p2321) ∨ (p3360) := by
  classical
  tauto

theorem initial19764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2321) ∨ (meaning t m 3360) := by
  have source := ElevenTheory.theory9020 t (m.theta 0 6) (m.theta 0 7) (m.theta 6 7)
  exact rule19764 (meaning t m 2003) (meaning t m 2313) (meaning t m 2321) (meaning t m 3360) source

theorem rule19765 (p2104 p2132 p4744 : Prop) (h : (¬ p2132) ∨ (¬ p2104) ∨ (¬ p4744)) : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p4744) := by
  classical
  tauto

theorem initial19765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 4744)) := by
  have source := ElevenTheory.theory9021 (m.theta 0 2) (m.theta 2 5) (m.theta 2 8)
  exact rule19765 (meaning t m 2104) (meaning t m 2132) (meaning t m 4744) source

theorem rule19766 (p2027 p2104 p2132 p3156 p4740 p4906 : Prop) (h : (¬ p4906) ∨ (¬ p3156) ∨ (¬ p2104) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p4740)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p3156) ∨ (¬ p4740) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial19766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4740)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory9022 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8)
  exact rule19766 (meaning t m 2027) (meaning t m 2104) (meaning t m 2132) (meaning t m 3156) (meaning t m 4740) (meaning t m 4906) source

theorem rule19767 (p2241 p2741 p3954 : Prop) (h : (¬ p2241) ∨ (¬ p2741) ∨ (¬ p3954)) : (¬ p2241) ∨ (¬ p2741) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial19767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory9023 (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule19767 (meaning t m 2241) (meaning t m 2741) (meaning t m 3954) source

theorem rule19768 (p2341 p3575 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p2341) ∨ (¬ p3575)) : (¬ p2341) ∨ (¬ p3575) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial19768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory9024 (m.theta 0 7) (m.theta 4 7) (m.theta 7 8)
  exact rule19768 (meaning t m 2341) (meaning t m 3575) (meaning t m 3644) source

theorem rule19769 (p2829 p3426 p3588 : Prop) (h : (¬ p3588) ∨ (¬ p2829) ∨ (¬ p3426)) : (¬ p2829) ∨ (¬ p3426) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial19769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory9025 (m.theta 1 2) (m.theta 2 6) (m.theta 2 7)
  exact rule19769 (meaning t m 2829) (meaning t m 3426) (meaning t m 3588) source

theorem rule19771 (p2027 p3379 p3688 p3954 p4030 p5221 : Prop) (h : (¬ p3688) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4030) ∨ (¬ p3379) ∨ (¬ p5221)) : (p2027) ∨ (¬ p3379) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p5221) := by
  classical
  tauto

theorem initial19771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 5221)) := by
  have source := ElevenTheory.theory9027 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6)
  exact rule19771 (meaning t m 2027) (meaning t m 3379) (meaning t m 3688) (meaning t m 3954) (meaning t m 4030) (meaning t m 5221) source

theorem rule19774 (p2104 p3471 p4805 : Prop) (h : (¬ p3471) ∨ (¬ p2104) ∨ (¬ p4805)) : (¬ p2104) ∨ (¬ p3471) ∨ (¬ p4805) := by
  classical
  tauto

theorem initial19774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4805)) := by
  have source := ElevenTheory.theory9030 (m.theta 0 2) (m.theta 2 7) (m.theta 2 8)
  exact rule19774 (meaning t m 2104) (meaning t m 3471) (meaning t m 4805) source

theorem rule19775 (p2104 p2341 p3819 p4800 : Prop) (h : (¬ p2104) ∨ (¬ p2341) ∨ (¬ p3819) ∨ (¬ p4800)) : (¬ p2104) ∨ (¬ p2341) ∨ (¬ p3819) ∨ (¬ p4800) := by
  classical
  tauto

theorem initial19775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4800)) := by
  have source := ElevenTheory.theory9031 (m.theta 0 2) (m.theta 0 7) (m.theta 2 8) (m.theta 7 8)
  exact rule19775 (meaning t m 2104) (meaning t m 2341) (meaning t m 3819) (meaning t m 4800) source

theorem rule19776 (p2829 p4242 p4861 : Prop) (h : (¬ p2829) ∨ (¬ p4242) ∨ (¬ p4861)) : (¬ p2829) ∨ (¬ p4242) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial19776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory9032 (m.theta 1 2) (m.theta 2 6) (m.theta 2 8)
  exact rule19776 (meaning t m 2829) (meaning t m 4242) (meaning t m 4861) source

theorem rule19778 (p2027 p2312 p2341 p2501 p2553 p3548 p4105 : Prop) (h : (¬ p2501) ∨ (¬ p2553) ∨ (¬ p2312) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p4105)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial19778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory9034 t (m.theta 0 7) (m.theta 1 6) (m.theta 1 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule19778 (meaning t m 2027) (meaning t m 2312) (meaning t m 2341) (meaning t m 2501) (meaning t m 2553) (meaning t m 3548) (meaning t m 4105) source

theorem rule19780 (p2187 p3744 p3990 : Prop) (h : (¬ p3744) ∨ (¬ p2187) ∨ (¬ p3990)) : (¬ p2187) ∨ (¬ p3744) ∨ (¬ p3990) := by
  classical
  tauto

theorem initial19780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3990)) := by
  have source := ElevenTheory.theory9036 (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule19780 (meaning t m 2187) (meaning t m 3744) (meaning t m 3990) source

theorem rule19781 (p2274 p3744 p4187 : Prop) (h : (¬ p3744) ∨ (¬ p2274) ∨ (¬ p4187)) : (¬ p2274) ∨ (¬ p3744) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial19781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory9037 (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule19781 (meaning t m 2274) (meaning t m 3744) (meaning t m 4187) source

theorem rule19785 (p2230 p3741 p3759 p3876 : Prop) (h : (¬ p3759) ∨ (¬ p3876) ∨ (¬ p2230) ∨ (¬ p3741)) : (¬ p2230) ∨ (¬ p3741) ∨ (¬ p3759) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial19785 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory9041 (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19785 (meaning t m 2230) (meaning t m 3741) (meaning t m 3759) (meaning t m 3876) source

theorem rule19786 (p3246 p4107 p4275 : Prop) (h : (¬ p4107) ∨ (¬ p3246) ∨ (¬ p4275)) : (¬ p3246) ∨ (¬ p4107) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial19786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory9042 (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule19786 (meaning t m 3246) (meaning t m 4107) (meaning t m 4275) source

theorem rule19789 (p2553 p3822 p4390 : Prop) (h : (¬ p3822) ∨ (¬ p2553) ∨ (¬ p4390)) : (¬ p2553) ∨ (¬ p3822) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial19789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory9045 (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule19789 (meaning t m 2553) (meaning t m 3822) (meaning t m 4390) source

theorem rule19790 (p3201 p3822 p4710 p5220 : Prop) (h : (¬ p3822) ∨ (¬ p4710) ∨ (¬ p3201) ∨ (¬ p5220)) : (¬ p3201) ∨ (¬ p3822) ∨ (¬ p4710) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial19790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4710)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory9046 (m.theta 2 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7)
  exact rule19790 (meaning t m 3201) (meaning t m 3822) (meaning t m 4710) (meaning t m 5220) source

theorem rule19793 (p2295 p3549 p3922 : Prop) (h : (¬ p3549) ∨ (¬ p2295) ∨ (¬ p3922)) : (¬ p2295) ∨ (¬ p3549) ∨ (¬ p3922) := by
  classical
  tauto

theorem initial19793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) := by
  have source := ElevenTheory.theory9049 (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule19793 (meaning t m 2295) (meaning t m 3549) (meaning t m 3922) source

theorem rule19794 (p2027 p2341 p3425 p3548 p3819 p4794 : Prop) (h : (¬ p3425) ∨ (¬ p3819) ∨ (¬ p2341) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p4794)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p4794) := by
  classical
  tauto

theorem initial19794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 4794)) := by
  have source := ElevenTheory.theory9050 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule19794 (meaning t m 2027) (meaning t m 2341) (meaning t m 3425) (meaning t m 3548) (meaning t m 3819) (meaning t m 4794) source

theorem rule19796 (p2027 p2707 p3583 p4235 p4344 p4885 : Prop) (h : (¬ p3583) ∨ (¬ p4885) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p4235) ∨ (¬ p4344)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3583) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial19796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory9052 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7)
  exact rule19796 (meaning t m 2027) (meaning t m 2707) (meaning t m 3583) (meaning t m 4235) (meaning t m 4344) (meaning t m 4885) source

theorem rule19798 (p2027 p2132 p2810 p3365 p4704 p5051 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4704) ∨ (¬ p5051)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4704) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial19798 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4704)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory9054 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule19798 (meaning t m 2027) (meaning t m 2132) (meaning t m 2810) (meaning t m 3365) (meaning t m 4704) (meaning t m 5051) source

theorem rule19799 (p2027 p2657 p2743 p3367 p3683 p4787 : Prop) (h : p2027 ∨ (¬ p4787) ∨ (¬ p2657) ∨ (¬ p3367) ∨ (¬ p2743) ∨ (¬ p3683)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial19799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory9055 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4)
  exact rule19799 (meaning t m 2027) (meaning t m 2657) (meaning t m 2743) (meaning t m 3367) (meaning t m 3683) (meaning t m 4787) source

theorem rule19800 (p2829 p3585 p5220 : Prop) (h : (¬ p3585) ∨ (¬ p2829) ∨ (¬ p5220)) : (¬ p2829) ∨ (¬ p3585) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial19800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory9056 (m.theta 1 2) (m.theta 2 4) (m.theta 2 6)
  exact rule19800 (meaning t m 2829) (meaning t m 3585) (meaning t m 5220) source

theorem rule19806 (p2230 p3238 p3519 : Prop) (h : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3519)) : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3519) := by
  classical
  tauto

theorem initial19806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3519)) := by
  have source := ElevenTheory.theory9062 (m.theta 0 4) (m.theta 1 4) (m.theta 4 5)
  exact rule19806 (meaning t m 2230) (meaning t m 3238) (meaning t m 3519) source

theorem rule19807 (p2264 p3570 p3699 : Prop) (h : (¬ p2264) ∨ (¬ p3570) ∨ (¬ p3699)) : (¬ p2264) ∨ (¬ p3570) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial19807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory9063 (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule19807 (meaning t m 2264) (meaning t m 3570) (meaning t m 3699) source

theorem rule19808 (p2563 p3695 p3758 : Prop) (h : (¬ p2563) ∨ (¬ p3758) ∨ (¬ p3695)) : (¬ p2563) ∨ (¬ p3695) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial19808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory9064 (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule19808 (meaning t m 2563) (meaning t m 3695) (meaning t m 3758) source

theorem rule19809 (p2027 p2230 p2563 p3054 p3758 p4730 : Prop) (h : (¬ p4730) ∨ (¬ p2230) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p3054)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p3758) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial19809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory9065 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule19809 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 3054) (meaning t m 3758) (meaning t m 4730) source

theorem rule19812 (p1991 p2247 p2254 p2688 : Prop) (h : (¬ p2247) ∨ (¬ p1991) ∨ p2688 ∨ p2254) : (¬ p1991) ∨ (¬ p2247) ∨ (p2254) ∨ (p2688) := by
  classical
  tauto

theorem initial19812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2254) ∨ (meaning t m 2688) := by
  have source := ElevenTheory.theory9068 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3)
  exact rule19812 (meaning t m 1991) (meaning t m 2247) (meaning t m 2254) (meaning t m 2688) source

theorem rule19813 (p2911 p3658 p3659 : Prop) (h : (¬ p2911) ∨ (¬ p3659) ∨ (¬ p3658)) : (¬ p2911) ∨ (¬ p3658) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial19813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory9069 (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule19813 (meaning t m 2911) (meaning t m 3658) (meaning t m 3659) source

theorem rule19816 (p2027 p2341 p2737 p3548 p3577 p4400 p4778 : Prop) (h : (¬ p3577) ∨ (¬ p2737) ∨ (¬ p2341) ∨ (¬ p4400) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p4778)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3548) ∨ (¬ p3577) ∨ (¬ p4400) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial19816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory9072 t (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule19816 (meaning t m 2027) (meaning t m 2341) (meaning t m 2737) (meaning t m 3548) (meaning t m 3577) (meaning t m 4400) (meaning t m 4778) source

theorem rule19818 (p2027 p2156 p2958 p3414 p3952 p4917 : Prop) (h : (¬ p3414) ∨ (¬ p2958) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p4917)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3414) ∨ (¬ p3952) ∨ (¬ p4917) := by
  classical
  tauto

theorem initial19818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4917)) := by
  have source := ElevenTheory.theory9074 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule19818 (meaning t m 2027) (meaning t m 2156) (meaning t m 2958) (meaning t m 3414) (meaning t m 3952) (meaning t m 4917) source

theorem rule19820 (p2331 p2952 p4153 : Prop) (h : (¬ p4153) ∨ (¬ p2952) ∨ (¬ p2331)) : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial19820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory9076 (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule19820 (meaning t m 2331) (meaning t m 2952) (meaning t m 4153) source

theorem rule19824 (p2761 p4321 p5362 : Prop) (h : (¬ p2761) ∨ (¬ p4321) ∨ (¬ p5362)) : (¬ p2761) ∨ (¬ p4321) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial19824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory9080 (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19824 (meaning t m 2761) (meaning t m 4321) (meaning t m 5362) source

theorem rule19825 (p3201 p3347 p3540 p4030 : Prop) (h : (¬ p3540) ∨ (¬ p3347) ∨ (¬ p3201) ∨ (¬ p4030)) : (¬ p3201) ∨ (¬ p3347) ∨ (¬ p3540) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial19825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory9081 (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule19825 (meaning t m 3201) (meaning t m 3347) (meaning t m 3540) (meaning t m 4030) source

theorem rule19828 (p2027 p2630 p2707 p2741 p4111 p4782 : Prop) (h : (¬ p2707) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2630) ∨ (¬ p2741) ∨ (¬ p4782)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2707) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial19828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory9084 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4)
  exact rule19828 (meaning t m 2027) (meaning t m 2630) (meaning t m 2707) (meaning t m 2741) (meaning t m 4111) (meaning t m 4782) source

theorem rule19830 (p2870 p4316 p4320 : Prop) (h : (¬ p2870) ∨ (¬ p4320) ∨ (¬ p4316)) : (¬ p2870) ∨ (¬ p4316) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial19830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory9086 (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule19830 (meaning t m 2870) (meaning t m 4316) (meaning t m 4320) source

theorem rule19831 (p2027 p2122 p2745 p3568 p4154 p4426 : Prop) (h : (¬ p3568) ∨ (¬ p2122) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p2745) ∨ (¬ p4426)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2745) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial19831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory9087 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule19831 (meaning t m 2027) (meaning t m 2122) (meaning t m 2745) (meaning t m 3568) (meaning t m 4154) (meaning t m 4426) source

theorem rule19832 (p2122 p3568 p4337 : Prop) (h : (¬ p2122) ∨ (¬ p3568) ∨ (¬ p4337)) : (¬ p2122) ∨ (¬ p3568) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial19832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory9088 (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule19832 (meaning t m 2122) (meaning t m 3568) (meaning t m 4337) source

theorem rule19834 (p3365 p3471 p4357 : Prop) (h : (¬ p3471) ∨ (¬ p3365) ∨ (¬ p4357)) : (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial19834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory9090 (m.theta 0 2) (m.theta 2 3) (m.theta 2 7)
  exact rule19834 (meaning t m 3365) (meaning t m 3471) (meaning t m 4357) source

theorem rule19835 (p2307 p3549 p5016 : Prop) (h : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p5016)) : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial19835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory9091 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule19835 (meaning t m 2307) (meaning t m 3549) (meaning t m 5016) source

theorem rule19836 (p3422 p3876 p3920 : Prop) (h : (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3920)) : (¬ p3422) ∨ (¬ p3876) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial19836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory9092 (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule19836 (meaning t m 3422) (meaning t m 3876) (meaning t m 3920) source

theorem rule19838 (p2299 p2911 p3921 : Prop) (h : (¬ p2911) ∨ (¬ p2299) ∨ (¬ p3921)) : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial19838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory9094 (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule19838 (meaning t m 2299) (meaning t m 2911) (meaning t m 3921) source

theorem rule19839 (p2230 p3684 p3759 : Prop) (h : (¬ p3759) ∨ (¬ p2230) ∨ (¬ p3684)) : (¬ p2230) ∨ (¬ p3684) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial19839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory9095 (m.theta 0 4) (m.theta 2 4) (m.theta 4 5)
  exact rule19839 (meaning t m 2230) (meaning t m 3684) (meaning t m 3759) source

theorem rule19840 (p2003 p2233 p2573 p2581 : Prop) (h : p2581 ∨ (¬ p2003) ∨ (¬ p2573) ∨ p2233) : (¬ p2003) ∨ (p2233) ∨ (¬ p2573) ∨ (p2581) := by
  classical
  tauto

theorem initial19840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2581) := by
  have source := ElevenTheory.theory9096 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6)
  exact rule19840 (meaning t m 2003) (meaning t m 2233) (meaning t m 2573) (meaning t m 2581) source

theorem rule19841 (p2230 p3540 p3741 : Prop) (h : (¬ p3540) ∨ (¬ p2230) ∨ (¬ p3741)) : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial19841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory9097 (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule19841 (meaning t m 2230) (meaning t m 3540) (meaning t m 3741) source

theorem rule19842 (p2230 p2476 p4355 : Prop) (h : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p4355)) : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p4355) := by
  classical
  tauto

theorem initial19842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 4355)) := by
  have source := ElevenTheory.theory9098 (m.theta 0 4) (m.theta 4 5) (m.theta 4 8)
  exact rule19842 (meaning t m 2230) (meaning t m 2476) (meaning t m 4355) source

theorem rule19843 (p2295 p3097 p3745 : Prop) (h : (¬ p2295) ∨ (¬ p3097) ∨ (¬ p3745)) : (¬ p2295) ∨ (¬ p3097) ∨ (¬ p3745) := by
  classical
  tauto

theorem initial19843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3745)) := by
  have source := ElevenTheory.theory9099 (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule19843 (meaning t m 2295) (meaning t m 3097) (meaning t m 3745) source

theorem rule19844 (p2383 p3743 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p2383) ∨ (¬ p3743)) : (¬ p2383) ∨ (¬ p3743) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial19844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory9100 (m.theta 0 6) (m.theta 5 6) (m.theta 6 8)
  exact rule19844 (meaning t m 2383) (meaning t m 3743) (meaning t m 3989) source

theorem rule19845 (p2027 p2230 p2737 p3238 p3759 p4257 p4749 : Prop) (h : (¬ p4257) ∨ (¬ p3238) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4749) ∨ (¬ p2737) ∨ (¬ p3759)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2737) ∨ (¬ p3238) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial19845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory9101 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule19845 (meaning t m 2027) (meaning t m 2230) (meaning t m 2737) (meaning t m 3238) (meaning t m 3759) (meaning t m 4257) (meaning t m 4749) source

theorem rule19847 (p2027 p3461 p3690 p4187 p4381 p4556 : Prop) (h : (¬ p3690) ∨ (¬ p4556) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p4187)) : (p2027) ∨ (¬ p3461) ∨ (¬ p3690) ∨ (¬ p4187) ∨ (¬ p4381) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial19847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory9103 t (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19847 (meaning t m 2027) (meaning t m 3461) (meaning t m 3690) (meaning t m 4187) (meaning t m 4381) (meaning t m 4556) source

theorem rule19848 (p3461 p4381 p4396 : Prop) (h : (¬ p3461) ∨ (¬ p4381) ∨ (¬ p4396)) : (¬ p3461) ∨ (¬ p4381) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial19848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory9104 (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule19848 (meaning t m 3461) (meaning t m 4381) (meaning t m 4396) source

theorem rule19849 (p2946 p2995 p3414 : Prop) (h : (¬ p2946) ∨ (¬ p3414) ∨ (¬ p2995)) : (¬ p2946) ∨ (¬ p2995) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial19849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory9105 (m.theta 0 3) (m.theta 3 5) (m.theta 3 7)
  exact rule19849 (meaning t m 2946) (meaning t m 2995) (meaning t m 3414) source

theorem rule19850 (p2958 p3051 p3414 p3699 : Prop) (h : (¬ p2958) ∨ (¬ p3414) ∨ (¬ p3051) ∨ (¬ p3699)) : (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3414) ∨ (¬ p3699) := by
  classical
  tauto

theorem initial19850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) := by
  have source := ElevenTheory.theory9106 (m.theta 0 3) (m.theta 0 5) (m.theta 3 7) (m.theta 5 7)
  exact rule19850 (meaning t m 2958) (meaning t m 3051) (meaning t m 3414) (meaning t m 3699) source

theorem rule19851 (p2027 p3355 p3540 p3947 p4327 p4451 : Prop) (h : (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ p2027 ∨ (¬ p3355) ∨ (¬ p4451)) : (p2027) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4451) := by
  classical
  tauto

theorem initial19851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4327)) ∨ (¬ (meaning t m 4451)) := by
  have source := ElevenTheory.theory9107 t (m.theta 0 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule19851 (meaning t m 2027) (meaning t m 3355) (meaning t m 3540) (meaning t m 3947) (meaning t m 4327) (meaning t m 4451) source

theorem rule19852 (p3355 p3540 p4635 : Prop) (h : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4635)) : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4635) := by
  classical
  tauto

theorem initial19852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4635)) := by
  have source := ElevenTheory.theory9108 (m.theta 0 4) (m.theta 4 7) (m.theta 4 9)
  exact rule19852 (meaning t m 3355) (meaning t m 3540) (meaning t m 4635) source

theorem rule19855 (p2891 p4192 p4363 : Prop) (h : (¬ p4363) ∨ (¬ p2891) ∨ (¬ p4192)) : (¬ p2891) ∨ (¬ p4192) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial19855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4192)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory9111 (m.theta 1 5) (m.theta 5 7) (m.theta 5 9)
  exact rule19855 (meaning t m 2891) (meaning t m 4192) (meaning t m 4363) source

theorem rule19856 (p2027 p2881 p2891 p4363 p4382 p4666 : Prop) (h : (¬ p2881) ∨ (¬ p4363) ∨ (¬ p2891) ∨ (¬ p4666) ∨ p2027 ∨ (¬ p4382)) : (p2027) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial19856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory9112 t (m.theta 1 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8) (m.theta 7 9)
  exact rule19856 (meaning t m 2027) (meaning t m 2881) (meaning t m 2891) (meaning t m 4363) (meaning t m 4382) (meaning t m 4666) source

theorem rule19857 (p2440 p2850 p4343 : Prop) (h : (¬ p2440) ∨ (¬ p2850) ∨ (¬ p4343)) : (¬ p2440) ∨ (¬ p2850) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial19857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory9113 (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule19857 (meaning t m 2440) (meaning t m 2850) (meaning t m 4343) source

theorem rule19858 (p3189 p3848 p5111 : Prop) (h : (¬ p3189) ∨ (¬ p3848) ∨ (¬ p5111)) : (¬ p3189) ∨ (¬ p3848) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial19858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory9114 (m.theta 1 3) (m.theta 3 8) (m.theta 3 9)
  exact rule19858 (meaning t m 3189) (meaning t m 3848) (meaning t m 5111) source

end SunPrize.SMT
