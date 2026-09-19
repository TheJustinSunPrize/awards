import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory065
import SunPrize.Certificate.Theory066
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule37731 (p1998 p2027 p2156 p2177 p2202 p2245 p2274 p2518 p2657 p3238 p4256 p4521 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p4521) ∨ (¬ p3238) ∨ p2202 ∨ (¬ p2177) ∨ (¬ p2245) ∨ (¬ p2156) ∨ (¬ p1998) ∨ (¬ p2274) ∨ (¬ p4256) ∨ (¬ p2518)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (p2202) ∨ (¬ p2245) ∨ (¬ p2274) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (¬ p3238) ∨ (¬ p4256) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial37731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory26987 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule37731 (meaning t m 1998) (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2202) (meaning t m 2245) (meaning t m 2274) (meaning t m 2518) (meaning t m 2657) (meaning t m 3238) (meaning t m 4256) (meaning t m 4521) source

theorem rule37734 (p5284 p5387 p5454 : Prop) (h : (¬ p5454) ∨ (¬ p5284) ∨ p5387) : (¬ p5284) ∨ (p5387) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial37734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5284)) ∨ (meaning t m 5387) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory26990 (m.theta 2 9) (m.theta 3 9) (m.theta 9 10)
  exact rule37734 (meaning t m 5284) (meaning t m 5387) (meaning t m 5454) source

theorem rule37735 (p2005 p2027 p2437 p2545 p2819 p3876 p3956 p4375 : Prop) (h : (¬ p2005) ∨ p2545 ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3876) ∨ (¬ p3956) ∨ (¬ p4375) ∨ (¬ p2819)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2819) ∨ (¬ p3876) ∨ (¬ p3956) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial37735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory26991 t (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule37735 (meaning t m 2005) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2819) (meaning t m 3876) (meaning t m 3956) (meaning t m 4375) source

theorem rule37738 (p1975 p2027 p2202 p2299 p2589 p2911 p3389 : Prop) (h : (¬ p2911) ∨ (¬ p1975) ∨ (¬ p2589) ∨ p2202 ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3389)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2299) ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial37738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory26994 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37738 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2299) (meaning t m 2589) (meaning t m 2911) (meaning t m 3389) source

theorem rule37743 (p2027 p2657 p2727 p2797 p4154 p4787 : Prop) (h : (¬ p2657) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p4787) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2797) ∨ (¬ p4154) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial37743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory26999 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule37743 (meaning t m 2027) (meaning t m 2657) (meaning t m 2727) (meaning t m 2797) (meaning t m 4154) (meaning t m 4787) source

theorem rule37744 (p2027 p2437 p3136 p3364 p3876 p4704 : Prop) (h : (¬ p3136) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p3364) ∨ (¬ p2437) ∨ (¬ p3876)) : (p2027) ∨ (¬ p2437) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3876) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial37744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory27000 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule37744 (meaning t m 2027) (meaning t m 2437) (meaning t m 3136) (meaning t m 3364) (meaning t m 3876) (meaning t m 4704) source

theorem rule37746 (p1994 p2027 p2440 p2765 p2972 p4031 p4032 p4173 : Prop) (h : p2765 ∨ p2027 ∨ (¬ p4031) ∨ (¬ p4173) ∨ (¬ p2972) ∨ (¬ p4032) ∨ (¬ p1994) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2765) ∨ (¬ p2972) ∨ (¬ p4031) ∨ (¬ p4032) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial37746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory27002 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule37746 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2765) (meaning t m 2972) (meaning t m 4031) (meaning t m 4032) (meaning t m 4173) source

theorem rule37753 (p2027 p2264 p2363 p2685 p2696 p3860 p4261 p4503 p4733 : Prop) (h : (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p2363) ∨ (¬ p4503) ∨ (¬ p3860) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4503) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory27009 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 3) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37753 (meaning t m 2027) (meaning t m 2264) (meaning t m 2363) (meaning t m 2685) (meaning t m 2696) (meaning t m 3860) (meaning t m 4261) (meaning t m 4503) (meaning t m 4733) source

theorem rule37760 (p2027 p2245 p2598 p2850 p2982 p3414 p3553 p4348 p4450 p4733 : Prop) (h : (¬ p2245) ∨ (¬ p2982) ∨ (¬ p2850) ∨ (¬ p3414) ∨ (¬ p2598) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4450)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial37760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory27016 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9)
  exact rule37760 (meaning t m 2027) (meaning t m 2245) (meaning t m 2598) (meaning t m 2850) (meaning t m 2982) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) (meaning t m 4450) (meaning t m 4733) source

theorem rule37762 (p1998 p2027 p2427 p2598 p2611 p2850 p2881 : Prop) (h : p2611 ∨ (¬ p2598) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2850) ∨ (¬ p2427) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial37762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory27018 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule37762 (meaning t m 1998) (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 2881) source

theorem rule37764 (p1997 p2027 p2766 p3941 p3961 p4235 p4283 p4348 p5590 : Prop) (h : (¬ p4235) ∨ (¬ p3941) ∨ (¬ p1997) ∨ (¬ p5590) ∨ (¬ p3961) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p4283) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (p2766) ∨ (¬ p3941) ∨ (¬ p3961) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4348) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial37764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory27020 t (m.theta 0 7) (m.theta 0 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37764 (meaning t m 1997) (meaning t m 2027) (meaning t m 2766) (meaning t m 3941) (meaning t m 3961) (meaning t m 4235) (meaning t m 4283) (meaning t m 4348) (meaning t m 5590) source

theorem rule37765 (p1984 p2027 p2633 p2737 p3365 p3553 p3588 p3873 p4777 : Prop) (h : (¬ p3365) ∨ (¬ p4777) ∨ (¬ p3553) ∨ (¬ p1984) ∨ p2027 ∨ p2633 ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p2737)) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4777) := by
  classical
  tauto

theorem initial37765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4777)) := by
  have source := ElevenTheory.theory27021 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule37765 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 2737) (meaning t m 3365) (meaning t m 3553) (meaning t m 3588) (meaning t m 3873) (meaning t m 4777) source

theorem rule37766 (p2027 p2553 p2573 p2665 p3568 p4194 : Prop) (h : (¬ p4194) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2553) ∨ (¬ p3568)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2665) ∨ (¬ p3568) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial37766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory27022 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule37766 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2665) (meaning t m 3568) (meaning t m 4194) source

theorem rule37767 (p2027 p2132 p2619 p3591 p3923 p3969 p4347 p4733 p5122 : Prop) (h : (¬ p2132) ∨ p2027 ∨ (¬ p5122) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p2619) ∨ (¬ p4733) ∨ (¬ p3969) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4733) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial37767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory27023 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37767 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 3591) (meaning t m 3923) (meaning t m 3969) (meaning t m 4347) (meaning t m 4733) (meaning t m 5122) source

theorem rule37769 (p2027 p2156 p2427 p2743 p3572 p3954 p4110 p4362 p4521 : Prop) (h : p2027 ∨ (¬ p4362) ∨ (¬ p3954) ∨ (¬ p2743) ∨ (¬ p2427) ∨ (¬ p3572) ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4521)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2743) ∨ (¬ p3572) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial37769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory27025 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule37769 (meaning t m 2027) (meaning t m 2156) (meaning t m 2427) (meaning t m 2743) (meaning t m 3572) (meaning t m 3954) (meaning t m 4110) (meaning t m 4362) (meaning t m 4521) source

theorem rule37770 (p2972 p3115 p3412 : Prop) (h : (¬ p3412) ∨ (¬ p2972) ∨ p3115) : (¬ p2972) ∨ (p3115) ∨ (¬ p3412) := by
  classical
  tauto

theorem initial37770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2972)) ∨ (meaning t m 3115) ∨ (¬ (meaning t m 3412)) := by
  have source := ElevenTheory.theory27026 (m.theta 1 5) (m.theta 3 5) (m.theta 5 9)
  exact rule37770 (meaning t m 2972) (meaning t m 3115) (meaning t m 3412) source

theorem rule37773 (p2027 p2295 p2563 p4235 p4275 p4560 : Prop) (h : (¬ p2295) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4560) ∨ p2027 ∨ (¬ p2563)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial37773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory27029 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule37773 (meaning t m 2027) (meaning t m 2295) (meaning t m 2563) (meaning t m 4235) (meaning t m 4275) (meaning t m 4560) source

theorem rule37774 (p2027 p2553 p2573 p3172 p3791 p4118 p4236 p4419 p4444 p4826 : Prop) (h : (¬ p2553) ∨ (¬ p4118) ∨ (¬ p4419) ∨ (¬ p4236) ∨ (¬ p3791) ∨ (¬ p4826) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3172) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3172) ∨ (¬ p3791) ∨ (¬ p4118) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial37774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory27030 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule37774 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 3172) (meaning t m 3791) (meaning t m 4118) (meaning t m 4236) (meaning t m 4419) (meaning t m 4444) (meaning t m 4826) source

theorem rule37775 (p1983 p2027 p2545 p2810 p3506 p3755 p4381 : Prop) (h : p2545 ∨ (¬ p4381) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p1983) ∨ (¬ p3755)) : (¬ p1983) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial37775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory27031 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule37775 (meaning t m 1983) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 3506) (meaning t m 3755) (meaning t m 4381) source

theorem rule37777 (p2027 p2156 p2252 p2396 p2553 p2741 p3005 p3096 p3172 p3519 p4035 p4376 p4399 p4663 : Prop) (h : (¬ p4376) ∨ (¬ p2252) ∨ (¬ p3096) ∨ (¬ p4399) ∨ (¬ p3005) ∨ (¬ p2553) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p2396) ∨ (¬ p4663) ∨ (¬ p4035) ∨ (¬ p3172) ∨ (¬ p2741)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2741) ∨ (¬ p3005) ∨ (¬ p3096) ∨ (¬ p3172) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4663) := by
  classical
  tauto

theorem initial37777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4663)) := by
  have source := ElevenTheory.theory27033 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule37777 (meaning t m 2027) (meaning t m 2156) (meaning t m 2252) (meaning t m 2396) (meaning t m 2553) (meaning t m 2741) (meaning t m 3005) (meaning t m 3096) (meaning t m 3172) (meaning t m 3519) (meaning t m 4035) (meaning t m 4376) (meaning t m 4399) (meaning t m 4663) source

theorem rule37780 (p2027 p2396 p3276 p3951 p4260 p4824 p4947 : Prop) (h : (¬ p4260) ∨ (¬ p2396) ∨ (¬ p3951) ∨ (¬ p4947) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4824)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3276) ∨ (¬ p3951) ∨ (¬ p4260) ∨ (¬ p4824) ∨ (¬ p4947) := by
  classical
  tauto

theorem initial37780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4824)) ∨ (¬ (meaning t m 4947)) := by
  have source := ElevenTheory.theory27036 t (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 7 9) (m.theta 9 10)
  exact rule37780 (meaning t m 2027) (meaning t m 2396) (meaning t m 3276) (meaning t m 3951) (meaning t m 4260) (meaning t m 4824) (meaning t m 4947) source

theorem rule37782 (p2027 p2352 p2363 p2573 p2743 p3954 p4035 p5113 p5190 : Prop) (h : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p5190) ∨ (¬ p5113) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3954) ∨ (¬ p4035) ∨ (¬ p5113) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5113)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory27038 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule37782 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 2573) (meaning t m 2743) (meaning t m 3954) (meaning t m 4035) (meaning t m 5113) (meaning t m 5190) source

theorem rule37790 (p2027 p2144 p2156 p3105 p3266 p3346 p3758 p4425 p4450 p4729 : Prop) (h : (¬ p3105) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p4729) ∨ p2027 ∨ (¬ p4450) ∨ (¬ p3758) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3105) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p3758) ∨ (¬ p4425) ∨ (¬ p4450) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial37790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory27046 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 5) (m.theta 4 9) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37790 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 3105) (meaning t m 3266) (meaning t m 3346) (meaning t m 3758) (meaning t m 4425) (meaning t m 4450) (meaning t m 4729) source

theorem rule37792 (p2027 p2363 p2630 p2696 p2753 p3083 p3645 p3692 p4120 p4596 p4877 : Prop) (h : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p4877) ∨ (¬ p3083) ∨ (¬ p4120) ∨ (¬ p4596) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p3645) ∨ (¬ p2753) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3083) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4596) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27048 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37792 (meaning t m 2027) (meaning t m 2363) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 3083) (meaning t m 3645) (meaning t m 3692) (meaning t m 4120) (meaning t m 4596) (meaning t m 4877) source

theorem rule37794 (p2027 p2663 p2810 p3389 p3742 p4790 : Prop) (h : (¬ p2663) ∨ (¬ p3742) ∨ (¬ p2810) ∨ (¬ p3389) ∨ (¬ p4790) ∨ p2027) : (p2027) ∨ (¬ p2663) ∨ (¬ p2810) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial37794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory27050 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule37794 (meaning t m 2027) (meaning t m 2663) (meaning t m 2810) (meaning t m 3389) (meaning t m 3742) (meaning t m 4790) source

theorem rule37795 (p2027 p2187 p2753 p3343 p3362 p3389 p3742 p3744 p3923 p4870 p5322 : Prop) (h : (¬ p3923) ∨ (¬ p5322) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4870) ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3744) ∨ (¬ p3923) ∨ (¬ p4870) ∨ (¬ p5322) := by
  classical
  tauto

theorem initial37795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5322)) := by
  have source := ElevenTheory.theory27051 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule37795 (meaning t m 2027) (meaning t m 2187) (meaning t m 2753) (meaning t m 3343) (meaning t m 3362) (meaning t m 3389) (meaning t m 3742) (meaning t m 3744) (meaning t m 3923) (meaning t m 4870) (meaning t m 5322) source

theorem rule37801 (p2027 p2145 p2191 p2192 p2264 p2685 p2696 p3646 p4905 : Prop) (h : (¬ p3646) ∨ (¬ p2191) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p4905) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3646) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial37801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory27057 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule37801 (meaning t m 2027) (meaning t m 2145) (meaning t m 2191) (meaning t m 2192) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 3646) (meaning t m 4905) source

theorem rule37807 (p2027 p2797 p3297 p3319 p4035 p4761 p5379 : Prop) (h : (¬ p5379) ∨ (¬ p4761) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p3319) ∨ (¬ p3297) ∨ (¬ p4035)) : (p2027) ∨ (¬ p2797) ∨ (¬ p3297) ∨ (¬ p3319) ∨ (¬ p4035) ∨ (¬ p4761) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial37807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4761)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory27063 t (m.theta 0 9) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9)
  exact rule37807 (meaning t m 2027) (meaning t m 2797) (meaning t m 3297) (meaning t m 3319) (meaning t m 4035) (meaning t m 4761) (meaning t m 5379) source

theorem rule37810 (p2027 p4075 p4235 p4431 p4632 p5660 : Prop) (h : (¬ p4632) ∨ (¬ p4235) ∨ (¬ p5660) ∨ (¬ p4431) ∨ p2027 ∨ (¬ p4075)) : (p2027) ∨ (¬ p4075) ∨ (¬ p4235) ∨ (¬ p4431) ∨ (¬ p4632) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial37810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4632)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory27066 t (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10)
  exact rule37810 (meaning t m 2027) (meaning t m 4075) (meaning t m 4235) (meaning t m 4431) (meaning t m 4632) (meaning t m 5660) source

theorem rule37812 (p1987 p2027 p2696 p2764 p3425 p4324 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p1987) ∨ (¬ p4324) ∨ p2764 ∨ (¬ p2696) ∨ (¬ p3425) ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (p2764) ∨ (¬ p3425) ∨ (¬ p4324) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial37812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory27068 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule37812 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 2764) (meaning t m 3425) (meaning t m 4324) (meaning t m 4381) source

theorem rule37814 (p3580 p4044 p4121 : Prop) (h : (¬ p3580) ∨ (¬ p4044) ∨ p4121) : (¬ p3580) ∨ (¬ p4044) ∨ (p4121) := by
  classical
  tauto

theorem initial37814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4044)) ∨ (meaning t m 4121) := by
  have source := ElevenTheory.theory27070 (m.theta 3 4) (m.theta 3 7) (m.theta 3 8)
  exact rule37814 (meaning t m 3580) (meaning t m 4044) (meaning t m 4121) source

theorem rule37817 (p2295 p3323 p4187 : Prop) (h : (¬ p2295) ∨ (¬ p4187) ∨ p3323) : (¬ p2295) ∨ (p3323) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial37817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2295)) ∨ (meaning t m 3323) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory27073 (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule37817 (meaning t m 2295) (meaning t m 3323) (meaning t m 4187) source

theorem rule37821 (p2027 p2331 p2589 p2819 p3979 p4117 p4322 p4337 p4729 p4948 p5119 : Prop) (h : (¬ p4729) ∨ (¬ p4117) ∨ (¬ p2819) ∨ (¬ p4337) ∨ (¬ p2331) ∨ (¬ p3979) ∨ (¬ p5119) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p4948)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2589) ∨ (¬ p2819) ∨ (¬ p3979) ∨ (¬ p4117) ∨ (¬ p4322) ∨ (¬ p4337) ∨ (¬ p4729) ∨ (¬ p4948) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial37821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory27077 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule37821 (meaning t m 2027) (meaning t m 2331) (meaning t m 2589) (meaning t m 2819) (meaning t m 3979) (meaning t m 4117) (meaning t m 4322) (meaning t m 4337) (meaning t m 4729) (meaning t m 4948) (meaning t m 5119) source

theorem rule37822 (p2027 p2470 p2528 p2630 p2656 p3414 p3659 p4325 p4787 p5118 p5558 : Prop) (h : (¬ p2656) ∨ (¬ p4325) ∨ (¬ p3414) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p5118) ∨ (¬ p3659) ∨ (¬ p5558) ∨ (¬ p4787) ∨ (¬ p2470)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3414) ∨ (¬ p3659) ∨ (¬ p4325) ∨ (¬ p4787) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial37822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory27078 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37822 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2630) (meaning t m 2656) (meaning t m 3414) (meaning t m 3659) (meaning t m 4325) (meaning t m 4787) (meaning t m 5118) (meaning t m 5558) source

theorem rule37823 (p2027 p2437 p2630 p4195 p4389 p4711 : Prop) (h : (¬ p4711) ∨ (¬ p4389) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p4195) ∨ p2027) : (p2027) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial37823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory27079 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7)
  exact rule37823 (meaning t m 2027) (meaning t m 2437) (meaning t m 2630) (meaning t m 4195) (meaning t m 4389) (meaning t m 4711) source

theorem rule37827 (p4171 p4190 p5107 : Prop) (h : (¬ p4171) ∨ (¬ p4190) ∨ p5107) : (¬ p4171) ∨ (¬ p4190) ∨ (p5107) := by
  classical
  tauto

theorem initial37827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4171)) ∨ (¬ (meaning t m 4190)) ∨ (meaning t m 5107) := by
  have source := ElevenTheory.theory27083 (m.theta 3 9) (m.theta 6 9) (m.theta 8 9)
  exact rule37827 (meaning t m 4171) (meaning t m 4190) (meaning t m 5107) source

theorem rule37833 (p2027 p2470 p2528 p2685 p2741 p2996 p3519 p3877 p4347 p4376 p4774 : Prop) (h : (¬ p2528) ∨ (¬ p2470) ∨ (¬ p3519) ∨ (¬ p2741) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4347) ∨ (¬ p4774) ∨ (¬ p3877) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2685) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p3519) ∨ (¬ p3877) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p4774) := by
  classical
  tauto

theorem initial37833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4774)) := by
  have source := ElevenTheory.theory27089 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37833 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2685) (meaning t m 2741) (meaning t m 2996) (meaning t m 3519) (meaning t m 3877) (meaning t m 4347) (meaning t m 4376) (meaning t m 4774) source

theorem rule37834 (p4492 p4877 p5317 : Prop) (h : (¬ p4492) ∨ (¬ p4877) ∨ p5317) : (¬ p4492) ∨ (¬ p4877) ∨ (p5317) := by
  classical
  tauto

theorem initial37834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4877)) ∨ (meaning t m 5317) := by
  have source := ElevenTheory.theory27090 t (m.theta 1 2) (m.theta 1 5) (m.theta 1 8)
  exact rule37834 (meaning t m 4492) (meaning t m 4877) (meaning t m 5317) source

theorem rule37835 (p2027 p3631 p3821 p4283 p4320 p4431 p4960 : Prop) (h : (¬ p4283) ∨ (¬ p3821) ∨ (¬ p3631) ∨ (¬ p4960) ∨ p2027 ∨ (¬ p4320) ∨ (¬ p4431)) : (p2027) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4431) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial37835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory27091 t (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule37835 (meaning t m 2027) (meaning t m 3631) (meaning t m 3821) (meaning t m 4283) (meaning t m 4320) (meaning t m 4431) (meaning t m 4960) source

theorem rule37837 (p2027 p2132 p3105 p3548 p3680 p4366 p4733 p5123 p5558 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p5558) ∨ (¬ p3105) ∨ (¬ p4366) ∨ (¬ p3548) ∨ (¬ p3680) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2132) ∨ (¬ p3105) ∨ (¬ p3548) ∨ (¬ p3680) ∨ (¬ p4366) ∨ (¬ p4733) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial37837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory27093 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 7) (m.theta 2 5) (m.theta 5 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule37837 (meaning t m 2027) (meaning t m 2132) (meaning t m 3105) (meaning t m 3548) (meaning t m 3680) (meaning t m 4366) (meaning t m 4733) (meaning t m 5123) (meaning t m 5558) source

theorem rule37839 (p2027 p2104 p2139 p2363 p2373 p3051 p4235 p4340 p4433 : Prop) (h : (¬ p2373) ∨ (¬ p4340) ∨ (¬ p2104) ∨ (¬ p3051) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4433) ∨ (¬ p2139)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2139) ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4340) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial37839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory27095 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule37839 (meaning t m 2027) (meaning t m 2104) (meaning t m 2139) (meaning t m 2363) (meaning t m 2373) (meaning t m 3051) (meaning t m 4235) (meaning t m 4340) (meaning t m 4433) source

theorem rule37842 (p1990 p2027 p2545 p2563 p2810 p3755 p4039 p4948 : Prop) (h : p2027 ∨ (¬ p2563) ∨ (¬ p4948) ∨ (¬ p1990) ∨ (¬ p2810) ∨ (¬ p4039) ∨ p2545 ∨ (¬ p3755)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p4039) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial37842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4039)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory27098 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule37842 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2563) (meaning t m 2810) (meaning t m 3755) (meaning t m 4039) (meaning t m 4948) source

theorem rule37844 (p2027 p2459 p2797 p2911 p2963 p3366 p3389 p3519 p4035 p4236 p4376 p5113 : Prop) (h : (¬ p2963) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p5113) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p4035) ∨ (¬ p3389) ∨ (¬ p2911) ∨ (¬ p4376) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p2963) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial37844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory27100 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37844 (meaning t m 2027) (meaning t m 2459) (meaning t m 2797) (meaning t m 2911) (meaning t m 2963) (meaning t m 3366) (meaning t m 3389) (meaning t m 3519) (meaning t m 4035) (meaning t m 4236) (meaning t m 4376) (meaning t m 5113) source

theorem rule37853 (p1980 p2027 p2114 p3093 p3309 p3568 p3954 : Prop) (h : (¬ p3093) ∨ (¬ p1980) ∨ p2114 ∨ (¬ p3954) ∨ (¬ p3568) ∨ (¬ p3309) ∨ p2027) : (¬ p1980) ∨ (p2027) ∨ (p2114) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial37853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory27109 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7)
  exact rule37853 (meaning t m 1980) (meaning t m 2027) (meaning t m 2114) (meaning t m 3093) (meaning t m 3309) (meaning t m 3568) (meaning t m 3954) source

theorem rule37855 (p2027 p2911 p2963 p3389 p3941 p4037 p4191 p4236 p4419 p5119 : Prop) (h : (¬ p2911) ∨ (¬ p3941) ∨ (¬ p4419) ∨ (¬ p3389) ∨ p2027 ∨ (¬ p4236) ∨ (¬ p2963) ∨ (¬ p4037) ∨ (¬ p5119) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2911) ∨ (¬ p2963) ∨ (¬ p3389) ∨ (¬ p3941) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial37855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory27111 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule37855 (meaning t m 2027) (meaning t m 2911) (meaning t m 2963) (meaning t m 3389) (meaning t m 3941) (meaning t m 4037) (meaning t m 4191) (meaning t m 4236) (meaning t m 4419) (meaning t m 5119) source

theorem rule37857 (p2027 p2982 p3051 p3292 p3366 p3461 p3519 p4235 p4236 p4376 p4397 p4399 p5284 : Prop) (h : (¬ p4397) ∨ (¬ p4399) ∨ (¬ p4376) ∨ (¬ p5284) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p4235) ∨ (¬ p3519) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p3292) ∨ (¬ p4236) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3051) ∨ (¬ p3292) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p3519) ∨ (¬ p4235) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4397) ∨ (¬ p4399) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial37857 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory27113 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 3 9) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule37857 (meaning t m 2027) (meaning t m 2982) (meaning t m 3051) (meaning t m 3292) (meaning t m 3366) (meaning t m 3461) (meaning t m 3519) (meaning t m 4235) (meaning t m 4236) (meaning t m 4376) (meaning t m 4397) (meaning t m 4399) (meaning t m 5284) source

theorem rule37859 (p2027 p2220 p2630 p2656 p3414 p3553 p3969 p4348 p4399 p4787 p5122 : Prop) (h : p2027 ∨ (¬ p5122) ∨ (¬ p2220) ∨ (¬ p3414) ∨ (¬ p2656) ∨ (¬ p2630) ∨ (¬ p3969) ∨ (¬ p3553) ∨ (¬ p4399) ∨ (¬ p4787) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p4399) ∨ (¬ p4787) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial37859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4787)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory27115 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37859 (meaning t m 2027) (meaning t m 2220) (meaning t m 2630) (meaning t m 2656) (meaning t m 3414) (meaning t m 3553) (meaning t m 3969) (meaning t m 4348) (meaning t m 4399) (meaning t m 4787) (meaning t m 5122) source

theorem rule37861 (p2027 p2797 p2911 p2922 p2963 p3379 p3877 p4041 p4236 p4736 : Prop) (h : p2027 ∨ (¬ p2922) ∨ (¬ p2911) ∨ (¬ p4736) ∨ (¬ p2797) ∨ (¬ p4236) ∨ (¬ p4041) ∨ (¬ p3379) ∨ (¬ p2963) ∨ (¬ p3877)) : (p2027) ∨ (¬ p2797) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2963) ∨ (¬ p3379) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial37861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27117 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8)
  exact rule37861 (meaning t m 2027) (meaning t m 2797) (meaning t m 2911) (meaning t m 2922) (meaning t m 2963) (meaning t m 3379) (meaning t m 3877) (meaning t m 4041) (meaning t m 4236) (meaning t m 4736) source

theorem rule37864 (p3192 p3201 p3333 : Prop) (h : (¬ p3201) ∨ (¬ p3192) ∨ p3333) : (¬ p3192) ∨ (¬ p3201) ∨ (p3333) := by
  classical
  tauto

theorem initial37864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3201)) ∨ (meaning t m 3333) := by
  have source := ElevenTheory.theory27120 (m.theta 2 4) (m.theta 4 7) (m.theta 4 9)
  exact rule37864 (meaning t m 3192) (meaning t m 3201) (meaning t m 3333) source

theorem rule37868 (p2027 p2589 p3347 p3399 p3527 p3690 p3954 p4235 p4666 p5216 : Prop) (h : p2027 ∨ (¬ p4666) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p3347) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p2589) ∨ (¬ p5216)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3347) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4235) ∨ (¬ p4666) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27124 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37868 (meaning t m 2027) (meaning t m 2589) (meaning t m 3347) (meaning t m 3399) (meaning t m 3527) (meaning t m 3690) (meaning t m 3954) (meaning t m 4235) (meaning t m 4666) (meaning t m 5216) source

theorem rule37871 (p1987 p2027 p2169 p2696 p2778 p3323 p3324 p3946 : Prop) (h : (¬ p2778) ∨ (¬ p1987) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3946) ∨ p2169 ∨ (¬ p3324) ∨ (¬ p3323)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2696) ∨ (¬ p2778) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial37871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory27127 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9)
  exact rule37871 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2696) (meaning t m 2778) (meaning t m 3323) (meaning t m 3324) (meaning t m 3946) source

theorem rule37874 (p2027 p2911 p3389 p3941 p3954 p4379 p5119 p5190 p5284 p5454 : Prop) (h : (¬ p3389) ∨ (¬ p5119) ∨ (¬ p2911) ∨ (¬ p3941) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p5190) ∨ (¬ p5454) ∨ (¬ p4379) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3941) ∨ (¬ p3954) ∨ (¬ p4379) ∨ (¬ p5119) ∨ (¬ p5190) ∨ (¬ p5284) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial37874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory27130 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 9) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule37874 (meaning t m 2027) (meaning t m 2911) (meaning t m 3389) (meaning t m 3941) (meaning t m 3954) (meaning t m 4379) (meaning t m 5119) (meaning t m 5190) (meaning t m 5284) (meaning t m 5454) source

theorem rule37875 (p2027 p2247 p2459 p2911 p3389 p4037 p4154 p4604 p5190 : Prop) (h : (¬ p4604) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p3389) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p4037) ∨ (¬ p4154)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4604) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial37875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory27131 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule37875 (meaning t m 2027) (meaning t m 2247) (meaning t m 2459) (meaning t m 2911) (meaning t m 3389) (meaning t m 4037) (meaning t m 4154) (meaning t m 4604) (meaning t m 5190) source

theorem rule37878 (p2027 p2249 p2299 p2534 p2963 p3189 p3256 p3549 p3922 p4420 : Prop) (h : (¬ p2299) ∨ (¬ p4420) ∨ (¬ p2249) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p3189) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2299) ∨ (¬ p2534) ∨ (¬ p2963) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3549) ∨ (¬ p3922) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial37878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory27134 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37878 (meaning t m 2027) (meaning t m 2249) (meaning t m 2299) (meaning t m 2534) (meaning t m 2963) (meaning t m 3189) (meaning t m 3256) (meaning t m 3549) (meaning t m 3922) (meaning t m 4420) source

theorem rule37880 (p2027 p3347 p3449 p3540 p3644 p3954 p4181 p4348 p5122 p5216 : Prop) (h : (¬ p5122) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3540) ∨ (¬ p3347) ∨ (¬ p4348) ∨ (¬ p4181) ∨ (¬ p3644) ∨ (¬ p3449)) : (p2027) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p4348) ∨ (¬ p5122) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27136 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37880 (meaning t m 2027) (meaning t m 3347) (meaning t m 3449) (meaning t m 3540) (meaning t m 3644) (meaning t m 3954) (meaning t m 4181) (meaning t m 4348) (meaning t m 5122) (meaning t m 5216) source

theorem rule37888 (p2662 p3343 p3355 : Prop) (h : (¬ p3343) ∨ (¬ p2662) ∨ p3355) : (¬ p2662) ∨ (¬ p3343) ∨ (p3355) := by
  classical
  tauto

theorem initial37888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3343)) ∨ (meaning t m 3355) := by
  have source := ElevenTheory.theory27144 (m.theta 0 4) (m.theta 3 4) (m.theta 4 9)
  exact rule37888 (meaning t m 2662) (meaning t m 3343) (meaning t m 3355) source

theorem rule37892 (p1984 p2027 p2299 p2633 p3791 p4366 p4442 : Prop) (h : p2633 ∨ (¬ p4442) ∨ (¬ p1984) ∨ (¬ p2299) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p3791)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3791) ∨ (¬ p4366) ∨ (¬ p4442) := by
  classical
  tauto

theorem initial37892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) := by
  have source := ElevenTheory.theory27148 t (m.theta 0 1) (m.theta 1 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule37892 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3791) (meaning t m 4366) (meaning t m 4442) source

theorem rule37894 (p1990 p2027 p2563 p2656 p2688 p2727 p3051 p4235 p4399 : Prop) (h : (¬ p1990) ∨ (¬ p4399) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p4235) ∨ p2688 ∨ (¬ p2656) ∨ (¬ p2563) ∨ (¬ p2727)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3051) ∨ (¬ p4235) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial37894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory27150 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule37894 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 3051) (meaning t m 4235) (meaning t m 4399) source

theorem rule37899 (p1984 p2027 p2545 p2810 p3483 p3591 p4026 p4426 : Prop) (h : (¬ p4026) ∨ (¬ p1984) ∨ p2545 ∨ p2027 ∨ (¬ p2810) ∨ (¬ p4426) ∨ (¬ p3591) ∨ (¬ p3483)) : (¬ p1984) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3483) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial37899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory27155 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 6 9)
  exact rule37899 (meaning t m 1984) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 3483) (meaning t m 3591) (meaning t m 4026) (meaning t m 4426) source

theorem rule37906 (p1975 p2027 p2166 p2534 p2553 p2873 p3146 p3573 : Prop) (h : (¬ p2166) ∨ p2873 ∨ p2027 ∨ (¬ p2553) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3573) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2534) ∨ (¬ p2553) ∨ (p2873) ∨ (¬ p3146) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial37906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory27162 t (m.theta 1 5) (m.theta 4 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 7) (m.theta 8 9)
  exact rule37906 (meaning t m 1975) (meaning t m 2027) (meaning t m 2166) (meaning t m 2534) (meaning t m 2553) (meaning t m 2873) (meaning t m 3146) (meaning t m 3573) source

theorem rule37907 (p2027 p2098 p2145 p2563 p3609 p3646 p3880 p4348 p4905 : Prop) (h : (¬ p2145) ∨ (¬ p2098) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3609) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4905) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial37907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory27163 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37907 (meaning t m 2027) (meaning t m 2098) (meaning t m 2145) (meaning t m 2563) (meaning t m 3609) (meaning t m 3646) (meaning t m 3880) (meaning t m 4348) (meaning t m 4905) source

theorem rule37910 (p2027 p2589 p2753 p3166 p3256 p3347 p3989 p4110 p4117 p4348 p4503 p5216 : Prop) (h : (¬ p4117) ∨ (¬ p3989) ∨ (¬ p3256) ∨ (¬ p4503) ∨ (¬ p2753) ∨ (¬ p4348) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p4110) ∨ (¬ p3347) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3347) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p4348) ∨ (¬ p4503) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27166 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37910 (meaning t m 2027) (meaning t m 2589) (meaning t m 2753) (meaning t m 3166) (meaning t m 3256) (meaning t m 3347) (meaning t m 3989) (meaning t m 4110) (meaning t m 4117) (meaning t m 4348) (meaning t m 4503) (meaning t m 5216) source

theorem rule37912 (p2363 p2459 p4138 : Prop) (h : (¬ p2363) ∨ (¬ p4138) ∨ p2459) : (¬ p2363) ∨ (p2459) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial37912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (meaning t m 2459) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory27168 (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37912 (meaning t m 2363) (meaning t m 2459) (meaning t m 4138) source

theorem rule37913 (p2027 p2505 p2696 p3319 p3425 p3461 p3590 p4324 p4444 p4669 p4749 : Prop) (h : p2027 ∨ (¬ p4444) ∨ (¬ p3319) ∨ (¬ p3425) ∨ (¬ p4324) ∨ (¬ p2696) ∨ (¬ p4749) ∨ (¬ p4669) ∨ (¬ p2505) ∨ (¬ p3590) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2505) ∨ (¬ p2696) ∨ (¬ p3319) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p3590) ∨ (¬ p4324) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial37913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory27169 t (m.theta 0 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37913 (meaning t m 2027) (meaning t m 2505) (meaning t m 2696) (meaning t m 3319) (meaning t m 3425) (meaning t m 3461) (meaning t m 3590) (meaning t m 4324) (meaning t m 4444) (meaning t m 4669) (meaning t m 4749) source

theorem rule37916 (p2027 p2145 p2528 p2651 p3097 p3641 p3646 p4107 p4117 p4343 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p3641) ∨ (¬ p2528) ∨ (¬ p4117) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p4343) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p2145) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3097) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4343) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial37916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory27172 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 4) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule37916 (meaning t m 2027) (meaning t m 2145) (meaning t m 2528) (meaning t m 2651) (meaning t m 3097) (meaning t m 3641) (meaning t m 3646) (meaning t m 4107) (meaning t m 4117) (meaning t m 4343) (meaning t m 4669) source

theorem rule37918 (p2027 p2241 p2553 p2598 p2750 p2753 p3324 p3422 p3591 p4319 p4501 : Prop) (h : (¬ p2598) ∨ (¬ p3591) ∨ (¬ p2750) ∨ (¬ p3324) ∨ (¬ p4319) ∨ p2027 ∨ (¬ p4501) ∨ (¬ p2553) ∨ (¬ p2241) ∨ (¬ p2753) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3324) ∨ (¬ p3422) ∨ (¬ p3591) ∨ (¬ p4319) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial37918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory27174 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule37918 (meaning t m 2027) (meaning t m 2241) (meaning t m 2553) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3324) (meaning t m 3422) (meaning t m 3591) (meaning t m 4319) (meaning t m 4501) source

theorem rule37921 (p2027 p2619 p2946 p3572 p3693 p3821 p4149 p4155 p4316 p4381 p4790 p5119 : Prop) (h : (¬ p2946) ∨ (¬ p3821) ∨ (¬ p4381) ∨ (¬ p4790) ∨ (¬ p4316) ∨ (¬ p2619) ∨ (¬ p3693) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p4155) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2619) ∨ (¬ p2946) ∨ (¬ p3572) ∨ (¬ p3693) ∨ (¬ p3821) ∨ (¬ p4149) ∨ (¬ p4155) ∨ (¬ p4316) ∨ (¬ p4381) ∨ (¬ p4790) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial37921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory27177 t (m.theta 0 3) (m.theta 0 7) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule37921 (meaning t m 2027) (meaning t m 2619) (meaning t m 2946) (meaning t m 3572) (meaning t m 3693) (meaning t m 3821) (meaning t m 4149) (meaning t m 4155) (meaning t m 4316) (meaning t m 4381) (meaning t m 4790) (meaning t m 5119) source

theorem rule37924 (p2027 p2274 p2313 p2651 p2787 p2810 p3744 p3755 p4117 p5276 : Prop) (h : (¬ p2313) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3755) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p2787) ∨ (¬ p2810) ∨ (¬ p5276) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2651) ∨ (¬ p2787) ∨ (¬ p2810) ∨ (¬ p3744) ∨ (¬ p3755) ∨ (¬ p4117) ∨ (¬ p5276) := by
  classical
  tauto

theorem initial37924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 5276)) := by
  have source := ElevenTheory.theory27180 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule37924 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2651) (meaning t m 2787) (meaning t m 2810) (meaning t m 3744) (meaning t m 3755) (meaning t m 4117) (meaning t m 5276) source

theorem rule37925 (p2027 p2274 p2313 p2528 p2598 p2787 p3641 p3744 p4604 : Prop) (h : (¬ p3744) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p4604) ∨ (¬ p2598) ∨ (¬ p2787)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2787) ∨ (¬ p3641) ∨ (¬ p3744) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial37925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory27181 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule37925 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2528) (meaning t m 2598) (meaning t m 2787) (meaning t m 3641) (meaning t m 3744) (meaning t m 4604) source

theorem rule37927 (p2027 p2387 p2528 p2619 p2667 p2946 p3693 p4195 p4316 p4790 p5118 p5580 : Prop) (h : (¬ p2946) ∨ (¬ p2387) ∨ (¬ p2528) ∨ (¬ p2619) ∨ (¬ p4316) ∨ (¬ p5580) ∨ (¬ p5118) ∨ p2027 ∨ (¬ p3693) ∨ (¬ p4790) ∨ (¬ p2667) ∨ (¬ p4195)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2528) ∨ (¬ p2619) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3693) ∨ (¬ p4195) ∨ (¬ p4316) ∨ (¬ p4790) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial37927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory27183 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 4 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule37927 (meaning t m 2027) (meaning t m 2387) (meaning t m 2528) (meaning t m 2619) (meaning t m 2667) (meaning t m 2946) (meaning t m 3693) (meaning t m 4195) (meaning t m 4316) (meaning t m 4790) (meaning t m 5118) (meaning t m 5580) source

theorem rule37929 (p2027 p2122 p2608 p2829 p2881 p3540 p3644 p4559 p5193 : Prop) (h : (¬ p3644) ∨ (¬ p2881) ∨ (¬ p2608) ∨ (¬ p2122) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p4559) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2608) ∨ (¬ p2829) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4559) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial37929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory27185 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37929 (meaning t m 2027) (meaning t m 2122) (meaning t m 2608) (meaning t m 2829) (meaning t m 2881) (meaning t m 3540) (meaning t m 3644) (meaning t m 4559) (meaning t m 5193) source

theorem rule37933 (p2027 p2210 p2449 p2685 p2696 p2753 p3548 p4366 p4668 p4877 : Prop) (h : (¬ p2685) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4366) ∨ (¬ p2449) ∨ (¬ p4668) ∨ (¬ p2753) ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27189 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37933 (meaning t m 2027) (meaning t m 2210) (meaning t m 2449) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3548) (meaning t m 4366) (meaning t m 4668) (meaning t m 4877) source

theorem rule37934 (p2518 p3641 p4030 : Prop) (h : (¬ p4030) ∨ (¬ p3641) ∨ p2518) : (p2518) ∨ (¬ p3641) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial37934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2518) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory27190 (m.theta 1 4) (m.theta 2 4) (m.theta 4 8)
  exact rule37934 (meaning t m 2518) (meaning t m 3641) (meaning t m 4030) source

theorem rule37936 (p2027 p2210 p2476 p2518 p3541 p4108 p4877 : Prop) (h : (¬ p3541) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p4108) ∨ (¬ p2476)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2476) ∨ (¬ p2518) ∨ (¬ p3541) ∨ (¬ p4108) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27192 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8)
  exact rule37936 (meaning t m 2027) (meaning t m 2210) (meaning t m 2476) (meaning t m 2518) (meaning t m 3541) (meaning t m 4108) (meaning t m 4877) source

theorem rule37939 (p2000 p2027 p2462 p2563 p3646 p3690 p3904 p4235 : Prop) (h : (¬ p2000) ∨ (¬ p2563) ∨ (¬ p3904) ∨ (¬ p4235) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3690) ∨ p2462) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p3904) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial37939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory27195 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule37939 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2563) (meaning t m 3646) (meaning t m 3690) (meaning t m 3904) (meaning t m 4235) source

theorem rule37940 (p1997 p2027 p2177 p2850 p2997 p3644 p3876 : Prop) (h : p2997 ∨ (¬ p1997) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p2177) ∨ (¬ p2850) ∨ (¬ p3644)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2850) ∨ (p2997) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial37940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory27196 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule37940 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2850) (meaning t m 2997) (meaning t m 3644) (meaning t m 3876) source

theorem rule37941 (p2027 p3830 p4107 p4366 p5145 p5362 : Prop) (h : (¬ p5145) ∨ (¬ p4107) ∨ p2027 ∨ (¬ p5362) ∨ (¬ p4366) ∨ (¬ p3830)) : (p2027) ∨ (¬ p3830) ∨ (¬ p4107) ∨ (¬ p4366) ∨ (¬ p5145) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial37941 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5145)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory27197 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 6 7) (m.theta 7 9)
  exact rule37941 (meaning t m 2027) (meaning t m 3830) (meaning t m 4107) (meaning t m 4366) (meaning t m 5145) (meaning t m 5362) source

theorem rule37942 (p2027 p2459 p2589 p2717 p3471 p3744 p3952 p4241 p4604 p4729 : Prop) (h : (¬ p3744) ∨ (¬ p4729) ∨ (¬ p2589) ∨ (¬ p4241) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p2459) ∨ (¬ p4604)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4241) ∨ (¬ p4604) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial37942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory27198 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 7) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule37942 (meaning t m 2027) (meaning t m 2459) (meaning t m 2589) (meaning t m 2717) (meaning t m 3471) (meaning t m 3744) (meaning t m 3952) (meaning t m 4241) (meaning t m 4604) (meaning t m 4729) source

theorem rule37944 (p2027 p3040 p3449 p3553 p4366 p5307 : Prop) (h : (¬ p4366) ∨ (¬ p5307) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3449) ∨ (¬ p3040)) : (p2027) ∨ (¬ p3040) ∨ (¬ p3449) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial37944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3040)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory27200 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8)
  exact rule37944 (meaning t m 2027) (meaning t m 3040) (meaning t m 3449) (meaning t m 3553) (meaning t m 4366) (meaning t m 5307) source

theorem rule37946 (p2027 p2122 p2313 p3952 p3985 p4356 p5053 : Prop) (h : (¬ p5053) ∨ (¬ p3985) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p4356) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p3952) ∨ (¬ p3985) ∨ (¬ p4356) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial37946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory27202 t (m.theta 0 6) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule37946 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 3952) (meaning t m 3985) (meaning t m 4356) (meaning t m 5053) source

theorem rule37947 (p1990 p2027 p2156 p2459 p2633 p3692 p4120 : Prop) (h : (¬ p3692) ∨ (¬ p4120) ∨ p2633 ∨ (¬ p2459) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2156)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial37947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory27203 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37947 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2459) (meaning t m 2633) (meaning t m 3692) (meaning t m 4120) source

theorem rule37949 (p2027 p2542 p2911 p3553 p4112 p4644 : Prop) (h : (¬ p2911) ∨ (¬ p4112) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4644) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2911) ∨ (¬ p3553) ∨ (¬ p4112) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial37949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory27205 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule37949 (meaning t m 2027) (meaning t m 2542) (meaning t m 2911) (meaning t m 3553) (meaning t m 4112) (meaning t m 4644) source

theorem rule37950 (p2027 p2542 p2911 p3551 p4112 p4155 p4644 : Prop) (h : p2027 ∨ (¬ p4155) ∨ (¬ p2911) ∨ (¬ p4112) ∨ (¬ p4644) ∨ (¬ p2542) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4112) ∨ (¬ p4155) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial37950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory27206 t (m.theta 0 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule37950 (meaning t m 2027) (meaning t m 2542) (meaning t m 2911) (meaning t m 3551) (meaning t m 4112) (meaning t m 4155) (meaning t m 4644) source

theorem rule37954 (p2027 p2210 p2528 p2598 p2753 p3641 p3817 p4366 p4669 p4877 : Prop) (h : (¬ p4669) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p3641) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27210 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule37954 (meaning t m 2027) (meaning t m 2210) (meaning t m 2528) (meaning t m 2598) (meaning t m 2753) (meaning t m 3641) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) (meaning t m 4877) source

theorem rule37956 (p2881 p3527 p4909 : Prop) (h : (¬ p4909) ∨ (¬ p3527) ∨ p2881) : (p2881) ∨ (¬ p3527) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial37956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2881) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory27212 (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule37956 (meaning t m 2881) (meaning t m 3527) (meaning t m 4909) source

theorem rule37958 (p2027 p2387 p2819 p3985 p4173 p4356 p4875 : Prop) (h : p2027 ∨ (¬ p2819) ∨ (¬ p4875) ∨ (¬ p4173) ∨ (¬ p3985) ∨ (¬ p2387) ∨ (¬ p4356)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p3985) ∨ (¬ p4173) ∨ (¬ p4356) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial37958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3985)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory27214 t (m.theta 0 6) (m.theta 1 5) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule37958 (meaning t m 2027) (meaning t m 2387) (meaning t m 2819) (meaning t m 3985) (meaning t m 4173) (meaning t m 4356) (meaning t m 4875) source

theorem rule37960 (p2027 p2406 p2427 p2509 p3693 p4901 : Prop) (h : (¬ p2406) ∨ p2027 ∨ (¬ p4901) ∨ (¬ p3693) ∨ (¬ p2427) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (¬ p2509) ∨ (¬ p3693) ∨ (¬ p4901) := by
  classical
  tauto

theorem initial37960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4901)) := by
  have source := ElevenTheory.theory27216 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8)
  exact rule37960 (meaning t m 2027) (meaning t m 2406) (meaning t m 2427) (meaning t m 2509) (meaning t m 3693) (meaning t m 4901) source

theorem rule37961 (p2027 p2210 p2598 p2753 p2911 p3201 p3817 p4366 p4666 p4877 : Prop) (h : (¬ p3817) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p4666) ∨ (¬ p2210) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p2598) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27217 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37961 (meaning t m 2027) (meaning t m 2210) (meaning t m 2598) (meaning t m 2753) (meaning t m 2911) (meaning t m 3201) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) (meaning t m 4877) source

theorem rule37968 (p1989 p2027 p2210 p2274 p2765 p3549 p3591 : Prop) (h : (¬ p1989) ∨ (¬ p2274) ∨ (¬ p3549) ∨ (¬ p2210) ∨ p2027 ∨ p2765 ∨ (¬ p3591)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial37968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory27224 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule37968 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2274) (meaning t m 2765) (meaning t m 3549) (meaning t m 3591) source

theorem rule37973 (p2027 p2210 p2534 p2753 p3166 p3256 p3548 p4117 p4366 p4420 p4877 : Prop) (h : (¬ p3166) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p4420) ∨ (¬ p3548) ∨ (¬ p4117) ∨ (¬ p3256) ∨ (¬ p4877) ∨ (¬ p2210) ∨ (¬ p4366) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2534) ∨ (¬ p2753) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3548) ∨ (¬ p4117) ∨ (¬ p4366) ∨ (¬ p4420) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27229 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule37973 (meaning t m 2027) (meaning t m 2210) (meaning t m 2534) (meaning t m 2753) (meaning t m 3166) (meaning t m 3256) (meaning t m 3548) (meaning t m 4117) (meaning t m 4366) (meaning t m 4420) (meaning t m 4877) source

theorem rule37974 (p2027 p2641 p2656 p3051 p3368 p3486 p4399 p4975 : Prop) (h : (¬ p4399) ∨ (¬ p3368) ∨ (¬ p2656) ∨ (¬ p2641) ∨ (¬ p4975) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2656) ∨ (¬ p3051) ∨ (¬ p3368) ∨ (¬ p3486) ∨ (¬ p4399) ∨ (¬ p4975) := by
  classical
  tauto

theorem initial37974 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4975)) := by
  have source := ElevenTheory.theory27230 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 6) (m.theta 5 7)
  exact rule37974 (meaning t m 2027) (meaning t m 2641) (meaning t m 2656) (meaning t m 3051) (meaning t m 3368) (meaning t m 3486) (meaning t m 4399) (meaning t m 4975) source

theorem rule37977 (p3434 p4253 p4823 : Prop) (h : (¬ p4823) ∨ (¬ p4253) ∨ p3434) : (p3434) ∨ (¬ p4253) ∨ (¬ p4823) := by
  classical
  tauto

theorem initial37977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3434) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4823)) := by
  have source := ElevenTheory.theory27233 (m.theta 2 7) (m.theta 7 10) (m.theta 7 9)
  exact rule37977 (meaning t m 3434) (meaning t m 4253) (meaning t m 4823) source

theorem rule37979 (p2027 p2192 p2751 p3952 p4315 p4365 : Prop) (h : (¬ p2751) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4365) ∨ p2027 ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2751) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial37979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory27235 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6)
  exact rule37979 (meaning t m 2027) (meaning t m 2192) (meaning t m 2751) (meaning t m 3952) (meaning t m 4315) (meaning t m 4365) source

theorem rule37980 (p2015 p2027 p2462 p2761 p3093 p3834 p4321 : Prop) (h : (¬ p2015) ∨ (¬ p2761) ∨ (¬ p3093) ∨ p2027 ∨ p2462 ∨ (¬ p4321) ∨ (¬ p3834)) : (¬ p2015) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p4321) := by
  classical
  tauto

theorem initial37980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4321)) := by
  have source := ElevenTheory.theory27236 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule37980 (meaning t m 2015) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 3093) (meaning t m 3834) (meaning t m 4321) source

theorem rule37981 (p1977 p2027 p2633 p2996 p3434 p3659 p3947 : Prop) (h : p2633 ∨ (¬ p1977) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p2996) ∨ (¬ p3947)) : (¬ p1977) ∨ (p2027) ∨ (p2633) ∨ (¬ p2996) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial37981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory27237 t (m.theta 1 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37981 (meaning t m 1977) (meaning t m 2027) (meaning t m 2633) (meaning t m 2996) (meaning t m 3434) (meaning t m 3659) (meaning t m 3947) source

theorem rule37986 (p1990 p2027 p2563 p2598 p2611 p2870 p3582 p4235 : Prop) (h : (¬ p2598) ∨ (¬ p3582) ∨ p2611 ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p4235) ∨ (¬ p2870)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2870) ∨ (¬ p3582) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial37986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory27242 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule37986 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2598) (meaning t m 2611) (meaning t m 2870) (meaning t m 3582) (meaning t m 4235) source

theorem rule37987 (p1990 p2027 p2563 p2598 p2611 p2619 p3582 p3880 : Prop) (h : (¬ p2598) ∨ (¬ p3582) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p3880) ∨ p2611 ∨ (¬ p2619)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2619) ∨ (¬ p3582) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial37987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory27243 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule37987 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2598) (meaning t m 2611) (meaning t m 2619) (meaning t m 3582) (meaning t m 3880) source

theorem rule37989 (p2027 p2145 p2187 p2387 p2417 p2437 p2651 p3744 p4117 p4198 p4625 : Prop) (h : (¬ p4117) ∨ (¬ p2387) ∨ (¬ p4198) ∨ (¬ p2417) ∨ (¬ p2145) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2187) ∨ (¬ p3744) ∨ (¬ p4625)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3744) ∨ (¬ p4117) ∨ (¬ p4198) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial37989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory27245 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 0 6) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule37989 (meaning t m 2027) (meaning t m 2145) (meaning t m 2187) (meaning t m 2387) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3744) (meaning t m 4117) (meaning t m 4198) (meaning t m 4625) source

theorem rule37990 (p2027 p2156 p2630 p2951 p3758 p4392 p4701 : Prop) (h : (¬ p4701) ∨ (¬ p4392) ∨ (¬ p2156) ∨ (¬ p3758) ∨ (¬ p2951) ∨ (¬ p2630) ∨ p2027) : (p2027) ∨ (¬ p2156) ∨ (¬ p2630) ∨ (¬ p2951) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial37990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory27246 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule37990 (meaning t m 2027) (meaning t m 2156) (meaning t m 2630) (meaning t m 2951) (meaning t m 3758) (meaning t m 4392) (meaning t m 4701) source

theorem rule37991 (p1998 p2027 p2177 p2765 p3125 p3309 p4026 : Prop) (h : (¬ p3309) ∨ (¬ p1998) ∨ p2027 ∨ p2765 ∨ (¬ p3125) ∨ (¬ p2177) ∨ (¬ p4026)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p3309) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial37991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory27247 t (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule37991 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2765) (meaning t m 3125) (meaning t m 3309) (meaning t m 4026) source

theorem rule37993 (p2027 p2264 p2685 p2696 p2753 p2927 p3379 p4278 p4366 p4666 p5216 : Prop) (h : (¬ p4278) ∨ (¬ p2685) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4666) ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p4366) ∨ (¬ p2927)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4278) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial37993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27249 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule37993 (meaning t m 2027) (meaning t m 2264) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 2927) (meaning t m 3379) (meaning t m 4278) (meaning t m 4366) (meaning t m 4666) (meaning t m 5216) source

theorem rule37994 (p1982 p2027 p2341 p2459 p2545 p3027 p4066 p4111 : Prop) (h : p2027 ∨ p2545 ∨ (¬ p2341) ∨ (¬ p4066) ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p4111) ∨ (¬ p3027)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (p2545) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial37994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory27250 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule37994 (meaning t m 1982) (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2545) (meaning t m 3027) (meaning t m 4066) (meaning t m 4111) source

theorem rule37995 (p2027 p2210 p2651 p2685 p2753 p2810 p3549 p3591 p4117 p4570 p4877 : Prop) (h : (¬ p4877) ∨ (¬ p3549) ∨ (¬ p2210) ∨ (¬ p3591) ∨ (¬ p2753) ∨ (¬ p4570) ∨ (¬ p2651) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2753) ∨ (¬ p2810) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4117) ∨ (¬ p4570) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial37995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27251 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7)
  exact rule37995 (meaning t m 2027) (meaning t m 2210) (meaning t m 2651) (meaning t m 2685) (meaning t m 2753) (meaning t m 2810) (meaning t m 3549) (meaning t m 3591) (meaning t m 4117) (meaning t m 4570) (meaning t m 4877) source

theorem rule37997 (p2027 p2177 p2589 p2850 p3093 p3309 p3874 p4438 p5193 : Prop) (h : (¬ p5193) ∨ (¬ p2850) ∨ (¬ p2589) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4438) ∨ (¬ p3309) ∨ (¬ p3874)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3874) ∨ (¬ p4438) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial37997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory27253 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule37997 (meaning t m 2027) (meaning t m 2177) (meaning t m 2589) (meaning t m 2850) (meaning t m 3093) (meaning t m 3309) (meaning t m 3874) (meaning t m 4438) (meaning t m 5193) source

theorem rule37998 (p2027 p2145 p2807 p3266 p3572 p3755 p3950 p4032 p4117 p4322 p4660 : Prop) (h : (¬ p4322) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p4032) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p2145) ∨ (¬ p3266) ∨ (¬ p3755) ∨ (¬ p3950) ∨ (¬ p4660)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2807) ∨ (¬ p3266) ∨ (¬ p3572) ∨ (¬ p3755) ∨ (¬ p3950) ∨ (¬ p4032) ∨ (¬ p4117) ∨ (¬ p4322) ∨ (¬ p4660) := by
  classical
  tauto

theorem initial37998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4660)) := by
  have source := ElevenTheory.theory27254 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule37998 (meaning t m 2027) (meaning t m 2145) (meaning t m 2807) (meaning t m 3266) (meaning t m 3572) (meaning t m 3755) (meaning t m 3950) (meaning t m 4032) (meaning t m 4117) (meaning t m 4322) (meaning t m 4660) source

theorem rule38000 (p2210 p4942 p5486 p5487 : Prop) (h : (¬ p5487) ∨ (¬ p4942) ∨ (¬ p2210) ∨ (¬ p5486)) : (¬ p2210) ∨ (¬ p4942) ∨ (¬ p5486) ∨ (¬ p5487) := by
  classical
  tauto

theorem initial38000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 4942)) ∨ (¬ (meaning t m 5486)) ∨ (¬ (meaning t m 5487)) := by
  have source := ElevenTheory.theory27256 (m.theta 0 1) (m.theta 0 9) (m.theta 1 5) (m.theta 1 9)
  exact rule38000 (meaning t m 2210) (meaning t m 4942) (meaning t m 5486) (meaning t m 5487) source

theorem rule38001 (p2027 p2470 p2630 p2665 p3877 p4437 : Prop) (h : (¬ p2470) ∨ (¬ p2665) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p4437) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2630) ∨ (¬ p2665) ∨ (¬ p3877) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial38001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory27257 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8)
  exact rule38001 (meaning t m 2027) (meaning t m 2470) (meaning t m 2630) (meaning t m 2665) (meaning t m 3877) (meaning t m 4437) source

theorem rule38005 (p2027 p2579 p2696 p3005 p3956 p4009 p4347 p4729 p5122 : Prop) (h : (¬ p2579) ∨ (¬ p4347) ∨ (¬ p3956) ∨ (¬ p5122) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p3005) ∨ (¬ p4009)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3956) ∨ (¬ p4009) ∨ (¬ p4347) ∨ (¬ p4729) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial38005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory27261 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule38005 (meaning t m 2027) (meaning t m 2579) (meaning t m 2696) (meaning t m 3005) (meaning t m 3956) (meaning t m 4009) (meaning t m 4347) (meaning t m 4729) (meaning t m 5122) source

theorem rule38011 (p2027 p2248 p2299 p2946 p3005 p3549 p3591 p4315 p4550 : Prop) (h : (¬ p3591) ∨ (¬ p4550) ∨ (¬ p3549) ∨ (¬ p4315) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p2248) ∨ (¬ p3005)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2299) ∨ (¬ p2946) ∨ (¬ p3005) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4315) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial38011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory27267 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule38011 (meaning t m 2027) (meaning t m 2248) (meaning t m 2299) (meaning t m 2946) (meaning t m 3005) (meaning t m 3549) (meaning t m 3591) (meaning t m 4315) (meaning t m 4550) source

theorem rule38015 (p2027 p2098 p2928 p3452 p3609 p3644 p4133 p4347 p4733 : Prop) (h : (¬ p3452) ∨ (¬ p3644) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p4733) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p2098) ∨ (¬ p3609)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial38015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory27271 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38015 (meaning t m 2027) (meaning t m 2098) (meaning t m 2928) (meaning t m 3452) (meaning t m 3609) (meaning t m 3644) (meaning t m 4133) (meaning t m 4347) (meaning t m 4733) source

theorem rule38016 (p2027 p2210 p2630 p2696 p2753 p3343 p3860 p4261 p4332 p4877 : Prop) (h : (¬ p3343) ∨ (¬ p4877) ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p4332) ∨ (¬ p4261) ∨ (¬ p3860) ∨ (¬ p2753) ∨ (¬ p2210) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3343) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4332) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial38016 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27272 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 8 9)
  exact rule38016 (meaning t m 2027) (meaning t m 2210) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 3343) (meaning t m 3860) (meaning t m 4261) (meaning t m 4332) (meaning t m 4877) source

theorem rule38019 (p2027 p2122 p2210 p2247 p2313 p2744 p2778 p2972 p3366 p3917 p4397 : Prop) (h : (¬ p3366) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2778) ∨ (¬ p2210) ∨ (¬ p3917) ∨ (¬ p2313) ∨ (¬ p2122) ∨ (¬ p2972) ∨ (¬ p2744) ∨ (¬ p4397)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2313) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2972) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4397) := by
  classical
  tauto

theorem initial38019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4397)) := by
  have source := ElevenTheory.theory27275 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule38019 (meaning t m 2027) (meaning t m 2122) (meaning t m 2210) (meaning t m 2247) (meaning t m 2313) (meaning t m 2744) (meaning t m 2778) (meaning t m 2972) (meaning t m 3366) (meaning t m 3917) (meaning t m 4397) source

theorem rule38021 (p2027 p2313 p2386 p2505 p3309 p3574 p4814 : Prop) (h : (¬ p2386) ∨ (¬ p4814) ∨ (¬ p2313) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p2505)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3309) ∨ (¬ p3574) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial38021 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory27277 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule38021 (meaning t m 2027) (meaning t m 2313) (meaning t m 2386) (meaning t m 2505) (meaning t m 3309) (meaning t m 3574) (meaning t m 4814) source

theorem rule38022 (p2027 p2252 p2363 p2518 p2750 p3172 p3379 p3954 p4118 p4596 : Prop) (h : (¬ p2750) ∨ (¬ p2518) ∨ (¬ p3954) ∨ (¬ p4596) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p3954) ∨ (¬ p4118) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial38022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory27278 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule38022 (meaning t m 2027) (meaning t m 2252) (meaning t m 2363) (meaning t m 2518) (meaning t m 2750) (meaning t m 3172) (meaning t m 3379) (meaning t m 3954) (meaning t m 4118) (meaning t m 4596) source

theorem rule38025 (p1990 p2027 p2396 p2563 p2997 p3690 p4235 : Prop) (h : (¬ p2396) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2563) ∨ p2997 ∨ (¬ p4235) ∨ (¬ p3690)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2563) ∨ (p2997) ∨ (¬ p3690) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial38025 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory27281 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule38025 (meaning t m 1990) (meaning t m 2027) (meaning t m 2396) (meaning t m 2563) (meaning t m 2997) (meaning t m 3690) (meaning t m 4235) source

theorem rule38026 (p2027 p2934 p3527 p3644 p3742 p4814 : Prop) (h : (¬ p4814) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2934) ∨ (¬ p3742) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial38026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory27282 t (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule38026 (meaning t m 2027) (meaning t m 2934) (meaning t m 3527) (meaning t m 3644) (meaning t m 3742) (meaning t m 4814) source

theorem rule38028 (p2027 p2449 p2579 p2685 p2696 p3950 p3956 p4347 p4729 : Prop) (h : (¬ p3956) ∨ p2027 ∨ (¬ p3950) ∨ (¬ p4729) ∨ (¬ p2696) ∨ (¬ p4347) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2579) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial38028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory27284 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38028 (meaning t m 2027) (meaning t m 2449) (meaning t m 2579) (meaning t m 2685) (meaning t m 2696) (meaning t m 3950) (meaning t m 3956) (meaning t m 4347) (meaning t m 4729) source

theorem rule38035 (p2246 p2946 p3842 p5038 : Prop) (h : (¬ p2246) ∨ (¬ p5038) ∨ (¬ p2946) ∨ p3842) : (¬ p2246) ∨ (¬ p2946) ∨ (p3842) ∨ (¬ p5038) := by
  classical
  tauto

theorem initial38035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 3842) ∨ (¬ (meaning t m 5038)) := by
  have source := ElevenTheory.theory27291 (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9)
  exact rule38035 (meaning t m 2246) (meaning t m 2946) (meaning t m 3842) (meaning t m 5038) source

theorem rule38045 (p2027 p3555 p3830 p4208 p4387 p4960 : Prop) (h : (¬ p3830) ∨ (¬ p4960) ∨ p2027 ∨ (¬ p4387) ∨ (¬ p4208) ∨ (¬ p3555)) : (p2027) ∨ (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4208) ∨ (¬ p4387) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial38045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4387)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory27301 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 9) (m.theta 3 5) (m.theta 5 9)
  exact rule38045 (meaning t m 2027) (meaning t m 3555) (meaning t m 3830) (meaning t m 4208) (meaning t m 4387) (meaning t m 4960) source

theorem rule38050 (p2027 p2579 p2685 p2696 p2753 p3347 p3931 p4137 p4191 p4826 p5216 : Prop) (h : (¬ p2696) ∨ (¬ p4137) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p4826) ∨ (¬ p2753) ∨ (¬ p2685) ∨ (¬ p3931)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3347) ∨ (¬ p3931) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27306 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule38050 (meaning t m 2027) (meaning t m 2579) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3347) (meaning t m 3931) (meaning t m 4137) (meaning t m 4191) (meaning t m 4826) (meaning t m 5216) source

theorem rule38051 (p1990 p2027 p2132 p2284 p2579 p2753 p2764 p2870 p3347 p4137 p4191 p4320 p5216 : Prop) (h : (¬ p5216) ∨ (¬ p4191) ∨ p2764 ∨ (¬ p2284) ∨ (¬ p4320) ∨ (¬ p1990) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p4137) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2870)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2284) ∨ (¬ p2579) ∨ (¬ p2753) ∨ (p2764) ∨ (¬ p2870) ∨ (¬ p3347) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4320) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2753)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27307 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9) (m.theta 9 10)
  exact rule38051 (meaning t m 1990) (meaning t m 2027) (meaning t m 2132) (meaning t m 2284) (meaning t m 2579) (meaning t m 2753) (meaning t m 2764) (meaning t m 2870) (meaning t m 3347) (meaning t m 4137) (meaning t m 4191) (meaning t m 4320) (meaning t m 5216) source

theorem rule38057 (p2011 p2027 p2156 p2622 p2630 p2656 p2982 p4110 p4399 : Prop) (h : (¬ p4399) ∨ (¬ p2156) ∨ p2027 ∨ p2622 ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p4110) ∨ (¬ p2011) ∨ (¬ p2982)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2156) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2982) ∨ (¬ p4110) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial38057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory27313 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule38057 (meaning t m 2011) (meaning t m 2027) (meaning t m 2156) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 2982) (meaning t m 4110) (meaning t m 4399) source

theorem rule38059 (p2027 p3055 p3172 p3361 p3471 p3658 p3868 p4118 p4444 p4749 p4826 : Prop) (h : p2027 ∨ (¬ p3471) ∨ (¬ p4826) ∨ (¬ p3868) ∨ (¬ p3658) ∨ (¬ p3055) ∨ (¬ p4749) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p4118) ∨ (¬ p4444)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p3471) ∨ (¬ p3658) ∨ (¬ p3868) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p4749) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial38059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory27315 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule38059 (meaning t m 2027) (meaning t m 3055) (meaning t m 3172) (meaning t m 3361) (meaning t m 3471) (meaning t m 3658) (meaning t m 3868) (meaning t m 4118) (meaning t m 4444) (meaning t m 4749) (meaning t m 4826) source

theorem rule38065 (p1987 p2027 p2737 p2780 p2997 p3619 p3822 p4379 : Prop) (h : (¬ p2737) ∨ (¬ p3822) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p4379) ∨ p2997 ∨ (¬ p3619)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3619) ∨ (¬ p3822) ∨ (¬ p4379) := by
  classical
  tauto

theorem initial38065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4379)) := by
  have source := ElevenTheory.theory27321 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 2 9) (m.theta 6 7)
  exact rule38065 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2780) (meaning t m 2997) (meaning t m 3619) (meaning t m 3822) (meaning t m 4379) source

theorem rule38067 (p2027 p3172 p3609 p4261 p4288 p4373 p4787 : Prop) (h : (¬ p3172) ∨ (¬ p4288) ∨ (¬ p4787) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p3609) ∨ (¬ p4373)) : (p2027) ∨ (¬ p3172) ∨ (¬ p3609) ∨ (¬ p4261) ∨ (¬ p4288) ∨ (¬ p4373) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial38067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4373)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory27323 t (m.theta 0 3) (m.theta 1 8) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9)
  exact rule38067 (meaning t m 2027) (meaning t m 3172) (meaning t m 3609) (meaning t m 4261) (meaning t m 4288) (meaning t m 4373) (meaning t m 4787) source

theorem rule38072 (p2027 p3449 p4366 p4442 p5307 p5559 : Prop) (h : (¬ p4366) ∨ (¬ p5307) ∨ (¬ p5559) ∨ (¬ p4442) ∨ p2027 ∨ (¬ p3449)) : (p2027) ∨ (¬ p3449) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p5307) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial38072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 5307)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory27328 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 7 10) (m.theta 7 8)
  exact rule38072 (meaning t m 2027) (meaning t m 3449) (meaning t m 4366) (meaning t m 4442) (meaning t m 5307) (meaning t m 5559) source

theorem rule38077 (p2027 p2132 p2579 p2753 p2870 p3347 p4129 p4137 p4191 p4826 p5216 : Prop) (h : (¬ p4826) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p2579) ∨ (¬ p5216) ∨ (¬ p3347) ∨ (¬ p2753) ∨ (¬ p4129) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3347) ∨ (¬ p4129) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4826) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27333 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule38077 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 2753) (meaning t m 2870) (meaning t m 3347) (meaning t m 4129) (meaning t m 4137) (meaning t m 4191) (meaning t m 4826) (meaning t m 5216) source

theorem rule38080 (p2027 p2132 p2476 p2534 p2870 p4129 p4444 p4729 p4826 : Prop) (h : (¬ p2476) ∨ (¬ p2132) ∨ (¬ p4444) ∨ (¬ p2534) ∨ (¬ p4729) ∨ (¬ p4826) ∨ (¬ p2870) ∨ p2027 ∨ (¬ p4129)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2870) ∨ (¬ p4129) ∨ (¬ p4444) ∨ (¬ p4729) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial38080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory27336 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule38080 (meaning t m 2027) (meaning t m 2132) (meaning t m 2476) (meaning t m 2534) (meaning t m 2870) (meaning t m 4129) (meaning t m 4444) (meaning t m 4729) (meaning t m 4826) source

theorem rule38081 (p2027 p2132 p2579 p2870 p3246 p3950 p3956 p4347 p4729 : Prop) (h : (¬ p4347) ∨ (¬ p2579) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p3956) ∨ (¬ p2870) ∨ (¬ p3950) ∨ (¬ p2132) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2579) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial38081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory27337 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule38081 (meaning t m 2027) (meaning t m 2132) (meaning t m 2579) (meaning t m 2870) (meaning t m 3246) (meaning t m 3950) (meaning t m 3956) (meaning t m 4347) (meaning t m 4729) source

theorem rule38083 (p2027 p2132 p2619 p2753 p3093 p3860 p3969 p4347 p4870 p4993 p5122 : Prop) (h : p2027 ∨ (¬ p3860) ∨ (¬ p3093) ∨ (¬ p4993) ∨ (¬ p4347) ∨ (¬ p3969) ∨ (¬ p4870) ∨ (¬ p2619) ∨ (¬ p2132) ∨ (¬ p2753) ∨ (¬ p5122)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2753) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p3969) ∨ (¬ p4347) ∨ (¬ p4870) ∨ (¬ p4993) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial38083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 4993)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory27339 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule38083 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2753) (meaning t m 3093) (meaning t m 3860) (meaning t m 3969) (meaning t m 4347) (meaning t m 4870) (meaning t m 4993) (meaning t m 5122) source

theorem rule38085 (p1995 p2027 p2997 p3097 p3379 p3555 p4034 p4110 : Prop) (h : (¬ p3555) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p1995) ∨ (¬ p4034) ∨ p2997 ∨ (¬ p3097)) : (¬ p1995) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial38085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory27341 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule38085 (meaning t m 1995) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3379) (meaning t m 3555) (meaning t m 4034) (meaning t m 4110) source

theorem rule38087 (p4242 p4379 p5344 : Prop) (h : (¬ p4379) ∨ (¬ p5344) ∨ p4242) : (p4242) ∨ (¬ p4379) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial38087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4242) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory27343 (m.theta 1 2) (m.theta 2 8) (m.theta 2 9)
  exact rule38087 (meaning t m 4242) (meaning t m 4379) (meaning t m 5344) source

theorem rule38088 (p2010 p2287 p2295 p4276 : Prop) (h : p2287 ∨ (¬ p2295) ∨ (¬ p2010) ∨ p4276) : (¬ p2010) ∨ (p2287) ∨ (¬ p2295) ∨ (p4276) := by
  classical
  tauto

theorem initial38088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 4276) := by
  have source := ElevenTheory.theory27344 t (m.theta 3 6) (m.theta 4 7) (m.theta 6 7)
  exact rule38088 (meaning t m 2010) (meaning t m 2287) (meaning t m 2295) (meaning t m 4276) source

theorem rule38089 (p2027 p2459 p2589 p3399 p3527 p3744 p4110 p4604 p5193 : Prop) (h : (¬ p3527) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2459) ∨ (¬ p5193) ∨ (¬ p3744) ∨ (¬ p4604) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4604) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial38089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory27345 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule38089 (meaning t m 2027) (meaning t m 2459) (meaning t m 2589) (meaning t m 3399) (meaning t m 3527) (meaning t m 3744) (meaning t m 4110) (meaning t m 4604) (meaning t m 5193) source

theorem rule38090 (p2027 p2696 p2753 p2911 p3389 p3759 p3941 p4379 p4749 p5119 p5284 p5454 : Prop) (h : (¬ p2753) ∨ (¬ p5454) ∨ (¬ p5284) ∨ (¬ p4379) ∨ (¬ p3389) ∨ (¬ p2696) ∨ (¬ p2911) ∨ (¬ p3759) ∨ (¬ p4749) ∨ p2027 ∨ (¬ p5119) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p3941) ∨ (¬ p4379) ∨ (¬ p4749) ∨ (¬ p5119) ∨ (¬ p5284) ∨ (¬ p5454) := by
  classical
  tauto

theorem initial38090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5454)) := by
  have source := ElevenTheory.theory27346 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 3 9) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule38090 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2911) (meaning t m 3389) (meaning t m 3759) (meaning t m 3941) (meaning t m 4379) (meaning t m 4749) (meaning t m 5119) (meaning t m 5284) (meaning t m 5454) source

theorem rule38098 (p2027 p2295 p2313 p3019 p3684 p4031 p4198 p4750 : Prop) (h : (¬ p2313) ∨ (¬ p4198) ∨ (¬ p4750) ∨ (¬ p3684) ∨ (¬ p2295) ∨ (¬ p3019) ∨ (¬ p4031) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3019) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial38098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory27354 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 6 7)
  exact rule38098 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 3019) (meaning t m 3684) (meaning t m 4031) (meaning t m 4198) (meaning t m 4750) source

theorem rule38103 (p2027 p2727 p2963 p3166 p4360 p4972 : Prop) (h : p2027 ∨ (¬ p3166) ∨ (¬ p4972) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial38103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory27359 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8)
  exact rule38103 (meaning t m 2027) (meaning t m 2727) (meaning t m 2963) (meaning t m 3166) (meaning t m 4360) (meaning t m 4972) source

theorem rule38105 (p2144 p3362 p4399 : Prop) (h : (¬ p4399) ∨ (¬ p3362) ∨ p2144) : (p2144) ∨ (¬ p3362) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial38105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2144) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory27361 (m.theta 0 2) (m.theta 0 4) (m.theta 0 5)
  exact rule38105 (meaning t m 2144) (meaning t m 3362) (meaning t m 4399) source

theorem rule38106 (p2027 p2241 p3055 p3189 p3979 p4417 p4425 p4736 p5119 p5160 : Prop) (h : p2027 ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p3055) ∨ (¬ p4417) ∨ (¬ p5160) ∨ (¬ p3979) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3055) ∨ (¬ p3189) ∨ (¬ p3979) ∨ (¬ p4417) ∨ (¬ p4425) ∨ (¬ p4736) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial38106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4417)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory27362 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule38106 (meaning t m 2027) (meaning t m 2241) (meaning t m 3055) (meaning t m 3189) (meaning t m 3979) (meaning t m 4417) (meaning t m 4425) (meaning t m 4736) (meaning t m 5119) (meaning t m 5160) source

theorem rule38108 (p2027 p2249 p2573 p2656 p2727 p3266 p3292 p3564 p3853 p4321 p4330 : Prop) (h : (¬ p2249) ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p3564) ∨ (¬ p2573) ∨ (¬ p4321) ∨ (¬ p3292) ∨ (¬ p4330) ∨ p2027 ∨ (¬ p3853) ∨ (¬ p3266)) : (p2027) ∨ (¬ p2249) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3564) ∨ (¬ p3853) ∨ (¬ p4321) ∨ (¬ p4330) := by
  classical
  tauto

theorem initial38108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4330)) := by
  have source := ElevenTheory.theory27364 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 3 9) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38108 (meaning t m 2027) (meaning t m 2249) (meaning t m 2573) (meaning t m 2656) (meaning t m 2727) (meaning t m 3266) (meaning t m 3292) (meaning t m 3564) (meaning t m 3853) (meaning t m 4321) (meaning t m 4330) source

theorem rule38109 (p2027 p2241 p2352 p2598 p2750 p2753 p3422 p3549 p3591 p4405 : Prop) (h : (¬ p3549) ∨ (¬ p2598) ∨ (¬ p3422) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p4405) ∨ (¬ p2753) ∨ (¬ p3591) ∨ (¬ p2241) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2352) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3422) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial38109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory27365 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule38109 (meaning t m 2027) (meaning t m 2241) (meaning t m 2352) (meaning t m 2598) (meaning t m 2750) (meaning t m 2753) (meaning t m 3422) (meaning t m 3549) (meaning t m 3591) (meaning t m 4405) source

theorem rule38111 (p2027 p2156 p2187 p2590 p3370 p3956 p4632 : Prop) (h : (¬ p2156) ∨ (¬ p2590) ∨ (¬ p4632) ∨ (¬ p3370) ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2590) ∨ (¬ p3370) ∨ (¬ p3956) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial38111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory27367 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule38111 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2590) (meaning t m 3370) (meaning t m 3956) (meaning t m 4632) source

theorem rule38115 (p2027 p2383 p2745 p2797 p3567 p3923 p4245 : Prop) (h : p2027 ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p2383) ∨ (¬ p4245) ∨ (¬ p3923) ∨ (¬ p3567)) : (p2027) ∨ (¬ p2383) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3923) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial38115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory27371 t (m.theta 0 6) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8)
  exact rule38115 (meaning t m 2027) (meaning t m 2383) (meaning t m 2745) (meaning t m 2797) (meaning t m 3567) (meaning t m 3923) (meaning t m 4245) source

theorem rule38118 (p2027 p2318 p2901 p3691 p3822 p3952 p4889 : Prop) (h : (¬ p3952) ∨ (¬ p3691) ∨ (¬ p3822) ∨ (¬ p4889) ∨ (¬ p2318) ∨ (¬ p2901) ∨ p2027) : (p2027) ∨ (¬ p2318) ∨ (¬ p2901) ∨ (¬ p3691) ∨ (¬ p3822) ∨ (¬ p3952) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial38118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory27374 t (m.theta 0 7) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule38118 (meaning t m 2027) (meaning t m 2318) (meaning t m 2901) (meaning t m 3691) (meaning t m 3822) (meaning t m 3952) (meaning t m 4889) source

theorem rule38119 (p2748 p3662 p4315 : Prop) (h : (¬ p2748) ∨ (¬ p3662) ∨ p4315) : (¬ p2748) ∨ (¬ p3662) ∨ (p4315) := by
  classical
  tauto

theorem initial38119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3662)) ∨ (meaning t m 4315) := by
  have source := ElevenTheory.theory27375 (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule38119 (meaning t m 2748) (meaning t m 3662) (meaning t m 4315) source

theorem rule38123 (p1976 p2027 p3008 p3201 p3365 p3572 p3584 p3740 : Prop) (h : (¬ p3201) ∨ (¬ p3584) ∨ (¬ p1976) ∨ p3008 ∨ (¬ p3740) ∨ (¬ p3572) ∨ p2027 ∨ (¬ p3365)) : (¬ p1976) ∨ (p2027) ∨ (p3008) ∨ (¬ p3201) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3584) ∨ (¬ p3740) := by
  classical
  tauto

theorem initial38123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3740)) := by
  have source := ElevenTheory.theory27379 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7)
  exact rule38123 (meaning t m 1976) (meaning t m 2027) (meaning t m 3008) (meaning t m 3201) (meaning t m 3365) (meaning t m 3572) (meaning t m 3584) (meaning t m 3740) source

theorem rule38128 (p2122 p3483 p4025 : Prop) (h : (¬ p4025) ∨ (¬ p3483) ∨ p2122) : (p2122) ∨ (¬ p3483) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial38128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory27384 (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule38128 (meaning t m 2122) (meaning t m 3483) (meaning t m 4025) source

theorem rule38130 (p1994 p2027 p2727 p2911 p2914 p2996 p3551 p4155 : Prop) (h : p2914 ∨ (¬ p3551) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p1994) ∨ (¬ p4155)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial38130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory27386 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule38130 (meaning t m 1994) (meaning t m 2027) (meaning t m 2727) (meaning t m 2911) (meaning t m 2914) (meaning t m 2996) (meaning t m 3551) (meaning t m 4155) source

theorem rule38131 (p2027 p2534 p2761 p3945 p4420 p4444 : Prop) (h : (¬ p2761) ∨ (¬ p3945) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p4420)) : (p2027) ∨ (¬ p2534) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4420) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial38131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory27387 t (m.theta 4 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38131 (meaning t m 2027) (meaning t m 2534) (meaning t m 2761) (meaning t m 3945) (meaning t m 4420) (meaning t m 4444) source

theorem rule38134 (p2122 p2819 p3955 : Prop) (h : (¬ p2819) ∨ (¬ p3955) ∨ p2122) : (p2122) ∨ (¬ p2819) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial38134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2122) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory27390 (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule38134 (meaning t m 2122) (meaning t m 2819) (meaning t m 3955) source

theorem rule38138 (p2027 p2608 p2901 p3333 p3367 p3497 p3556 p4045 p4158 p4524 : Prop) (h : (¬ p3497) ∨ (¬ p4158) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2608) ∨ (¬ p3333) ∨ (¬ p4045) ∨ (¬ p3367) ∨ (¬ p4524)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2901) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4045) ∨ (¬ p4158) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial38138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4045)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory27394 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 3 5) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 5 8)
  exact rule38138 (meaning t m 2027) (meaning t m 2608) (meaning t m 2901) (meaning t m 3333) (meaning t m 3367) (meaning t m 3497) (meaning t m 3556) (meaning t m 4045) (meaning t m 4158) (meaning t m 4524) source

theorem rule38139 (p1976 p2027 p2630 p2657 p2911 p2914 p3659 p4236 p4357 : Prop) (h : p2027 ∨ (¬ p4357) ∨ p2914 ∨ (¬ p2911) ∨ (¬ p1976) ∨ (¬ p3659) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3659) ∨ (¬ p4236) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial38139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory27395 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule38139 (meaning t m 1976) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2911) (meaning t m 2914) (meaning t m 3659) (meaning t m 4236) (meaning t m 4357) source

theorem rule38143 (p2006 p2027 p2264 p2766 p3266 p3659 p4136 p4429 p5284 : Prop) (h : (¬ p2264) ∨ (¬ p2006) ∨ (¬ p3659) ∨ (¬ p4429) ∨ p2027 ∨ (¬ p5284) ∨ (¬ p3266) ∨ p2766 ∨ (¬ p4136)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2264) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p4429) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial38143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory27399 t (m.theta 2 5) (m.theta 2 7) (m.theta 3 7) (m.theta 3 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule38143 (meaning t m 2006) (meaning t m 2027) (meaning t m 2264) (meaning t m 2766) (meaning t m 3266) (meaning t m 3659) (meaning t m 4136) (meaning t m 4429) (meaning t m 5284) source

theorem rule38144 (p2027 p2252 p2750 p2952 p3222 p3379 p3497 p3692 p3954 p4332 : Prop) (h : (¬ p3497) ∨ (¬ p3222) ∨ (¬ p2252) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4332) ∨ (¬ p2750) ∨ (¬ p2952)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3222) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4332) := by
  classical
  tauto

theorem initial38144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4332)) := by
  have source := ElevenTheory.theory27400 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule38144 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3222) (meaning t m 3379) (meaning t m 3497) (meaning t m 3692) (meaning t m 3954) (meaning t m 4332) source

theorem rule38145 (p1997 p2027 p2192 p2233 p2470 p2509 p3948 p4110 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p3948) ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p2192) ∨ (¬ p2470) ∨ (¬ p2509)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2192) ∨ (p2233) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p3948) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial38145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory27401 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule38145 (meaning t m 1997) (meaning t m 2027) (meaning t m 2192) (meaning t m 2233) (meaning t m 2470) (meaning t m 2509) (meaning t m 3948) (meaning t m 4110) source

theorem rule38149 (p2002 p2027 p2114 p3093 p3309 p3822 p3954 : Prop) (h : (¬ p3822) ∨ (¬ p2002) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3954) ∨ p2114 ∨ (¬ p3093)) : (¬ p2002) ∨ (p2027) ∨ (p2114) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial38149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory27405 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule38149 (meaning t m 2002) (meaning t m 2027) (meaning t m 2114) (meaning t m 3093) (meaning t m 3309) (meaning t m 3822) (meaning t m 3954) source

theorem rule38151 (p2027 p2264 p2318 p3551 p3822 p4156 p4843 : Prop) (h : (¬ p4843) ∨ (¬ p2318) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4156) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2318) ∨ (¬ p3551) ∨ (¬ p3822) ∨ (¬ p4156) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial38151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory27407 t (m.theta 0 7) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule38151 (meaning t m 2027) (meaning t m 2264) (meaning t m 2318) (meaning t m 3551) (meaning t m 3822) (meaning t m 4156) (meaning t m 4843) source

theorem rule38152 (p2027 p3399 p3547 p3591 p3822 p4871 : Prop) (h : (¬ p4871) ∨ (¬ p3547) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3399) ∨ (¬ p3591)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p3822) ∨ (¬ p4871) := by
  classical
  tauto

theorem initial38152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4871)) := by
  have source := ElevenTheory.theory27408 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7)
  exact rule38152 (meaning t m 2027) (meaning t m 3399) (meaning t m 3547) (meaning t m 3591) (meaning t m 3822) (meaning t m 4871) source

theorem rule38155 (p2027 p2427 p2542 p3096 p3574 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p2427) ∨ (¬ p2542) ∨ p2027) : (p2027) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial38155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory27411 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule38155 (meaning t m 2027) (meaning t m 2427) (meaning t m 2542) (meaning t m 3096) (meaning t m 3574) (meaning t m 4558) source

theorem rule38156 (p2589 p3540 p3741 : Prop) (h : (¬ p3741) ∨ (¬ p3540) ∨ p2589) : (p2589) ∨ (¬ p3540) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial38156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2589) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory27412 (m.theta 0 4) (m.theta 4 5) (m.theta 4 7)
  exact rule38156 (meaning t m 2589) (meaning t m 3540) (meaning t m 3741) source

theorem rule38158 (p1988 p2027 p2252 p2437 p2655 p2750 p3093 p3319 p3461 p3498 p3540 p3954 p4256 : Prop) (h : p3498 ∨ (¬ p1988) ∨ (¬ p3461) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p2655) ∨ (¬ p3319) ∨ (¬ p2252) ∨ (¬ p3540) ∨ (¬ p2437) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p2750)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (p3498) ∨ (¬ p3540) ∨ (¬ p3954) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial38158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory27414 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 9) (m.theta 9 10)
  exact rule38158 (meaning t m 1988) (meaning t m 2027) (meaning t m 2252) (meaning t m 2437) (meaning t m 2655) (meaning t m 2750) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 3498) (meaning t m 3540) (meaning t m 3954) (meaning t m 4256) source

theorem rule38159 (p2027 p2088 p2299 p2482 p2534 p2630 p2656 p2963 p3822 p4328 p4420 p4787 : Prop) (h : (¬ p4787) ∨ (¬ p2656) ∨ (¬ p2963) ∨ (¬ p4328) ∨ (¬ p3822) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2630) ∨ (¬ p2482) ∨ (¬ p4420) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2299) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2963) ∨ (¬ p3822) ∨ (¬ p4328) ∨ (¬ p4420) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial38159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2482)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4328)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory27415 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 8) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule38159 (meaning t m 2027) (meaning t m 2088) (meaning t m 2299) (meaning t m 2482) (meaning t m 2534) (meaning t m 2630) (meaning t m 2656) (meaning t m 2963) (meaning t m 3822) (meaning t m 4328) (meaning t m 4420) (meaning t m 4787) source

theorem rule38163 (p2027 p2476 p2534 p2753 p2807 p3005 p3146 p3347 p3572 p4117 p5063 p5216 : Prop) (h : (¬ p3146) ∨ (¬ p2534) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p3005) ∨ (¬ p4117) ∨ (¬ p2807) ∨ (¬ p2753) ∨ (¬ p2476) ∨ (¬ p5063) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2753) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3146) ∨ (¬ p3347) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p5063) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 5063)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27419 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule38163 (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2753) (meaning t m 2807) (meaning t m 3005) (meaning t m 3146) (meaning t m 3347) (meaning t m 3572) (meaning t m 4117) (meaning t m 5063) (meaning t m 5216) source

theorem rule38165 (p2027 p2264 p2476 p2534 p2685 p2696 p2753 p3146 p3347 p4905 p5216 : Prop) (h : (¬ p3146) ∨ (¬ p2534) ∨ (¬ p3347) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p2476) ∨ (¬ p2696) ∨ (¬ p4905) ∨ (¬ p2685) ∨ (¬ p2264)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3347) ∨ (¬ p4905) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27421 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38165 (meaning t m 2027) (meaning t m 2264) (meaning t m 2476) (meaning t m 2534) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3146) (meaning t m 3347) (meaning t m 4905) (meaning t m 5216) source

theorem rule38172 (p2027 p2498 p2753 p2807 p3005 p3379 p3572 p3591 p3956 p4117 p4771 p5216 : Prop) (h : (¬ p3591) ∨ (¬ p4771) ∨ (¬ p3956) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p2807) ∨ (¬ p5216) ∨ (¬ p2498) ∨ (¬ p3379) ∨ (¬ p2753) ∨ (¬ p3005) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2498) ∨ (¬ p2753) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3379) ∨ (¬ p3572) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4117) ∨ (¬ p4771) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial38172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory27428 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule38172 (meaning t m 2027) (meaning t m 2498) (meaning t m 2753) (meaning t m 2807) (meaning t m 3005) (meaning t m 3379) (meaning t m 3572) (meaning t m 3591) (meaning t m 3956) (meaning t m 4117) (meaning t m 4771) (meaning t m 5216) source

theorem rule38178 (p2027 p2901 p2946 p2963 p3745 p4558 : Prop) (h : (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3745) ∨ (¬ p4558) ∨ p2027 ∨ (¬ p2963)) : (p2027) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial38178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory27434 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7)
  exact rule38178 (meaning t m 2027) (meaning t m 2901) (meaning t m 2946) (meaning t m 2963) (meaning t m 3745) (meaning t m 4558) source

theorem rule38180 (p2027 p2510 p2528 p2573 p3588 p3659 p3954 p4133 p4347 p5190 : Prop) (h : (¬ p2573) ∨ (¬ p3954) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p4133) ∨ (¬ p3588) ∨ (¬ p2510) ∨ (¬ p4347) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial38180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory27436 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 7) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38180 (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 2573) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4133) (meaning t m 4347) (meaning t m 5190) source

theorem rule38181 (p1979 p2027 p2633 p3434 p3659 p3821 p4283 p4320 : Prop) (h : (¬ p4283) ∨ p2027 ∨ p2633 ∨ (¬ p3434) ∨ (¬ p3821) ∨ (¬ p3659) ∨ (¬ p1979) ∨ (¬ p4320)) : (¬ p1979) ∨ (p2027) ∨ (p2633) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial38181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory27437 t (m.theta 0 7) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38181 (meaning t m 1979) (meaning t m 2027) (meaning t m 2633) (meaning t m 3434) (meaning t m 3659) (meaning t m 3821) (meaning t m 4283) (meaning t m 4320) source

theorem rule38184 (p2298 p3032 p4427 : Prop) (h : (¬ p3032) ∨ (¬ p2298) ∨ p4427) : (¬ p2298) ∨ (¬ p3032) ∨ (p4427) := by
  classical
  tauto

theorem initial38184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 3032)) ∨ (meaning t m 4427) := by
  have source := ElevenTheory.theory27440 (m.theta 1 7) (m.theta 3 7) (m.theta 6 7)
  exact rule38184 (meaning t m 2298) (meaning t m 3032) (meaning t m 4427) source

theorem rule38185 (p2027 p2341 p2608 p3246 p3519 p3569 p3591 p3644 p4026 p4376 p4399 p4625 p4988 : Prop) (h : (¬ p4376) ∨ (¬ p4625) ∨ (¬ p4026) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p2608) ∨ (¬ p3644) ∨ (¬ p4399) ∨ (¬ p3569) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p4988) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2608) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3569) ∨ (¬ p3591) ∨ (¬ p3644) ∨ (¬ p4026) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p4625) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial38185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory27441 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule38185 (meaning t m 2027) (meaning t m 2341) (meaning t m 2608) (meaning t m 3246) (meaning t m 3519) (meaning t m 3569) (meaning t m 3591) (meaning t m 3644) (meaning t m 4026) (meaning t m 4376) (meaning t m 4399) (meaning t m 4625) (meaning t m 4988) source

theorem rule38186 (p2027 p2104 p2352 p2459 p2493 p3379 p4133 p4340 p4736 : Prop) (h : (¬ p4736) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p2104) ∨ (¬ p4133) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27442 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 8) (m.theta 4 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38186 (meaning t m 2027) (meaning t m 2104) (meaning t m 2352) (meaning t m 2459) (meaning t m 2493) (meaning t m 3379) (meaning t m 4133) (meaning t m 4340) (meaning t m 4736) source

theorem rule38187 (p2027 p2104 p2241 p2459 p2641 p2668 p4133 p4340 p4736 : Prop) (h : (¬ p2668) ∨ (¬ p2459) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p4736) ∨ (¬ p2641) ∨ (¬ p4340) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27443 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38187 (meaning t m 2027) (meaning t m 2104) (meaning t m 2241) (meaning t m 2459) (meaning t m 2641) (meaning t m 2668) (meaning t m 4133) (meaning t m 4340) (meaning t m 4736) source

theorem rule38188 (p2027 p2230 p2246 p2373 p3366 p3519 p3969 p4037 p4154 p4191 p4236 p4376 p5119 : Prop) (h : (¬ p4191) ∨ (¬ p2246) ∨ (¬ p4236) ∨ (¬ p2230) ∨ (¬ p4154) ∨ (¬ p3366) ∨ (¬ p4037) ∨ (¬ p3969) ∨ (¬ p2373) ∨ (¬ p5119) ∨ (¬ p3519) ∨ (¬ p4376) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2373) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3969) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4191) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial38188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory27444 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule38188 (meaning t m 2027) (meaning t m 2230) (meaning t m 2246) (meaning t m 2373) (meaning t m 3366) (meaning t m 3519) (meaning t m 3969) (meaning t m 4037) (meaning t m 4154) (meaning t m 4191) (meaning t m 4236) (meaning t m 4376) (meaning t m 5119) source

theorem rule38189 (p2027 p2230 p2373 p3954 p3969 p4379 p5119 p5190 p5387 : Prop) (h : (¬ p3969) ∨ (¬ p5119) ∨ (¬ p2230) ∨ (¬ p5387) ∨ (¬ p2373) ∨ (¬ p5190) ∨ (¬ p3954) ∨ (¬ p4379) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3954) ∨ (¬ p3969) ∨ (¬ p4379) ∨ (¬ p5119) ∨ (¬ p5190) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial38189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory27445 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule38189 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3954) (meaning t m 3969) (meaning t m 4379) (meaning t m 5119) (meaning t m 5190) (meaning t m 5387) source

theorem rule38190 (p2027 p2230 p2373 p3365 p3969 p4035 p4419 p5119 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p2230) ∨ (¬ p5119) ∨ (¬ p4419) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p3365) ∨ (¬ p4035) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3969) ∨ (¬ p4035) ∨ (¬ p4419) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial38190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory27446 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule38190 (meaning t m 2027) (meaning t m 2230) (meaning t m 2373) (meaning t m 3365) (meaning t m 3969) (meaning t m 4035) (meaning t m 4419) (meaning t m 5119) (meaning t m 5284) source

theorem rule38191 (p2027 p2246 p2744 p2780 p2946 p3146 p3156 p3366 p3822 p4107 p4669 : Prop) (h : (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial38191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory27447 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule38191 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2780) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3366) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) source

theorem rule38192 (p2387 p3989 p4356 : Prop) (h : (¬ p2387) ∨ (¬ p4356) ∨ p3989) : (¬ p2387) ∨ (p3989) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial38192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2387)) ∨ (meaning t m 3989) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory27448 (m.theta 0 6) (m.theta 5 6) (m.theta 6 8)
  exact rule38192 (meaning t m 2387) (meaning t m 3989) (meaning t m 4356) source

theorem rule38197 (p2027 p2406 p2440 p2751 p2810 p4281 : Prop) (h : (¬ p4281) ∨ (¬ p2810) ∨ (¬ p2751) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2440)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p2751) ∨ (¬ p2810) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial38197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory27453 t (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5)
  exact rule38197 (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2751) (meaning t m 2810) (meaning t m 4281) source

theorem rule38204 (p1981 p2027 p2470 p2528 p2622 p2630 p2656 p4347 : Prop) (h : (¬ p2528) ∨ (¬ p1981) ∨ (¬ p2656) ∨ p2622 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2470)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial38204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory27460 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule38204 (meaning t m 1981) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2622) (meaning t m 2630) (meaning t m 2656) (meaning t m 4347) source

theorem rule38205 (p2027 p2132 p2470 p3343 p3366 p3475 p3588 p3759 p4256 p4324 p4638 p5052 : Prop) (h : (¬ p4638) ∨ (¬ p3759) ∨ p3366 ∨ (¬ p5052) ∨ (¬ p2132) ∨ (¬ p4324) ∨ (¬ p4256) ∨ (¬ p3588) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p3475)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2470) ∨ (¬ p3343) ∨ (p3366) ∨ (¬ p3475) ∨ (¬ p3588) ∨ (¬ p3759) ∨ (¬ p4256) ∨ (¬ p4324) ∨ (¬ p4638) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial38205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3343)) ∨ (meaning t m 3366) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory27461 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 9)
  exact rule38205 (meaning t m 2027) (meaning t m 2132) (meaning t m 2470) (meaning t m 3343) (meaning t m 3366) (meaning t m 3475) (meaning t m 3588) (meaning t m 3759) (meaning t m 4256) (meaning t m 4324) (meaning t m 4638) (meaning t m 5052) source

theorem rule38209 (p3096 p4203 : Prop) (h : p4203 ∨ p3096) : (p3096) ∨ (p4203) := by
  classical
  tauto

theorem initial38209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3096) ∨ (meaning t m 4203) := by
  have source := ElevenTheory.theory27465 (m.theta 4 6) (m.theta 5 6)
  exact rule38209 (meaning t m 3096) (meaning t m 4203) source

theorem rule38220 (p3366 p3414 p3588 p4236 p4325 : Prop) (h : (¬ p3414) ∨ (¬ p4325) ∨ (¬ p4236) ∨ (¬ p3366) ∨ p3588) : (¬ p3366) ∨ (¬ p3414) ∨ (p3588) ∨ (¬ p4236) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial38220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (meaning t m 3588) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory27476 (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 7)
  exact rule38220 (meaning t m 3366) (meaning t m 3414) (meaning t m 3588) (meaning t m 4236) (meaning t m 4325) source

theorem rule38221 (p2027 p2156 p2737 p3759 p4173 p4399 p4749 p4874 : Prop) (h : (¬ p4749) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4173) ∨ (¬ p3759) ∨ (¬ p4874) ∨ (¬ p4399)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2737) ∨ (¬ p3759) ∨ (¬ p4173) ∨ (¬ p4399) ∨ (¬ p4749) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial38221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory27477 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 6)
  exact rule38221 (meaning t m 2027) (meaning t m 2156) (meaning t m 2737) (meaning t m 3759) (meaning t m 4173) (meaning t m 4399) (meaning t m 4749) (meaning t m 4874) source

theorem rule38225 (p1975 p2027 p2274 p2284 p2545 p2810 p3136 : Prop) (h : (¬ p2810) ∨ p2545 ∨ (¬ p2274) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2284)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial38225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory27481 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule38225 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2545) (meaning t m 2810) (meaning t m 3136) source

theorem rule38229 (p2027 p2098 p2138 p3880 p4188 p4885 : Prop) (h : (¬ p3880) ∨ (¬ p2138) ∨ (¬ p4188) ∨ (¬ p4885) ∨ (¬ p2098) ∨ p2027) : (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p3880) ∨ (¬ p4188) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial38229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory27485 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 4 5) (m.theta 5 8)
  exact rule38229 (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 3880) (meaning t m 4188) (meaning t m 4885) source

theorem rule38230 (p2027 p2246 p2608 p2651 p2744 p3016 p3834 p3888 p4321 p5250 : Prop) (h : (¬ p4321) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p3888) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p5250) ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3834)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3834) ∨ (¬ p3888) ∨ (¬ p4321) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial38230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory27486 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 9 10)
  exact rule38230 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3834) (meaning t m 3888) (meaning t m 4321) (meaning t m 5250) source

theorem rule38232 (p2027 p2138 p2534 p3073 p3449 p3758 p3989 p4596 p4736 : Prop) (h : (¬ p4596) ∨ (¬ p2138) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p4736) ∨ (¬ p3073) ∨ (¬ p2534) ∨ (¬ p3449)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3758) ∨ (¬ p3989) ∨ (¬ p4596) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial38232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory27488 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 8) (m.theta 2 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule38232 (meaning t m 2027) (meaning t m 2138) (meaning t m 2534) (meaning t m 3073) (meaning t m 3449) (meaning t m 3758) (meaning t m 3989) (meaning t m 4596) (meaning t m 4736) source

theorem rule38234 (p2027 p3146 p3322 p3767 p4134 p4191 p4456 : Prop) (h : (¬ p3767) ∨ (¬ p4456) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p3146) ∨ (¬ p4134) ∨ p2027) : (p2027) ∨ (¬ p3146) ∨ (¬ p3322) ∨ (¬ p3767) ∨ (¬ p4134) ∨ (¬ p4191) ∨ (¬ p4456) := by
  classical
  tauto

theorem initial38234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4456)) := by
  have source := ElevenTheory.theory27490 t (m.theta 0 9) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule38234 (meaning t m 2027) (meaning t m 3146) (meaning t m 3322) (meaning t m 3767) (meaning t m 4134) (meaning t m 4191) (meaning t m 4456) source

theorem rule38247 (p2459 p3146 p4132 : Prop) (h : (¬ p4132) ∨ (¬ p3146) ∨ p2459) : (p2459) ∨ (¬ p3146) ∨ (¬ p4132) := by
  classical
  tauto

theorem initial38247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2459) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4132)) := by
  have source := ElevenTheory.theory27503 (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38247 (meaning t m 2459) (meaning t m 3146) (meaning t m 4132) source

theorem rule38249 (p2027 p2098 p2534 p2743 p2963 p3073 p3324 p3361 p4353 p4596 p4737 : Prop) (h : (¬ p4353) ∨ (¬ p2743) ∨ (¬ p4737) ∨ (¬ p2098) ∨ (¬ p3361) ∨ (¬ p3073) ∨ (¬ p3324) ∨ (¬ p4596) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2534) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3073) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p4353) ∨ (¬ p4596) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4353)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27505 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 8) (m.theta 2 3) (m.theta 2 8) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule38249 (meaning t m 2027) (meaning t m 2098) (meaning t m 2534) (meaning t m 2743) (meaning t m 2963) (meaning t m 3073) (meaning t m 3324) (meaning t m 3361) (meaning t m 4353) (meaning t m 4596) (meaning t m 4737) source

theorem rule38250 (p2027 p2493 p2553 p2598 p2743 p2963 p3361 p3590 p4037 p4620 p4737 : Prop) (h : (¬ p4620) ∨ (¬ p3590) ∨ (¬ p3361) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2493) ∨ (¬ p2963) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p4037)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p3590) ∨ (¬ p4037) ∨ (¬ p4620) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4620)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27506 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule38250 (meaning t m 2027) (meaning t m 2493) (meaning t m 2553) (meaning t m 2598) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 3590) (meaning t m 4037) (meaning t m 4620) (meaning t m 4737) source

theorem rule38253 (p2027 p2470 p2509 p2656 p2992 p3402 p4704 : Prop) (h : (¬ p2656) ∨ (¬ p3402) ∨ (¬ p4704) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2470) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial38253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory27509 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 8)
  exact rule38253 (meaning t m 2027) (meaning t m 2470) (meaning t m 2509) (meaning t m 2656) (meaning t m 2992) (meaning t m 3402) (meaning t m 4704) source

theorem rule38256 (p1982 p2027 p2114 p2528 p3379 p3641 p3954 p4030 : Prop) (h : (¬ p3954) ∨ p2027 ∨ (¬ p4030) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p1982) ∨ p2114 ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3954) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial38256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory27512 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9)
  exact rule38256 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2528) (meaning t m 3379) (meaning t m 3641) (meaning t m 3954) (meaning t m 4030) source

theorem rule38258 (p2027 p2299 p2313 p3333 p3379 p3645 p3954 p4030 p4198 p4332 p4348 p4877 : Prop) (h : (¬ p4030) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p3954) ∨ (¬ p3379) ∨ (¬ p4877) ∨ (¬ p2299) ∨ (¬ p3333) ∨ (¬ p3645) ∨ (¬ p4198) ∨ (¬ p4332) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p3333) ∨ (¬ p3379) ∨ (¬ p3645) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4198) ∨ (¬ p4332) ∨ (¬ p4348) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial38258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27514 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule38258 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 3333) (meaning t m 3379) (meaning t m 3645) (meaning t m 3954) (meaning t m 4030) (meaning t m 4198) (meaning t m 4332) (meaning t m 4348) (meaning t m 4877) source

theorem rule38259 (p2027 p3136 p3256 p4121 p4340 p4364 p4704 : Prop) (h : (¬ p4364) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p4121) ∨ (¬ p3136) ∨ (¬ p4340) ∨ (¬ p3256)) : (p2027) ∨ (¬ p3136) ∨ (¬ p3256) ∨ (¬ p4121) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial38259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory27515 t (m.theta 2 3) (m.theta 2 8) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule38259 (meaning t m 2027) (meaning t m 3136) (meaning t m 3256) (meaning t m 4121) (meaning t m 4340) (meaning t m 4364) (meaning t m 4704) source

theorem rule38260 (p2027 p2241 p2459 p3189 p3645 p3692 p3954 p4120 p4550 p4877 : Prop) (h : (¬ p3189) ∨ (¬ p2459) ∨ (¬ p2241) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4550) ∨ (¬ p4877) ∨ (¬ p4120) ∨ (¬ p3645)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2459) ∨ (¬ p3189) ∨ (¬ p3645) ∨ (¬ p3692) ∨ (¬ p3954) ∨ (¬ p4120) ∨ (¬ p4550) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial38260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4550)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory27516 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38260 (meaning t m 2027) (meaning t m 2241) (meaning t m 2459) (meaning t m 3189) (meaning t m 3645) (meaning t m 3692) (meaning t m 3954) (meaning t m 4120) (meaning t m 4550) (meaning t m 4877) source

theorem rule38261 (p1990 p2027 p2156 p2545 p2810 p2870 p3556 p4313 : Prop) (h : p2545 ∨ (¬ p2870) ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2156) ∨ (¬ p2810) ∨ (¬ p4313) ∨ (¬ p3556)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial38261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory27517 t (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 5 6) (m.theta 5 7)
  exact rule38261 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2545) (meaning t m 2810) (meaning t m 2870) (meaning t m 3556) (meaning t m 4313) source

theorem rule38264 (p1987 p2027 p2766 p2957 p3556 p3570 p4315 p4348 : Prop) (h : (¬ p4348) ∨ p2027 ∨ (¬ p2957) ∨ (¬ p3570) ∨ (¬ p3556) ∨ (¬ p1987) ∨ (¬ p4315) ∨ p2766) : (¬ p1987) ∨ (p2027) ∨ (p2766) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4315) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial38264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory27520 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule38264 (meaning t m 1987) (meaning t m 2027) (meaning t m 2766) (meaning t m 2957) (meaning t m 3556) (meaning t m 3570) (meaning t m 4315) (meaning t m 4348) source

theorem rule38265 (p2027 p2459 p2608 p3367 p3641 p3692 p4120 p4420 p4524 : Prop) (h : p2027 ∨ (¬ p4420) ∨ (¬ p4524) ∨ (¬ p3641) ∨ (¬ p3367) ∨ (¬ p2608) ∨ (¬ p3692) ∨ (¬ p2459) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4420) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial38265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory27521 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule38265 (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 3367) (meaning t m 3641) (meaning t m 3692) (meaning t m 4120) (meaning t m 4420) (meaning t m 4524) source

theorem rule38267 (p2027 p2143 p2417 p2598 p2922 p3556 p3570 p3583 p3590 p4668 p4737 : Prop) (h : (¬ p3570) ∨ (¬ p3556) ∨ (¬ p2143) ∨ (¬ p4737) ∨ (¬ p2598) ∨ (¬ p4668) ∨ (¬ p3583) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2143) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2922) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p3590) ∨ (¬ p4668) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial38267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory27523 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule38267 (meaning t m 2027) (meaning t m 2143) (meaning t m 2417) (meaning t m 2598) (meaning t m 2922) (meaning t m 3556) (meaning t m 3570) (meaning t m 3583) (meaning t m 3590) (meaning t m 4668) (meaning t m 4737) source

end SunPrize.SMT
