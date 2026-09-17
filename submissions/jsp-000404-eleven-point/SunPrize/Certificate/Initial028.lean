import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory013
import SunPrize.Certificate.Theory014
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule13693 (p1978 p2027 p2284 p2462 p3646 p3690 p4320 : Prop) (h : (¬ p3646) ∨ (¬ p3690) ∨ (¬ p1978) ∨ p2462 ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4320)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2284) ∨ (p2462) ∨ (¬ p3646) ∨ (¬ p3690) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial13693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory3525 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule13693 (meaning t m 1978) (meaning t m 2027) (meaning t m 2284) (meaning t m 2462) (meaning t m 3646) (meaning t m 3690) (meaning t m 4320) source

theorem rule13696 (p1982 p2027 p2528 p2598 p2699 p3537 p3585 p3589 p5373 : Prop) (h : (¬ p2598) ∨ p2027 ∨ p2699 ∨ (¬ p2528) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p5373) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial13696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory3528 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule13696 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2598) (meaning t m 2699) (meaning t m 3537) (meaning t m 3585) (meaning t m 3589) (meaning t m 5373) source

theorem rule13697 (p3874 p5368 p5369 p5370 p5371 : Prop) : (p5369) ∨ (((¬ p5369) ∨ (¬ p3874) ∨ (¬ p5368) ∨ (¬ p5370) ∨ (¬ p5371))) := by
  classical
  tauto

theorem initial13697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5369) ∨ (meaning t m 6097) := by
  exact rule13697 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule13698 (p3874 p5368 p5369 p5370 p5371 : Prop) : (p3874) ∨ (((¬ p5369) ∨ (¬ p3874) ∨ (¬ p5368) ∨ (¬ p5370) ∨ (¬ p5371))) := by
  classical
  tauto

theorem initial13698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3874) ∨ (meaning t m 6097) := by
  exact rule13698 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule13699 (p3874 p5368 p5369 p5370 p5371 : Prop) : (p5368) ∨ (((¬ p5369) ∨ (¬ p3874) ∨ (¬ p5368) ∨ (¬ p5370) ∨ (¬ p5371))) := by
  classical
  tauto

theorem initial13699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5368) ∨ (meaning t m 6097) := by
  exact rule13699 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule13700 (p3874 p5368 p5369 p5370 p5371 : Prop) : (p5370) ∨ (((¬ p5369) ∨ (¬ p3874) ∨ (¬ p5368) ∨ (¬ p5370) ∨ (¬ p5371))) := by
  classical
  tauto

theorem initial13700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5370) ∨ (meaning t m 6097) := by
  exact rule13700 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule13703 (p3641 p4354 p5373 p5374 p5375 : Prop) : (p5373) ∨ (((¬ p5373) ∨ (¬ p4354) ∨ (¬ p3641) ∨ (¬ p5374) ∨ (¬ p5375))) := by
  classical
  tauto

theorem initial13703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5373) ∨ (meaning t m 6098) := by
  exact rule13703 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule13704 (p3641 p4354 p5373 p5374 p5375 : Prop) : (p4354) ∨ (((¬ p5373) ∨ (¬ p4354) ∨ (¬ p3641) ∨ (¬ p5374) ∨ (¬ p5375))) := by
  classical
  tauto

theorem initial13704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4354) ∨ (meaning t m 6098) := by
  exact rule13704 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule13705 (p3641 p4354 p5373 p5374 p5375 : Prop) : (p3641) ∨ (((¬ p5373) ∨ (¬ p4354) ∨ (¬ p3641) ∨ (¬ p5374) ∨ (¬ p5375))) := by
  classical
  tauto

theorem initial13705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3641) ∨ (meaning t m 6098) := by
  exact rule13705 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule13707 (p3641 p4354 p5373 p5374 p5375 : Prop) : (p5375) ∨ (((¬ p5373) ∨ (¬ p4354) ∨ (¬ p3641) ∨ (¬ p5374) ∨ (¬ p5375))) := by
  classical
  tauto

theorem initial13707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5375) ∨ (meaning t m 6098) := by
  exact rule13707 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule13711 (p6097 p6098 : Prop) : (¬ ((¬ p6097) ∨ (¬ p6098))) ∨ (¬ p6097) ∨ (¬ p6098) := by
  classical
  tauto

theorem initial13711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6096)) ∨ (¬ (meaning t m 6097)) ∨ (¬ (meaning t m 6098)) := by
  exact rule13711 (meaning t m 6097) (meaning t m 6098)

theorem rule13712 (p5366 p6096 : Prop) (h : (p5366 ↔ p6096)) : (¬ p5366) ∨ (p6096) := by
  classical
  tauto

theorem initial13712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5366)) ∨ (meaning t m 6096) := by
  have source := ElevenTheory.theory3529 t (m.theta 2 4) (m.theta 2 8) (m.theta 4 8)
  exact rule13712 (meaning t m 5366) (meaning t m 6096) source

theorem rule13714 (p1975 p2027 p2274 p2608 p2699 p2839 p2860 : Prop) (h : (¬ p2839) ∨ (¬ p2860) ∨ (¬ p2608) ∨ (¬ p2274) ∨ (¬ p1975) ∨ p2027 ∨ p2699) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial13714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory3530 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule13714 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2860) source

theorem rule13717 (p1985 p2027 p2699 p2911 p2922 p3379 p3570 : Prop) (h : p2699 ∨ (¬ p1985) ∨ (¬ p2922) ∨ (¬ p3570) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p2911)) : (¬ p1985) ∨ (p2027) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial13717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory3533 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule13717 (meaning t m 1985) (meaning t m 2027) (meaning t m 2699) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3570) source

theorem rule13718 (p1991 p2027 p2766 p2952 p3952 p3989 p4347 : Prop) (h : (¬ p3952) ∨ (¬ p1991) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2952) ∨ (¬ p4347) ∨ p2766) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3534 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule13718 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 2952) (meaning t m 3952) (meaning t m 3989) (meaning t m 4347) source

theorem rule13719 (p1998 p2027 p2177 p2493 p2553 p2699 p3379 : Prop) (h : (¬ p2177) ∨ (¬ p2493) ∨ p2699 ∨ (¬ p3379) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p2553)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial13719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3535 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule13719 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2493) (meaning t m 2553) (meaning t m 2699) (meaning t m 3379) source

theorem rule13720 (p1997 p2027 p2493 p2699 p2850 p3379 p3584 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p3379) ∨ (¬ p2850) ∨ (¬ p1997) ∨ (¬ p3584) ∨ (¬ p2493)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2493) ∨ (p2699) ∨ (¬ p2850) ∨ (¬ p3379) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial13720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory3536 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule13720 (meaning t m 1997) (meaning t m 2027) (meaning t m 2493) (meaning t m 2699) (meaning t m 2850) (meaning t m 3379) (meaning t m 3584) source

theorem rule13721 (p1975 p2027 p2553 p2608 p2699 p3367 p3422 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p2608) ∨ (¬ p3422) ∨ (¬ p3367) ∨ (¬ p2553) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3367) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial13721 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory3537 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule13721 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2608) (meaning t m 2699) (meaning t m 3367) (meaning t m 3422) source

theorem rule13723 (p1998 p2027 p2608 p2699 p2839 p2870 p2881 : Prop) (h : p2027 ∨ (¬ p2839) ∨ p2699 ∨ (¬ p2608) ∨ (¬ p2870) ∨ (¬ p1998) ∨ (¬ p2881)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial13723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory3539 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8)
  exact rule13723 (meaning t m 1998) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2870) (meaning t m 2881) source

theorem rule13724 (p2001 p2169 p3989 p4509 : Prop) (h : (¬ p3989) ∨ p2169 ∨ (¬ p2001) ∨ p4509) : (¬ p2001) ∨ (p2169) ∨ (¬ p3989) ∨ (p4509) := by
  classical
  tauto

theorem initial13724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3989)) ∨ (meaning t m 4509) := by
  have source := ElevenTheory.theory3540 t (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule13724 (meaning t m 2001) (meaning t m 2169) (meaning t m 3989) (meaning t m 4509) source

theorem rule13725 (p1990 p2027 p2563 p2608 p2699 p2850 p3367 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p2563) ∨ (¬ p1990) ∨ p2699 ∨ (¬ p2850) ∨ (¬ p3367)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2850) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial13725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory3541 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule13725 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2608) (meaning t m 2699) (meaning t m 2850) (meaning t m 3367) source

theorem rule13726 (p2156 p2951 p3952 : Prop) (h : (¬ p3952) ∨ (¬ p2156) ∨ (¬ p2951)) : (¬ p2156) ∨ (¬ p2951) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial13726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory3542 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6)
  exact rule13726 (meaning t m 2156) (meaning t m 2951) (meaning t m 3952) source

theorem rule13727 (p1982 p2027 p2459 p2699 p2911 p2922 p3379 : Prop) (h : (¬ p3379) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p1982) ∨ p2699 ∨ p2027 ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial13727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3543 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule13727 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2699) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) source

theorem rule13728 (p3946 p5378 p5379 p5380 p5381 : Prop) : (p5378) ∨ (((¬ p5378) ∨ (¬ p5379) ∨ (¬ p3946) ∨ (¬ p5380) ∨ (¬ p5381))) := by
  classical
  tauto

theorem initial13728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5378) ∨ (meaning t m 6100) := by
  exact rule13728 (meaning t m 3946) (meaning t m 5378) (meaning t m 5379) (meaning t m 5380) (meaning t m 5381)

theorem rule13729 (p3946 p5378 p5379 p5380 p5381 : Prop) : (p5379) ∨ (((¬ p5378) ∨ (¬ p5379) ∨ (¬ p3946) ∨ (¬ p5380) ∨ (¬ p5381))) := by
  classical
  tauto

theorem initial13729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5379) ∨ (meaning t m 6100) := by
  exact rule13729 (meaning t m 3946) (meaning t m 5378) (meaning t m 5379) (meaning t m 5380) (meaning t m 5381)

theorem rule13730 (p3946 p5378 p5379 p5380 p5381 : Prop) : (p3946) ∨ (((¬ p5378) ∨ (¬ p5379) ∨ (¬ p3946) ∨ (¬ p5380) ∨ (¬ p5381))) := by
  classical
  tauto

theorem initial13730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3946) ∨ (meaning t m 6100) := by
  exact rule13730 (meaning t m 3946) (meaning t m 5378) (meaning t m 5379) (meaning t m 5380) (meaning t m 5381)

theorem rule13735 (p3654 p4036 p4038 p5383 p5384 : Prop) : (p4038) ∨ (((¬ p5384) ∨ (¬ p4038) ∨ (¬ p4036) ∨ (¬ p5383) ∨ (¬ p3654))) := by
  classical
  tauto

theorem initial13735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4038) ∨ (meaning t m 6101) := by
  exact rule13735 (meaning t m 3654) (meaning t m 4036) (meaning t m 4038) (meaning t m 5383) (meaning t m 5384)

theorem rule13736 (p3654 p4036 p4038 p5383 p5384 : Prop) : (p4036) ∨ (((¬ p5384) ∨ (¬ p4038) ∨ (¬ p4036) ∨ (¬ p5383) ∨ (¬ p3654))) := by
  classical
  tauto

theorem initial13736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4036) ∨ (meaning t m 6101) := by
  exact rule13736 (meaning t m 3654) (meaning t m 4036) (meaning t m 4038) (meaning t m 5383) (meaning t m 5384)

theorem rule13738 (p3654 p4036 p4038 p5383 p5384 : Prop) : (p3654) ∨ (((¬ p5384) ∨ (¬ p4038) ∨ (¬ p4036) ∨ (¬ p5383) ∨ (¬ p3654))) := by
  classical
  tauto

theorem initial13738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3654) ∨ (meaning t m 6101) := by
  exact rule13738 (meaning t m 3654) (meaning t m 4036) (meaning t m 4038) (meaning t m 5383) (meaning t m 5384)

theorem rule13742 (p6100 p6101 : Prop) : (¬ ((¬ p6100) ∨ (¬ p6101))) ∨ (¬ p6100) ∨ (¬ p6101) := by
  classical
  tauto

theorem initial13742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6099)) ∨ (¬ (meaning t m 6100)) ∨ (¬ (meaning t m 6101)) := by
  exact rule13742 (meaning t m 6100) (meaning t m 6101)

theorem rule13743 (p5376 p6099 : Prop) (h : (p5376 ↔ p6099)) : (¬ p5376) ∨ (p6099) := by
  classical
  tauto

theorem initial13743 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5376)) ∨ (meaning t m 6099) := by
  have source := ElevenTheory.theory3544 t (m.theta 0 6) (m.theta 0 9) (m.theta 6 9)
  exact rule13743 (meaning t m 5376) (meaning t m 6099) source

theorem rule13747 (p1998 p2027 p2518 p2528 p2699 p3379 p4348 : Prop) (h : p2027 ∨ (¬ p1998) ∨ p2699 ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p2528) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial13747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3547 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule13747 (meaning t m 1998) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2699) (meaning t m 3379) (meaning t m 4348) source

theorem rule13748 (p2952 p2963 p4153 : Prop) (h : (¬ p4153) ∨ (¬ p2952) ∨ p2963) : (¬ p2952) ∨ (p2963) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial13748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2952)) ∨ (meaning t m 2963) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory3548 (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule13748 (meaning t m 2952) (meaning t m 2963) (meaning t m 4153) source

theorem rule13749 (p1992 p2027 p2341 p3360 p3585 p3644 p3876 : Prop) (h : p3360 ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p1992) ∨ (¬ p2341) ∨ (¬ p3644)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2341) ∨ (p3360) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial13749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory3549 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule13749 (meaning t m 1992) (meaning t m 2027) (meaning t m 2341) (meaning t m 3360) (meaning t m 3585) (meaning t m 3644) (meaning t m 3876) source

theorem rule13750 (p2005 p2027 p2608 p2630 p2699 p2737 p3016 : Prop) (h : p2699 ∨ (¬ p3016) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p2630) ∨ (¬ p2005) ∨ p2027) : (¬ p2005) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial13750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory3550 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 6)
  exact rule13750 (meaning t m 2005) (meaning t m 2027) (meaning t m 2608) (meaning t m 2630) (meaning t m 2699) (meaning t m 2737) (meaning t m 3016) source

theorem rule13751 (p1985 p2027 p2284 p2323 p2427 p2651 p3413 p4110 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p4110) ∨ (¬ p2284) ∨ (¬ p2651) ∨ (¬ p3413) ∨ (¬ p1985) ∨ (¬ p2427)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2427) ∨ (¬ p2651) ∨ (¬ p3413) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13751 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3551 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13751 (meaning t m 1985) (meaning t m 2027) (meaning t m 2284) (meaning t m 2323) (meaning t m 2427) (meaning t m 2651) (meaning t m 3413) (meaning t m 4110) source

theorem rule13752 (p1985 p2027 p2233 p2427 p2542 p2573 p3574 : Prop) (h : p2233 ∨ (¬ p3574) ∨ (¬ p1985) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p2427)) : (¬ p1985) ∨ (p2027) ∨ (p2233) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial13752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory3552 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule13752 (meaning t m 1985) (meaning t m 2027) (meaning t m 2233) (meaning t m 2427) (meaning t m 2542) (meaning t m 2573) (meaning t m 3574) source

theorem rule13753 (p1990 p2027 p2542 p2563 p2611 p2630 p2696 : Prop) (h : (¬ p2696) ∨ (¬ p2563) ∨ p2611 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2542) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2696) := by
  classical
  tauto

theorem initial13753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) := by
  have source := ElevenTheory.theory3553 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule13753 (meaning t m 1990) (meaning t m 2027) (meaning t m 2542) (meaning t m 2563) (meaning t m 2611) (meaning t m 2630) (meaning t m 2696) source

theorem rule13755 (p2331 p2780 p4117 p4337 : Prop) (h : (¬ p2331) ∨ (¬ p4117) ∨ (¬ p2780) ∨ (¬ p4337)) : (¬ p2331) ∨ (¬ p2780) ∨ (¬ p4117) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial13755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory3555 (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 6)
  exact rule13755 (meaning t m 2331) (meaning t m 2780) (meaning t m 4117) (meaning t m 4337) source

theorem rule13756 (p1998 p2027 p2323 p2881 p2946 p3027 p3662 p4333 : Prop) (h : (¬ p4333) ∨ (¬ p2946) ∨ (¬ p3662) ∨ p2027 ∨ p2323 ∨ (¬ p3027) ∨ (¬ p2881) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial13756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory3556 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule13756 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2881) (meaning t m 2946) (meaning t m 3027) (meaning t m 3662) (meaning t m 4333) source

theorem rule13757 (p2004 p2027 p2202 p2589 p2911 p3389 p3548 : Prop) (h : p2027 ∨ (¬ p2004) ∨ (¬ p2911) ∨ (¬ p3548) ∨ (¬ p2589) ∨ (¬ p3389) ∨ p2202) : (¬ p2004) ∨ (p2027) ∨ (p2202) ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3548) := by
  classical
  tauto

theorem initial13757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3548)) := by
  have source := ElevenTheory.theory3557 t (m.theta 0 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule13757 (meaning t m 2004) (meaning t m 2027) (meaning t m 2202) (meaning t m 2589) (meaning t m 2911) (meaning t m 3389) (meaning t m 3548) source

theorem rule13759 (p2005 p2027 p2622 p2727 p3016 p3136 p3662 : Prop) (h : p2622 ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (p2622) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3136) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial13759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3559 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule13759 (meaning t m 2005) (meaning t m 2027) (meaning t m 2622) (meaning t m 2727) (meaning t m 3016) (meaning t m 3136) (meaning t m 3662) source

theorem rule13760 (p1980 p2027 p2545 p2641 p2657 p2946 p3662 : Prop) (h : (¬ p2641) ∨ (¬ p2946) ∨ (¬ p1980) ∨ (¬ p3662) ∨ p2027 ∨ p2545 ∨ (¬ p2657)) : (¬ p1980) ∨ (p2027) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial13760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3560 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule13760 (meaning t m 1980) (meaning t m 2027) (meaning t m 2545) (meaning t m 2641) (meaning t m 2657) (meaning t m 2946) (meaning t m 3662) source

theorem rule13761 (p1997 p2027 p2608 p2699 p2839 p2860 p4110 : Prop) (h : (¬ p2608) ∨ (¬ p2860) ∨ (¬ p4110) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p1997) ∨ p2699) : (¬ p1997) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13761 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3561 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule13761 (meaning t m 1997) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2860) (meaning t m 4110) source

theorem rule13763 (p1983 p2027 p2253 p2449 p2699 p2946 p3027 p3662 : Prop) (h : (¬ p3027) ∨ (¬ p1983) ∨ (¬ p2253) ∨ p2699 ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p2449)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2449) ∨ (p2699) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial13763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3563 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule13763 (meaning t m 1983) (meaning t m 2027) (meaning t m 2253) (meaning t m 2449) (meaning t m 2699) (meaning t m 2946) (meaning t m 3027) (meaning t m 3662) source

theorem rule13764 (p4027 p4028 p5387 p5388 p5389 : Prop) : (p4027) ∨ (((¬ p4027) ∨ (¬ p5387) ∨ (¬ p4028) ∨ (¬ p5388) ∨ (¬ p5389))) := by
  classical
  tauto

theorem initial13764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4027) ∨ (meaning t m 6103) := by
  exact rule13764 (meaning t m 4027) (meaning t m 4028) (meaning t m 5387) (meaning t m 5388) (meaning t m 5389)

theorem rule13765 (p4027 p4028 p5387 p5388 p5389 : Prop) : (p5387) ∨ (((¬ p4027) ∨ (¬ p5387) ∨ (¬ p4028) ∨ (¬ p5388) ∨ (¬ p5389))) := by
  classical
  tauto

theorem initial13765 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5387) ∨ (meaning t m 6103) := by
  exact rule13765 (meaning t m 4027) (meaning t m 4028) (meaning t m 5387) (meaning t m 5388) (meaning t m 5389)

theorem rule13766 (p4027 p4028 p5387 p5388 p5389 : Prop) : (p4028) ∨ (((¬ p4027) ∨ (¬ p5387) ∨ (¬ p4028) ∨ (¬ p5388) ∨ (¬ p5389))) := by
  classical
  tauto

theorem initial13766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4028) ∨ (meaning t m 6103) := by
  exact rule13766 (meaning t m 4027) (meaning t m 4028) (meaning t m 5387) (meaning t m 5388) (meaning t m 5389)

theorem rule13770 (p3670 p5391 p5392 p5393 p5394 : Prop) : (p5391) ∨ (((¬ p5391) ∨ (¬ p5392) ∨ (¬ p3670) ∨ (¬ p5393) ∨ (¬ p5394))) := by
  classical
  tauto

theorem initial13770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5391) ∨ (meaning t m 6104) := by
  exact rule13770 (meaning t m 3670) (meaning t m 5391) (meaning t m 5392) (meaning t m 5393) (meaning t m 5394)

theorem rule13772 (p3670 p5391 p5392 p5393 p5394 : Prop) : (p3670) ∨ (((¬ p5391) ∨ (¬ p5392) ∨ (¬ p3670) ∨ (¬ p5393) ∨ (¬ p5394))) := by
  classical
  tauto

theorem initial13772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3670) ∨ (meaning t m 6104) := by
  exact rule13772 (meaning t m 3670) (meaning t m 5391) (meaning t m 5392) (meaning t m 5393) (meaning t m 5394)

theorem rule13778 (p6103 p6104 : Prop) : (¬ ((¬ p6103) ∨ (¬ p6104))) ∨ (¬ p6103) ∨ (¬ p6104) := by
  classical
  tauto

theorem initial13778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6102)) ∨ (¬ (meaning t m 6103)) ∨ (¬ (meaning t m 6104)) := by
  exact rule13778 (meaning t m 6103) (meaning t m 6104)

theorem rule13779 (p5385 p6102 : Prop) (h : (p5385 ↔ p6102)) : (¬ p5385) ∨ (p6102) := by
  classical
  tauto

theorem initial13779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5385)) ∨ (meaning t m 6102) := by
  have source := ElevenTheory.theory3564 t (m.theta 2 10) (m.theta 2 9) (m.theta 9 10)
  exact rule13779 (meaning t m 5385) (meaning t m 6102) source

theorem rule13781 (p2011 p2027 p2608 p2699 p2839 p3670 p4322 p5031 : Prop) (h : (¬ p2011) ∨ p2699 ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p4322) ∨ (¬ p3670) ∨ (¬ p5031)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p3670) ∨ (¬ p4322) ∨ (¬ p5031) := by
  classical
  tauto

theorem initial13781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 5031)) := by
  have source := ElevenTheory.theory3565 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 2 9) (m.theta 5 9) (m.theta 9 10)
  exact rule13781 (meaning t m 2011) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 3670) (meaning t m 4322) (meaning t m 5031) source

theorem rule13783 (p4322 p5397 p5398 p5399 p5400 : Prop) : (p4322) ∨ (((¬ p5398) ∨ (¬ p4322) ∨ (¬ p5397) ∨ (¬ p5399) ∨ (¬ p5400))) := by
  classical
  tauto

theorem initial13783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4322) ∨ (meaning t m 6106) := by
  exact rule13783 (meaning t m 4322) (meaning t m 5397) (meaning t m 5398) (meaning t m 5399) (meaning t m 5400)

theorem rule13790 (p3680 p5402 p5403 p5404 p5405 : Prop) : (p3680) ∨ (((¬ p5402) ∨ (¬ p5403) ∨ (¬ p3680) ∨ (¬ p5404) ∨ (¬ p5405))) := by
  classical
  tauto

theorem initial13790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3680) ∨ (meaning t m 6107) := by
  exact rule13790 (meaning t m 3680) (meaning t m 5402) (meaning t m 5403) (meaning t m 5404) (meaning t m 5405)

theorem rule13796 (p6106 p6107 : Prop) : (¬ ((¬ p6106) ∨ (¬ p6107))) ∨ (¬ p6106) ∨ (¬ p6107) := by
  classical
  tauto

theorem initial13796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6105)) ∨ (¬ (meaning t m 6106)) ∨ (¬ (meaning t m 6107)) := by
  exact rule13796 (meaning t m 6106) (meaning t m 6107)

theorem rule13797 (p5395 p6105 : Prop) (h : (p5395 ↔ p6105)) : (¬ p5395) ∨ (p6105) := by
  classical
  tauto

theorem initial13797 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5395)) ∨ (meaning t m 6105) := by
  have source := ElevenTheory.theory3566 t (m.theta 5 10) (m.theta 5 9) (m.theta 9 10)
  exact rule13797 (meaning t m 5395) (meaning t m 6105) source

theorem rule13799 (p1995 p2027 p2499 p2764 p3956 p4347 p4444 : Prop) (h : (¬ p2499) ∨ (¬ p3956) ∨ (¬ p1995) ∨ p2764 ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4444)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (p2764) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial13799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory3567 t (m.theta 1 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule13799 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2764) (meaning t m 3956) (meaning t m 4347) (meaning t m 4444) source

theorem rule13800 (p1996 p2027 p2545 p2657 p2946 p3027 p3662 : Prop) (h : p2027 ∨ (¬ p1996) ∨ (¬ p3662) ∨ (¬ p3027) ∨ (¬ p2946) ∨ (¬ p2657) ∨ p2545) : (¬ p1996) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial13800 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3568 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7)
  exact rule13800 (meaning t m 1996) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) (meaning t m 3027) (meaning t m 3662) source

theorem rule13802 (p1992 p2254 p2323 p2608 p3576 p4794 : Prop) (h : (¬ p1992) ∨ (¬ p2608) ∨ p4794 ∨ (¬ p3576) ∨ p2323 ∨ (¬ p2254)) : (¬ p1992) ∨ (¬ p2254) ∨ (p2323) ∨ (¬ p2608) ∨ (¬ p3576) ∨ (p4794) := by
  classical
  tauto

theorem initial13802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (¬ (meaning t m 2254)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3576)) ∨ (meaning t m 4794) := by
  have source := ElevenTheory.theory3570 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7)
  exact rule13802 (meaning t m 1992) (meaning t m 2254) (meaning t m 2323) (meaning t m 2608) (meaning t m 3576) (meaning t m 4794) source

theorem rule13803 (p1983 p2766 p4348 p4668 : Prop) (h : (¬ p4348) ∨ p2766 ∨ (¬ p1983) ∨ p4668) : (¬ p1983) ∨ (p2766) ∨ (¬ p4348) ∨ (p4668) := by
  classical
  tauto

theorem initial13803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4348)) ∨ (meaning t m 4668) := by
  have source := ElevenTheory.theory3571 t (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule13803 (meaning t m 1983) (meaning t m 2766) (meaning t m 4348) (meaning t m 4668) source

theorem rule13804 (p1975 p2027 p2553 p2699 p2774 p2819 p3589 p3956 : Prop) (h : (¬ p1975) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p3589) ∨ (¬ p3956) ∨ (¬ p2553) ∨ (¬ p2819) ∨ p2699) : (¬ p1975) ∨ (p2027) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3589) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial13804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory3572 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule13804 (meaning t m 1975) (meaning t m 2027) (meaning t m 2553) (meaning t m 2699) (meaning t m 2774) (meaning t m 2819) (meaning t m 3589) (meaning t m 3956) source

theorem rule13805 (p2341 p3516 p3945 : Prop) (h : (¬ p3945) ∨ (¬ p2341) ∨ p3516) : (¬ p2341) ∨ (p3516) ∨ (¬ p3945) := by
  classical
  tauto

theorem initial13805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (meaning t m 3516) ∨ (¬ (meaning t m 3945)) := by
  have source := ElevenTheory.theory3573 (m.theta 0 7) (m.theta 7 8) (m.theta 7 9)
  exact rule13805 (meaning t m 2341) (meaning t m 3516) (meaning t m 3945) source

theorem rule13806 (p1981 p2027 p2518 p2528 p2699 p3379 p4347 : Prop) (h : (¬ p3379) ∨ (¬ p4347) ∨ p2027 ∨ p2699 ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial13806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3574 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule13806 (meaning t m 1981) (meaning t m 2027) (meaning t m 2518) (meaning t m 2528) (meaning t m 2699) (meaning t m 3379) (meaning t m 4347) source

theorem rule13807 (p1983 p2027 p2122 p2396 p2608 p2699 p2829 : Prop) (h : (¬ p2829) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2122) ∨ p2699 ∨ (¬ p2396) ∨ (¬ p2608)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial13807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory3575 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule13807 (meaning t m 1983) (meaning t m 2027) (meaning t m 2122) (meaning t m 2396) (meaning t m 2608) (meaning t m 2699) (meaning t m 2829) source

theorem rule13808 (p2005 p2027 p2588 p2598 p2611 p3309 p3585 p4869 : Prop) (h : p2611 ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p2588) ∨ (¬ p2005) ∨ (¬ p4869) ∨ p2027 ∨ (¬ p3309)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3309) ∨ (¬ p3585) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial13808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory3576 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule13808 (meaning t m 2005) (meaning t m 2027) (meaning t m 2588) (meaning t m 2598) (meaning t m 2611) (meaning t m 3309) (meaning t m 3585) (meaning t m 4869) source

theorem rule13809 (p1992 p2027 p2143 p2765 p2901 p3556 p3583 p3952 : Prop) (h : (¬ p1992) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p2143) ∨ p2765 ∨ (¬ p3952) ∨ (¬ p2901)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2765) ∨ (¬ p2901) ∨ (¬ p3556) ∨ (¬ p3583) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial13809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory3577 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13809 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2765) (meaning t m 2901) (meaning t m 3556) (meaning t m 3583) (meaning t m 3952) source

theorem rule13810 (p1992 p2027 p2143 p2765 p3156 p3583 p3952 p4120 : Prop) (h : p2765 ∨ (¬ p2143) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p1992) ∨ (¬ p3583) ∨ (¬ p3156)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2143) ∨ (p2765) ∨ (¬ p3156) ∨ (¬ p3583) ∨ (¬ p3952) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial13810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2143)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory3578 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule13810 (meaning t m 1992) (meaning t m 2027) (meaning t m 2143) (meaning t m 2765) (meaning t m 3156) (meaning t m 3583) (meaning t m 3952) (meaning t m 4120) source

theorem rule13811 (p1983 p2027 p2417 p2598 p2611 p2707 p3585 p3658 : Prop) (h : (¬ p2417) ∨ (¬ p1983) ∨ (¬ p2598) ∨ p2027 ∨ p2611 ∨ (¬ p3658) ∨ (¬ p3585) ∨ (¬ p2707)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) := by
  classical
  tauto

theorem initial13811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3658)) := by
  have source := ElevenTheory.theory3579 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule13811 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2598) (meaning t m 2611) (meaning t m 2707) (meaning t m 3585) (meaning t m 3658) source

theorem rule13812 (p2010 p2027 p2608 p2699 p2707 p3434 p4278 : Prop) (h : (¬ p2010) ∨ p2027 ∨ p2699 ∨ (¬ p2608) ∨ (¬ p3434) ∨ (¬ p2707) ∨ (¬ p4278)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial13812 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory3580 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule13812 (meaning t m 2010) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 3434) (meaning t m 4278) source

theorem rule13814 (p2008 p2027 p2699 p2707 p3654 p3688 p3917 p5020 : Prop) (h : (¬ p2008) ∨ (¬ p2707) ∨ p2699 ∨ (¬ p3654) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p5020) ∨ (¬ p3688)) : (¬ p2008) ∨ (p2027) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p3654) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial13814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory3582 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 9)
  exact rule13814 (meaning t m 2008) (meaning t m 2027) (meaning t m 2699) (meaning t m 2707) (meaning t m 3654) (meaning t m 3688) (meaning t m 3917) (meaning t m 5020) source

theorem rule13815 (p1991 p2027 p2766 p2952 p3570 p4320 p4348 : Prop) (h : p2027 ∨ (¬ p1991) ∨ (¬ p4348) ∨ p2766 ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p2952)) : (¬ p1991) ∨ (p2027) ∨ (p2766) ∨ (¬ p2952) ∨ (¬ p3570) ∨ (¬ p4320) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial13815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3583 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule13815 (meaning t m 1991) (meaning t m 2027) (meaning t m 2766) (meaning t m 2952) (meaning t m 3570) (meaning t m 4320) (meaning t m 4348) source

theorem rule13816 (p1991 p2027 p2619 p2765 p2952 p3497 p3758 : Prop) (h : (¬ p1991) ∨ p2765 ∨ (¬ p3497) ∨ (¬ p2952) ∨ (¬ p2619) ∨ p2027 ∨ (¬ p3758)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2619) ∨ (p2765) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial13816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory3584 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule13816 (meaning t m 1991) (meaning t m 2027) (meaning t m 2619) (meaning t m 2765) (meaning t m 2952) (meaning t m 3497) (meaning t m 3758) source

theorem rule13817 (p1991 p2027 p2630 p2657 p2938 p4315 p4320 : Prop) (h : p2027 ∨ (¬ p1991) ∨ (¬ p2630) ∨ (¬ p2657) ∨ p2938 ∨ (¬ p4320) ∨ (¬ p4315)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2938) ∨ (¬ p4315) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial13817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory3585 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule13817 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2938) (meaning t m 4315) (meaning t m 4320) source

theorem rule13818 (p1987 p2027 p2331 p2938 p2952 p4195 p4320 : Prop) (h : p2027 ∨ (¬ p2952) ∨ p2938 ∨ (¬ p2331) ∨ (¬ p4320) ∨ (¬ p1987) ∨ (¬ p4195)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2331) ∨ (p2938) ∨ (¬ p2952) ∨ (¬ p4195) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial13818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory3586 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule13818 (meaning t m 1987) (meaning t m 2027) (meaning t m 2331) (meaning t m 2938) (meaning t m 2952) (meaning t m 4195) (meaning t m 4320) source

theorem rule13819 (p2010 p2027 p2437 p2598 p2611 p3422 p3574 : Prop) (h : (¬ p3574) ∨ (¬ p3422) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p2010) ∨ (¬ p2598) ∨ p2611) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3422) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial13819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory3587 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule13819 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 2598) (meaning t m 2611) (meaning t m 3422) (meaning t m 3574) source

theorem rule13820 (p1997 p2542 p2842 p4753 : Prop) (h : (¬ p1997) ∨ p4753 ∨ (¬ p2542) ∨ p2842) : (¬ p1997) ∨ (¬ p2542) ∨ (p2842) ∨ (p4753) := by
  classical
  tauto

theorem initial13820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2842) ∨ (meaning t m 4753) := by
  have source := ElevenTheory.theory3588 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule13820 (meaning t m 1997) (meaning t m 2542) (meaning t m 2842) (meaning t m 4753) source

theorem rule13822 (p1987 p2027 p2331 p2766 p3172 p4118 p4195 : Prop) (h : p2027 ∨ (¬ p4118) ∨ (¬ p2331) ∨ (¬ p4195) ∨ p2766 ∨ (¬ p3172) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2331) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial13822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory3590 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule13822 (meaning t m 1987) (meaning t m 2027) (meaning t m 2331) (meaning t m 2766) (meaning t m 3172) (meaning t m 4118) (meaning t m 4195) source

theorem rule13824 (p2274 p2311 p2312 p4356 : Prop) (h : (¬ p4356) ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p2311)) : (¬ p2274) ∨ (¬ p2311) ∨ (¬ p2312) ∨ (¬ p4356) := by
  classical
  tauto

theorem initial13824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 4356)) := by
  have source := ElevenTheory.theory3592 (m.theta 0 6) (m.theta 0 7) (m.theta 5 6) (m.theta 6 7)
  exact rule13824 (meaning t m 2274) (meaning t m 2311) (meaning t m 2312) (meaning t m 4356) source

theorem rule13827 (p4321 p5408 p5409 p5410 p5411 : Prop) : (p4321) ∨ (((¬ p5409) ∨ (¬ p4321) ∨ (¬ p5408) ∨ (¬ p5410) ∨ (¬ p5411))) := by
  classical
  tauto

theorem initial13827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4321) ∨ (meaning t m 6109) := by
  exact rule13827 (meaning t m 4321) (meaning t m 5408) (meaning t m 5409) (meaning t m 5410) (meaning t m 5411)

theorem rule13832 (p3707 p5413 p5414 p5415 p5416 : Prop) : (p5413) ∨ (((¬ p5413) ∨ (¬ p5414) ∨ (¬ p3707) ∨ (¬ p5415) ∨ (¬ p5416))) := by
  classical
  tauto

theorem initial13832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5413) ∨ (meaning t m 6110) := by
  exact rule13832 (meaning t m 3707) (meaning t m 5413) (meaning t m 5414) (meaning t m 5415) (meaning t m 5416)

theorem rule13833 (p3707 p5413 p5414 p5415 p5416 : Prop) : (p5414) ∨ (((¬ p5413) ∨ (¬ p5414) ∨ (¬ p3707) ∨ (¬ p5415) ∨ (¬ p5416))) := by
  classical
  tauto

theorem initial13833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5414) ∨ (meaning t m 6110) := by
  exact rule13833 (meaning t m 3707) (meaning t m 5413) (meaning t m 5414) (meaning t m 5415) (meaning t m 5416)

theorem rule13834 (p3707 p5413 p5414 p5415 p5416 : Prop) : (p3707) ∨ (((¬ p5413) ∨ (¬ p5414) ∨ (¬ p3707) ∨ (¬ p5415) ∨ (¬ p5416))) := by
  classical
  tauto

theorem initial13834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3707) ∨ (meaning t m 6110) := by
  exact rule13834 (meaning t m 3707) (meaning t m 5413) (meaning t m 5414) (meaning t m 5415) (meaning t m 5416)

theorem rule13840 (p6109 p6110 : Prop) : (¬ ((¬ p6109) ∨ (¬ p6110))) ∨ (¬ p6109) ∨ (¬ p6110) := by
  classical
  tauto

theorem initial13840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6108)) ∨ (¬ (meaning t m 6109)) ∨ (¬ (meaning t m 6110)) := by
  exact rule13840 (meaning t m 6109) (meaning t m 6110)

theorem rule13841 (p5406 p6108 : Prop) (h : (p5406 ↔ p6108)) : (¬ p5406) ∨ (p6108) := by
  classical
  tauto

theorem initial13841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5406)) ∨ (meaning t m 6108) := by
  have source := ElevenTheory.theory3594 t (m.theta 1 10) (m.theta 1 9) (m.theta 9 10)
  exact rule13841 (meaning t m 5406) (meaning t m 6108) source

theorem rule13843 (p2012 p2027 p2230 p2233 p3233 p3238 p3707 p4425 : Prop) (h : p2233 ∨ (¬ p3233) ∨ (¬ p3707) ∨ (¬ p2012) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p4425)) : (¬ p2012) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial13843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory3595 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 9) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule13843 (meaning t m 2012) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 3233) (meaning t m 3238) (meaning t m 3707) (meaning t m 4425) source

theorem rule13848 (p5419 p5420 p5421 p5422 p5423 : Prop) : (p5421) ∨ (((¬ p5420) ∨ (¬ p5421) ∨ (¬ p5419) ∨ (¬ p5422) ∨ (¬ p5423))) := by
  classical
  tauto

theorem initial13848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5421) ∨ (meaning t m 6112) := by
  exact rule13848 (meaning t m 5419) (meaning t m 5420) (meaning t m 5421) (meaning t m 5422) (meaning t m 5423)

theorem rule13855 (p3717 p5425 p5426 p5427 p5428 : Prop) : (p3717) ∨ (((¬ p5425) ∨ (¬ p5426) ∨ (¬ p3717) ∨ (¬ p5427) ∨ (¬ p5428))) := by
  classical
  tauto

theorem initial13855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3717) ∨ (meaning t m 6113) := by
  exact rule13855 (meaning t m 3717) (meaning t m 5425) (meaning t m 5426) (meaning t m 5427) (meaning t m 5428)

theorem rule13861 (p6112 p6113 : Prop) : (¬ ((¬ p6112) ∨ (¬ p6113))) ∨ (¬ p6112) ∨ (¬ p6113) := by
  classical
  tauto

theorem initial13861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6111)) ∨ (¬ (meaning t m 6112)) ∨ (¬ (meaning t m 6113)) := by
  exact rule13861 (meaning t m 6112) (meaning t m 6113)

theorem rule13862 (p5417 p6111 : Prop) (h : (p5417 ↔ p6111)) : (¬ p5417) ∨ (p6111) := by
  classical
  tauto

theorem initial13862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5417)) ∨ (meaning t m 6111) := by
  have source := ElevenTheory.theory3599 t (m.theta 2 10) (m.theta 2 5) (m.theta 5 10)
  exact rule13862 (meaning t m 5417) (meaning t m 6111) source

theorem rule13870 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p5437) ∨ (((¬ p5437) ∨ (¬ p4258) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p5439))) := by
  classical
  tauto

theorem initial13870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5437) ∨ (meaning t m 6116) := by
  exact rule13870 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule13871 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p4258) ∨ (((¬ p5437) ∨ (¬ p4258) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p5439))) := by
  classical
  tauto

theorem initial13871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4258) ∨ (meaning t m 6116) := by
  exact rule13871 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule13872 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p3727) ∨ (((¬ p5437) ∨ (¬ p4258) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p5439))) := by
  classical
  tauto

theorem initial13872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3727) ∨ (meaning t m 6116) := by
  exact rule13872 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule13873 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p5438) ∨ (((¬ p5437) ∨ (¬ p4258) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p5439))) := by
  classical
  tauto

theorem initial13873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5438) ∨ (meaning t m 6116) := by
  exact rule13873 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule13874 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p5439) ∨ (((¬ p5437) ∨ (¬ p4258) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p5439))) := by
  classical
  tauto

theorem initial13874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5439) ∨ (meaning t m 6116) := by
  exact rule13874 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule13875 (p3727 p4258 p5437 p5438 p5439 : Prop) : (¬ p3727) ∨ (¬ p4258) ∨ (¬ p5437) ∨ (¬ p5438) ∨ (¬ p5439) ∨ (¬ ((¬ p5437) ∨ (¬ p4258) ∨ (¬ p3727) ∨ (¬ p5438) ∨ (¬ p5439))) := by
  classical
  tauto

theorem initial13875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4258)) ∨ (¬ (meaning t m 5437)) ∨ (¬ (meaning t m 5438)) ∨ (¬ (meaning t m 5439)) ∨ (¬ (meaning t m 6116)) := by
  exact rule13875 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule13881 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p5444) ∨ (((¬ p5444) ∨ (¬ p4393) ∨ (¬ p5443) ∨ (¬ p5440) ∨ (¬ p5445))) := by
  classical
  tauto

theorem initial13881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5444) ∨ (meaning t m 6118) := by
  exact rule13881 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule13882 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p4393) ∨ (((¬ p5444) ∨ (¬ p4393) ∨ (¬ p5443) ∨ (¬ p5440) ∨ (¬ p5445))) := by
  classical
  tauto

theorem initial13882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4393) ∨ (meaning t m 6118) := by
  exact rule13882 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule13883 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p5443) ∨ (((¬ p5444) ∨ (¬ p4393) ∨ (¬ p5443) ∨ (¬ p5440) ∨ (¬ p5445))) := by
  classical
  tauto

theorem initial13883 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5443) ∨ (meaning t m 6118) := by
  exact rule13883 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule13884 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p5440) ∨ (((¬ p5444) ∨ (¬ p4393) ∨ (¬ p5443) ∨ (¬ p5440) ∨ (¬ p5445))) := by
  classical
  tauto

theorem initial13884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5440) ∨ (meaning t m 6118) := by
  exact rule13884 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule13885 (p4393 p5440 p5443 p5444 p5445 : Prop) : (p5445) ∨ (((¬ p5444) ∨ (¬ p4393) ∨ (¬ p5443) ∨ (¬ p5440) ∨ (¬ p5445))) := by
  classical
  tauto

theorem initial13885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5445) ∨ (meaning t m 6118) := by
  exact rule13885 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule13886 (p4393 p5440 p5443 p5444 p5445 : Prop) : (¬ p4393) ∨ (¬ p5440) ∨ (¬ p5443) ∨ (¬ p5444) ∨ (¬ p5445) ∨ (¬ ((¬ p5444) ∨ (¬ p4393) ∨ (¬ p5443) ∨ (¬ p5440) ∨ (¬ p5445))) := by
  classical
  tauto

theorem initial13886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5440)) ∨ (¬ (meaning t m 5443)) ∨ (¬ (meaning t m 5444)) ∨ (¬ (meaning t m 5445)) ∨ (¬ (meaning t m 6118)) := by
  exact rule13886 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

theorem rule13889 (p3737 p5447 p5448 p5449 p5450 : Prop) : (p3737) ∨ (((¬ p5447) ∨ (¬ p5448) ∨ (¬ p3737) ∨ (¬ p5449) ∨ (¬ p5450))) := by
  classical
  tauto

theorem initial13889 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3737) ∨ (meaning t m 6119) := by
  exact rule13889 (meaning t m 3737) (meaning t m 5447) (meaning t m 5448) (meaning t m 5449) (meaning t m 5450)

theorem rule13890 (p3737 p5447 p5448 p5449 p5450 : Prop) : (p5449) ∨ (((¬ p5447) ∨ (¬ p5448) ∨ (¬ p3737) ∨ (¬ p5449) ∨ (¬ p5450))) := by
  classical
  tauto

theorem initial13890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5449) ∨ (meaning t m 6119) := by
  exact rule13890 (meaning t m 3737) (meaning t m 5447) (meaning t m 5448) (meaning t m 5449) (meaning t m 5450)

theorem rule13895 (p6118 p6119 : Prop) : (¬ ((¬ p6118) ∨ (¬ p6119))) ∨ (¬ p6118) ∨ (¬ p6119) := by
  classical
  tauto

theorem initial13895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6117)) ∨ (¬ (meaning t m 6118)) ∨ (¬ (meaning t m 6119)) := by
  exact rule13895 (meaning t m 6118) (meaning t m 6119)

theorem rule13896 (p5441 p6117 : Prop) (h : (p5441 ↔ p6117)) : (¬ p5441) ∨ (p6117) := by
  classical
  tauto

theorem initial13896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5441)) ∨ (meaning t m 6117) := by
  have source := ElevenTheory.theory3601 t (m.theta 5 10) (m.theta 5 6) (m.theta 6 10)
  exact rule13896 (meaning t m 5441) (meaning t m 6117) source

theorem rule13899 (p1982 p2027 p2608 p2619 p2699 p2839 p3146 : Prop) (h : (¬ p2619) ∨ (¬ p3146) ∨ p2699 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2619) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial13899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory3603 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule13899 (meaning t m 1982) (meaning t m 2027) (meaning t m 2608) (meaning t m 2619) (meaning t m 2699) (meaning t m 2839) (meaning t m 3146) source

theorem rule13901 (p1997 p2132 p2611 p4885 : Prop) (h : p4885 ∨ p2611 ∨ (¬ p2132) ∨ (¬ p1997)) : (¬ p1997) ∨ (¬ p2132) ∨ (p2611) ∨ (p4885) := by
  classical
  tauto

theorem initial13901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (meaning t m 4885) := by
  have source := ElevenTheory.theory3605 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5)
  exact rule13901 (meaning t m 1997) (meaning t m 2132) (meaning t m 2611) (meaning t m 4885) source

theorem rule13902 (p2010 p2027 p2202 p2573 p2589 p3201 p3584 : Prop) (h : (¬ p3201) ∨ p2027 ∨ (¬ p2010) ∨ (¬ p3584) ∨ p2202 ∨ (¬ p2589) ∨ (¬ p2573)) : (¬ p2010) ∨ (p2027) ∨ (p2202) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3201) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial13902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory3606 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule13902 (meaning t m 2010) (meaning t m 2027) (meaning t m 2202) (meaning t m 2573) (meaning t m 2589) (meaning t m 3201) (meaning t m 3584) source

theorem rule13903 (p1983 p2027 p2406 p2427 p2699 p3246 p3379 : Prop) (h : (¬ p3379) ∨ (¬ p2427) ∨ p2699 ∨ (¬ p1983) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2406)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2427) ∨ (p2699) ∨ (¬ p3246) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial13903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3607 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule13903 (meaning t m 1983) (meaning t m 2027) (meaning t m 2406) (meaning t m 2427) (meaning t m 2699) (meaning t m 3246) (meaning t m 3379) source

theorem rule13904 (p1983 p2027 p2608 p2699 p2839 p2870 p3246 : Prop) (h : p2699 ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p1983) ∨ (¬ p2608)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial13904 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory3608 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9)
  exact rule13904 (meaning t m 1983) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2870) (meaning t m 3246) source

theorem rule13905 (p1990 p2388 p2901 p4555 : Prop) (h : p2388 ∨ (¬ p1990) ∨ (¬ p2901) ∨ p4555) : (¬ p1990) ∨ (p2388) ∨ (¬ p2901) ∨ (p4555) := by
  classical
  tauto

theorem initial13905 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2901)) ∨ (meaning t m 4555) := by
  have source := ElevenTheory.theory3609 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13905 (meaning t m 1990) (meaning t m 2388) (meaning t m 2901) (meaning t m 4555) source

theorem rule13906 (p1985 p2027 p2122 p2132 p2177 p2611 p3570 p3985 : Prop) (h : p2611 ∨ p2027 ∨ (¬ p3985) ∨ (¬ p2132) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p1985) ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2132) ∨ (¬ p2177) ∨ (p2611) ∨ (¬ p3570) ∨ (¬ p3985) := by
  classical
  tauto

theorem initial13906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3985)) := by
  have source := ElevenTheory.theory3610 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule13906 (meaning t m 1985) (meaning t m 2027) (meaning t m 2122) (meaning t m 2132) (meaning t m 2177) (meaning t m 2611) (meaning t m 3570) (meaning t m 3985) source

theorem rule13907 (p2318 p2319 p2962 p3556 p4275 : Prop) (h : (¬ p2962) ∨ (¬ p2319) ∨ (¬ p2318) ∨ (¬ p3556) ∨ (¬ p4275)) : (¬ p2318) ∨ (¬ p2319) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p4275) := by
  classical
  tauto

theorem initial13907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4275)) := by
  have source := ElevenTheory.theory3611 (m.theta 0 5) (m.theta 0 6) (m.theta 0 7) (m.theta 5 7) (m.theta 6 7)
  exact rule13907 (meaning t m 2318) (meaning t m 2319) (meaning t m 2962) (meaning t m 3556) (meaning t m 4275) source

theorem rule13909 (p1976 p3055 p3474 p3684 p4885 : Prop) (h : (¬ p3684) ∨ (¬ p1976) ∨ (¬ p3055) ∨ p4885 ∨ p3474) : (¬ p1976) ∨ (¬ p3055) ∨ (p3474) ∨ (¬ p3684) ∨ (p4885) := by
  classical
  tauto

theorem initial13909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (¬ (meaning t m 3055)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3684)) ∨ (meaning t m 4885) := by
  have source := ElevenTheory.theory3613 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule13909 (meaning t m 1976) (meaning t m 3055) (meaning t m 3474) (meaning t m 3684) (meaning t m 4885) source

theorem rule13911 (p1976 p2027 p2138 p2284 p2938 p3758 p4320 : Prop) (h : (¬ p1976) ∨ (¬ p2284) ∨ p2938 ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3758) ∨ (¬ p2138)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2284) ∨ (p2938) ∨ (¬ p3758) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial13911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory3615 t (m.theta 0 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13911 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2284) (meaning t m 2938) (meaning t m 3758) (meaning t m 4320) source

theorem rule13912 (p3984 p4037 p4331 p4422 : Prop) (h : (¬ p4037) ∨ (¬ p3984) ∨ (¬ p4331) ∨ (¬ p4422)) : (¬ p3984) ∨ (¬ p4037) ∨ (¬ p4331) ∨ (¬ p4422) := by
  classical
  tauto

theorem initial13912 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4422)) := by
  have source := ElevenTheory.theory3616 (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule13912 (meaning t m 3984) (meaning t m 4037) (meaning t m 4331) (meaning t m 4422) source

theorem rule13913 (p4035 p5453 p5454 p5455 p5456 : Prop) : (p5454) ∨ (((¬ p5454) ∨ (¬ p4035) ∨ (¬ p5453) ∨ (¬ p5455) ∨ (¬ p5456))) := by
  classical
  tauto

theorem initial13913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5454) ∨ (meaning t m 6121) := by
  exact rule13913 (meaning t m 4035) (meaning t m 5453) (meaning t m 5454) (meaning t m 5455) (meaning t m 5456)

theorem rule13914 (p4035 p5453 p5454 p5455 p5456 : Prop) : (p4035) ∨ (((¬ p5454) ∨ (¬ p4035) ∨ (¬ p5453) ∨ (¬ p5455) ∨ (¬ p5456))) := by
  classical
  tauto

theorem initial13914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4035) ∨ (meaning t m 6121) := by
  exact rule13914 (meaning t m 4035) (meaning t m 5453) (meaning t m 5454) (meaning t m 5455) (meaning t m 5456)

theorem rule13915 (p4035 p5453 p5454 p5455 p5456 : Prop) : (p5453) ∨ (((¬ p5454) ∨ (¬ p4035) ∨ (¬ p5453) ∨ (¬ p5455) ∨ (¬ p5456))) := by
  classical
  tauto

theorem initial13915 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5453) ∨ (meaning t m 6121) := by
  exact rule13915 (meaning t m 4035) (meaning t m 5453) (meaning t m 5454) (meaning t m 5455) (meaning t m 5456)

theorem rule13919 (p3755 p5458 p5459 p5460 p5461 : Prop) : (p5458) ∨ (((¬ p5458) ∨ (¬ p5459) ∨ (¬ p3755) ∨ (¬ p5460) ∨ (¬ p5461))) := by
  classical
  tauto

theorem initial13919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5458) ∨ (meaning t m 6122) := by
  exact rule13919 (meaning t m 3755) (meaning t m 5458) (meaning t m 5459) (meaning t m 5460) (meaning t m 5461)

theorem rule13920 (p3755 p5458 p5459 p5460 p5461 : Prop) : (p5459) ∨ (((¬ p5458) ∨ (¬ p5459) ∨ (¬ p3755) ∨ (¬ p5460) ∨ (¬ p5461))) := by
  classical
  tauto

theorem initial13920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5459) ∨ (meaning t m 6122) := by
  exact rule13920 (meaning t m 3755) (meaning t m 5458) (meaning t m 5459) (meaning t m 5460) (meaning t m 5461)

theorem rule13921 (p3755 p5458 p5459 p5460 p5461 : Prop) : (p3755) ∨ (((¬ p5458) ∨ (¬ p5459) ∨ (¬ p3755) ∨ (¬ p5460) ∨ (¬ p5461))) := by
  classical
  tauto

theorem initial13921 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3755) ∨ (meaning t m 6122) := by
  exact rule13921 (meaning t m 3755) (meaning t m 5458) (meaning t m 5459) (meaning t m 5460) (meaning t m 5461)

theorem rule13922 (p3755 p5458 p5459 p5460 p5461 : Prop) : (p5460) ∨ (((¬ p5458) ∨ (¬ p5459) ∨ (¬ p3755) ∨ (¬ p5460) ∨ (¬ p5461))) := by
  classical
  tauto

theorem initial13922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5460) ∨ (meaning t m 6122) := by
  exact rule13922 (meaning t m 3755) (meaning t m 5458) (meaning t m 5459) (meaning t m 5460) (meaning t m 5461)

theorem rule13927 (p6121 p6122 : Prop) : (¬ ((¬ p6121) ∨ (¬ p6122))) ∨ (¬ p6121) ∨ (¬ p6122) := by
  classical
  tauto

theorem initial13927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6120)) ∨ (¬ (meaning t m 6121)) ∨ (¬ (meaning t m 6122)) := by
  exact rule13927 (meaning t m 6121) (meaning t m 6122)

theorem rule13928 (p5451 p6120 : Prop) (h : (p5451 ↔ p6120)) : (¬ p5451) ∨ (p6120) := by
  classical
  tauto

theorem initial13928 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5451)) ∨ (meaning t m 6120) := by
  have source := ElevenTheory.theory3617 t (m.theta 2 3) (m.theta 2 9) (m.theta 3 9)
  exact rule13928 (meaning t m 5451) (meaning t m 6120) source

theorem rule13930 (p2088 p3171 p4349 p5107 : Prop) (h : (¬ p4349) ∨ (¬ p3171) ∨ (¬ p5107) ∨ (¬ p2088)) : (¬ p2088) ∨ (¬ p3171) ∨ (¬ p4349) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial13930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 4349)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory3618 (m.theta 0 8) (m.theta 3 8) (m.theta 3 9) (m.theta 8 9)
  exact rule13930 (meaning t m 2088) (meaning t m 3171) (meaning t m 4349) (meaning t m 5107) source

theorem rule13931 (p1992 p2027 p2220 p2765 p3583 p3646 p3694 : Prop) (h : (¬ p3646) ∨ p2027 ∨ (¬ p3694) ∨ (¬ p1992) ∨ (¬ p3583) ∨ (¬ p2220) ∨ p2765) : (¬ p1992) ∨ (p2027) ∨ (¬ p2220) ∨ (p2765) ∨ (¬ p3583) ∨ (¬ p3646) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial13931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory3619 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8)
  exact rule13931 (meaning t m 1992) (meaning t m 2027) (meaning t m 2220) (meaning t m 2765) (meaning t m 3583) (meaning t m 3646) (meaning t m 3694) source

theorem rule13932 (p1976 p2027 p2766 p3365 p3497 p3692 p4315 : Prop) (h : (¬ p3497) ∨ p2766 ∨ (¬ p1976) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p4315)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3365) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial13932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory3620 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule13932 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3365) (meaning t m 3497) (meaning t m 3692) (meaning t m 4315) source

theorem rule13935 (p1985 p2027 p2344 p2427 p3654 p3744 p4110 : Prop) (h : (¬ p2427) ∨ p2344 ∨ (¬ p3654) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (p2344) ∨ (¬ p2427) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial13935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2344) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3623 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule13935 (meaning t m 1985) (meaning t m 2027) (meaning t m 2344) (meaning t m 2427) (meaning t m 3654) (meaning t m 3744) (meaning t m 4110) source

theorem rule13936 (p1985 p2427 p2914 p4644 : Prop) (h : (¬ p1985) ∨ p2914 ∨ (¬ p2427) ∨ p4644) : (¬ p1985) ∨ (¬ p2427) ∨ (p2914) ∨ (p4644) := by
  classical
  tauto

theorem initial13936 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2914) ∨ (meaning t m 4644) := by
  have source := ElevenTheory.theory3624 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule13936 (meaning t m 1985) (meaning t m 2427) (meaning t m 2914) (meaning t m 4644) source

theorem rule13937 (p1976 p2027 p2138 p2765 p3115 p3952 p4385 : Prop) (h : (¬ p1976) ∨ (¬ p3952) ∨ (¬ p4385) ∨ (¬ p2138) ∨ p2027 ∨ p2765 ∨ (¬ p3115)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2765) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial13937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory3625 t (m.theta 0 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9)
  exact rule13937 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2765) (meaning t m 3115) (meaning t m 3952) (meaning t m 4385) source

theorem rule13938 (p1981 p2027 p2187 p2230 p2476 p2563 p3498 : Prop) (h : p3498 ∨ (¬ p2230) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p1981) ∨ (¬ p2476)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2563) ∨ (p3498) := by
  classical
  tauto

theorem initial13938 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3498) := by
  have source := ElevenTheory.theory3626 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule13938 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2230) (meaning t m 2476) (meaning t m 2563) (meaning t m 3498) source

theorem rule13942 (p1983 p2027 p2299 p2396 p2842 p2911 p3201 : Prop) (h : p2027 ∨ (¬ p1983) ∨ (¬ p2911) ∨ (¬ p2396) ∨ (¬ p2299) ∨ p2842 ∨ (¬ p3201)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2842) ∨ (¬ p2911) ∨ (¬ p3201) := by
  classical
  tauto

theorem initial13942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) := by
  have source := ElevenTheory.theory3630 t (m.theta 2 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule13942 (meaning t m 1983) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2842) (meaning t m 2911) (meaning t m 3201) source

theorem rule13944 (p1983 p2027 p2396 p2553 p2598 p2611 p3422 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p3422) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p1983) ∨ (¬ p2598)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial13944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory3632 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9)
  exact rule13944 (meaning t m 1983) (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2598) (meaning t m 2611) (meaning t m 3422) source

theorem rule13947 (p1992 p2027 p2132 p2914 p3055 p3583 p3876 : Prop) (h : p2914 ∨ p2027 ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (p2914) ∨ (¬ p3055) ∨ (¬ p3583) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial13947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory3635 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7)
  exact rule13947 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2914) (meaning t m 3055) (meaning t m 3583) (meaning t m 3876) source

theorem rule13948 (p2504 p3564 p4026 : Prop) (h : (¬ p4026) ∨ (¬ p3564) ∨ (¬ p2504)) : (¬ p2504) ∨ (¬ p3564) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial13948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory3636 (m.theta 1 6) (m.theta 4 6) (m.theta 6 9)
  exact rule13948 (meaning t m 2504) (meaning t m 3564) (meaning t m 4026) source

theorem rule13949 (p1997 p2938 p4110 p4555 : Prop) (h : (¬ p1997) ∨ p2938 ∨ p4555 ∨ (¬ p4110)) : (¬ p1997) ∨ (p2938) ∨ (¬ p4110) ∨ (p4555) := by
  classical
  tauto

theorem initial13949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4555) := by
  have source := ElevenTheory.theory3637 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13949 (meaning t m 1997) (meaning t m 2938) (meaning t m 4110) (meaning t m 4555) source

theorem rule13950 (p1995 p2027 p2476 p2499 p2534 p2573 p2766 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p1995) ∨ (¬ p2534) ∨ (¬ p2573)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (¬ p2573) ∨ (p2766) := by
  classical
  tauto

theorem initial13950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2766) := by
  have source := ElevenTheory.theory3638 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule13950 (meaning t m 1995) (meaning t m 2027) (meaning t m 2476) (meaning t m 2499) (meaning t m 2534) (meaning t m 2573) (meaning t m 2766) source

theorem rule13951 (p1995 p2027 p2230 p2579 p2588 p2997 p3238 : Prop) (h : (¬ p1995) ∨ (¬ p2588) ∨ (¬ p3238) ∨ (¬ p2579) ∨ p2997 ∨ (¬ p2230) ∨ p2027) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial13951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory3639 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule13951 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2579) (meaning t m 2588) (meaning t m 2997) (meaning t m 3238) source

theorem rule13953 (p1991 p2148 p2952 p2960 : Prop) (h : (¬ p1991) ∨ p2148 ∨ (¬ p2952) ∨ p2960) : (¬ p1991) ∨ (p2148) ∨ (¬ p2952) ∨ (p2960) := by
  classical
  tauto

theorem initial13953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2960) := by
  have source := ElevenTheory.theory3641 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5)
  exact rule13953 (meaning t m 1991) (meaning t m 2148) (meaning t m 2952) (meaning t m 2960) source

theorem rule13954 (p1975 p2027 p2241 p2274 p2284 p2699 p2992 : Prop) (h : (¬ p1975) ∨ (¬ p2274) ∨ p2027 ∨ p2699 ∨ (¬ p2284) ∨ (¬ p2241) ∨ (¬ p2992)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial13954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory3642 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule13954 (meaning t m 1975) (meaning t m 2027) (meaning t m 2241) (meaning t m 2274) (meaning t m 2284) (meaning t m 2699) (meaning t m 2992) source

theorem rule13955 (p1992 p2027 p2138 p2696 p2743 p2938 p4244 : Prop) (h : (¬ p1992) ∨ p2938 ∨ (¬ p2743) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2138)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (p2938) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial13955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory3643 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 7)
  exact rule13955 (meaning t m 1992) (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2743) (meaning t m 2938) (meaning t m 4244) source

theorem rule13957 (p4260 p5470 p5471 p5472 p5473 : Prop) : (p4260) ∨ (((¬ p5471) ∨ (¬ p4260) ∨ (¬ p5470) ∨ (¬ p5472) ∨ (¬ p5473))) := by
  classical
  tauto

theorem initial13957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4260) ∨ (meaning t m 6124) := by
  exact rule13957 (meaning t m 4260) (meaning t m 5470) (meaning t m 5471) (meaning t m 5472) (meaning t m 5473)

theorem rule13964 (p3791 p5475 p5476 p5477 p5478 : Prop) : (p3791) ∨ (((¬ p5475) ∨ (¬ p5476) ∨ (¬ p3791) ∨ (¬ p5477) ∨ (¬ p5478))) := by
  classical
  tauto

theorem initial13964 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3791) ∨ (meaning t m 6125) := by
  exact rule13964 (meaning t m 3791) (meaning t m 5475) (meaning t m 5476) (meaning t m 5477) (meaning t m 5478)

theorem rule13970 (p6124 p6125 : Prop) : (¬ ((¬ p6124) ∨ (¬ p6125))) ∨ (¬ p6124) ∨ (¬ p6125) := by
  classical
  tauto

theorem initial13970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6123)) ∨ (¬ (meaning t m 6124)) ∨ (¬ (meaning t m 6125)) := by
  exact rule13970 (meaning t m 6124) (meaning t m 6125)

theorem rule13971 (p5468 p6123 : Prop) (h : (p5468 ↔ p6123)) : (¬ p5468) ∨ (p6123) := by
  classical
  tauto

theorem initial13971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5468)) ∨ (meaning t m 6123) := by
  have source := ElevenTheory.theory3644 t (m.theta 6 10) (m.theta 6 7) (m.theta 7 10)
  exact rule13971 (meaning t m 5468) (meaning t m 6123) source

theorem rule13975 (p1988 p2027 p2608 p2699 p2707 p2761 p3434 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2707) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p1988) ∨ (¬ p3434)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2761) ∨ (¬ p3434) := by
  classical
  tauto

theorem initial13975 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) := by
  have source := ElevenTheory.theory3647 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 7 9) (m.theta 9 10)
  exact rule13975 (meaning t m 1988) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 2761) (meaning t m 3434) source

theorem rule13976 (p1992 p2027 p2766 p3266 p3322 p3688 p4191 p4358 : Prop) (h : (¬ p3322) ∨ (¬ p3688) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4358) ∨ (¬ p3266) ∨ p2766) : (¬ p1992) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3688) ∨ (¬ p4191) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial13976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory3648 t (m.theta 1 2) (m.theta 2 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule13976 (meaning t m 1992) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3322) (meaning t m 3688) (meaning t m 4191) (meaning t m 4358) source

theorem rule13981 (p1992 p2027 p2387 p2764 p2785 p3688 p4347 p4444 : Prop) (h : (¬ p3688) ∨ (¬ p1992) ∨ (¬ p2785) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p2387) ∨ p2027 ∨ p2764) : (¬ p1992) ∨ (p2027) ∨ (¬ p2387) ∨ (p2764) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial13981 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory3653 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule13981 (meaning t m 1992) (meaning t m 2027) (meaning t m 2387) (meaning t m 2764) (meaning t m 2785) (meaning t m 3688) (meaning t m 4347) (meaning t m 4444) source

theorem rule13983 (p1976 p2027 p2764 p2780 p4347 p4358 p4444 : Prop) (h : p2764 ∨ (¬ p1976) ∨ (¬ p4444) ∨ (¬ p4347) ∨ (¬ p2780) ∨ (¬ p4358) ∨ p2027) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p2780) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial13983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory3655 t (m.theta 0 2) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule13983 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 2780) (meaning t m 4347) (meaning t m 4358) (meaning t m 4444) source

theorem rule13984 (p1990 p2027 p2192 p2323 p2901 p2946 p3486 : Prop) (h : (¬ p2192) ∨ (¬ p1990) ∨ (¬ p2901) ∨ (¬ p3486) ∨ p2027 ∨ p2323 ∨ (¬ p2946)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2192) ∨ (p2323) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial13984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory3656 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule13984 (meaning t m 1990) (meaning t m 2027) (meaning t m 2192) (meaning t m 2323) (meaning t m 2901) (meaning t m 2946) (meaning t m 3486) source

theorem rule13985 (p1983 p2027 p2241 p2699 p2901 p2992 p3246 : Prop) (h : p2699 ∨ (¬ p3246) ∨ (¬ p2241) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2901)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial13985 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory3657 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9)
  exact rule13985 (meaning t m 1983) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2901) (meaning t m 2992) (meaning t m 3246) source

theorem rule13986 (p1988 p2027 p2241 p2699 p3189 p3256 p3266 : Prop) (h : (¬ p1988) ∨ p2699 ∨ p2027 ∨ (¬ p3189) ∨ (¬ p2241) ∨ (¬ p3256) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial13986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory3658 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule13986 (meaning t m 1988) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3189) (meaning t m 3256) (meaning t m 3266) source

theorem rule13987 (p1988 p2027 p2241 p2641 p2699 p3323 p3461 : Prop) (h : (¬ p1988) ∨ (¬ p2641) ∨ p2699 ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3323) ∨ (¬ p3461)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (p2699) ∨ (¬ p3323) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial13987 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory3659 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule13987 (meaning t m 1988) (meaning t m 2027) (meaning t m 2241) (meaning t m 2641) (meaning t m 2699) (meaning t m 3323) (meaning t m 3461) source

theorem rule13991 (p1992 p2027 p2462 p2696 p2743 p3425 p4324 : Prop) (h : p2462 ∨ p2027 ∨ (¬ p3425) ∨ (¬ p4324) ∨ (¬ p2696) ∨ (¬ p1992) ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial13991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory3663 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 9)
  exact rule13991 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2696) (meaning t m 2743) (meaning t m 3425) (meaning t m 4324) source

theorem rule13993 (p1975 p2027 p2274 p2323 p2641 p2946 p3662 p3986 : Prop) (h : (¬ p3662) ∨ (¬ p1975) ∨ (¬ p3986) ∨ (¬ p2274) ∨ (¬ p2946) ∨ p2027 ∨ p2323 ∨ (¬ p2641)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2323) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial13993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory3665 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule13993 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2323) (meaning t m 2641) (meaning t m 2946) (meaning t m 3662) (meaning t m 3986) source

theorem rule13994 (p2010 p2027 p2437 p2608 p2630 p2699 p2737 : Prop) (h : (¬ p2608) ∨ (¬ p2010) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2737) ∨ p2699) : (¬ p2010) ∨ (p2027) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p2737) := by
  classical
  tauto

theorem initial13994 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) := by
  have source := ElevenTheory.theory3666 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7)
  exact rule13994 (meaning t m 2010) (meaning t m 2027) (meaning t m 2437) (meaning t m 2608) (meaning t m 2630) (meaning t m 2699) (meaning t m 2737) source

theorem rule13997 (p2005 p2027 p2230 p2233 p2493 p2982 p4202 p4363 : Prop) (h : p2027 ∨ (¬ p2493) ∨ (¬ p4363) ∨ p2233 ∨ (¬ p4202) ∨ (¬ p2005) ∨ (¬ p2982) ∨ (¬ p2230)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2493) ∨ (¬ p2982) ∨ (¬ p4202) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial13997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory3669 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule13997 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2493) (meaning t m 2982) (meaning t m 4202) (meaning t m 4363) source

theorem rule13998 (p1988 p2027 p2241 p2699 p2992 p3115 p3680 : Prop) (h : (¬ p1988) ∨ (¬ p3680) ∨ (¬ p2992) ∨ (¬ p2241) ∨ p2699 ∨ p2027 ∨ (¬ p3115)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial13998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory3670 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule13998 (meaning t m 1988) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2992) (meaning t m 3115) (meaning t m 3680) source

theorem rule13999 (p1992 p2027 p2462 p2774 p3425 p3688 p4107 p4471 : Prop) (h : p2462 ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p3688) ∨ (¬ p2774) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4107)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3688) ∨ (¬ p4107) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial13999 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory3671 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule13999 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2774) (meaning t m 3425) (meaning t m 3688) (meaning t m 4107) (meaning t m 4471) source

theorem rule14001 (p1994 p2027 p2440 p2765 p3051 p3646 p4235 : Prop) (h : (¬ p4235) ∨ p2765 ∨ p2027 ∨ (¬ p2440) ∨ (¬ p1994) ∨ (¬ p3646) ∨ (¬ p3051)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2765) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3673 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14001 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2765) (meaning t m 3051) (meaning t m 3646) (meaning t m 4235) source

theorem rule14002 (p1997 p2027 p2608 p2699 p2839 p2870 p4235 : Prop) (h : (¬ p2608) ∨ p2027 ∨ (¬ p2839) ∨ p2699 ∨ (¬ p1997) ∨ (¬ p4235) ∨ (¬ p2870)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3674 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule14002 (meaning t m 1997) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2870) (meaning t m 4235) source

theorem rule14003 (p2004 p2027 p2241 p2449 p2699 p3027 p3817 : Prop) (h : (¬ p2004) ∨ p2027 ∨ p2699 ∨ (¬ p3027) ∨ (¬ p3817) ∨ (¬ p2449) ∨ (¬ p2241)) : (¬ p2004) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial14003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory3675 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 9)
  exact rule14003 (meaning t m 2004) (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2699) (meaning t m 3027) (meaning t m 3817) source

theorem rule14004 (p3773 p4374 p5413 p5414 : Prop) (h : (¬ p4374) ∨ (¬ p5413) ∨ (¬ p3773) ∨ (¬ p5414)) : (¬ p3773) ∨ (¬ p4374) ∨ (¬ p5413) ∨ (¬ p5414) := by
  classical
  tauto

theorem initial14004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 4374)) ∨ (¬ (meaning t m 5413)) ∨ (¬ (meaning t m 5414)) := by
  have source := ElevenTheory.theory3676 (m.theta 0 9) (m.theta 1 10) (m.theta 1 9) (m.theta 9 10)
  exact rule14004 (meaning t m 3773) (meaning t m 4374) (meaning t m 5413) (meaning t m 5414) source

theorem rule14006 (p3834 p5486 p5487 p5488 p5489 : Prop) : (p5486) ∨ (((¬ p5488) ∨ (¬ p5486) ∨ (¬ p5487) ∨ (¬ p3834) ∨ (¬ p5489))) := by
  classical
  tauto

theorem initial14006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5486) ∨ (meaning t m 6127) := by
  exact rule14006 (meaning t m 3834) (meaning t m 5486) (meaning t m 5487) (meaning t m 5488) (meaning t m 5489)

theorem rule14007 (p3834 p5486 p5487 p5488 p5489 : Prop) : (p5487) ∨ (((¬ p5488) ∨ (¬ p5486) ∨ (¬ p5487) ∨ (¬ p3834) ∨ (¬ p5489))) := by
  classical
  tauto

theorem initial14007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5487) ∨ (meaning t m 6127) := by
  exact rule14007 (meaning t m 3834) (meaning t m 5486) (meaning t m 5487) (meaning t m 5488) (meaning t m 5489)

theorem rule14008 (p3834 p5486 p5487 p5488 p5489 : Prop) : (p3834) ∨ (((¬ p5488) ∨ (¬ p5486) ∨ (¬ p5487) ∨ (¬ p3834) ∨ (¬ p5489))) := by
  classical
  tauto

theorem initial14008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3834) ∨ (meaning t m 6127) := by
  exact rule14008 (meaning t m 3834) (meaning t m 5486) (meaning t m 5487) (meaning t m 5488) (meaning t m 5489)

theorem rule14012 (p3830 p4374 p4439 p5491 p5492 : Prop) : (p3830) ∨ (((¬ p5491) ∨ (¬ p3830) ∨ (¬ p4374) ∨ (¬ p4439) ∨ (¬ p5492))) := by
  classical
  tauto

theorem initial14012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3830) ∨ (meaning t m 6128) := by
  exact rule14012 (meaning t m 3830) (meaning t m 4374) (meaning t m 4439) (meaning t m 5491) (meaning t m 5492)

theorem rule14013 (p3830 p4374 p4439 p5491 p5492 : Prop) : (p4374) ∨ (((¬ p5491) ∨ (¬ p3830) ∨ (¬ p4374) ∨ (¬ p4439) ∨ (¬ p5492))) := by
  classical
  tauto

theorem initial14013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4374) ∨ (meaning t m 6128) := by
  exact rule14013 (meaning t m 3830) (meaning t m 4374) (meaning t m 4439) (meaning t m 5491) (meaning t m 5492)

theorem rule14014 (p3830 p4374 p4439 p5491 p5492 : Prop) : (p4439) ∨ (((¬ p5491) ∨ (¬ p3830) ∨ (¬ p4374) ∨ (¬ p4439) ∨ (¬ p5492))) := by
  classical
  tauto

theorem initial14014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4439) ∨ (meaning t m 6128) := by
  exact rule14014 (meaning t m 3830) (meaning t m 4374) (meaning t m 4439) (meaning t m 5491) (meaning t m 5492)

theorem rule14019 (p6127 p6128 : Prop) : (¬ ((¬ p6127) ∨ (¬ p6128))) ∨ (¬ p6127) ∨ (¬ p6128) := by
  classical
  tauto

theorem initial14019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6126)) ∨ (¬ (meaning t m 6127)) ∨ (¬ (meaning t m 6128)) := by
  exact rule14019 (meaning t m 6127) (meaning t m 6128)

theorem rule14020 (p5484 p6126 : Prop) (h : (p5484 ↔ p6126)) : (¬ p5484) ∨ (p6126) := by
  classical
  tauto

theorem initial14020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5484)) ∨ (meaning t m 6126) := by
  have source := ElevenTheory.theory3677 t (m.theta 0 1) (m.theta 0 9) (m.theta 1 9)
  exact rule14020 (meaning t m 5484) (meaning t m 6126) source

theorem rule14022 (p1994 p2027 p2630 p2688 p3506 p3842 p5387 p5453 : Prop) (h : (¬ p2630) ∨ (¬ p3842) ∨ p2027 ∨ (¬ p3506) ∨ p2688 ∨ (¬ p5387) ∨ (¬ p5453) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2688) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p5387) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial14022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory3678 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 9) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule14022 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2688) (meaning t m 3506) (meaning t m 3842) (meaning t m 5387) (meaning t m 5453) source

theorem rule14023 (p1991 p2027 p2440 p2657 p2997 p3097 p4110 : Prop) (h : p2997 ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p1991) ∨ (¬ p2657) ∨ (¬ p2440) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3679 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14023 (meaning t m 1991) (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2997) (meaning t m 3097) (meaning t m 4110) source

theorem rule14024 (p2002 p2027 p2914 p3016 p3564 p3742 p3917 : Prop) (h : (¬ p3016) ∨ p2027 ∨ p2914 ∨ (¬ p3564) ∨ (¬ p3742) ∨ (¬ p2002) ∨ (¬ p3917)) : (¬ p2002) ∨ (p2027) ∨ (p2914) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3742) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial14024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory3680 t (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule14024 (meaning t m 2002) (meaning t m 2027) (meaning t m 2914) (meaning t m 3016) (meaning t m 3564) (meaning t m 3742) (meaning t m 3917) source

theorem rule14028 (p1988 p2027 p2122 p2177 p2459 p3266 p3586 : Prop) (h : (¬ p1988) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2122) ∨ (¬ p2177) ∨ p3586) : (¬ p1988) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (p3586) := by
  classical
  tauto

theorem initial14028 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3266)) ∨ (meaning t m 3586) := by
  have source := ElevenTheory.theory3684 t (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14028 (meaning t m 1988) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2459) (meaning t m 3266) (meaning t m 3586) source

theorem rule14029 (p1997 p2027 p2542 p2938 p3246 p3742 p4278 : Prop) (h : (¬ p3246) ∨ p2938 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p1997) ∨ (¬ p3742)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory3685 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14029 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2938) (meaning t m 3246) (meaning t m 3742) (meaning t m 4278) source

theorem rule14030 (p3227 p3707 p5126 p5127 : Prop) (h : (¬ p3707) ∨ (¬ p5126) ∨ (¬ p5127) ∨ (¬ p3227)) : (¬ p3227) ∨ (¬ p3707) ∨ (¬ p5126) ∨ (¬ p5127) := by
  classical
  tauto

theorem initial14030 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 5126)) ∨ (¬ (meaning t m 5127)) := by
  have source := ElevenTheory.theory3686 (m.theta 1 9) (m.theta 4 10) (m.theta 4 9) (m.theta 9 10)
  exact rule14030 (meaning t m 3227) (meaning t m 3707) (meaning t m 5126) (meaning t m 5127) source

theorem rule14032 (p5501 p5502 p5503 p5504 p5505 : Prop) : (p5502) ∨ (((¬ p5502) ∨ (¬ p5503) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))) := by
  classical
  tauto

theorem initial14032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5502) ∨ (meaning t m 6130) := by
  exact rule14032 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule14033 (p5501 p5502 p5503 p5504 p5505 : Prop) : (p5503) ∨ (((¬ p5502) ∨ (¬ p5503) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))) := by
  classical
  tauto

theorem initial14033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5503) ∨ (meaning t m 6130) := by
  exact rule14033 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule14034 (p5501 p5502 p5503 p5504 p5505 : Prop) : (p5501) ∨ (((¬ p5502) ∨ (¬ p5503) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))) := by
  classical
  tauto

theorem initial14034 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5501) ∨ (meaning t m 6130) := by
  exact rule14034 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule14035 (p5501 p5502 p5503 p5504 p5505 : Prop) : (p5504) ∨ (((¬ p5502) ∨ (¬ p5503) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))) := by
  classical
  tauto

theorem initial14035 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5504) ∨ (meaning t m 6130) := by
  exact rule14035 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule14036 (p5501 p5502 p5503 p5504 p5505 : Prop) : (p5505) ∨ (((¬ p5502) ∨ (¬ p5503) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))) := by
  classical
  tauto

theorem initial14036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5505) ∨ (meaning t m 6130) := by
  exact rule14036 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule14037 (p5501 p5502 p5503 p5504 p5505 : Prop) : (¬ p5501) ∨ (¬ p5502) ∨ (¬ p5503) ∨ (¬ p5504) ∨ (¬ p5505) ∨ (¬ ((¬ p5502) ∨ (¬ p5503) ∨ (¬ p5501) ∨ (¬ p5504) ∨ (¬ p5505))) := by
  classical
  tauto

theorem initial14037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5501)) ∨ (¬ (meaning t m 5502)) ∨ (¬ (meaning t m 5503)) ∨ (¬ (meaning t m 5504)) ∨ (¬ (meaning t m 5505)) ∨ (¬ (meaning t m 6130)) := by
  exact rule14037 (meaning t m 5501) (meaning t m 5502) (meaning t m 5503) (meaning t m 5504) (meaning t m 5505)

theorem rule14038 (p3868 p5507 p5508 p5509 p5510 : Prop) : (p5507) ∨ (((¬ p5507) ∨ (¬ p5508) ∨ (¬ p3868) ∨ (¬ p5509) ∨ (¬ p5510))) := by
  classical
  tauto

theorem initial14038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5507) ∨ (meaning t m 6131) := by
  exact rule14038 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule14039 (p3868 p5507 p5508 p5509 p5510 : Prop) : (p5508) ∨ (((¬ p5507) ∨ (¬ p5508) ∨ (¬ p3868) ∨ (¬ p5509) ∨ (¬ p5510))) := by
  classical
  tauto

theorem initial14039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5508) ∨ (meaning t m 6131) := by
  exact rule14039 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule14040 (p3868 p5507 p5508 p5509 p5510 : Prop) : (p3868) ∨ (((¬ p5507) ∨ (¬ p5508) ∨ (¬ p3868) ∨ (¬ p5509) ∨ (¬ p5510))) := by
  classical
  tauto

theorem initial14040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3868) ∨ (meaning t m 6131) := by
  exact rule14040 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule14041 (p3868 p5507 p5508 p5509 p5510 : Prop) : (p5509) ∨ (((¬ p5507) ∨ (¬ p5508) ∨ (¬ p3868) ∨ (¬ p5509) ∨ (¬ p5510))) := by
  classical
  tauto

theorem initial14041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5509) ∨ (meaning t m 6131) := by
  exact rule14041 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule14042 (p3868 p5507 p5508 p5509 p5510 : Prop) : (p5510) ∨ (((¬ p5507) ∨ (¬ p5508) ∨ (¬ p3868) ∨ (¬ p5509) ∨ (¬ p5510))) := by
  classical
  tauto

theorem initial14042 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5510) ∨ (meaning t m 6131) := by
  exact rule14042 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule14043 (p3868 p5507 p5508 p5509 p5510 : Prop) : (¬ p3868) ∨ (¬ p5507) ∨ (¬ p5508) ∨ (¬ p5509) ∨ (¬ p5510) ∨ (¬ ((¬ p5507) ∨ (¬ p5508) ∨ (¬ p3868) ∨ (¬ p5509) ∨ (¬ p5510))) := by
  classical
  tauto

theorem initial14043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 5507)) ∨ (¬ (meaning t m 5508)) ∨ (¬ (meaning t m 5509)) ∨ (¬ (meaning t m 5510)) ∨ (¬ (meaning t m 6131)) := by
  exact rule14043 (meaning t m 3868) (meaning t m 5507) (meaning t m 5508) (meaning t m 5509) (meaning t m 5510)

theorem rule14046 (p6130 p6131 : Prop) : (¬ ((¬ p6130) ∨ (¬ p6131))) ∨ (¬ p6130) ∨ (¬ p6131) := by
  classical
  tauto

theorem initial14046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6129)) ∨ (¬ (meaning t m 6130)) ∨ (¬ (meaning t m 6131)) := by
  exact rule14046 (meaning t m 6130) (meaning t m 6131)

theorem rule14047 (p5499 p6129 : Prop) (h : (p5499 ↔ p6129)) : (¬ p5499) ∨ (p6129) := by
  classical
  tauto

theorem initial14047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5499)) ∨ (meaning t m 6129) := by
  have source := ElevenTheory.theory3688 t (m.theta 4 10) (m.theta 4 7) (m.theta 7 10)
  exact rule14047 (meaning t m 5499) (meaning t m 6129) source

theorem rule14049 (p2017 p2027 p2230 p2233 p2922 p3238 p3868 : Prop) (h : p2233 ∨ (¬ p2017) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3868) ∨ (¬ p2922)) : (¬ p2017) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3868) := by
  classical
  tauto

theorem initial14049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3868)) := by
  have source := ElevenTheory.theory3689 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 10)
  exact rule14049 (meaning t m 2017) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2922) (meaning t m 3238) (meaning t m 3868) source

theorem rule14051 (p1994 p2027 p2241 p2630 p2699 p3189 p3877 : Prop) (h : (¬ p1994) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p2630) ∨ (¬ p3877) ∨ p2027 ∨ p2699) : (¬ p1994) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p3189) ∨ (¬ p3877) := by
  classical
  tauto

theorem initial14051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3877)) := by
  have source := ElevenTheory.theory3691 t (m.theta 0 1) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8)
  exact rule14051 (meaning t m 1994) (meaning t m 2027) (meaning t m 2241) (meaning t m 2630) (meaning t m 2699) (meaning t m 3189) (meaning t m 3877) source

theorem rule14052 (p1982 p2027 p2611 p2696 p2743 p3537 p3609 : Prop) (h : (¬ p1982) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3609) ∨ p2027 ∨ (¬ p3537)) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3609) := by
  classical
  tauto

theorem initial14052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) := by
  have source := ElevenTheory.theory3692 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 8 9)
  exact rule14052 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2743) (meaning t m 3537) (meaning t m 3609) source

theorem rule14054 (p1982 p2027 p2611 p2774 p3537 p3609 p3688 : Prop) (h : (¬ p3609) ∨ (¬ p1982) ∨ p2611 ∨ p2027 ∨ (¬ p3537) ∨ (¬ p3688) ∨ (¬ p2774)) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial14054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory3694 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 8 9)
  exact rule14054 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2774) (meaning t m 3537) (meaning t m 3609) (meaning t m 3688) source

theorem rule14055 (p1975 p2027 p2295 p2608 p2699 p2737 p2797 : Prop) (h : (¬ p1975) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p2608) ∨ p2699) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p2797) := by
  classical
  tauto

theorem initial14055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) := by
  have source := ElevenTheory.theory3695 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7)
  exact rule14055 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2608) (meaning t m 2699) (meaning t m 2737) (meaning t m 2797) source

theorem rule14056 (p2008 p2027 p2341 p3360 p3548 p3631 p4324 : Prop) (h : p3360 ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p4324) ∨ (¬ p2008)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2341) ∨ (p3360) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial14056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory3696 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14056 (meaning t m 2008) (meaning t m 2027) (meaning t m 2341) (meaning t m 3360) (meaning t m 3548) (meaning t m 3631) (meaning t m 4324) source

theorem rule14057 (p1975 p2027 p2608 p2699 p2707 p3434 p4107 : Prop) (h : (¬ p2707) ∨ (¬ p3434) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4107) ∨ p2699 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial14057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory3697 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule14057 (meaning t m 1975) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 3434) (meaning t m 4107) source

end SunPrize.SMT
