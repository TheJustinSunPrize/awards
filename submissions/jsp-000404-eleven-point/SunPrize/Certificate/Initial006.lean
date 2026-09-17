import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory002
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule5948 (p1718 p1724 : Prop) : (¬ p1718) ∨ ((p1718 ∨ p1724)) := by
  classical
  tauto

theorem initial5948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1718)) ∨ (meaning t m 4002) := by
  exact rule5948 (meaning t m 1718) (meaning t m 1724)

theorem rule5949 (p1718 p1724 : Prop) : (¬ p1724) ∨ ((p1718 ∨ p1724)) := by
  classical
  tauto

theorem initial5949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1724)) ∨ (meaning t m 4002) := by
  exact rule5949 (meaning t m 1718) (meaning t m 1724)

theorem rule5966 (p4002 p4003 : Prop) (h : (p4002 ↔ p4003)) : (¬ p4002) ∨ (p4003) := by
  classical
  tauto

theorem initial5966 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4002)) ∨ (meaning t m 4003) := by
  have source := ElevenTheory.theory450 t (m.theta 3 10) (m.theta 3 8) (m.theta 8 10)
  exact rule5966 (meaning t m 4002) (meaning t m 4003) source

theorem rule5968 (p1730 p1736 : Prop) : (¬ p1730) ∨ ((p1730 ∨ p1736)) := by
  classical
  tauto

theorem initial5968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1730)) ∨ (meaning t m 4012) := by
  exact rule5968 (meaning t m 1730) (meaning t m 1736)

theorem rule5969 (p1730 p1736 : Prop) : (¬ p1736) ∨ ((p1730 ∨ p1736)) := by
  classical
  tauto

theorem initial5969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1736)) ∨ (meaning t m 4012) := by
  exact rule5969 (meaning t m 1730) (meaning t m 1736)

theorem rule5986 (p4012 p4013 : Prop) (h : (p4012 ↔ p4013)) : (¬ p4012) ∨ (p4013) := by
  classical
  tauto

theorem initial5986 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4012)) ∨ (meaning t m 4013) := by
  have source := ElevenTheory.theory451 t (m.theta 2 10) (m.theta 2 8) (m.theta 8 10)
  exact rule5986 (meaning t m 4012) (meaning t m 4013) source

theorem rule5990 (p2352 p3746 p3990 p4022 : Prop) (h : (¬ p3746) ∨ (¬ p4022) ∨ (¬ p2352) ∨ (¬ p3990)) : (¬ p2352) ∨ (¬ p3746) ∨ (¬ p3990) ∨ (¬ p4022) := by
  classical
  tauto

theorem initial5990 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3746)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4022)) := by
  have source := ElevenTheory.theory454 (m.theta 4 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9)
  exact rule5990 (meaning t m 2352) (meaning t m 3746) (meaning t m 3990) (meaning t m 4022) source

theorem rule5991 (p2074 p4023 : Prop) (h : ((¬ p2074) ↔ (¬ p4023))) : (p2074) ∨ (¬ p4023) := by
  classical
  tauto

theorem initial5991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2074) ∨ (¬ (meaning t m 4023)) := by
  have source := ElevenTheory.theory455 t (m.theta 1 9)
  exact rule5991 (meaning t m 2074) (meaning t m 4023) source

theorem rule5993 (p3549 p3822 p4024 : Prop) (h : (¬ p4024) ∨ (¬ p3549) ∨ p3822) : (¬ p3549) ∨ (p3822) ∨ (¬ p4024) := by
  classical
  tauto

theorem initial5993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3549)) ∨ (meaning t m 3822) ∨ (¬ (meaning t m 4024)) := by
  have source := ElevenTheory.theory456 (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule5993 (meaning t m 3549) (meaning t m 3822) (meaning t m 4024) source

theorem rule5995 (p3549 p4025 p4026 : Prop) (h : (¬ p3549) ∨ (¬ p4025) ∨ p4026) : (¬ p3549) ∨ (¬ p4025) ∨ (p4026) := by
  classical
  tauto

theorem initial5995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4025)) ∨ (meaning t m 4026) := by
  have source := ElevenTheory.theory458 (m.theta 1 6) (m.theta 6 7) (m.theta 6 9)
  exact rule5995 (meaning t m 3549) (meaning t m 4025) (meaning t m 4026) source

theorem rule5996 (p3707 p4027 p4028 p4029 : Prop) (h : (¬ p4027) ∨ (¬ p4028) ∨ (¬ p3707) ∨ (¬ p4029)) : (¬ p3707) ∨ (¬ p4027) ∨ (¬ p4028) ∨ (¬ p4029) := by
  classical
  tauto

theorem initial5996 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4027)) ∨ (¬ (meaning t m 4028)) ∨ (¬ (meaning t m 4029)) := by
  have source := ElevenTheory.theory459 (m.theta 1 9) (m.theta 2 10) (m.theta 2 9) (m.theta 9 10)
  exact rule5996 (meaning t m 3707) (meaning t m 4027) (meaning t m 4028) (meaning t m 4029) source

theorem rule5998 (p2284 p3646 p3879 p4031 : Prop) (h : (¬ p4031) ∨ (¬ p2284) ∨ (¬ p3879) ∨ (¬ p3646)) : (¬ p2284) ∨ (¬ p3646) ∨ (¬ p3879) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial5998 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory461 (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule5998 (meaning t m 2284) (meaning t m 3646) (meaning t m 3879) (meaning t m 4031) source

theorem rule6002 (p2191 p3880 p4034 : Prop) (h : (¬ p4034) ∨ (¬ p3880) ∨ p2191) : (p2191) ∨ (¬ p3880) ∨ (¬ p4034) := by
  classical
  tauto

theorem initial6002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2191) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4034)) := by
  have source := ElevenTheory.theory465 (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule6002 (meaning t m 2191) (meaning t m 3880) (meaning t m 4034) source

theorem rule6003 (p2811 p3286 p4035 : Prop) (h : (¬ p2811) ∨ (¬ p4035) ∨ (¬ p3286)) : (¬ p2811) ∨ (¬ p3286) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial6003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory466 (m.theta 0 3) (m.theta 2 3) (m.theta 3 9)
  exact rule6003 (meaning t m 2811) (meaning t m 3286) (meaning t m 4035) source

theorem rule6004 (p2187 p3324 p3986 : Prop) (h : (¬ p3324) ∨ (¬ p3986) ∨ (¬ p2187)) : (¬ p2187) ∨ (¬ p3324) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial6004 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory467 (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule6004 (meaning t m 2187) (meaning t m 3324) (meaning t m 3986) source

theorem rule6005 (p3567 p4036 p4037 p4038 : Prop) (h : (¬ p3567) ∨ (¬ p4036) ∨ (¬ p4037) ∨ (¬ p4038)) : (¬ p3567) ∨ (¬ p4036) ∨ (¬ p4037) ∨ (¬ p4038) := by
  classical
  tauto

theorem initial6005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4036)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4038)) := by
  have source := ElevenTheory.theory468 (m.theta 0 6) (m.theta 0 9) (m.theta 3 6) (m.theta 6 9)
  exact rule6005 (meaning t m 3567) (meaning t m 4036) (meaning t m 4037) (meaning t m 4038) source

theorem rule6006 (p2951 p2957 : Prop) (h : p2951 ∨ p2957) : (p2951) ∨ (p2957) := by
  classical
  tauto

theorem initial6006 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2951) ∨ (meaning t m 2957) := by
  have source := ElevenTheory.theory469 (m.theta 0 5) (m.theta 3 5)
  exact rule6006 (meaning t m 2951) (meaning t m 2957) source

theorem rule6008 (p4041 p4042 p4043 : Prop) (h : (¬ p4041) ∨ (¬ p4042) ∨ p4043) : (¬ p4041) ∨ (¬ p4042) ∨ (p4043) := by
  classical
  tauto

theorem initial6008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4042)) ∨ (meaning t m 4043) := by
  have source := ElevenTheory.theory471 t (m.theta 3 8) (m.theta 5 8) (m.theta 7 8)
  exact rule6008 (meaning t m 4041) (meaning t m 4042) (meaning t m 4043) source

theorem rule6009 (p2807 p2811 p3877 p4044 : Prop) (h : (¬ p3877) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p4044)) : (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3877) ∨ (¬ p4044) := by
  classical
  tauto

theorem initial6009 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4044)) := by
  have source := ElevenTheory.theory472 (m.theta 0 3) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8)
  exact rule6009 (meaning t m 2807) (meaning t m 2811) (meaning t m 3877) (meaning t m 4044) source

theorem rule6010 (p2509 p3193 p4045 : Prop) (h : (¬ p4045) ∨ (¬ p2509) ∨ p3193) : (¬ p2509) ∨ (p3193) ∨ (¬ p4045) := by
  classical
  tauto

theorem initial6010 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (meaning t m 3193) ∨ (¬ (meaning t m 4045)) := by
  have source := ElevenTheory.theory473 (m.theta 1 4) (m.theta 4 8) (m.theta 4 9)
  exact rule6010 (meaning t m 2509) (meaning t m 3193) (meaning t m 4045) source

theorem rule6011 (p1742 p1748 : Prop) : (¬ p1742) ∨ ((p1742 ∨ p1748)) := by
  classical
  tauto

theorem initial6011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1742)) ∨ (meaning t m 4046) := by
  exact rule6011 (meaning t m 1742) (meaning t m 1748)

theorem rule6012 (p1742 p1748 : Prop) : (¬ p1748) ∨ ((p1742 ∨ p1748)) := by
  classical
  tauto

theorem initial6012 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1748)) ∨ (meaning t m 4046) := by
  exact rule6012 (meaning t m 1742) (meaning t m 1748)

theorem rule6029 (p4046 p4047 : Prop) (h : (p4046 ↔ p4047)) : (¬ p4046) ∨ (p4047) := by
  classical
  tauto

theorem initial6029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4046)) ∨ (meaning t m 4047) := by
  have source := ElevenTheory.theory474 t (m.theta 1 10) (m.theta 1 6) (m.theta 6 10)
  exact rule6029 (meaning t m 4046) (meaning t m 4047) source

theorem rule6031 (p1754 p1760 : Prop) : (¬ p1754) ∨ ((p1754 ∨ p1760)) := by
  classical
  tauto

theorem initial6031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1754)) ∨ (meaning t m 4056) := by
  exact rule6031 (meaning t m 1754) (meaning t m 1760)

theorem rule6032 (p1754 p1760 : Prop) : (¬ p1760) ∨ ((p1754 ∨ p1760)) := by
  classical
  tauto

theorem initial6032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1760)) ∨ (meaning t m 4056) := by
  exact rule6032 (meaning t m 1754) (meaning t m 1760)

theorem rule6049 (p4056 p4057 : Prop) (h : (p4056 ↔ p4057)) : (¬ p4056) ∨ (p4057) := by
  classical
  tauto

theorem initial6049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4056)) ∨ (meaning t m 4057) := by
  have source := ElevenTheory.theory475 t (m.theta 0 10) (m.theta 0 7) (m.theta 7 10)
  exact rule6049 (meaning t m 4056) (meaning t m 4057) source

theorem rule6051 (p3516 p3947 p4066 : Prop) (h : (¬ p3516) ∨ (¬ p4066) ∨ (¬ p3947)) : (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial6051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory476 (m.theta 0 7) (m.theta 3 7) (m.theta 7 9)
  exact rule6051 (meaning t m 3516) (meaning t m 3947) (meaning t m 4066) source

theorem rule6052 (p2807 p2963 p4067 : Prop) (h : (¬ p4067) ∨ (¬ p2807) ∨ (¬ p2963)) : (¬ p2807) ∨ (¬ p2963) ∨ (¬ p4067) := by
  classical
  tauto

theorem initial6052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4067)) := by
  have source := ElevenTheory.theory477 (m.theta 0 3) (m.theta 3 6) (m.theta 3 7)
  exact rule6052 (meaning t m 2807) (meaning t m 2963) (meaning t m 4067) source

theorem rule6053 (p1766 p1772 : Prop) : (¬ p1766) ∨ ((p1766 ∨ p1772)) := by
  classical
  tauto

theorem initial6053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1766)) ∨ (meaning t m 4068) := by
  exact rule6053 (meaning t m 1766) (meaning t m 1772)

theorem rule6054 (p1766 p1772 : Prop) : (¬ p1772) ∨ ((p1766 ∨ p1772)) := by
  classical
  tauto

theorem initial6054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1772)) ∨ (meaning t m 4068) := by
  exact rule6054 (meaning t m 1766) (meaning t m 1772)

theorem rule6071 (p4068 p4069 : Prop) (h : (p4068 ↔ p4069)) : (¬ p4068) ∨ (p4069) := by
  classical
  tauto

theorem initial6071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4068)) ∨ (meaning t m 4069) := by
  have source := ElevenTheory.theory478 t (m.theta 1 10) (m.theta 1 7) (m.theta 7 10)
  exact rule6071 (meaning t m 4068) (meaning t m 4069) source

theorem rule6073 (p2104 p2780 p4078 : Prop) (h : (¬ p2780) ∨ (¬ p4078) ∨ p2104) : (p2104) ∨ (¬ p2780) ∨ (¬ p4078) := by
  classical
  tauto

theorem initial6073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2104) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4078)) := by
  have source := ElevenTheory.theory479 (m.theta 0 2) (m.theta 2 6) (m.theta 2 8)
  exact rule6073 (meaning t m 2104) (meaning t m 2780) (meaning t m 4078) source

theorem rule6074 (p2210 p2230 p4034 p4079 : Prop) (h : (¬ p2230) ∨ (¬ p4034) ∨ (¬ p4079) ∨ p2210) : (p2210) ∨ (¬ p2230) ∨ (¬ p4034) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial6074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2210) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory480 (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 5)
  exact rule6074 (meaning t m 2210) (meaning t m 2230) (meaning t m 4034) (meaning t m 4079) source

theorem rule6075 (p2470 p3389 p3875 : Prop) (h : (¬ p3389) ∨ (¬ p3875) ∨ p2470) : (p2470) ∨ (¬ p3389) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial6075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2470) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory481 (m.theta 0 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6075 (meaning t m 2470) (meaning t m 3389) (meaning t m 3875) source

theorem rule6076 (p2075 p4080 : Prop) (h : ((¬ p2075) ↔ (¬ p4080))) : (p2075) ∨ (¬ p4080) := by
  classical
  tauto

theorem initial6076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2075) ∨ (¬ (meaning t m 4080)) := by
  have source := ElevenTheory.theory482 t (m.theta 0 8)
  exact rule6076 (meaning t m 2075) (meaning t m 4080) source

theorem rule6078 (p1778 p1784 : Prop) : (¬ p1778) ∨ ((p1778 ∨ p1784)) := by
  classical
  tauto

theorem initial6078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1778)) ∨ (meaning t m 4081) := by
  exact rule6078 (meaning t m 1778) (meaning t m 1784)

theorem rule6079 (p1778 p1784 : Prop) : (¬ p1784) ∨ ((p1778 ∨ p1784)) := by
  classical
  tauto

theorem initial6079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1784)) ∨ (meaning t m 4081) := by
  exact rule6079 (meaning t m 1778) (meaning t m 1784)

theorem rule6096 (p4081 p4082 : Prop) (h : (p4081 ↔ p4082)) : (¬ p4081) ∨ (p4082) := by
  classical
  tauto

theorem initial6096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4081)) ∨ (meaning t m 4082) := by
  have source := ElevenTheory.theory483 t (m.theta 0 10) (m.theta 0 6) (m.theta 6 10)
  exact rule6096 (meaning t m 4081) (meaning t m 4082) source

theorem rule6100 (p4092 p4093 p4094 p4095 p4096 : Prop) : (¬ (p4092 ∧ p4093 ∧ p4094 ∧ p4095 ∧ p4096)) ∨ (p4094) := by
  classical
  tauto

theorem initial6100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4091)) ∨ (meaning t m 4094) := by
  exact rule6100 (meaning t m 4092) (meaning t m 4093) (meaning t m 4094) (meaning t m 4095) (meaning t m 4096)

theorem rule6114 (p4088 p4099 p4100 p4101 p4102 : Prop) : (p4088) ∨ (¬ (p4099 ∧ p4100 ∧ p4088 ∧ p4101 ∧ p4102)) := by
  classical
  tauto

theorem initial6114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4088) ∨ (¬ (meaning t m 4098)) := by
  exact rule6114 (meaning t m 4088) (meaning t m 4099) (meaning t m 4100) (meaning t m 4101) (meaning t m 4102)

theorem rule6127 (p3362 p3389 p3425 p4106 : Prop) (h : (¬ p3389) ∨ (¬ p3362) ∨ (¬ p3425) ∨ (¬ p4106)) : (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3425) ∨ (¬ p4106) := by
  classical
  tauto

theorem initial6127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4106)) := by
  have source := ElevenTheory.theory487 (m.theta 0 2) (m.theta 0 4) (m.theta 2 7) (m.theta 4 7)
  exact rule6127 (meaning t m 3362) (meaning t m 3389) (meaning t m 3425) (meaning t m 4106) source

theorem rule6128 (p3238 p3684 p4030 : Prop) (h : (¬ p3238) ∨ (¬ p4030) ∨ p3684) : (¬ p3238) ∨ (p3684) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial6128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3238)) ∨ (meaning t m 3684) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory488 (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule6128 (meaning t m 3238) (meaning t m 3684) (meaning t m 4030) source

theorem rule6129 (p2138 p2839 p3366 : Prop) (h : (¬ p2138) ∨ (¬ p3366) ∨ (¬ p2839)) : (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3366) := by
  classical
  tauto

theorem initial6129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3366)) := by
  have source := ElevenTheory.theory489 (m.theta 0 2) (m.theta 1 2) (m.theta 2 5)
  exact rule6129 (meaning t m 2138) (meaning t m 2839) (meaning t m 3366) source

theorem rule6130 (p2406 p2922 p3741 : Prop) (h : (¬ p3741) ∨ (¬ p2406) ∨ p2922) : (¬ p2406) ∨ (p2922) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial6130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2406)) ∨ (meaning t m 2922) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory490 (m.theta 1 4) (m.theta 4 5) (m.theta 4 7)
  exact rule6130 (meaning t m 2406) (meaning t m 2922) (meaning t m 3741) source

theorem rule6131 (p2743 p3475 p3585 : Prop) (h : (¬ p3585) ∨ (¬ p3475) ∨ p2743) : (p2743) ∨ (¬ p3475) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial6131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2743) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory491 (m.theta 1 2) (m.theta 2 3) (m.theta 2 4)
  exact rule6131 (meaning t m 2743) (meaning t m 3475) (meaning t m 3585) source

theorem rule6132 (p2497 p3093 p3452 : Prop) (h : (¬ p2497) ∨ (¬ p3452) ∨ (¬ p3093)) : (¬ p2497) ∨ (¬ p3093) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial6132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory492 (m.theta 0 1) (m.theta 1 4) (m.theta 1 6)
  exact rule6132 (meaning t m 2497) (meaning t m 3093) (meaning t m 3452) source

theorem rule6133 (p2742 p2748 : Prop) (h : p2742 ∨ p2748) : (p2742) ∨ (p2748) := by
  classical
  tauto

theorem initial6133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2742) ∨ (meaning t m 2748) := by
  have source := ElevenTheory.theory493 (m.theta 1 3) (m.theta 2 3)
  exact rule6133 (meaning t m 2742) (meaning t m 2748) source

theorem rule6134 (p2088 p3692 p3696 : Prop) (h : (¬ p3696) ∨ (¬ p2088) ∨ (¬ p3692)) : (¬ p2088) ∨ (¬ p3692) ∨ (¬ p3696) := by
  classical
  tauto

theorem initial6134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3696)) := by
  have source := ElevenTheory.theory494 (m.theta 0 8) (m.theta 5 8) (m.theta 8 9)
  exact rule6134 (meaning t m 2088) (meaning t m 3692) (meaning t m 3696) source

theorem rule6135 (p2299 p3657 p4107 : Prop) (h : (¬ p2299) ∨ (¬ p3657) ∨ p4107) : (¬ p2299) ∨ (¬ p3657) ∨ (p4107) := by
  classical
  tauto

theorem initial6135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3657)) ∨ (meaning t m 4107) := by
  have source := ElevenTheory.theory495 (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule6135 (meaning t m 2299) (meaning t m 3657) (meaning t m 4107) source

theorem rule6136 (p2210 p3370 p3904 p4108 : Prop) (h : (¬ p4108) ∨ (¬ p3904) ∨ (¬ p2210) ∨ (¬ p3370)) : (¬ p2210) ∨ (¬ p3370) ∨ (¬ p3904) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial6136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory496 (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 5)
  exact rule6136 (meaning t m 2210) (meaning t m 3370) (meaning t m 3904) (meaning t m 4108) source

theorem rule6137 (p2307 p2383 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p2307) ∨ p2383) : (¬ p2307) ∨ (p2383) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial6137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (meaning t m 2383) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory497 (m.theta 0 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6137 (meaning t m 2307) (meaning t m 2383) (meaning t m 3325) source

theorem rule6138 (p3646 p4109 p4110 : Prop) (h : (¬ p4109) ∨ (¬ p4110) ∨ p3646) : (p3646) ∨ (¬ p4109) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial6138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3646) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory498 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6138 (meaning t m 3646) (meaning t m 4109) (meaning t m 4110) source

theorem rule6139 (p2748 p2810 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p2748) ∨ p2810) : (¬ p2748) ∨ (p2810) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial6139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2748)) ∨ (meaning t m 2810) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory499 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule6139 (meaning t m 2748) (meaning t m 2810) (meaning t m 4111) source

theorem rule6141 (p2313 p3955 p4113 p4114 : Prop) (h : (¬ p4113) ∨ (¬ p2313) ∨ (¬ p4114) ∨ (¬ p3955)) : (¬ p2313) ∨ (¬ p3955) ∨ (¬ p4113) ∨ (¬ p4114) := by
  classical
  tauto

theorem initial6141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4114)) := by
  have source := ElevenTheory.theory501 (m.theta 0 6) (m.theta 0 8) (m.theta 6 7) (m.theta 6 8)
  exact rule6141 (meaning t m 2313) (meaning t m 3955) (meaning t m 4113) (meaning t m 4114) source

theorem rule6142 (p2318 p2396 p3821 : Prop) (h : (¬ p2318) ∨ (¬ p3821) ∨ (¬ p2396)) : (¬ p2318) ∨ (¬ p2396) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial6142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory502 (m.theta 0 7) (m.theta 6 7) (m.theta 7 9)
  exact rule6142 (meaning t m 2318) (meaning t m 2396) (meaning t m 3821) source

theorem rule6143 (p3692 p3857 p4115 : Prop) (h : (¬ p3857) ∨ (¬ p4115) ∨ p3692) : (p3692) ∨ (¬ p3857) ∨ (¬ p4115) := by
  classical
  tauto

theorem initial6143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3692) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4115)) := by
  have source := ElevenTheory.theory503 (m.theta 0 8) (m.theta 5 8) (m.theta 8 9)
  exact rule6143 (meaning t m 3692) (meaning t m 3857) (meaning t m 4115) source

theorem rule6144 (p2253 p2651 p3452 p4116 : Prop) (h : (¬ p4116) ∨ (¬ p2651) ∨ (¬ p2253) ∨ (¬ p3452)) : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p3452) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial6144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory504 (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 4)
  exact rule6144 (meaning t m 2253) (meaning t m 2651) (meaning t m 3452) (meaning t m 4116) source

theorem rule6146 (p2542 p2589 p2662 : Prop) (h : (¬ p2662) ∨ (¬ p2589) ∨ (¬ p2542)) : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2662) := by
  classical
  tauto

theorem initial6146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) := by
  have source := ElevenTheory.theory506 (m.theta 0 4) (m.theta 3 4) (m.theta 4 5)
  exact rule6146 (meaning t m 2542) (meaning t m 2589) (meaning t m 2662) source

theorem rule6147 (p2476 p3389 p3875 : Prop) (h : (¬ p2476) ∨ (¬ p3875) ∨ (¬ p3389)) : (¬ p2476) ∨ (¬ p3389) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial6147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory507 (m.theta 0 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6147 (meaning t m 2476) (meaning t m 3389) (meaning t m 3875) source

theorem rule6148 (p3177 p3857 p4118 : Prop) (h : (¬ p3857) ∨ (¬ p3177) ∨ p4118) : (¬ p3177) ∨ (¬ p3857) ∨ (p4118) := by
  classical
  tauto

theorem initial6148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3857)) ∨ (meaning t m 4118) := by
  have source := ElevenTheory.theory508 (m.theta 0 8) (m.theta 3 8) (m.theta 8 9)
  exact rule6148 (meaning t m 3177) (meaning t m 3857) (meaning t m 4118) source

theorem rule6149 (p3556 p4119 p4120 : Prop) (h : (¬ p4119) ∨ (¬ p3556) ∨ p4120) : (¬ p3556) ∨ (¬ p4119) ∨ (p4120) := by
  classical
  tauto

theorem initial6149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4119)) ∨ (meaning t m 4120) := by
  have source := ElevenTheory.theory509 (m.theta 0 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6149 (meaning t m 3556) (meaning t m 4119) (meaning t m 4120) source

theorem rule6150 (p2651 p3172 p4121 : Prop) (h : (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4121)) : (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4121) := by
  classical
  tauto

theorem initial6150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4121)) := by
  have source := ElevenTheory.theory510 (m.theta 0 3) (m.theta 3 4) (m.theta 3 8)
  exact rule6150 (meaning t m 2651) (meaning t m 3172) (meaning t m 4121) source

theorem rule6151 (p3222 p3359 p4116 : Prop) (h : (¬ p3359) ∨ (¬ p4116) ∨ (¬ p3222)) : (¬ p3222) ∨ (¬ p3359) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial6151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory511 (m.theta 1 4) (m.theta 3 4) (m.theta 4 9)
  exact rule6151 (meaning t m 3222) (meaning t m 3359) (meaning t m 4116) source

theorem rule6152 (p1790 p1796 : Prop) : (¬ p1790) ∨ ((p1790 ∨ p1796)) := by
  classical
  tauto

theorem initial6152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1790)) ∨ (meaning t m 4122) := by
  exact rule6152 (meaning t m 1790) (meaning t m 1796)

theorem rule6153 (p1790 p1796 : Prop) : (¬ p1796) ∨ ((p1790 ∨ p1796)) := by
  classical
  tauto

theorem initial6153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1796)) ∨ (meaning t m 4122) := by
  exact rule6153 (meaning t m 1790) (meaning t m 1796)

theorem rule6170 (p4122 p4123 : Prop) (h : (p4122 ↔ p4123)) : (¬ p4122) ∨ (p4123) := by
  classical
  tauto

theorem initial6170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4122)) ∨ (meaning t m 4123) := by
  have source := ElevenTheory.theory512 t (m.theta 5 10) (m.theta 5 7) (m.theta 7 10)
  exact rule6170 (meaning t m 4122) (meaning t m 4123) source

theorem rule6175 (p3644 p3920 p3990 p4137 p4138 : Prop) (h : (¬ p4137) ∨ (¬ p3990) ∨ (¬ p4138) ∨ (¬ p3920) ∨ p3644) : (p3644) ∨ (¬ p3920) ∨ (¬ p3990) ∨ (¬ p4137) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial6175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3644) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory516 (m.theta 4 6) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8)
  exact rule6175 (meaning t m 3644) (meaning t m 3920) (meaning t m 3990) (meaning t m 4137) (meaning t m 4138) source

theorem rule6178 (p3791 p4139 p4140 p4141 : Prop) (h : (¬ p4139) ∨ (¬ p4140) ∨ (¬ p4141) ∨ (¬ p3791)) : (¬ p3791) ∨ (¬ p4139) ∨ (¬ p4140) ∨ (¬ p4141) := by
  classical
  tauto

theorem initial6178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4139)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4141)) := by
  have source := ElevenTheory.theory519 (m.theta 5 10) (m.theta 5 7) (m.theta 6 7) (m.theta 7 10)
  exact rule6178 (meaning t m 3791) (meaning t m 4139) (meaning t m 4140) (meaning t m 4141) source

theorem rule6179 (p1802 p1808 : Prop) : (¬ p1802) ∨ ((p1802 ∨ p1808)) := by
  classical
  tauto

theorem initial6179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1802)) ∨ (meaning t m 4142) := by
  exact rule6179 (meaning t m 1802) (meaning t m 1808)

theorem rule6180 (p1802 p1808 : Prop) : (¬ p1808) ∨ ((p1802 ∨ p1808)) := by
  classical
  tauto

theorem initial6180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1808)) ∨ (meaning t m 4142) := by
  exact rule6180 (meaning t m 1802) (meaning t m 1808)

theorem rule6197 (p4142 p4143 : Prop) (h : (p4142 ↔ p4143)) : (¬ p4142) ∨ (p4143) := by
  classical
  tauto

theorem initial6197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4142)) ∨ (meaning t m 4143) := by
  have source := ElevenTheory.theory520 t (m.theta 4 10) (m.theta 4 8) (m.theta 8 10)
  exact rule6197 (meaning t m 4142) (meaning t m 4143) source

theorem rule6201 (p3662 p4153 p4154 : Prop) (h : (¬ p3662) ∨ (¬ p4153) ∨ p4154) : (¬ p3662) ∨ (¬ p4153) ∨ (p4154) := by
  classical
  tauto

theorem initial6201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4153)) ∨ (meaning t m 4154) := by
  have source := ElevenTheory.theory522 (m.theta 1 3) (m.theta 3 5) (m.theta 3 6)
  exact rule6201 (meaning t m 3662) (meaning t m 4153) (meaning t m 4154) source

theorem rule6202 (p3551 p3553 p4155 : Prop) (h : (¬ p3551) ∨ (¬ p4155) ∨ p3553) : (¬ p3551) ∨ (p3553) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial6202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3551)) ∨ (meaning t m 3553) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory523 (m.theta 0 7) (m.theta 3 7) (m.theta 7 8)
  exact rule6202 (meaning t m 3551) (meaning t m 3553) (meaning t m 4155) source

theorem rule6204 (p2331 p2807 p4156 : Prop) (h : (¬ p4156) ∨ (¬ p2331) ∨ p2807) : (¬ p2331) ∨ (p2807) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial6204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2331)) ∨ (meaning t m 2807) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory525 (m.theta 0 3) (m.theta 3 6) (m.theta 3 7)
  exact rule6204 (meaning t m 2331) (meaning t m 2807) (meaning t m 4156) source

theorem rule6207 (p4134 p4157 p4158 : Prop) (h : (¬ p4157) ∨ (¬ p4134) ∨ p4158) : (¬ p4134) ∨ (¬ p4157) ∨ (p4158) := by
  classical
  tauto

theorem initial6207 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4157)) ∨ (meaning t m 4158) := by
  have source := ElevenTheory.theory528 t (m.theta 4 8) (m.theta 5 8) (m.theta 6 8)
  exact rule6207 (meaning t m 4134) (meaning t m 4157) (meaning t m 4158) source

theorem rule6208 (p2651 p3166 p4121 : Prop) (h : (¬ p2651) ∨ (¬ p4121) ∨ p3166) : (¬ p2651) ∨ (p3166) ∨ (¬ p4121) := by
  classical
  tauto

theorem initial6208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (meaning t m 3166) ∨ (¬ (meaning t m 4121)) := by
  have source := ElevenTheory.theory529 (m.theta 0 3) (m.theta 3 4) (m.theta 3 8)
  exact rule6208 (meaning t m 2651) (meaning t m 3166) (meaning t m 4121) source

theorem rule6209 (p1814 p1820 : Prop) : (¬ p1814) ∨ ((p1814 ∨ p1820)) := by
  classical
  tauto

theorem initial6209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1814)) ∨ (meaning t m 4159) := by
  exact rule6209 (meaning t m 1814) (meaning t m 1820)

theorem rule6210 (p1814 p1820 : Prop) : (¬ p1820) ∨ ((p1814 ∨ p1820)) := by
  classical
  tauto

theorem initial6210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1820)) ∨ (meaning t m 4159) := by
  exact rule6210 (meaning t m 1814) (meaning t m 1820)

theorem rule6227 (p4159 p4160 : Prop) (h : (p4159 ↔ p4160)) : (¬ p4159) ∨ (p4160) := by
  classical
  tauto

theorem initial6227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4159)) ∨ (meaning t m 4160) := by
  have source := ElevenTheory.theory530 t (m.theta 2 10) (m.theta 2 4) (m.theta 4 10)
  exact rule6227 (meaning t m 4159) (meaning t m 4160) source

theorem rule6229 (p3027 p3189 p3919 : Prop) (h : (¬ p3919) ∨ (¬ p3189) ∨ p3027) : (p3027) ∨ (¬ p3189) ∨ (¬ p3919) := by
  classical
  tauto

theorem initial6229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3919)) := by
  have source := ElevenTheory.theory531 (m.theta 1 3) (m.theta 3 7) (m.theta 3 8)
  exact rule6229 (meaning t m 3027) (meaning t m 3189) (meaning t m 3919) source

theorem rule6231 (p2253 p2651 p3379 p4116 : Prop) (h : (¬ p2651) ∨ (¬ p2253) ∨ (¬ p4116) ∨ p3379) : (¬ p2253) ∨ (¬ p2651) ∨ (p3379) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial6231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 3379) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory533 (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 4)
  exact rule6231 (meaning t m 2253) (meaning t m 2651) (meaning t m 3379) (meaning t m 4116) source

theorem rule6234 (p3570 p3659 p4169 : Prop) (h : (¬ p4169) ∨ (¬ p3570) ∨ p3659) : (¬ p3570) ∨ (p3659) ∨ (¬ p4169) := by
  classical
  tauto

theorem initial6234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3570)) ∨ (meaning t m 3659) ∨ (¬ (meaning t m 4169)) := by
  have source := ElevenTheory.theory536 (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule6234 (meaning t m 3570) (meaning t m 3659) (meaning t m 4169) source

theorem rule6235 (p2088 p3322 p4170 p4171 : Prop) (h : (¬ p2088) ∨ (¬ p4170) ∨ (¬ p3322) ∨ (¬ p4171)) : (¬ p2088) ∨ (¬ p3322) ∨ (¬ p4170) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial6235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory537 (m.theta 0 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule6235 (meaning t m 2088) (meaning t m 3322) (meaning t m 4170) (meaning t m 4171) source

theorem rule6236 (p2156 p3591 p3957 p4172 : Prop) (h : (¬ p4172) ∨ (¬ p3957) ∨ (¬ p2156) ∨ (¬ p3591)) : (¬ p2156) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4172) := by
  classical
  tauto

theorem initial6236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4172)) := by
  have source := ElevenTheory.theory538 (m.theta 0 1) (m.theta 0 5) (m.theta 1 6) (m.theta 5 6)
  exact rule6236 (meaning t m 2156) (meaning t m 3591) (meaning t m 3957) (meaning t m 4172) source

theorem rule6237 (p3412 p3952 p4173 : Prop) (h : (¬ p3952) ∨ (¬ p3412) ∨ p4173) : (¬ p3412) ∨ (¬ p3952) ∨ (p4173) := by
  classical
  tauto

theorem initial6237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3412)) ∨ (¬ (meaning t m 3952)) ∨ (meaning t m 4173) := by
  have source := ElevenTheory.theory539 (m.theta 1 5) (m.theta 3 5) (m.theta 5 6)
  exact rule6237 (meaning t m 3412) (meaning t m 3952) (meaning t m 4173) source

theorem rule6238 (p1826 p1832 : Prop) : (¬ p1826) ∨ ((p1826 ∨ p1832)) := by
  classical
  tauto

theorem initial6238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1826)) ∨ (meaning t m 4174) := by
  exact rule6238 (meaning t m 1826) (meaning t m 1832)

theorem rule6239 (p1826 p1832 : Prop) : (¬ p1832) ∨ ((p1826 ∨ p1832)) := by
  classical
  tauto

theorem initial6239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1832)) ∨ (meaning t m 4174) := by
  exact rule6239 (meaning t m 1826) (meaning t m 1832)

theorem rule6256 (p4174 p4175 : Prop) (h : (p4174 ↔ p4175)) : (¬ p4174) ∨ (p4175) := by
  classical
  tauto

theorem initial6256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4174)) ∨ (meaning t m 4175) := by
  have source := ElevenTheory.theory540 t (m.theta 1 10) (m.theta 1 8) (m.theta 8 10)
  exact rule6256 (meaning t m 4174) (meaning t m 4175) source

theorem rule6259 (p2641 p2992 p4153 : Prop) (h : (¬ p2641) ∨ (¬ p4153) ∨ p2992) : (¬ p2641) ∨ (p2992) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial6259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (meaning t m 2992) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory542 (m.theta 1 3) (m.theta 3 5) (m.theta 3 6)
  exact rule6259 (meaning t m 2641) (meaning t m 2992) (meaning t m 4153) source

theorem rule6261 (p3125 p3917 p4185 : Prop) (h : (¬ p3917) ∨ (¬ p3125) ∨ (¬ p4185)) : (¬ p3125) ∨ (¬ p3917) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial6261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory544 (m.theta 2 6) (m.theta 5 6) (m.theta 6 9)
  exact rule6261 (meaning t m 3125) (meaning t m 3917) (meaning t m 4185) source

theorem rule6262 (p2298 p2299 p3553 : Prop) (h : (¬ p2298) ∨ (¬ p2299) ∨ p3553) : (¬ p2298) ∨ (¬ p2299) ∨ (p3553) := by
  classical
  tauto

theorem initial6262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 3553) := by
  have source := ElevenTheory.theory545 (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule6262 (meaning t m 2298) (meaning t m 2299) (meaning t m 3553) source

theorem rule6264 (p2797 p3136 p4153 : Prop) (h : (¬ p4153) ∨ (¬ p2797) ∨ p3136) : (¬ p2797) ∨ (p3136) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial6264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2797)) ∨ (meaning t m 3136) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory547 (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule6264 (meaning t m 2797) (meaning t m 3136) (meaning t m 4153) source

theorem rule6265 (p2630 p3136 p3413 : Prop) (h : (¬ p3413) ∨ (¬ p2630) ∨ p3136) : (¬ p2630) ∨ (p3136) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial6265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (meaning t m 3136) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory548 (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule6265 (meaning t m 2630) (meaning t m 3136) (meaning t m 3413) source

theorem rule6266 (p2470 p3540 p4186 : Prop) (h : (¬ p3540) ∨ (¬ p2470) ∨ (¬ p4186)) : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial6266 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory549 (m.theta 0 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6266 (meaning t m 2470) (meaning t m 3540) (meaning t m 4186) source

theorem rule6267 (p2241 p2741 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p2741) ∨ (¬ p2241)) : (¬ p2241) ∨ (¬ p2741) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial6267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory550 (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule6267 (meaning t m 2241) (meaning t m 2741) (meaning t m 3954) source

theorem rule6268 (p2387 p2785 p2819 : Prop) (h : (¬ p2387) ∨ (¬ p2819) ∨ (¬ p2785)) : (¬ p2387) ∨ (¬ p2785) ∨ (¬ p2819) := by
  classical
  tauto

theorem initial6268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 2819)) := by
  have source := ElevenTheory.theory551 (m.theta 0 6) (m.theta 2 6) (m.theta 6 8)
  exact rule6268 (meaning t m 2387) (meaning t m 2785) (meaning t m 2819) source

theorem rule6269 (p2553 p4137 p4187 : Prop) (h : (¬ p4137) ∨ (¬ p4187) ∨ (¬ p2553)) : (¬ p2553) ∨ (¬ p4137) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial6269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory552 (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule6269 (meaning t m 2553) (meaning t m 4137) (meaning t m 4187) source

theorem rule6270 (p2098 p2136 p4120 p4188 : Prop) (h : (¬ p2136) ∨ (¬ p2098) ∨ (¬ p4188) ∨ (¬ p4120)) : (¬ p2098) ∨ (¬ p2136) ∨ (¬ p4120) ∨ (¬ p4188) := by
  classical
  tauto

theorem initial6270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4188)) := by
  have source := ElevenTheory.theory553 (m.theta 0 2) (m.theta 0 5) (m.theta 2 8) (m.theta 5 8)
  exact rule6270 (meaning t m 2098) (meaning t m 2136) (meaning t m 4120) (meaning t m 4188) source

theorem rule6271 (p3399 p3860 p4189 : Prop) (h : (¬ p3860) ∨ (¬ p4189) ∨ (¬ p3399)) : (¬ p3399) ∨ (¬ p3860) ∨ (¬ p4189) := by
  classical
  tauto

theorem initial6271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4189)) := by
  have source := ElevenTheory.theory554 (m.theta 0 1) (m.theta 1 7) (m.theta 1 8)
  exact rule6271 (meaning t m 3399) (meaning t m 3860) (meaning t m 4189) source

theorem rule6272 (p2553 p3325 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p3325) ∨ (¬ p2553)) : (¬ p2553) ∨ (¬ p3325) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial6272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory555 (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6272 (meaning t m 2553) (meaning t m 3325) (meaning t m 3956) source

theorem rule6273 (p2122 p2313 p2785 : Prop) (h : (¬ p2122) ∨ (¬ p2785) ∨ (¬ p2313)) : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2785) := by
  classical
  tauto

theorem initial6273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2785)) := by
  have source := ElevenTheory.theory556 (m.theta 0 6) (m.theta 2 6) (m.theta 6 7)
  exact rule6273 (meaning t m 2122) (meaning t m 2313) (meaning t m 2785) source

theorem rule6274 (p3096 p3956 p3989 : Prop) (h : (¬ p3989) ∨ (¬ p3096) ∨ p3956) : (¬ p3096) ∨ (p3956) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial6274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3096)) ∨ (meaning t m 3956) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory557 (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule6274 (meaning t m 3096) (meaning t m 3956) (meaning t m 3989) source

theorem rule6275 (p3506 p4190 p4191 : Prop) (h : (¬ p4190) ∨ (¬ p3506) ∨ (¬ p4191)) : (¬ p3506) ∨ (¬ p4190) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial6275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4190)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory558 (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule6275 (meaning t m 3506) (meaning t m 4190) (meaning t m 4191) source

theorem rule6276 (p3292 p3361 p3755 : Prop) (h : (¬ p3755) ∨ (¬ p3361) ∨ (¬ p3292)) : (¬ p3292) ∨ (¬ p3361) ∨ (¬ p3755) := by
  classical
  tauto

theorem initial6276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3755)) := by
  have source := ElevenTheory.theory559 (m.theta 0 3) (m.theta 2 3) (m.theta 3 9)
  exact rule6276 (meaning t m 3292) (meaning t m 3361) (meaning t m 3755) source

theorem rule6277 (p2911 p3920 p3956 p4138 : Prop) (h : (¬ p2911) ∨ (¬ p4138) ∨ (¬ p3956) ∨ (¬ p3920)) : (¬ p2911) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial6277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory560 (m.theta 4 6) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule6277 (meaning t m 2911) (meaning t m 3920) (meaning t m 3956) (meaning t m 4138) source

theorem rule6278 (p2427 p2982 p4192 : Prop) (h : (¬ p4192) ∨ (¬ p2427) ∨ p2982) : (¬ p2427) ∨ (p2982) ∨ (¬ p4192) := by
  classical
  tauto

theorem initial6278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (meaning t m 2982) ∨ (¬ (meaning t m 4192)) := by
  have source := ElevenTheory.theory561 (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule6278 (meaning t m 2427) (meaning t m 2982) (meaning t m 4192) source

theorem rule6279 (p2190 p3880 p4110 : Prop) (h : (¬ p2190) ∨ (¬ p3880) ∨ p4110) : (¬ p2190) ∨ (¬ p3880) ∨ (p4110) := by
  classical
  tauto

theorem initial6279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3880)) ∨ (meaning t m 4110) := by
  have source := ElevenTheory.theory562 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule6279 (meaning t m 2190) (meaning t m 3880) (meaning t m 4110) source

theorem rule6281 (p2829 p2839 p4193 : Prop) (h : (¬ p2829) ∨ (¬ p4193) ∨ p2839) : (¬ p2829) ∨ (p2839) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial6281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2829)) ∨ (meaning t m 2839) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory564 (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule6281 (meaning t m 2829) (meaning t m 2839) (meaning t m 4193) source

theorem rule6282 (p2891 p3747 p3880 p4034 : Prop) (h : (¬ p4034) ∨ (¬ p3747) ∨ (¬ p3880) ∨ (¬ p2891)) : (¬ p2891) ∨ (¬ p3747) ∨ (¬ p3880) ∨ (¬ p4034) := by
  classical
  tauto

theorem initial6282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4034)) := by
  have source := ElevenTheory.theory565 (m.theta 1 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6282 (meaning t m 2891) (meaning t m 3747) (meaning t m 3880) (meaning t m 4034) source

theorem rule6284 (p2352 p2553 p3325 : Prop) (h : (¬ p3325) ∨ (¬ p2553) ∨ p2352) : (p2352) ∨ (¬ p2553) ∨ (¬ p3325) := by
  classical
  tauto

theorem initial6284 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3325)) := by
  have source := ElevenTheory.theory567 (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6284 (meaning t m 2352) (meaning t m 2553) (meaning t m 3325) source

theorem rule6285 (p3691 p3699 p4155 : Prop) (h : (¬ p3691) ∨ (¬ p4155) ∨ p3699) : (¬ p3691) ∨ (p3699) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial6285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3691)) ∨ (meaning t m 3699) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory568 (m.theta 0 7) (m.theta 3 7) (m.theta 5 7)
  exact rule6285 (meaning t m 3691) (meaning t m 3699) (meaning t m 4155) source

theorem rule6286 (p2810 p4194 p4195 : Prop) (h : (¬ p4194) ∨ (¬ p2810) ∨ p4195) : (¬ p2810) ∨ (¬ p4194) ∨ (p4195) := by
  classical
  tauto

theorem initial6286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 4194)) ∨ (meaning t m 4195) := by
  have source := ElevenTheory.theory569 (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule6286 (meaning t m 2810) (meaning t m 4194) (meaning t m 4195) source

theorem rule6287 (p2449 p3516 p4155 : Prop) (h : (¬ p4155) ∨ (¬ p2449) ∨ p3516) : (¬ p2449) ∨ (p3516) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial6287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (meaning t m 3516) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory570 (m.theta 0 7) (m.theta 3 7) (m.theta 7 9)
  exact rule6287 (meaning t m 2449) (meaning t m 3516) (meaning t m 4155) source

theorem rule6288 (p2264 p3551 p4155 : Prop) (h : (¬ p4155) ∨ (¬ p2264) ∨ (¬ p3551)) : (¬ p2264) ∨ (¬ p3551) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial6288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory571 (m.theta 0 7) (m.theta 3 7) (m.theta 7 8)
  exact rule6288 (meaning t m 2264) (meaning t m 3551) (meaning t m 4155) source

theorem rule6289 (p2667 p2952 p3987 p4153 : Prop) (h : (¬ p2667) ∨ (¬ p4153) ∨ (¬ p3987) ∨ (¬ p2952)) : (¬ p2667) ∨ (¬ p2952) ∨ (¬ p3987) ∨ (¬ p4153) := by
  classical
  tauto

theorem initial6289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4153)) := by
  have source := ElevenTheory.theory572 (m.theta 0 3) (m.theta 0 6) (m.theta 3 5) (m.theta 3 6)
  exact rule6289 (meaning t m 2667) (meaning t m 2952) (meaning t m 3987) (meaning t m 4153) source

theorem rule6290 (p3744 p3986 p4037 : Prop) (h : (¬ p3986) ∨ (¬ p4037) ∨ p3744) : (p3744) ∨ (¬ p3986) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial6290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3744) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory573 (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule6290 (meaning t m 3744) (meaning t m 3986) (meaning t m 4037) source

theorem rule6291 (p3661 p4153 p4196 : Prop) (h : (¬ p4153) ∨ (¬ p4196) ∨ p3661) : (p3661) ∨ (¬ p4153) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial6291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3661) ∨ (¬ (meaning t m 4153)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory574 (m.theta 3 5) (m.theta 3 6) (m.theta 3 8)
  exact rule6291 (meaning t m 3661) (meaning t m 4153) (meaning t m 4196) source

theorem rule6294 (p2166 p3988 p4173 : Prop) (h : (¬ p2166) ∨ (¬ p3988) ∨ (¬ p4173)) : (¬ p2166) ∨ (¬ p3988) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial6294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory577 (m.theta 1 5) (m.theta 5 6) (m.theta 5 8)
  exact rule6294 (meaning t m 2166) (meaning t m 3988) (meaning t m 4173) source

theorem rule6295 (p3452 p3555 p4202 : Prop) (h : (¬ p4202) ∨ (¬ p3452) ∨ p3555) : (¬ p3452) ∨ (p3555) ∨ (¬ p4202) := by
  classical
  tauto

theorem initial6295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3452)) ∨ (meaning t m 3555) ∨ (¬ (meaning t m 4202)) := by
  have source := ElevenTheory.theory578 (m.theta 0 1) (m.theta 1 4) (m.theta 1 5)
  exact rule6295 (meaning t m 3452) (meaning t m 3555) (meaning t m 4202) source

theorem rule6296 (p2588 p3325 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p3325) ∨ p2588) : (p2588) ∨ (¬ p3325) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial6296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2588) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory579 (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule6296 (meaning t m 2588) (meaning t m 3325) (meaning t m 3956) source

theorem rule6298 (p2295 p3323 p4025 : Prop) (h : (¬ p3323) ∨ (¬ p4025) ∨ p2295) : (p2295) ∨ (¬ p3323) ∨ (¬ p4025) := by
  classical
  tauto

theorem initial6298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2295) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4025)) := by
  have source := ElevenTheory.theory581 (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule6298 (meaning t m 2295) (meaning t m 3323) (meaning t m 4025) source

theorem rule6299 (p2373 p2533 p2982 : Prop) (h : (¬ p2373) ∨ (¬ p2533) ∨ p2982) : (¬ p2373) ∨ (¬ p2533) ∨ (p2982) := by
  classical
  tauto

theorem initial6299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2533)) ∨ (meaning t m 2982) := by
  have source := ElevenTheory.theory582 (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule6299 (meaning t m 2373) (meaning t m 2533) (meaning t m 2982) source

theorem rule6302 (p2077 p4206 : Prop) (h : ((¬ p2077) ↔ (¬ p4206))) : (p2077) ∨ (¬ p4206) := by
  classical
  tauto

theorem initial6302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2077) ∨ (¬ (meaning t m 4206)) := by
  have source := ElevenTheory.theory585 t (m.theta 6 10)
  exact rule6302 (meaning t m 2077) (meaning t m 4206) source

theorem rule6304 (p2951 p4207 p4208 p4209 : Prop) (h : (¬ p2951) ∨ (¬ p4207) ∨ (¬ p4208) ∨ (¬ p4209)) : (¬ p2951) ∨ (¬ p4207) ∨ (¬ p4208) ∨ (¬ p4209) := by
  classical
  tauto

theorem initial6304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 4207)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4209)) := by
  have source := ElevenTheory.theory586 (m.theta 0 5) (m.theta 0 9) (m.theta 3 5) (m.theta 5 9)
  exact rule6304 (meaning t m 2951) (meaning t m 4207) (meaning t m 4208) (meaning t m 4209) source

theorem rule6305 (p4110 p4173 p4210 : Prop) (h : (¬ p4210) ∨ (¬ p4173) ∨ p4110) : (p4110) ∨ (¬ p4173) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial6305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4110) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory587 (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6305 (meaning t m 4110) (meaning t m 4173) (meaning t m 4210) source

theorem rule6306 (p2589 p3555 p4108 p4210 : Prop) (h : (¬ p2589) ∨ (¬ p4210) ∨ (¬ p4108) ∨ p3555) : (¬ p2589) ∨ (p3555) ∨ (¬ p4108) ∨ (¬ p4210) := by
  classical
  tauto

theorem initial6306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (meaning t m 3555) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4210)) := by
  have source := ElevenTheory.theory588 (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 5)
  exact rule6306 (meaning t m 2589) (meaning t m 3555) (meaning t m 4108) (meaning t m 4210) source

theorem rule6327 (p2313 p3204 p3549 : Prop) (h : (¬ p3204) ∨ (¬ p2313) ∨ p3549) : (¬ p2313) ∨ (¬ p3204) ∨ (p3549) := by
  classical
  tauto

theorem initial6327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3204)) ∨ (meaning t m 3549) := by
  have source := ElevenTheory.theory590 (m.theta 0 6) (m.theta 1 6) (m.theta 6 7)
  exact rule6327 (meaning t m 2313) (meaning t m 3204) (meaning t m 3549) source

theorem rule6329 (p2383 p3063 p3204 : Prop) (h : (¬ p3204) ∨ (¬ p3063) ∨ p2383) : (p2383) ∨ (¬ p3063) ∨ (¬ p3204) := by
  classical
  tauto

theorem initial6329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2383) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3204)) := by
  have source := ElevenTheory.theory592 (m.theta 0 6) (m.theta 1 6) (m.theta 6 8)
  exact rule6329 (meaning t m 2383) (meaning t m 3063) (meaning t m 3204) source

theorem rule6331 (p1850 p1856 : Prop) : (¬ p1850) ∨ ((p1850 ∨ p1856)) := by
  classical
  tauto

theorem initial6331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1850)) ∨ (meaning t m 4221) := by
  exact rule6331 (meaning t m 1850) (meaning t m 1856)

theorem rule6332 (p1850 p1856 : Prop) : (¬ p1856) ∨ ((p1850 ∨ p1856)) := by
  classical
  tauto

theorem initial6332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1856)) ∨ (meaning t m 4221) := by
  exact rule6332 (meaning t m 1850) (meaning t m 1856)

theorem rule6349 (p4221 p4222 : Prop) (h : (p4221 ↔ p4222)) : (¬ p4221) ∨ (p4222) := by
  classical
  tauto

theorem initial6349 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4221)) ∨ (meaning t m 4222) := by
  have source := ElevenTheory.theory594 t (m.theta 3 10) (m.theta 3 6) (m.theta 6 10)
  exact rule6349 (meaning t m 4221) (meaning t m 4222) source

theorem rule6351 (p3370 p3646 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p3370) ∨ p3646) : (¬ p3370) ∨ (p3646) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial6351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3370)) ∨ (meaning t m 3646) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory595 (m.theta 0 5) (m.theta 1 5) (m.theta 5 6)
  exact rule6351 (meaning t m 3370) (meaning t m 3646) (meaning t m 4173) source

theorem rule6353 (p3589 p3873 : Prop) (h : p3589 ∨ p3873) : (p3589) ∨ (p3873) := by
  classical
  tauto

theorem initial6353 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3589) ∨ (meaning t m 3873) := by
  have source := ElevenTheory.theory597 (m.theta 0 1) (m.theta 0 2)
  exact rule6353 (meaning t m 3589) (meaning t m 3873) source

theorem rule6356 (p4110 p4204 p4235 : Prop) (h : (¬ p4110) ∨ (¬ p4204) ∨ p4235) : (¬ p4110) ∨ (¬ p4204) ∨ (p4235) := by
  classical
  tauto

theorem initial6356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4204)) ∨ (meaning t m 4235) := by
  have source := ElevenTheory.theory600 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6356 (meaning t m 4110) (meaning t m 4204) (meaning t m 4235) source

theorem rule6359 (p2589 p3363 p3684 : Prop) (h : (¬ p3363) ∨ (¬ p2589) ∨ p3684) : (¬ p2589) ∨ (¬ p3363) ∨ (p3684) := by
  classical
  tauto

theorem initial6359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3363)) ∨ (meaning t m 3684) := by
  have source := ElevenTheory.theory603 (m.theta 0 4) (m.theta 2 4) (m.theta 4 5)
  exact rule6359 (meaning t m 2589) (meaning t m 3363) (meaning t m 3684) source

theorem rule6364 (p2499 p3487 p3574 : Prop) (h : (¬ p3487) ∨ (¬ p2499) ∨ p3574) : (¬ p2499) ∨ (¬ p3487) ∨ (p3574) := by
  classical
  tauto

theorem initial6364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3487)) ∨ (meaning t m 3574) := by
  have source := ElevenTheory.theory608 (m.theta 1 4) (m.theta 3 4) (m.theta 4 6)
  exact rule6364 (meaning t m 2499) (meaning t m 3487) (meaning t m 3574) source

theorem rule6367 (p2156 p3952 p4109 p4241 : Prop) (h : (¬ p4109) ∨ (¬ p4241) ∨ (¬ p2156) ∨ (¬ p3952)) : (¬ p2156) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial6367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory611 (m.theta 0 5) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6367 (meaning t m 2156) (meaning t m 3952) (meaning t m 4109) (meaning t m 4241) source

theorem rule6368 (p2509 p3874 p4030 : Prop) (h : (¬ p2509) ∨ (¬ p4030) ∨ p3874) : (¬ p2509) ∨ (p3874) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial6368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2509)) ∨ (meaning t m 3874) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory612 (m.theta 1 4) (m.theta 2 4) (m.theta 4 8)
  exact rule6368 (meaning t m 2509) (meaning t m 3874) (meaning t m 4030) source

theorem rule6369 (p2098 p2753 p4242 : Prop) (h : (¬ p4242) ∨ (¬ p2753) ∨ (¬ p2098)) : (¬ p2098) ∨ (¬ p2753) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial6369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory613 (m.theta 0 2) (m.theta 1 2) (m.theta 2 8)
  exact rule6369 (meaning t m 2098) (meaning t m 2753) (meaning t m 4242) source

theorem rule6370 (p3486 p4243 p4244 : Prop) (h : (¬ p4243) ∨ (¬ p3486) ∨ p4244) : (¬ p3486) ∨ (¬ p4243) ∨ (p4244) := by
  classical
  tauto

theorem initial6370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4243)) ∨ (meaning t m 4244) := by
  have source := ElevenTheory.theory614 (m.theta 1 5) (m.theta 2 5) (m.theta 5 7)
  exact rule6370 (meaning t m 3486) (meaning t m 4243) (meaning t m 4244) source

theorem rule6371 (p2437 p2662 p3540 : Prop) (h : (¬ p2437) ∨ (¬ p2662) ∨ (¬ p3540)) : (¬ p2437) ∨ (¬ p2662) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial6371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory615 (m.theta 0 4) (m.theta 3 4) (m.theta 4 7)
  exact rule6371 (meaning t m 2437) (meaning t m 2662) (meaning t m 3540) source

theorem rule6373 (p2499 p2922 p3581 : Prop) (h : (¬ p2922) ∨ (¬ p3581) ∨ (¬ p2499)) : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3581) := by
  classical
  tauto

theorem initial6373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3581)) := by
  have source := ElevenTheory.theory617 (m.theta 1 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6373 (meaning t m 2499) (meaning t m 2922) (meaning t m 3581) source

theorem rule6374 (p2427 p2870 p3698 : Prop) (h : (¬ p2870) ∨ (¬ p3698) ∨ p2427) : (p2427) ∨ (¬ p2870) ∨ (¬ p3698) := by
  classical
  tauto

theorem initial6374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2427) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3698)) := by
  have source := ElevenTheory.theory618 (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule6374 (meaning t m 2427) (meaning t m 2870) (meaning t m 3698) source

theorem rule6376 (p2247 p3093 p4245 : Prop) (h : (¬ p3093) ∨ (¬ p4245) ∨ (¬ p2247)) : (¬ p2247) ∨ (¬ p3093) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial6376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory620 (m.theta 0 1) (m.theta 1 3) (m.theta 1 6)
  exact rule6376 (meaning t m 2247) (meaning t m 3093) (meaning t m 4245) source

theorem rule6378 (p2926 p3379 p3399 : Prop) (h : (¬ p2926) ∨ (¬ p3399) ∨ p3379) : (¬ p2926) ∨ (p3379) ∨ (¬ p3399) := by
  classical
  tauto

theorem initial6378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2926)) ∨ (meaning t m 3379) ∨ (¬ (meaning t m 3399)) := by
  have source := ElevenTheory.theory622 (m.theta 0 1) (m.theta 1 4) (m.theta 1 7)
  exact rule6378 (meaning t m 2926) (meaning t m 3379) (meaning t m 3399) source

theorem rule6379 (p3434 p3821 p3959 : Prop) (h : (¬ p3821) ∨ (¬ p3434) ∨ (¬ p3959)) : (¬ p3434) ∨ (¬ p3821) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial6379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory623 (m.theta 0 7) (m.theta 2 7) (m.theta 7 9)
  exact rule6379 (meaning t m 3434) (meaning t m 3821) (meaning t m 3959) source

theorem rule6380 (p1862 p1868 : Prop) : (¬ p1862) ∨ ((p1862 ∨ p1868)) := by
  classical
  tauto

theorem initial6380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1862)) ∨ (meaning t m 4246) := by
  exact rule6380 (meaning t m 1862) (meaning t m 1868)

theorem rule6381 (p1862 p1868 : Prop) : (¬ p1868) ∨ ((p1862 ∨ p1868)) := by
  classical
  tauto

theorem initial6381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1868)) ∨ (meaning t m 4246) := by
  exact rule6381 (meaning t m 1862) (meaning t m 1868)

theorem rule6398 (p4246 p4247 : Prop) (h : (p4246 ↔ p4247)) : (¬ p4246) ∨ (p4247) := by
  classical
  tauto

theorem initial6398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4246)) ∨ (meaning t m 4247) := by
  have source := ElevenTheory.theory624 t (m.theta 2 10) (m.theta 2 7) (m.theta 7 10)
  exact rule6398 (meaning t m 4246) (meaning t m 4247) source

theorem rule6402 (p3742 p4186 p4256 : Prop) (h : (¬ p4186) ∨ (¬ p3742) ∨ p4256) : (¬ p3742) ∨ (¬ p4186) ∨ (p4256) := by
  classical
  tauto

theorem initial6402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) ∨ (meaning t m 4256) := by
  have source := ElevenTheory.theory627 (m.theta 3 4) (m.theta 4 7) (m.theta 4 8)
  exact rule6402 (meaning t m 3742) (meaning t m 4186) (meaning t m 4256) source

theorem rule6403 (p2578 p3946 p4137 : Prop) (h : (¬ p4137) ∨ (¬ p2578) ∨ p3946) : (¬ p2578) ∨ (p3946) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial6403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2578)) ∨ (meaning t m 3946) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory628 (m.theta 0 6) (m.theta 4 6) (m.theta 6 9)
  exact rule6403 (meaning t m 2578) (meaning t m 3946) (meaning t m 4137) source

theorem rule6404 (p3370 p3645 : Prop) (h : p3370 ∨ p3645) : (p3370) ∨ (p3645) := by
  classical
  tauto

theorem initial6404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3370) ∨ (meaning t m 3645) := by
  have source := ElevenTheory.theory629 (m.theta 0 5) (m.theta 1 5)
  exact rule6404 (meaning t m 3370) (meaning t m 3645) source

theorem rule6405 (p2138 p3645 p3873 p4172 p4243 : Prop) (h : (¬ p2138) ∨ (¬ p3645) ∨ (¬ p4172) ∨ (¬ p4243) ∨ (¬ p3873)) : (¬ p2138) ∨ (¬ p3645) ∨ (¬ p3873) ∨ (¬ p4172) ∨ (¬ p4243) := by
  classical
  tauto

theorem initial6405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4243)) := by
  have source := ElevenTheory.theory630 (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 5) (m.theta 2 5)
  exact rule6405 (meaning t m 2138) (meaning t m 3645) (meaning t m 3873) (meaning t m 4172) (meaning t m 4243) source

theorem rule6406 (p2252 p2657 p4111 : Prop) (h : (¬ p2657) ∨ (¬ p2252) ∨ p4111) : (¬ p2252) ∨ (¬ p2657) ∨ (p4111) := by
  classical
  tauto

theorem initial6406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 4111) := by
  have source := ElevenTheory.theory631 (m.theta 0 3) (m.theta 1 3) (m.theta 3 4)
  exact rule6406 (meaning t m 2252) (meaning t m 2657) (meaning t m 4111) source

theorem rule6407 (p2860 p2870 p4204 : Prop) (h : (¬ p2870) ∨ (¬ p4204) ∨ p2860) : (p2860) ∨ (¬ p2870) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial6407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2860) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory632 (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6407 (meaning t m 2860) (meaning t m 2870) (meaning t m 4204) source

theorem rule6408 (p3055 p3364 p3365 : Prop) (h : (¬ p3364) ∨ (¬ p3365) ∨ p3055) : (p3055) ∨ (¬ p3364) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial6408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3055) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory633 (m.theta 0 2) (m.theta 2 3) (m.theta 2 4)
  exact rule6408 (meaning t m 3055) (meaning t m 3364) (meaning t m 3365) source

theorem rule6412 (p2499 p2928 p3920 : Prop) (h : (¬ p2928) ∨ (¬ p3920) ∨ p2499) : (p2499) ∨ (¬ p2928) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6412 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2499) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory637 (m.theta 1 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6412 (meaning t m 2499) (meaning t m 2928) (meaning t m 3920) source

theorem rule6413 (p3574 p3742 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p3742) ∨ p3574) : (p3574) ∨ (¬ p3742) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3574) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory638 (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6413 (meaning t m 3574) (meaning t m 3742) (meaning t m 3920) source

theorem rule6421 (p3434 p3576 p3631 : Prop) (h : (¬ p3434) ∨ (¬ p3576) ∨ p3631) : (¬ p3434) ∨ (¬ p3576) ∨ (p3631) := by
  classical
  tauto

theorem initial6421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3576)) ∨ (meaning t m 3631) := by
  have source := ElevenTheory.theory645 (m.theta 1 7) (m.theta 2 7) (m.theta 7 9)
  exact rule6421 (meaning t m 3434) (meaning t m 3576) (meaning t m 3631) source

theorem rule6425 (p3369 p3399 p3556 p3571 : Prop) (h : (¬ p3369) ∨ (¬ p3571) ∨ (¬ p3399) ∨ (¬ p3556)) : (¬ p3369) ∨ (¬ p3399) ∨ (¬ p3556) ∨ (¬ p3571) := by
  classical
  tauto

theorem initial6425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3571)) := by
  have source := ElevenTheory.theory649 (m.theta 0 1) (m.theta 0 5) (m.theta 1 7) (m.theta 5 7)
  exact rule6425 (meaning t m 3369) (meaning t m 3399) (meaning t m 3556) (meaning t m 3571) source

theorem rule6426 (p3325 p3955 : Prop) (h : p3955 ∨ p3325) : (p3325) ∨ (p3955) := by
  classical
  tauto

theorem initial6426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3325) ∨ (meaning t m 3955) := by
  have source := ElevenTheory.theory650 (m.theta 6 7) (m.theta 6 8)
  exact rule6426 (meaning t m 3325) (meaning t m 3955) source

theorem rule6429 (p2476 p3363 p3874 : Prop) (h : (¬ p2476) ∨ (¬ p3363) ∨ p3874) : (¬ p2476) ∨ (¬ p3363) ∨ (p3874) := by
  classical
  tauto

theorem initial6429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3363)) ∨ (meaning t m 3874) := by
  have source := ElevenTheory.theory653 (m.theta 0 4) (m.theta 2 4) (m.theta 4 8)
  exact rule6429 (meaning t m 2476) (meaning t m 3363) (meaning t m 3874) source

theorem rule6430 (p2579 p3346 p3746 : Prop) (h : (¬ p3746) ∨ (¬ p2579) ∨ p3346) : (¬ p2579) ∨ (p3346) ∨ (¬ p3746) := by
  classical
  tauto

theorem initial6430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2579)) ∨ (meaning t m 3346) ∨ (¬ (meaning t m 3746)) := by
  have source := ElevenTheory.theory654 (m.theta 0 4) (m.theta 4 6) (m.theta 4 9)
  exact rule6430 (meaning t m 2579) (meaning t m 3346) (meaning t m 3746) source

theorem rule6431 (p2110 p2144 p4238 : Prop) (h : (¬ p4238) ∨ (¬ p2144) ∨ p2110) : (p2110) ∨ (¬ p2144) ∨ (¬ p4238) := by
  classical
  tauto

theorem initial6431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2110) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 4238)) := by
  have source := ElevenTheory.theory655 (m.theta 0 2) (m.theta 0 5) (m.theta 0 8)
  exact rule6431 (meaning t m 2110) (meaning t m 2144) (meaning t m 4238) source

theorem rule6433 (p2247 p3449 p4262 : Prop) (h : (¬ p4262) ∨ (¬ p3449) ∨ (¬ p2247)) : (¬ p2247) ∨ (¬ p3449) ∨ (¬ p4262) := by
  classical
  tauto

theorem initial6433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4262)) := by
  have source := ElevenTheory.theory657 (m.theta 0 1) (m.theta 1 3) (m.theta 1 8)
  exact rule6433 (meaning t m 2247) (meaning t m 3449) (meaning t m 4262) source

theorem rule6434 (p2656 p3359 p4263 p4264 : Prop) (h : (¬ p4263) ∨ (¬ p2656) ∨ (¬ p3359) ∨ (¬ p4264)) : (¬ p2656) ∨ (¬ p3359) ∨ (¬ p4263) ∨ (¬ p4264) := by
  classical
  tauto

theorem initial6434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 4263)) ∨ (¬ (meaning t m 4264)) := by
  have source := ElevenTheory.theory658 (m.theta 0 4) (m.theta 0 9) (m.theta 3 4) (m.theta 4 9)
  exact rule6434 (meaning t m 2656) (meaning t m 3359) (meaning t m 4263) (meaning t m 4264) source

theorem rule6438 (p1874 p1880 : Prop) : (¬ p1874) ∨ ((p1874 ∨ p1880)) := by
  classical
  tauto

theorem initial6438 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1874)) ∨ (meaning t m 4265) := by
  exact rule6438 (meaning t m 1874) (meaning t m 1880)

theorem rule6439 (p1874 p1880 : Prop) : (¬ p1880) ∨ ((p1874 ∨ p1880)) := by
  classical
  tauto

theorem initial6439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1880)) ∨ (meaning t m 4265) := by
  exact rule6439 (meaning t m 1874) (meaning t m 1880)

theorem rule6456 (p4265 p4266 : Prop) (h : (p4265 ↔ p4266)) : (¬ p4265) ∨ (p4266) := by
  classical
  tauto

theorem initial6456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4265)) ∨ (meaning t m 4266) := by
  have source := ElevenTheory.theory662 t (m.theta 3 10) (m.theta 3 5) (m.theta 5 10)
  exact rule6456 (meaning t m 4265) (meaning t m 4266) source

theorem rule6458 (p2727 p2996 p3580 : Prop) (h : (¬ p3580) ∨ (¬ p2996) ∨ (¬ p2727)) : (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial6458 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory663 (m.theta 1 3) (m.theta 3 4) (m.theta 3 7)
  exact rule6458 (meaning t m 2727) (meaning t m 2996) (meaning t m 3580) source

theorem rule6459 (p4275 p4276 p4277 : Prop) (h : (¬ p4275) ∨ (¬ p4276) ∨ p4277) : (¬ p4275) ∨ (¬ p4276) ∨ (p4277) := by
  classical
  tauto

theorem initial6459 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4276)) ∨ (meaning t m 4277) := by
  have source := ElevenTheory.theory664 t (m.theta 4 7) (m.theta 5 7) (m.theta 6 7)
  exact rule6459 (meaning t m 4275) (meaning t m 4276) (meaning t m 4277) source

theorem rule6462 (p2417 p3516 p4279 : Prop) (h : (¬ p4279) ∨ (¬ p2417) ∨ p3516) : (¬ p2417) ∨ (p3516) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial6462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2417)) ∨ (meaning t m 3516) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory667 (m.theta 0 7) (m.theta 4 7) (m.theta 7 9)
  exact rule6462 (meaning t m 2417) (meaning t m 3516) (meaning t m 4279) source

theorem rule6463 (p2952 p3172 p3661 : Prop) (h : (¬ p3661) ∨ (¬ p2952) ∨ p3172) : (¬ p2952) ∨ (p3172) ∨ (¬ p3661) := by
  classical
  tauto

theorem initial6463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2952)) ∨ (meaning t m 3172) ∨ (¬ (meaning t m 3661)) := by
  have source := ElevenTheory.theory668 (m.theta 0 3) (m.theta 3 5) (m.theta 3 8)
  exact rule6463 (meaning t m 2952) (meaning t m 3172) (meaning t m 3661) source

theorem rule6465 (p3952 p4110 p4241 : Prop) (h : (¬ p3952) ∨ (¬ p4241) ∨ p4110) : (¬ p3952) ∨ (p4110) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial6465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3952)) ∨ (meaning t m 4110) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory670 (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6465 (meaning t m 3952) (meaning t m 4110) (meaning t m 4241) source

theorem rule6466 (p3556 p3646 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p3646) ∨ p3556) : (p3556) ∨ (¬ p3646) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial6466 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3556) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory671 (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6466 (meaning t m 3556) (meaning t m 3646) (meaning t m 4204) source

theorem rule6467 (p3579 p4277 p4280 : Prop) (h : (¬ p3579) ∨ (¬ p4277) ∨ p4280) : (¬ p3579) ∨ (¬ p4277) ∨ (p4280) := by
  classical
  tauto

theorem initial6467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4277)) ∨ (meaning t m 4280) := by
  have source := ElevenTheory.theory672 t (m.theta 3 7) (m.theta 4 7) (m.theta 5 7)
  exact rule6467 (meaning t m 3579) (meaning t m 4277) (meaning t m 4280) source

theorem rule6469 (p2449 p3821 p4155 : Prop) (h : (¬ p3821) ∨ (¬ p4155) ∨ (¬ p2449)) : (¬ p2449) ∨ (¬ p3821) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial6469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory674 (m.theta 0 7) (m.theta 3 7) (m.theta 7 9)
  exact rule6469 (meaning t m 2449) (meaning t m 3821) (meaning t m 4155) source

theorem rule6470 (p2476 p2579 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p2579) ∨ p2476) : (p2476) ∨ (¬ p2579) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial6470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2476) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory675 (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule6470 (meaning t m 2476) (meaning t m 2579) (meaning t m 3573) source

theorem rule6471 (p2630 p2727 p2742 : Prop) (h : (¬ p2727) ∨ (¬ p2742) ∨ p2630) : (p2630) ∨ (¬ p2727) ∨ (¬ p2742) := by
  classical
  tauto

theorem initial6471 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2630) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2742)) := by
  have source := ElevenTheory.theory676 (m.theta 1 3) (m.theta 2 3) (m.theta 3 4)
  exact rule6471 (meaning t m 2630) (meaning t m 2727) (meaning t m 2742) source

theorem rule6473 (p2241 p3379 p4281 : Prop) (h : (¬ p2241) ∨ (¬ p4281) ∨ p3379) : (¬ p2241) ∨ (p3379) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial6473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (meaning t m 3379) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory678 (m.theta 0 1) (m.theta 1 3) (m.theta 1 4)
  exact rule6473 (meaning t m 2241) (meaning t m 3379) (meaning t m 4281) source

theorem rule6474 (p2901 p3156 p4119 : Prop) (h : (¬ p3156) ∨ (¬ p4119) ∨ p2901) : (p2901) ∨ (¬ p3156) ∨ (¬ p4119) := by
  classical
  tauto

theorem initial6474 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2901) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4119)) := by
  have source := ElevenTheory.theory679 (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule6474 (meaning t m 2901) (meaning t m 3156) (meaning t m 4119) source

theorem rule6475 (p2166 p3156 p4282 : Prop) (h : (¬ p3156) ∨ (¬ p4282) ∨ p2166) : (p2166) ∨ (¬ p3156) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial6475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory680 (m.theta 1 5) (m.theta 3 5) (m.theta 5 8)
  exact rule6475 (meaning t m 2166) (meaning t m 3156) (meaning t m 4282) source

theorem rule6477 (p3690 p3821 p4283 : Prop) (h : (¬ p3821) ∨ (¬ p4283) ∨ p3690) : (p3690) ∨ (¬ p3821) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial6477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3690) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory682 (m.theta 0 7) (m.theta 5 7) (m.theta 7 9)
  exact rule6477 (meaning t m 3690) (meaning t m 3821) (meaning t m 4283) source

theorem rule6478 (p2156 p2284 p2957 : Prop) (h : (¬ p2284) ∨ (¬ p2957) ∨ p2156) : (p2156) ∨ (¬ p2284) ∨ (¬ p2957) := by
  classical
  tauto

theorem initial6478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2957)) := by
  have source := ElevenTheory.theory683 (m.theta 0 5) (m.theta 3 5) (m.theta 5 6)
  exact rule6478 (meaning t m 2156) (meaning t m 2284) (meaning t m 2957) source

theorem rule6481 (p2881 p2911 p3569 : Prop) (h : (¬ p3569) ∨ (¬ p2881) ∨ p2911) : (¬ p2881) ∨ (p2911) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial6481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2881)) ∨ (meaning t m 2911) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory686 (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule6481 (meaning t m 2881) (meaning t m 2911) (meaning t m 3569) source

theorem rule6482 (p2247 p3830 p3846 : Prop) (h : (¬ p3830) ∨ (¬ p2247) ∨ (¬ p3846)) : (¬ p2247) ∨ (¬ p3830) ∨ (¬ p3846) := by
  classical
  tauto

theorem initial6482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3846)) := by
  have source := ElevenTheory.theory687 (m.theta 0 1) (m.theta 1 3) (m.theta 1 9)
  exact rule6482 (meaning t m 2247) (meaning t m 3830) (meaning t m 3846) source

theorem rule6483 (p3073 p3256 p4288 : Prop) (h : (¬ p4288) ∨ (¬ p3256) ∨ p3073) : (p3073) ∨ (¬ p3256) ∨ (¬ p4288) := by
  classical
  tauto

theorem initial6483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3073) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4288)) := by
  have source := ElevenTheory.theory688 (m.theta 1 8) (m.theta 3 8) (m.theta 8 9)
  exact rule6483 (meaning t m 3073) (meaning t m 3256) (meaning t m 4288) source

theorem rule6524 (p3646 p3988 p4120 : Prop) (h : (¬ p3988) ∨ (¬ p3646) ∨ p4120) : (¬ p3646) ∨ (¬ p3988) ∨ (p4120) := by
  classical
  tauto

theorem initial6524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3988)) ∨ (meaning t m 4120) := by
  have source := ElevenTheory.theory691 (m.theta 0 5) (m.theta 5 6) (m.theta 5 8)
  exact rule6524 (meaning t m 3646) (meaning t m 3988) (meaning t m 4120) source

theorem rule6525 (p3177 p4009 p4309 p4310 : Prop) (h : (¬ p4309) ∨ (¬ p3177) ∨ (¬ p4310) ∨ (¬ p4009)) : (¬ p3177) ∨ (¬ p4009) ∨ (¬ p4309) ∨ (¬ p4310) := by
  classical
  tauto

theorem initial6525 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4309)) ∨ (¬ (meaning t m 4310)) := by
  have source := ElevenTheory.theory692 (m.theta 0 10) (m.theta 0 8) (m.theta 3 8) (m.theta 8 10)
  exact rule6525 (meaning t m 3177) (meaning t m 4009) (meaning t m 4309) (meaning t m 4310) source

theorem rule6528 (p2138 p2696 p4313 : Prop) (h : (¬ p2696) ∨ (¬ p4313) ∨ (¬ p2138)) : (¬ p2138) ∨ (¬ p2696) ∨ (¬ p4313) := by
  classical
  tauto

theorem initial6528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4313)) := by
  have source := ElevenTheory.theory695 (m.theta 0 2) (m.theta 2 3) (m.theta 2 5)
  exact rule6528 (meaning t m 2138) (meaning t m 2696) (meaning t m 4313) source

theorem rule6529 (p2742 p2992 p3136 : Prop) (h : (¬ p2992) ∨ (¬ p2742) ∨ p3136) : (¬ p2742) ∨ (¬ p2992) ∨ (p3136) := by
  classical
  tauto

theorem initial6529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 3136) := by
  have source := ElevenTheory.theory696 (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule6529 (meaning t m 2742) (meaning t m 2992) (meaning t m 3136) source

theorem rule6530 (p2427 p2563 p4204 : Prop) (h : (¬ p4204) ∨ (¬ p2427) ∨ p2563) : (¬ p2427) ∨ (p2563) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial6530 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2427)) ∨ (meaning t m 2563) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory697 (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6530 (meaning t m 2427) (meaning t m 2563) (meaning t m 4204) source

theorem rule6533 (p2284 p2563 p4241 : Prop) (h : (¬ p4241) ∨ (¬ p2563) ∨ p2284) : (p2284) ∨ (¬ p2563) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial6533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2284) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory700 (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule6533 (meaning t m 2284) (meaning t m 2563) (meaning t m 4241) source

theorem rule6534 (p2493 p2928 p3920 : Prop) (h : (¬ p3920) ∨ (¬ p2493) ∨ (¬ p2928)) : (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory701 (m.theta 1 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6534 (meaning t m 2493) (meaning t m 2928) (meaning t m 3920) source

theorem rule6535 (p2373 p3988 p4110 : Prop) (h : (¬ p3988) ∨ (¬ p4110) ∨ (¬ p2373)) : (¬ p2373) ∨ (¬ p3988) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial6535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory702 (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule6535 (meaning t m 2373) (meaning t m 3988) (meaning t m 4110) source

theorem rule6536 (p3755 p4314 p4315 : Prop) (h : (¬ p4314) ∨ (¬ p4315) ∨ (¬ p3755)) : (¬ p3755) ∨ (¬ p4314) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial6536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4314)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory703 (m.theta 2 3) (m.theta 3 5) (m.theta 3 9)
  exact rule6536 (meaning t m 3755) (meaning t m 4314) (meaning t m 4315) source

theorem rule6537 (p3497 p3694 p4316 : Prop) (h : (¬ p4316) ∨ (¬ p3497) ∨ p3694) : (¬ p3497) ∨ (p3694) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial6537 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3497)) ∨ (meaning t m 3694) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory704 (m.theta 2 5) (m.theta 3 5) (m.theta 5 8)
  exact rule6537 (meaning t m 3497) (meaning t m 3694) (meaning t m 4316) source

theorem rule6538 (p3324 p4317 p4318 p4319 : Prop) (h : (¬ p4317) ∨ (¬ p4318) ∨ (¬ p4319) ∨ (¬ p3324)) : (¬ p3324) ∨ (¬ p4317) ∨ (¬ p4318) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial6538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4317)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory705 (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8)
  exact rule6538 (meaning t m 3324) (meaning t m 4317) (meaning t m 4318) (meaning t m 4319) source

theorem rule6539 (p3952 p4204 p4320 : Prop) (h : (¬ p3952) ∨ (¬ p4204) ∨ p4320) : (¬ p3952) ∨ (¬ p4204) ∨ (p4320) := by
  classical
  tauto

theorem initial6539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4204)) ∨ (meaning t m 4320) := by
  have source := ElevenTheory.theory706 (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule6539 (meaning t m 3952) (meaning t m 4204) (meaning t m 4320) source

theorem rule6540 (p2573 p3540 p3920 : Prop) (h : (¬ p3540) ∨ (¬ p3920) ∨ (¬ p2573)) : (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3920) := by
  classical
  tauto

theorem initial6540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3920)) := by
  have source := ElevenTheory.theory707 (m.theta 0 4) (m.theta 4 6) (m.theta 4 7)
  exact rule6540 (meaning t m 2573) (meaning t m 3540) (meaning t m 3920) source

end SunPrize.SMT
