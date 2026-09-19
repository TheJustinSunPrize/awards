import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory044
import SunPrize.Certificate.Theory045
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule25874 (p2027 p2247 p2744 p3449 p3688 p4009 p4288 p4347 p4358 p5122 : Prop) (h : (¬ p4288) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p2247) ∨ (¬ p5122) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p4009) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3449) ∨ (¬ p3688) ∨ (¬ p4009) ∨ (¬ p4288) ∨ (¬ p4347) ∨ (¬ p4358) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial25874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15130 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25874 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3449) (meaning t m 3688) (meaning t m 4009) (meaning t m 4288) (meaning t m 4347) (meaning t m 4358) (meaning t m 5122) source

theorem rule25875 (p2027 p2247 p2744 p3688 p3707 p3830 p4358 p5123 p5580 : Prop) (h : (¬ p2744) ∨ (¬ p5123) ∨ (¬ p3830) ∨ (¬ p5580) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p3707) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3688) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4358) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial25875 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory15131 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule25875 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3688) (meaning t m 3707) (meaning t m 3830) (meaning t m 4358) (meaning t m 5123) (meaning t m 5580) source

theorem rule25876 (p2027 p2210 p2247 p2387 p2744 p2819 p2891 p3204 p3822 p3953 p4556 : Prop) (h : (¬ p3204) ∨ (¬ p3953) ∨ (¬ p3822) ∨ (¬ p2387) ∨ (¬ p2247) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4556) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2387) ∨ (¬ p2744) ∨ (¬ p2819) ∨ (¬ p2891) ∨ (¬ p3204) ∨ (¬ p3822) ∨ (¬ p3953) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial25876 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory15132 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 2 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule25876 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2387) (meaning t m 2744) (meaning t m 2819) (meaning t m 2891) (meaning t m 3204) (meaning t m 3822) (meaning t m 3953) (meaning t m 4556) source

theorem rule25878 (p2027 p2210 p3038 p3631 p3821 p4959 p5206 : Prop) (h : (¬ p5206) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p3038) ∨ (¬ p2210) ∨ (¬ p4959) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p3038) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4959) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial25878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3038)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4959)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory15134 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 7 9)
  exact rule25878 (meaning t m 2027) (meaning t m 2210) (meaning t m 3038) (meaning t m 3631) (meaning t m 3821) (meaning t m 4959) (meaning t m 5206) source

theorem rule25880 (p2027 p2247 p2470 p2509 p2744 p4079 p4257 : Prop) (h : (¬ p4079) ∨ (¬ p2470) ∨ (¬ p2247) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p4257)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2744) ∨ (¬ p4079) ∨ (¬ p4257) := by
  classical
  tauto

theorem initial25880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) := by
  have source := ElevenTheory.theory15136 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 4 8)
  exact rule25880 (meaning t m 2027) (meaning t m 2247) (meaning t m 2470) (meaning t m 2509) (meaning t m 2744) (meaning t m 4079) (meaning t m 4257) source

theorem rule25882 (p2027 p2934 p3238 p3631 p3821 p4279 p4646 : Prop) (h : p2027 ∨ (¬ p4279) ∨ (¬ p4646) ∨ (¬ p3238) ∨ (¬ p3631) ∨ (¬ p2934) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial25882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory15138 t (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule25882 (meaning t m 2027) (meaning t m 2934) (meaning t m 3238) (meaning t m 3631) (meaning t m 3821) (meaning t m 4279) (meaning t m 4646) source

theorem rule25884 (p2027 p2313 p2383 p3550 p3570 p4556 : Prop) (h : (¬ p2383) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p3550) ∨ (¬ p4556) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p3570) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial25884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory15140 t (m.theta 0 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule25884 (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3550) (meaning t m 3570) (meaning t m 4556) source

theorem rule25885 (p2027 p2341 p3570 p3646 p4558 p4988 : Prop) (h : (¬ p2341) ∨ (¬ p4988) ∨ (¬ p4558) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3646)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4558) ∨ (¬ p4988) := by
  classical
  tauto

theorem initial25885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4558)) ∨ (¬ (meaning t m 4988)) := by
  have source := ElevenTheory.theory15141 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule25885 (meaning t m 2027) (meaning t m 2341) (meaning t m 3570) (meaning t m 3646) (meaning t m 4558) (meaning t m 4988) source

theorem rule25886 (p2027 p2341 p3570 p4032 p4988 p5102 : Prop) (h : (¬ p4988) ∨ (¬ p3570) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p5102) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p4032) ∨ (¬ p4988) ∨ (¬ p5102) := by
  classical
  tauto

theorem initial25886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4988)) ∨ (¬ (meaning t m 5102)) := by
  have source := ElevenTheory.theory15142 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 8)
  exact rule25886 (meaning t m 2027) (meaning t m 2341) (meaning t m 3570) (meaning t m 4032) (meaning t m 4988) (meaning t m 5102) source

theorem rule25888 (p1994 p2027 p2299 p2493 p2633 p2928 p3574 p3921 : Prop) (h : p2633 ∨ (¬ p2299) ∨ (¬ p3921) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p1994) ∨ (¬ p3574) ∨ (¬ p2928)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2493) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p3574) ∨ (¬ p3921) := by
  classical
  tauto

theorem initial25888 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3921)) := by
  have source := ElevenTheory.theory15144 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule25888 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2493) (meaning t m 2633) (meaning t m 2928) (meaning t m 3574) (meaning t m 3921) source

theorem rule25894 (p1998 p2027 p2114 p2177 p3093 p3309 p3954 : Prop) (h : p2027 ∨ (¬ p3309) ∨ (¬ p1998) ∨ (¬ p3954) ∨ (¬ p3093) ∨ p2114 ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial25894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory15150 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule25894 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2177) (meaning t m 3093) (meaning t m 3309) (meaning t m 3954) source

theorem rule25895 (p2505 p3379 p3591 : Prop) (h : (¬ p3379) ∨ (¬ p2505) ∨ (¬ p3591)) : (¬ p2505) ∨ (¬ p3379) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial25895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory15151 (m.theta 0 1) (m.theta 1 4) (m.theta 1 6)
  exact rule25895 (meaning t m 2505) (meaning t m 3379) (meaning t m 3591) source

theorem rule25896 (p1976 p2027 p2633 p2952 p3136 p3553 p3572 p4236 : Prop) (h : (¬ p3553) ∨ p2633 ∨ (¬ p2952) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p3572) ∨ (¬ p3136)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial25896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory15152 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule25896 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 2952) (meaning t m 3136) (meaning t m 3553) (meaning t m 3572) (meaning t m 4236) source

theorem rule25898 (p2027 p2352 p2363 p4118 p4196 p4973 : Prop) (h : (¬ p2363) ∨ (¬ p4973) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4196) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial25898 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory15154 t (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule25898 (meaning t m 2027) (meaning t m 2352) (meaning t m 2363) (meaning t m 4118) (meaning t m 4196) (meaning t m 4973) source

theorem rule25900 (p2027 p2312 p2668 p3767 p4405 p5274 p5284 p5300 : Prop) (h : (¬ p2668) ∨ (¬ p2312) ∨ p2027 ∨ (¬ p5300) ∨ (¬ p4405) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p3767)) : (p2027) ∨ (¬ p2312) ∨ (¬ p2668) ∨ (¬ p3767) ∨ (¬ p4405) ∨ (¬ p5274) ∨ (¬ p5284) ∨ (¬ p5300) := by
  classical
  tauto

theorem initial25900 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) ∨ (¬ (meaning t m 5300)) := by
  have source := ElevenTheory.theory15156 t (m.theta 0 7) (m.theta 0 9) (m.theta 3 6) (m.theta 3 9) (m.theta 6 7) (m.theta 6 8) (m.theta 9 10)
  exact rule25900 (meaning t m 2027) (meaning t m 2312) (meaning t m 2668) (meaning t m 3767) (meaning t m 4405) (meaning t m 5274) (meaning t m 5284) (meaning t m 5300) source

theorem rule25901 (p2027 p2137 p3051 p3367 p3486 p4874 p4881 : Prop) (h : (¬ p3051) ∨ (¬ p4874) ∨ (¬ p3486) ∨ (¬ p2137) ∨ (¬ p4881) ∨ p2027 ∨ (¬ p3367)) : (p2027) ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3367) ∨ (¬ p3486) ∨ (¬ p4874) ∨ (¬ p4881) := by
  classical
  tauto

theorem initial25901 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 4881)) := by
  have source := ElevenTheory.theory15157 t (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule25901 (meaning t m 2027) (meaning t m 2137) (meaning t m 3051) (meaning t m 3367) (meaning t m 3486) (meaning t m 4874) (meaning t m 4881) source

theorem rule25902 (p1995 p2114 p3367 p5214 : Prop) (h : p2114 ∨ p5214 ∨ (¬ p3367) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2114) ∨ (¬ p3367) ∨ (p5214) := by
  classical
  tauto

theorem initial25902 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 5214) := by
  have source := ElevenTheory.theory15158 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 4)
  exact rule25902 (meaning t m 1995) (meaning t m 2114) (meaning t m 3367) (meaning t m 5214) source

theorem rule25906 (p2027 p2839 p2928 p3201 p3475 p4257 p5052 : Prop) (h : (¬ p4257) ∨ (¬ p2928) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p2839) ∨ (¬ p3201) ∨ (¬ p3475)) : (p2027) ∨ (¬ p2839) ∨ (¬ p2928) ∨ (¬ p3201) ∨ (¬ p3475) ∨ (¬ p4257) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial25906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory15162 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7)
  exact rule25906 (meaning t m 2027) (meaning t m 2839) (meaning t m 2928) (meaning t m 3201) (meaning t m 3475) (meaning t m 4257) (meaning t m 5052) source

theorem rule25907 (p2027 p2406 p2598 p2780 p3590 p4342 p4715 : Prop) (h : (¬ p4715) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3590) ∨ (¬ p2406) ∨ (¬ p4342) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p3590) ∨ (¬ p4342) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial25907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory15163 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6)
  exact rule25907 (meaning t m 2027) (meaning t m 2406) (meaning t m 2598) (meaning t m 2780) (meaning t m 3590) (meaning t m 4342) (meaning t m 4715) source

theorem rule25910 (p2027 p2299 p3156 p4042 p4320 p4559 : Prop) (h : (¬ p4320) ∨ (¬ p3156) ∨ (¬ p4042) ∨ (¬ p4559) ∨ (¬ p2299) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p3156) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial25910 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory15166 t (m.theta 3 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule25910 (meaning t m 2027) (meaning t m 2299) (meaning t m 3156) (meaning t m 4042) (meaning t m 4320) (meaning t m 4559) source

theorem rule25911 (p2027 p2220 p2958 p2963 p3497 p4700 p4972 : Prop) (h : (¬ p2963) ∨ p2027 ∨ (¬ p4700) ∨ (¬ p3497) ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p4972)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p2963) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial25911 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15167 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule25911 (meaning t m 2027) (meaning t m 2220) (meaning t m 2958) (meaning t m 2963) (meaning t m 3497) (meaning t m 4700) (meaning t m 4972) source

theorem rule25916 (p3178 p4104 p4590 : Prop) (h : (¬ p4590) ∨ (¬ p4104) ∨ p3178) : (p3178) ∨ (¬ p4104) ∨ (¬ p4590) := by
  classical
  tauto

theorem initial25916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3178) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4590)) := by
  have source := ElevenTheory.theory15172 (m.theta 0 3) (m.theta 0 7) (m.theta 0 8)
  exact rule25916 (meaning t m 3178) (meaning t m 4104) (meaning t m 4590) source

theorem rule25917 (p2027 p2247 p2579 p2744 p3366 p3399 p3631 p3905 p3950 p3956 p4347 : Prop) (h : (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2247) ∨ (¬ p3631) ∨ (¬ p3399) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3950) ∨ (¬ p2579) ∨ (¬ p3905)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3905) ∨ (¬ p3950) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial25917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory15173 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 4 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule25917 (meaning t m 2027) (meaning t m 2247) (meaning t m 2579) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3631) (meaning t m 3905) (meaning t m 3950) (meaning t m 3956) (meaning t m 4347) source

theorem rule25918 (p2027 p2248 p2331 p2509 p2534 p2668 p3452 p3979 p5122 : Prop) (h : (¬ p2534) ∨ (¬ p2509) ∨ (¬ p3452) ∨ (¬ p5122) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p3979)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p3452) ∨ (¬ p3979) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial25918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15174 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25918 (meaning t m 2027) (meaning t m 2248) (meaning t m 2331) (meaning t m 2509) (meaning t m 2534) (meaning t m 2668) (meaning t m 3452) (meaning t m 3979) (meaning t m 5122) source

theorem rule25920 (p2027 p2138 p2247 p2744 p3222 p3366 p3379 p3692 p3694 p4332 : Prop) (h : (¬ p3694) ∨ (¬ p3366) ∨ (¬ p3222) ∨ (¬ p3379) ∨ (¬ p4332) ∨ (¬ p2247) ∨ (¬ p2138) ∨ (¬ p2744) ∨ (¬ p3692) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3222) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p4332) := by
  classical
  tauto

theorem initial25920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4332)) := by
  have source := ElevenTheory.theory15176 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule25920 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3222) (meaning t m 3366) (meaning t m 3379) (meaning t m 3692) (meaning t m 3694) (meaning t m 4332) source

theorem rule25922 (p3434 p3631 p4424 : Prop) (h : (¬ p3631) ∨ (¬ p4424) ∨ p3434) : (p3434) ∨ (¬ p3631) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial25922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3434) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory15178 (m.theta 1 7) (m.theta 2 7) (m.theta 7 9)
  exact rule25922 (meaning t m 3434) (meaning t m 3631) (meaning t m 4424) source

theorem rule25924 (p1982 p2027 p2363 p2622 p2743 p2819 p2829 : Prop) (h : (¬ p2819) ∨ p2622 ∨ (¬ p2363) ∨ (¬ p1982) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2743)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2819) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial25924 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory15180 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule25924 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2622) (meaning t m 2743) (meaning t m 2819) (meaning t m 2829) source

theorem rule25925 (p1982 p2027 p2114 p2363 p2668 p2737 p2797 : Prop) (h : (¬ p2737) ∨ p2114 ∨ (¬ p2668) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2797)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p2797) := by
  classical
  tauto

theorem initial25925 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) := by
  have source := ElevenTheory.theory15181 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule25925 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2363) (meaning t m 2668) (meaning t m 2737) (meaning t m 2797) source

theorem rule25929 (p2010 p2027 p2766 p3644 p3979 p4347 p5558 : Prop) (h : (¬ p4347) ∨ p2766 ∨ p2027 ∨ (¬ p2010) ∨ (¬ p3644) ∨ (¬ p3979) ∨ (¬ p5558)) : (¬ p2010) ∨ (p2027) ∨ (p2766) ∨ (¬ p3644) ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial25929 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory15185 t (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule25929 (meaning t m 2010) (meaning t m 2027) (meaning t m 2766) (meaning t m 3644) (meaning t m 3979) (meaning t m 4347) (meaning t m 5558) source

theorem rule25935 (p2542 p3878 p4355 p4437 : Prop) (h : (¬ p3878) ∨ (¬ p4437) ∨ (¬ p2542) ∨ (¬ p4355)) : (¬ p2542) ∨ (¬ p3878) ∨ (¬ p4355) ∨ (¬ p4437) := by
  classical
  tauto

theorem initial25935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 4355)) ∨ (¬ (meaning t m 4437)) := by
  have source := ElevenTheory.theory15191 (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8)
  exact rule25935 (meaning t m 2542) (meaning t m 3878) (meaning t m 4355) (meaning t m 4437) source

theorem rule25937 (p2027 p2192 p2210 p2274 p2476 p3641 p3876 p3905 p4712 p4736 : Prop) (h : (¬ p2476) ∨ (¬ p2210) ∨ (¬ p3641) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p4712) ∨ (¬ p2274) ∨ (¬ p3876) ∨ (¬ p4736) ∨ (¬ p2192)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p4712) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial25937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4712)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory15193 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule25937 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2274) (meaning t m 2476) (meaning t m 3641) (meaning t m 3876) (meaning t m 3905) (meaning t m 4712) (meaning t m 4736) source

theorem rule25939 (p1995 p2287 p2499 p4976 : Prop) (h : p2287 ∨ (¬ p2499) ∨ (¬ p1995) ∨ p4976) : (¬ p1995) ∨ (p2287) ∨ (¬ p2499) ∨ (p4976) := by
  classical
  tauto

theorem initial25939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 4976) := by
  have source := ElevenTheory.theory15195 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6)
  exact rule25939 (meaning t m 1995) (meaning t m 2287) (meaning t m 2499) (meaning t m 4976) source

theorem rule25940 (p3016 p3422 p4343 : Prop) (h : (¬ p3422) ∨ (¬ p4343) ∨ p3016) : (p3016) ∨ (¬ p3422) ∨ (¬ p4343) := by
  classical
  tauto

theorem initial25940 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3016) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4343)) := by
  have source := ElevenTheory.theory15196 (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule25940 (meaning t m 3016) (meaning t m 3422) (meaning t m 4343) source

theorem rule25942 (p1979 p2027 p2132 p2192 p2622 p3365 p3952 p4418 : Prop) (h : p2622 ∨ (¬ p1979) ∨ (¬ p2132) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2192) ∨ (¬ p4418)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2192) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4418) := by
  classical
  tauto

theorem initial25942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4418)) := by
  have source := ElevenTheory.theory15198 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule25942 (meaning t m 1979) (meaning t m 2027) (meaning t m 2132) (meaning t m 2192) (meaning t m 2622) (meaning t m 3365) (meaning t m 3952) (meaning t m 4418) source

theorem rule25943 (p2027 p2156 p2437 p3952 p4109 p4646 p4700 : Prop) (h : (¬ p3952) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p4109) ∨ (¬ p4646) ∨ (¬ p2437) ∨ (¬ p4700)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2437) ∨ (¬ p3952) ∨ (¬ p4109) ∨ (¬ p4646) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial25943 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory15199 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule25943 (meaning t m 2027) (meaning t m 2156) (meaning t m 2437) (meaning t m 3952) (meaning t m 4109) (meaning t m 4646) (meaning t m 4700) source

theorem rule25946 (p2027 p2248 p2928 p3166 p3256 p3452 p3644 p4133 p4347 : Prop) (h : (¬ p3452) ∨ (¬ p3256) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p4347) ∨ (¬ p4133) ∨ (¬ p2928) ∨ (¬ p2248)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial25946 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory15202 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule25946 (meaning t m 2027) (meaning t m 2248) (meaning t m 2928) (meaning t m 3166) (meaning t m 3256) (meaning t m 3452) (meaning t m 3644) (meaning t m 4133) (meaning t m 4347) source

theorem rule25947 (p2027 p2138 p3471 p4320 p4344 p5053 : Prop) (h : (¬ p4320) ∨ (¬ p5053) ∨ (¬ p3471) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p4344)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p4320) ∨ (¬ p4344) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial25947 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory15203 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7)
  exact rule25947 (meaning t m 2027) (meaning t m 2138) (meaning t m 3471) (meaning t m 4320) (meaning t m 4344) (meaning t m 5053) source

theorem rule25948 (p2027 p2958 p2963 p3051 p4320 p4700 p4972 : Prop) (h : (¬ p4972) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4700) ∨ (¬ p4320) ∨ (¬ p2958) ∨ (¬ p3051)) : (p2027) ∨ (¬ p2958) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial25948 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15204 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule25948 (meaning t m 2027) (meaning t m 2958) (meaning t m 2963) (meaning t m 3051) (meaning t m 4320) (meaning t m 4700) (meaning t m 4972) source

theorem rule25949 (p1983 p2027 p2611 p2717 p3246 p3471 p3570 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p1983) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3570) ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (p2611) ∨ (¬ p2717) ∨ (¬ p3246) ∨ (¬ p3471) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial25949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory15205 t (m.theta 0 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25949 (meaning t m 1983) (meaning t m 2027) (meaning t m 2611) (meaning t m 2717) (meaning t m 3246) (meaning t m 3471) (meaning t m 3570) source

theorem rule25950 (p1994 p2027 p2493 p2764 p3193 p3574 p4022 p4191 : Prop) (h : p2027 ∨ (¬ p4022) ∨ (¬ p1994) ∨ (¬ p3574) ∨ (¬ p2493) ∨ p2764 ∨ (¬ p4191) ∨ (¬ p3193)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2493) ∨ (p2764) ∨ (¬ p3193) ∨ (¬ p3574) ∨ (¬ p4022) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial25950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory15206 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule25950 (meaning t m 1994) (meaning t m 2027) (meaning t m 2493) (meaning t m 2764) (meaning t m 3193) (meaning t m 3574) (meaning t m 4022) (meaning t m 4191) source

theorem rule25951 (p2001 p2027 p2619 p2699 p2839 p3471 p3588 p3589 : Prop) (h : p2699 ∨ (¬ p3588) ∨ p2027 ∨ (¬ p2001) ∨ (¬ p2619) ∨ (¬ p3589) ∨ (¬ p2839) ∨ (¬ p3471)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2619) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p3471) ∨ (¬ p3588) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial25951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory15207 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 7) (m.theta 5 8)
  exact rule25951 (meaning t m 2001) (meaning t m 2027) (meaning t m 2619) (meaning t m 2699) (meaning t m 2839) (meaning t m 3471) (meaning t m 3588) (meaning t m 3589) source

theorem rule25952 (p2352 p2819 p4342 : Prop) (h : (¬ p4342) ∨ (¬ p2819) ∨ p2352) : (p2352) ∨ (¬ p2819) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial25952 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2352) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory15208 (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule25952 (meaning t m 2352) (meaning t m 2819) (meaning t m 4342) source

theorem rule25954 (p2819 p3956 p4342 : Prop) (h : (¬ p4342) ∨ (¬ p2819) ∨ (¬ p3956)) : (¬ p2819) ∨ (¬ p3956) ∨ (¬ p4342) := by
  classical
  tauto

theorem initial25954 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4342)) := by
  have source := ElevenTheory.theory15210 (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule25954 (meaning t m 2819) (meaning t m 3956) (meaning t m 4342) source

theorem rule25955 (p2166 p3537 p4188 p4874 : Prop) (h : (¬ p3537) ∨ (¬ p4188) ∨ (¬ p4874) ∨ p2166) : (p2166) ∨ (¬ p3537) ∨ (¬ p4188) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial25955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2166) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4188)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory15211 (m.theta 1 2) (m.theta 1 5) (m.theta 2 8) (m.theta 5 8)
  exact rule25955 (meaning t m 2166) (meaning t m 3537) (meaning t m 4188) (meaning t m 4874) source

theorem rule25957 (p2027 p2210 p2579 p2588 p2881 p2891 p4107 p4666 p5193 : Prop) (h : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2881)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4107) ∨ (¬ p4666) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial25957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory15213 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25957 (meaning t m 2027) (meaning t m 2210) (meaning t m 2579) (meaning t m 2588) (meaning t m 2881) (meaning t m 2891) (meaning t m 4107) (meaning t m 4666) (meaning t m 5193) source

theorem rule25958 (p2027 p3365 p3366 p3399 p3527 p3555 p3572 p3947 p4377 p4666 : Prop) (h : (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p3947) ∨ (¬ p3555) ∨ (¬ p3527) ∨ (¬ p4377)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4377) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial25958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15214 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule25958 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3555) (meaning t m 3572) (meaning t m 3947) (meaning t m 4377) (meaning t m 4666) source

theorem rule25959 (p2027 p2417 p3097 p3920 p4107 p4718 : Prop) (h : (¬ p4107) ∨ (¬ p3920) ∨ (¬ p4718) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3097) ∨ (¬ p3920) ∨ (¬ p4107) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial25959 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory15215 t (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule25959 (meaning t m 2027) (meaning t m 2417) (meaning t m 3097) (meaning t m 3920) (meaning t m 4107) (meaning t m 4718) source

theorem rule25960 (p1977 p2027 p2202 p2241 p2440 p2476 p3083 p4108 : Prop) (h : p2027 ∨ (¬ p4108) ∨ p2202 ∨ (¬ p2476) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p1977) ∨ (¬ p2241)) : (¬ p1977) ∨ (p2027) ∨ (p2202) ∨ (¬ p2241) ∨ (¬ p2440) ∨ (¬ p2476) ∨ (¬ p3083) ∨ (¬ p4108) := by
  classical
  tauto

theorem initial25960 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 4108)) := by
  have source := ElevenTheory.theory15216 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule25960 (meaning t m 1977) (meaning t m 2027) (meaning t m 2202) (meaning t m 2241) (meaning t m 2440) (meaning t m 2476) (meaning t m 3083) (meaning t m 4108) source

theorem rule25961 (p2573 p3363 p3422 : Prop) (h : (¬ p3363) ∨ (¬ p3422) ∨ p2573) : (p2573) ∨ (¬ p3363) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial25961 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2573) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory15217 (m.theta 0 4) (m.theta 2 4) (m.theta 4 6)
  exact rule25961 (meaning t m 2573) (meaning t m 3363) (meaning t m 3422) source

theorem rule25963 (p2027 p2619 p3097 p3758 p4405 p4441 : Prop) (h : (¬ p4405) ∨ (¬ p4441) ∨ (¬ p3097) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2619)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3097) ∨ (¬ p3758) ∨ (¬ p4405) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial25963 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory15219 t (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule25963 (meaning t m 2027) (meaning t m 2619) (meaning t m 3097) (meaning t m 3758) (meaning t m 4405) (meaning t m 4441) source

theorem rule25967 (p3583 p3688 p4193 : Prop) (h : (¬ p3583) ∨ (¬ p4193) ∨ p3688) : (¬ p3583) ∨ (p3688) ∨ (¬ p4193) := by
  classical
  tauto

theorem initial25967 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3583)) ∨ (meaning t m 3688) ∨ (¬ (meaning t m 4193)) := by
  have source := ElevenTheory.theory15223 (m.theta 1 2) (m.theta 2 5) (m.theta 2 6)
  exact rule25967 (meaning t m 3583) (meaning t m 3688) (meaning t m 4193) source

theorem rule25968 (p2027 p2088 p3005 p3180 p4035 p5107 : Prop) (h : (¬ p4035) ∨ (¬ p5107) ∨ (¬ p2088) ∨ (¬ p3180) ∨ (¬ p3005) ∨ p2027) : (p2027) ∨ (¬ p2088) ∨ (¬ p3005) ∨ (¬ p3180) ∨ (¬ p4035) ∨ (¬ p5107) := by
  classical
  tauto

theorem initial25968 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3180)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5107)) := by
  have source := ElevenTheory.theory15224 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 8) (m.theta 3 9) (m.theta 8 9)
  exact rule25968 (meaning t m 2027) (meaning t m 2088) (meaning t m 3005) (meaning t m 3180) (meaning t m 4035) (meaning t m 5107) source

theorem rule25969 (p2027 p2187 p2307 p2509 p2608 p2962 p3097 p3370 p3452 p4377 p4384 : Prop) (h : (¬ p2962) ∨ (¬ p2608) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p4377) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p3097) ∨ (¬ p2509) ∨ (¬ p2307) ∨ (¬ p4384)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4377) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial25969 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory15225 t (m.theta 0 1) (m.theta 0 5) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25969 (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2509) (meaning t m 2608) (meaning t m 2962) (meaning t m 3097) (meaning t m 3370) (meaning t m 3452) (meaning t m 4377) (meaning t m 4384) source

theorem rule25970 (p2027 p2132 p2870 p3193 p3452 p4129 p4425 p4733 p4826 : Prop) (h : (¬ p3193) ∨ (¬ p4826) ∨ (¬ p4425) ∨ (¬ p4733) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p3452) ∨ (¬ p4129) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4129) ∨ (¬ p4425) ∨ (¬ p4733) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial25970 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory15226 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 5) (m.theta 4 9) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule25970 (meaning t m 2027) (meaning t m 2132) (meaning t m 2870) (meaning t m 3193) (meaning t m 3452) (meaning t m 4129) (meaning t m 4425) (meaning t m 4733) (meaning t m 4826) source

theorem rule25971 (p2027 p2651 p2685 p2745 p3414 p4111 : Prop) (h : (¬ p4111) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p2745) ∨ (¬ p2651) ∨ (¬ p2685)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3414) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial25971 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory15227 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule25971 (meaning t m 2027) (meaning t m 2651) (meaning t m 2685) (meaning t m 2745) (meaning t m 3414) (meaning t m 4111) source

theorem rule25972 (p1977 p2027 p2352 p2387 p2577 p2588 p2662 p2997 p4111 : Prop) (h : (¬ p2577) ∨ (¬ p2387) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p1977) ∨ p2997 ∨ (¬ p2662) ∨ (¬ p2588)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (p2997) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial25972 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory15228 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25972 (meaning t m 1977) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2577) (meaning t m 2588) (meaning t m 2662) (meaning t m 2997) (meaning t m 4111) source

theorem rule25979 (p2027 p2668 p3791 p4067 p4391 p4405 : Prop) (h : p2027 ∨ (¬ p4405) ∨ (¬ p3791) ∨ (¬ p4391) ∨ (¬ p4067) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p4391) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial25979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4391)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory15235 t (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule25979 (meaning t m 2027) (meaning t m 2668) (meaning t m 3791) (meaning t m 4067) (meaning t m 4391) (meaning t m 4405) source

theorem rule25984 (p1975 p2027 p2274 p2542 p2545 p2962 p3654 p3744 p4109 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p2542) ∨ (¬ p4109) ∨ (¬ p1975) ∨ (¬ p2962) ∨ (¬ p3744) ∨ (¬ p3654) ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p2962) ∨ (¬ p3654) ∨ (¬ p3744) ∨ (¬ p4109) := by
  classical
  tauto

theorem initial25984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4109)) := by
  have source := ElevenTheory.theory15240 t (m.theta 0 5) (m.theta 0 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule25984 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2542) (meaning t m 2545) (meaning t m 2962) (meaning t m 3654) (meaning t m 3744) (meaning t m 4109) source

theorem rule25989 (p2027 p2138 p2341 p3097 p3367 p3644 p3759 p4173 p4243 p4276 p4734 p5201 : Prop) (h : (¬ p5201) ∨ (¬ p4243) ∨ (¬ p2341) ∨ (¬ p3097) ∨ (¬ p4734) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3644) ∨ (¬ p4173) ∨ (¬ p2138) ∨ (¬ p4276)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2341) ∨ (¬ p3097) ∨ (¬ p3367) ∨ (¬ p3644) ∨ (¬ p3759) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4276) ∨ (¬ p4734) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial25989 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4734)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory15245 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule25989 (meaning t m 2027) (meaning t m 2138) (meaning t m 2341) (meaning t m 3097) (meaning t m 3367) (meaning t m 3644) (meaning t m 3759) (meaning t m 4173) (meaning t m 4243) (meaning t m 4276) (meaning t m 4734) (meaning t m 5201) source

theorem rule25993 (p2027 p3073 p3857 p3859 p3961 p4111 p4155 p4652 : Prop) (h : p2027 ∨ (¬ p4652) ∨ (¬ p3859) ∨ (¬ p3073) ∨ (¬ p4155) ∨ (¬ p4111) ∨ (¬ p3961) ∨ (¬ p3857)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p3859) ∨ (¬ p3961) ∨ (¬ p4111) ∨ (¬ p4155) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial25993 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory15249 t (m.theta 0 7) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 3 4) (m.theta 3 7) (m.theta 8 9)
  exact rule25993 (meaning t m 2027) (meaning t m 3073) (meaning t m 3857) (meaning t m 3859) (meaning t m 3961) (meaning t m 4111) (meaning t m 4155) (meaning t m 4652) source

theorem rule25995 (p2027 p2295 p2387 p2819 p3822 p4581 : Prop) (h : (¬ p2819) ∨ (¬ p2295) ∨ (¬ p3822) ∨ (¬ p4581) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2387) ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p4581) := by
  classical
  tauto

theorem initial25995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4581)) := by
  have source := ElevenTheory.theory15251 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule25995 (meaning t m 2027) (meaning t m 2295) (meaning t m 2387) (meaning t m 2819) (meaning t m 3822) (meaning t m 4581) source

theorem rule25997 (p2027 p2341 p3346 p3644 p4637 p5201 : Prop) (h : (¬ p4637) ∨ (¬ p3644) ∨ (¬ p5201) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p4637) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial25997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4637)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory15253 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8)
  exact rule25997 (meaning t m 2027) (meaning t m 2341) (meaning t m 3346) (meaning t m 3644) (meaning t m 4637) (meaning t m 5201) source

theorem rule26001 (p2027 p2138 p2774 p3758 p3958 p4390 : Prop) (h : (¬ p4390) ∨ (¬ p2138) ∨ (¬ p3958) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2774) ∨ (¬ p3758) ∨ (¬ p3958) ∨ (¬ p4390) := by
  classical
  tauto

theorem initial26001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4390)) := by
  have source := ElevenTheory.theory15257 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 4 6) (m.theta 5 6)
  exact rule26001 (meaning t m 2027) (meaning t m 2138) (meaning t m 2774) (meaning t m 3758) (meaning t m 3958) (meaning t m 4390) source

theorem rule26003 (p1991 p2027 p2914 p2952 p2992 p3742 p4111 : Prop) (h : (¬ p1991) ∨ (¬ p4111) ∨ (¬ p2952) ∨ (¬ p2992) ∨ p2027 ∨ p2914 ∨ (¬ p3742)) : (¬ p1991) ∨ (p2027) ∨ (p2914) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3742) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial26003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory15259 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule26003 (meaning t m 1991) (meaning t m 2027) (meaning t m 2914) (meaning t m 2952) (meaning t m 2992) (meaning t m 3742) (meaning t m 4111) source

theorem rule26007 (p3096 p3564 p3744 : Prop) (h : (¬ p3564) ∨ (¬ p3744) ∨ (¬ p3096)) : (¬ p3096) ∨ (¬ p3564) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial26007 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory15263 (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule26007 (meaning t m 3096) (meaning t m 3564) (meaning t m 3744) source

theorem rule26008 (p2027 p2245 p2608 p2744 p3027 p3414 : Prop) (h : (¬ p2245) ∨ (¬ p2744) ∨ (¬ p3414) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p2608)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3027) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial26008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory15264 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 7)
  exact rule26008 (meaning t m 2027) (meaning t m 2245) (meaning t m 2608) (meaning t m 2744) (meaning t m 3027) (meaning t m 3414) source

theorem rule26011 (p2010 p2027 p2462 p3644 p4019 p4324 p4805 p5558 : Prop) (h : (¬ p4019) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p5558) ∨ (¬ p4805) ∨ (¬ p2010) ∨ p2462 ∨ (¬ p4324)) : (¬ p2010) ∨ (p2027) ∨ (p2462) ∨ (¬ p3644) ∨ (¬ p4019) ∨ (¬ p4324) ∨ (¬ p4805) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial26011 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory15267 t (m.theta 2 7) (m.theta 2 8) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule26011 (meaning t m 2010) (meaning t m 2027) (meaning t m 2462) (meaning t m 3644) (meaning t m 4019) (meaning t m 4324) (meaning t m 4805) (meaning t m 5558) source

theorem rule26015 (p1988 p2027 p2307 p2396 p2578 p2761 p2842 p3422 : Prop) (h : (¬ p2761) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2396) ∨ p2842 ∨ (¬ p2307) ∨ (¬ p2578) ∨ (¬ p3422)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2578) ∨ (¬ p2761) ∨ (p2842) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial26015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory15271 t (m.theta 0 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule26015 (meaning t m 1988) (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2578) (meaning t m 2761) (meaning t m 2842) (meaning t m 3422) source

theorem rule26018 (p1988 p2027 p2307 p2396 p2622 p2761 p2797 p3567 : Prop) (h : (¬ p2396) ∨ (¬ p3567) ∨ p2027 ∨ (¬ p2797) ∨ p2622 ∨ (¬ p2307) ∨ (¬ p2761) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (p2622) ∨ (¬ p2761) ∨ (¬ p2797) ∨ (¬ p3567) := by
  classical
  tauto

theorem initial26018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) := by
  have source := ElevenTheory.theory15274 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule26018 (meaning t m 1988) (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2622) (meaning t m 2761) (meaning t m 2797) (meaning t m 3567) source

theorem rule26020 (p2027 p2246 p2363 p2383 p2608 p2744 p3555 p3694 p3987 p4348 p4418 p4905 : Prop) (h : (¬ p4418) ∨ (¬ p3987) ∨ (¬ p3555) ∨ (¬ p4905) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2608) ∨ (¬ p2363) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3555) ∨ (¬ p3694) ∨ (¬ p3987) ∨ (¬ p4348) ∨ (¬ p4418) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial26020 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4418)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory15276 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26020 (meaning t m 2027) (meaning t m 2246) (meaning t m 2363) (meaning t m 2383) (meaning t m 2608) (meaning t m 2744) (meaning t m 3555) (meaning t m 3694) (meaning t m 3987) (meaning t m 4348) (meaning t m 4418) (meaning t m 4905) source

theorem rule26023 (p1998 p2027 p2230 p2427 p2622 p2630 p2881 p3519 p4116 : Prop) (h : p2622 ∨ (¬ p3519) ∨ (¬ p4116) ∨ (¬ p1998) ∨ (¬ p2630) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2427)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial26023 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory15279 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule26023 (meaning t m 1998) (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2622) (meaning t m 2630) (meaning t m 2881) (meaning t m 3519) (meaning t m 4116) source

theorem rule26027 (p1987 p2027 p2545 p3073 p3859 p4111 p4118 p4195 p4196 : Prop) (h : (¬ p3073) ∨ (¬ p4196) ∨ (¬ p3859) ∨ (¬ p4195) ∨ (¬ p4118) ∨ p2027 ∨ p2545 ∨ (¬ p1987) ∨ (¬ p4111)) : (¬ p1987) ∨ (p2027) ∨ (p2545) ∨ (¬ p3073) ∨ (¬ p3859) ∨ (¬ p4111) ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial26027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3859)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory15283 t (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule26027 (meaning t m 1987) (meaning t m 2027) (meaning t m 2545) (meaning t m 3073) (meaning t m 3859) (meaning t m 4111) (meaning t m 4118) (meaning t m 4195) (meaning t m 4196) source

theorem rule26029 (p1981 p2027 p2202 p2510 p2528 p2573 p2589 p4347 : Prop) (h : (¬ p2573) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p2589) ∨ p2202 ∨ (¬ p1981) ∨ (¬ p2528) ∨ (¬ p2510)) : (¬ p1981) ∨ (p2027) ∨ (p2202) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial26029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory15285 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26029 (meaning t m 1981) (meaning t m 2027) (meaning t m 2202) (meaning t m 2510) (meaning t m 2528) (meaning t m 2573) (meaning t m 2589) (meaning t m 4347) source

theorem rule26031 (p1997 p2027 p2169 p2363 p2534 p2850 p3874 : Prop) (h : (¬ p2850) ∨ (¬ p1997) ∨ (¬ p2363) ∨ (¬ p3874) ∨ p2169 ∨ p2027 ∨ (¬ p2534)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2850) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial26031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory15287 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26031 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 2850) (meaning t m 3874) source

theorem rule26032 (p1997 p2027 p2169 p2363 p2481 p2850 p3857 p3874 : Prop) (h : p2169 ∨ (¬ p2850) ∨ (¬ p1997) ∨ (¬ p3857) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p2481)) : (¬ p1997) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2481) ∨ (¬ p2850) ∨ (¬ p3857) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial26032 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory15288 t (m.theta 0 8) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule26032 (meaning t m 1997) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2481) (meaning t m 2850) (meaning t m 3857) (meaning t m 3874) source

theorem rule26033 (p1998 p2027 p2766 p2881 p3266 p3690 p4191 p4623 : Prop) (h : (¬ p4191) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p4623) ∨ (¬ p3690) ∨ (¬ p2881) ∨ (¬ p1998) ∨ p2766) : (¬ p1998) ∨ (p2027) ∨ (p2766) ∨ (¬ p2881) ∨ (¬ p3266) ∨ (¬ p3690) ∨ (¬ p4191) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial26033 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory15289 t (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26033 (meaning t m 1998) (meaning t m 2027) (meaning t m 2766) (meaning t m 2881) (meaning t m 3266) (meaning t m 3690) (meaning t m 4191) (meaning t m 4623) source

theorem rule26036 (p1985 p2027 p2264 p2611 p2696 p2995 p3136 p3570 : Prop) (h : p2027 ∨ (¬ p1985) ∨ p2611 ∨ (¬ p2264) ∨ (¬ p3570) ∨ (¬ p3136) ∨ (¬ p2696) ∨ (¬ p2995)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2264) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2995) ∨ (¬ p3136) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial26036 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory15292 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule26036 (meaning t m 1985) (meaning t m 2027) (meaning t m 2264) (meaning t m 2611) (meaning t m 2696) (meaning t m 2995) (meaning t m 3136) (meaning t m 3570) source

theorem rule26037 (p2247 p3591 p4759 : Prop) (h : (¬ p4759) ∨ (¬ p3591) ∨ p2247) : (p2247) ∨ (¬ p3591) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial26037 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2247) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory15293 (m.theta 0 1) (m.theta 1 3) (m.theta 1 6)
  exact rule26037 (meaning t m 2247) (meaning t m 3591) (meaning t m 4759) source

theorem rule26039 (p2027 p2363 p2427 p2774 p2819 p3556 p3904 p4382 p4669 p4729 p4948 : Prop) (h : (¬ p4382) ∨ (¬ p2363) ∨ (¬ p4948) ∨ (¬ p2819) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p4729) ∨ (¬ p2427) ∨ (¬ p3904) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2427) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4382) ∨ (¬ p4669) ∨ (¬ p4729) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial26039 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory15295 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 2 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26039 (meaning t m 2027) (meaning t m 2363) (meaning t m 2427) (meaning t m 2774) (meaning t m 2819) (meaning t m 3556) (meaning t m 3904) (meaning t m 4382) (meaning t m 4669) (meaning t m 4729) (meaning t m 4948) source

theorem rule26040 (p2027 p2630 p2807 p2963 p3572 p4972 : Prop) (h : (¬ p2630) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p3572) ∨ (¬ p4972) ∨ (¬ p2807)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3572) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial26040 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15296 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule26040 (meaning t m 2027) (meaning t m 2630) (meaning t m 2807) (meaning t m 2963) (meaning t m 3572) (meaning t m 4972) source

theorem rule26041 (p2027 p2630 p2668 p4358 p4841 p4972 : Prop) (h : (¬ p4972) ∨ (¬ p4358) ∨ (¬ p2630) ∨ (¬ p4841) ∨ p2027 ∨ (¬ p2668)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2668) ∨ (¬ p4358) ∨ (¬ p4841) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial26041 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4841)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15297 t (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule26041 (meaning t m 2027) (meaning t m 2630) (meaning t m 2668) (meaning t m 4358) (meaning t m 4841) (meaning t m 4972) source

theorem rule26043 (p2027 p2373 p3136 p3877 p4312 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p3877) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p4312) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4312) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial26043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory15299 t (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule26043 (meaning t m 2027) (meaning t m 2373) (meaning t m 3136) (meaning t m 3877) (meaning t m 4312) (meaning t m 4702) source

theorem rule26044 (p2027 p2588 p3347 p3646 p3707 p3830 p3904 p3954 p4203 p4260 p4831 p5216 : Prop) (h : (¬ p2588) ∨ (¬ p5216) ∨ (¬ p3904) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4203) ∨ (¬ p3707) ∨ (¬ p4831) ∨ (¬ p3646) ∨ (¬ p3347) ∨ (¬ p4260) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2588) ∨ (¬ p3347) ∨ (¬ p3646) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4203) ∨ (¬ p4260) ∨ (¬ p4831) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial26044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory15300 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule26044 (meaning t m 2027) (meaning t m 2588) (meaning t m 3347) (meaning t m 3646) (meaning t m 3707) (meaning t m 3830) (meaning t m 3904) (meaning t m 3954) (meaning t m 4203) (meaning t m 4260) (meaning t m 4831) (meaning t m 5216) source

theorem rule26047 (p2027 p2589 p3073 p3347 p3449 p3690 p3954 p4235 p4669 p5216 : Prop) (h : (¬ p3073) ∨ (¬ p4235) ∨ (¬ p3449) ∨ (¬ p3690) ∨ (¬ p5216) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3347) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial26047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory15303 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule26047 (meaning t m 2027) (meaning t m 2589) (meaning t m 3073) (meaning t m 3347) (meaning t m 3449) (meaning t m 3690) (meaning t m 3954) (meaning t m 4235) (meaning t m 4669) (meaning t m 5216) source

theorem rule26048 (p2027 p2210 p4181 p4416 p4877 p5316 p5590 : Prop) (h : (¬ p4416) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p5590) ∨ (¬ p4877) ∨ (¬ p4181) ∨ (¬ p5316)) : (p2027) ∨ (¬ p2210) ∨ (¬ p4181) ∨ (¬ p4416) ∨ (¬ p4877) ∨ (¬ p5316) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial26048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5316)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory15304 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 8 10)
  exact rule26048 (meaning t m 2027) (meaning t m 2210) (meaning t m 4181) (meaning t m 4416) (meaning t m 4877) (meaning t m 5316) (meaning t m 5590) source

theorem rule26051 (p2027 p2396 p2696 p2742 p3027 p3276 p3552 p3585 p4641 p4737 p5158 p5387 : Prop) (h : (¬ p2742) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2696) ∨ (¬ p3276) ∨ (¬ p4737) ∨ (¬ p3027) ∨ (¬ p5387) ∨ (¬ p3552) ∨ (¬ p2396) ∨ (¬ p5158) ∨ (¬ p4641)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3276) ∨ (¬ p3552) ∨ (¬ p3585) ∨ (¬ p4641) ∨ (¬ p4737) ∨ (¬ p5158) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial26051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4641)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5158)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory15307 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 3 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule26051 (meaning t m 2027) (meaning t m 2396) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3276) (meaning t m 3552) (meaning t m 3585) (meaning t m 4641) (meaning t m 4737) (meaning t m 5158) (meaning t m 5387) source

theorem rule26053 (p1981 p2027 p2352 p2622 p2630 p3019 p3323 p4137 : Prop) (h : (¬ p3019) ∨ p2622 ∨ (¬ p3323) ∨ (¬ p4137) ∨ (¬ p1981) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2630)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial26053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory15309 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule26053 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2622) (meaning t m 2630) (meaning t m 3019) (meaning t m 3323) (meaning t m 4137) source

theorem rule26054 (p2027 p2246 p2387 p2417 p2437 p2651 p2744 p2778 p2819 p3366 p3917 p4625 : Prop) (h : (¬ p2778) ∨ (¬ p2387) ∨ (¬ p3917) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2651) ∨ (¬ p2819) ∨ (¬ p2437) ∨ (¬ p2417)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2387) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial26054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory15310 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule26054 (meaning t m 2027) (meaning t m 2246) (meaning t m 2387) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2744) (meaning t m 2778) (meaning t m 2819) (meaning t m 3366) (meaning t m 3917) (meaning t m 4625) source

theorem rule26055 (p2027 p2247 p2744 p3654 p3953 p4026 p5020 : Prop) (h : p2027 ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p3654) ∨ (¬ p3953) ∨ (¬ p5020) ∨ (¬ p4026)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3654) ∨ (¬ p3953) ∨ (¬ p4026) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial26055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory15311 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 6 9)
  exact rule26055 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3654) (meaning t m 3953) (meaning t m 4026) (meaning t m 5020) source

theorem rule26056 (p2027 p2246 p2417 p2437 p2651 p2744 p3266 p3950 p4379 p5387 : Prop) (h : p2027 ∨ (¬ p4379) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p5387) ∨ (¬ p2744) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p3266) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p3950) ∨ (¬ p4379) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial26056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory15312 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 9) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26056 (meaning t m 2027) (meaning t m 2246) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 2744) (meaning t m 3266) (meaning t m 3950) (meaning t m 4379) (meaning t m 5387) source

theorem rule26059 (p2901 p3156 p3747 : Prop) (h : (¬ p3747) ∨ (¬ p2901) ∨ p3156) : (¬ p2901) ∨ (p3156) ∨ (¬ p3747) := by
  classical
  tauto

theorem initial26059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (meaning t m 3156) ∨ (¬ (meaning t m 3747)) := by
  have source := ElevenTheory.theory15315 (m.theta 3 5) (m.theta 5 7) (m.theta 5 8)
  exact rule26059 (meaning t m 2901) (meaning t m 3156) (meaning t m 3747) source

theorem rule26061 (p2027 p2651 p3365 p4117 p4195 p4972 : Prop) (h : (¬ p4195) ∨ (¬ p4972) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2651) ∨ (¬ p3365) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial26061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15317 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule26061 (meaning t m 2027) (meaning t m 2651) (meaning t m 3365) (meaning t m 4117) (meaning t m 4195) (meaning t m 4972) source

theorem rule26062 (p1997 p2027 p2132 p2622 p2870 p3365 p4235 : Prop) (h : (¬ p1997) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3365) ∨ p2622 ∨ (¬ p2870) ∨ (¬ p2132)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p2870) ∨ (¬ p3365) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial26062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory15318 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule26062 (meaning t m 1997) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 2870) (meaning t m 3365) (meaning t m 4235) source

theorem rule26064 (p2027 p2246 p2437 p2608 p2651 p2744 p2911 p3817 p4366 p4666 : Prop) (h : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2437) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4666) ∨ (¬ p4366) ∨ (¬ p3817) ∨ (¬ p2911) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2437) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2911) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial26064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory15320 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26064 (meaning t m 2027) (meaning t m 2246) (meaning t m 2437) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 2911) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) source

theorem rule26065 (p2027 p2247 p2383 p2744 p3923 p3953 p5020 : Prop) (h : (¬ p5020) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2383) ∨ (¬ p2247) ∨ (¬ p3923) ∨ (¬ p3953)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2383) ∨ (¬ p2744) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial26065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory15321 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 6 8)
  exact rule26065 (meaning t m 2027) (meaning t m 2247) (meaning t m 2383) (meaning t m 2744) (meaning t m 3923) (meaning t m 3953) (meaning t m 5020) source

theorem rule26066 (p2027 p2247 p2744 p2774 p3589 p3688 : Prop) (h : (¬ p2247) ∨ (¬ p2774) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3589) ∨ (¬ p3688)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial26066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory15322 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6)
  exact rule26066 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 2774) (meaning t m 3589) (meaning t m 3688) source

theorem rule26067 (p2027 p2187 p2246 p2284 p2608 p2744 p2946 p3548 p4133 p4366 : Prop) (h : (¬ p2744) ∨ (¬ p3548) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p4133) ∨ (¬ p2946) ∨ (¬ p4366)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial26067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory15323 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule26067 (meaning t m 2027) (meaning t m 2187) (meaning t m 2246) (meaning t m 2284) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3548) (meaning t m 4133) (meaning t m 4366) source

theorem rule26076 (p2577 p2778 p3905 : Prop) (h : p2778 ∨ (¬ p3905) ∨ (¬ p2577)) : (¬ p2577) ∨ (p2778) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial26076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (meaning t m 2778) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory15332 (m.theta 0 2) (m.theta 0 4) (m.theta 0 6)
  exact rule26076 (meaning t m 2577) (meaning t m 2778) (meaning t m 3905) source

theorem rule26077 (p2027 p2138 p3166 p3256 p3570 p4133 p4244 p4347 p4786 : Prop) (h : (¬ p3256) ∨ (¬ p3570) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p4133) ∨ (¬ p3166) ∨ (¬ p4347) ∨ (¬ p4786)) : (p2027) ∨ (¬ p2138) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4244) ∨ (¬ p4347) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial26077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory15333 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26077 (meaning t m 2027) (meaning t m 2138) (meaning t m 3166) (meaning t m 3256) (meaning t m 3570) (meaning t m 4133) (meaning t m 4244) (meaning t m 4347) (meaning t m 4786) source

theorem rule26078 (p2027 p2387 p2651 p2668 p3983 p4972 : Prop) (h : (¬ p4972) ∨ (¬ p2668) ∨ (¬ p2387) ∨ (¬ p3983) ∨ p2027 ∨ (¬ p2651)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2651) ∨ (¬ p2668) ∨ (¬ p3983) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial26078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3983)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory15334 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule26078 (meaning t m 2027) (meaning t m 2387) (meaning t m 2651) (meaning t m 2668) (meaning t m 3983) (meaning t m 4972) source

theorem rule26082 (p2027 p2553 p2573 p2608 p3519 p3791 p3834 p3847 p4376 p4826 p5284 : Prop) (h : (¬ p2573) ∨ (¬ p3791) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p3834) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3847) ∨ (¬ p4826) ∨ (¬ p5284)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4376) ∨ (¬ p4826) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial26082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3847)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory15338 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 9) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule26082 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2608) (meaning t m 3519) (meaning t m 3791) (meaning t m 3834) (meaning t m 3847) (meaning t m 4376) (meaning t m 4826) (meaning t m 5284) source

theorem rule26084 (p2598 p4232 p5165 : Prop) (h : (¬ p4232) ∨ (¬ p2598) ∨ (¬ p5165)) : (¬ p2598) ∨ (¬ p4232) ∨ (¬ p5165) := by
  classical
  tauto

theorem initial26084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 4232)) ∨ (¬ (meaning t m 5165)) := by
  have source := ElevenTheory.theory15340 (m.theta 0 2) (m.theta 2 4) (m.theta 2 9)
  exact rule26084 (meaning t m 2598) (meaning t m 4232) (meaning t m 5165) source

theorem rule26086 (p1987 p2027 p2396 p2696 p2997 p3425 p4324 : Prop) (h : (¬ p4324) ∨ p2997 ∨ (¬ p2396) ∨ (¬ p3425) ∨ (¬ p2696) ∨ (¬ p1987) ∨ p2027) : (¬ p1987) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2696) ∨ (p2997) ∨ (¬ p3425) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial26086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory15342 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule26086 (meaning t m 1987) (meaning t m 2027) (meaning t m 2396) (meaning t m 2696) (meaning t m 2997) (meaning t m 3425) (meaning t m 4324) source

theorem rule26087 (p1987 p2027 p2313 p2462 p2737 p2785 p3688 p4107 : Prop) (h : p2462 ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4107) ∨ (¬ p2313)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2313) ∨ (p2462) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial26087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory15343 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9)
  exact rule26087 (meaning t m 1987) (meaning t m 2027) (meaning t m 2313) (meaning t m 2462) (meaning t m 2737) (meaning t m 2785) (meaning t m 3688) (meaning t m 4107) source

theorem rule26088 (p3917 p4037 p4328 : Prop) (h : (¬ p3917) ∨ (¬ p4328) ∨ p4037) : (¬ p3917) ∨ (p4037) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial26088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3917)) ∨ (meaning t m 4037) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory15344 (m.theta 2 6) (m.theta 3 6) (m.theta 6 9)
  exact rule26088 (meaning t m 3917) (meaning t m 4037) (meaning t m 4328) source

theorem rule26095 (p2027 p2122 p2774 p3549 p3953 p4737 : Prop) (h : (¬ p2122) ∨ (¬ p4737) ∨ (¬ p3953) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p3549)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3549) ∨ (¬ p3953) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial26095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory15351 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7)
  exact rule26095 (meaning t m 2027) (meaning t m 2122) (meaning t m 2774) (meaning t m 3549) (meaning t m 3953) (meaning t m 4737) source

theorem rule26096 (p2005 p2027 p2122 p2588 p2774 p2842 p3055 : Prop) (h : p2842 ∨ (¬ p2588) ∨ (¬ p2005) ∨ (¬ p2774) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p3055)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2774) ∨ (p2842) ∨ (¬ p3055) := by
  classical
  tauto

theorem initial26096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) := by
  have source := ElevenTheory.theory15352 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule26096 (meaning t m 2005) (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 2774) (meaning t m 2842) (meaning t m 3055) source

theorem rule26097 (p2010 p2027 p2341 p2545 p2579 p3016 p3644 p5201 : Prop) (h : p2027 ∨ (¬ p2579) ∨ (¬ p2010) ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p3644) ∨ (¬ p3016) ∨ p2545) : (¬ p2010) ∨ (p2027) ∨ (¬ p2341) ∨ (p2545) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3644) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial26097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory15353 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule26097 (meaning t m 2010) (meaning t m 2027) (meaning t m 2341) (meaning t m 2545) (meaning t m 2579) (meaning t m 3016) (meaning t m 3644) (meaning t m 5201) source

theorem rule26098 (p1995 p2027 p2202 p2427 p3379 p3486 p3555 : Prop) (h : p2027 ∨ p2202 ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p2427) ∨ (¬ p1995) ∨ (¬ p3486)) : (¬ p1995) ∨ (p2027) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p3379) ∨ (¬ p3486) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial26098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory15354 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 7)
  exact rule26098 (meaning t m 1995) (meaning t m 2027) (meaning t m 2202) (meaning t m 2427) (meaning t m 3379) (meaning t m 3486) (meaning t m 3555) source

theorem rule26105 (p2088 p2475 p2534 : Prop) (h : (¬ p2475) ∨ (¬ p2088) ∨ (¬ p2534)) : (¬ p2088) ∨ (¬ p2475) ∨ (¬ p2534) := by
  classical
  tauto

theorem initial26105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2475)) ∨ (¬ (meaning t m 2534)) := by
  have source := ElevenTheory.theory15361 (m.theta 0 8) (m.theta 4 8) (m.theta 8 9)
  exact rule26105 (meaning t m 2088) (meaning t m 2475) (meaning t m 2534) source

theorem rule26111 (p2027 p2295 p2829 p3588 p4471 p4843 : Prop) (h : (¬ p2829) ∨ p2027 ∨ (¬ p4843) ∨ (¬ p2295) ∨ (¬ p4471) ∨ (¬ p3588)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4471) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial26111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory15367 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7)
  exact rule26111 (meaning t m 2027) (meaning t m 2295) (meaning t m 2829) (meaning t m 3588) (meaning t m 4471) (meaning t m 4843) source

theorem rule26112 (p2027 p2870 p3556 p3582 p3584 p4031 p4715 : Prop) (h : (¬ p2870) ∨ (¬ p3582) ∨ (¬ p4715) ∨ (¬ p3556) ∨ (¬ p4031) ∨ p2027 ∨ (¬ p3584)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3582) ∨ (¬ p3584) ∨ (¬ p4031) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial26112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory15368 t (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule26112 (meaning t m 2027) (meaning t m 2870) (meaning t m 3556) (meaning t m 3582) (meaning t m 3584) (meaning t m 4031) (meaning t m 4715) source

theorem rule26113 (p2027 p2901 p3413 p3556 p3574 p4031 p4715 : Prop) (h : (¬ p3556) ∨ (¬ p4715) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p4031) ∨ p2027 ∨ (¬ p3574)) : (p2027) ∨ (¬ p2901) ∨ (¬ p3413) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p4031) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial26113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory15369 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule26113 (meaning t m 2027) (meaning t m 2901) (meaning t m 3413) (meaning t m 3556) (meaning t m 3574) (meaning t m 4031) (meaning t m 4715) source

theorem rule26116 (p2563 p3646 p4031 : Prop) (h : (¬ p4031) ∨ (¬ p3646) ∨ (¬ p2563)) : (¬ p2563) ∨ (¬ p3646) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial26116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory15372 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule26116 (meaning t m 2563) (meaning t m 3646) (meaning t m 4031) source

theorem rule26118 (p2027 p2299 p2373 p2406 p2780 p3379 p3822 p4736 p4902 : Prop) (h : (¬ p2780) ∨ (¬ p2299) ∨ (¬ p4736) ∨ (¬ p2406) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p4902) ∨ (¬ p3822) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p2780) ∨ (¬ p3379) ∨ (¬ p3822) ∨ (¬ p4736) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory15374 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule26118 (meaning t m 2027) (meaning t m 2299) (meaning t m 2373) (meaning t m 2406) (meaning t m 2780) (meaning t m 3379) (meaning t m 3822) (meaning t m 4736) (meaning t m 4902) source

theorem rule26119 (p3646 p4031 p4110 : Prop) (h : (¬ p4031) ∨ (¬ p3646) ∨ p4110) : (¬ p3646) ∨ (¬ p4031) ∨ (p4110) := by
  classical
  tauto

theorem initial26119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) ∨ (meaning t m 4110) := by
  have source := ElevenTheory.theory15375 (m.theta 0 5) (m.theta 4 5) (m.theta 5 6)
  exact rule26119 (meaning t m 3646) (meaning t m 4031) (meaning t m 4110) source

theorem rule26120 (p3440 p4492 p4938 : Prop) (h : (¬ p4492) ∨ (¬ p3440) ∨ p4938) : (¬ p3440) ∨ (¬ p4492) ∨ (p4938) := by
  classical
  tauto

theorem initial26120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3440)) ∨ (¬ (meaning t m 4492)) ∨ (meaning t m 4938) := by
  have source := ElevenTheory.theory15376 (m.theta 1 5) (m.theta 1 8) (m.theta 1 9)
  exact rule26120 (meaning t m 3440) (meaning t m 4492) (meaning t m 4938) source

theorem rule26124 (p2373 p4031 p4120 : Prop) (h : (¬ p2373) ∨ (¬ p4031) ∨ (¬ p4120)) : (¬ p2373) ∨ (¬ p4031) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial26124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory15380 (m.theta 0 5) (m.theta 4 5) (m.theta 5 8)
  exact rule26124 (meaning t m 2373) (meaning t m 4031) (meaning t m 4120) source

theorem rule26125 (p2027 p2352 p2573 p3365 p3366 p3519 p3979 p4035 p4376 p5119 p5284 : Prop) (h : (¬ p3366) ∨ (¬ p2573) ∨ (¬ p4376) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p3979) ∨ (¬ p5284) ∨ (¬ p3365) ∨ (¬ p2352) ∨ (¬ p5119) ∨ p2027) : (p2027) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3979) ∨ (¬ p4035) ∨ (¬ p4376) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial26125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory15381 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 9) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26125 (meaning t m 2027) (meaning t m 2352) (meaning t m 2573) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 3979) (meaning t m 4035) (meaning t m 4376) (meaning t m 5119) (meaning t m 5284) source

theorem rule26126 (p2027 p2951 p3136 p3212 p3745 p4195 p5046 : Prop) (h : (¬ p4195) ∨ (¬ p2951) ∨ (¬ p3212) ∨ p2027 ∨ (¬ p3745) ∨ (¬ p5046) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3212) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p5046) := by
  classical
  tauto

theorem initial26126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 5046)) := by
  have source := ElevenTheory.theory15382 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9)
  exact rule26126 (meaning t m 2027) (meaning t m 2951) (meaning t m 3136) (meaning t m 3212) (meaning t m 3745) (meaning t m 4195) (meaning t m 5046) source

theorem rule26127 (p2922 p3201 p3590 : Prop) (h : (¬ p2922) ∨ (¬ p3590) ∨ p3201) : (¬ p2922) ∨ (p3201) ∨ (¬ p3590) := by
  classical
  tauto

theorem initial26127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2922)) ∨ (meaning t m 3201) ∨ (¬ (meaning t m 3590)) := by
  have source := ElevenTheory.theory15383 (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule26127 (meaning t m 2922) (meaning t m 3201) (meaning t m 3590) source

theorem rule26133 (p2144 p2950 p4117 : Prop) (h : p4117 ∨ (¬ p2144) ∨ (¬ p2950)) : (¬ p2144) ∨ (¬ p2950) ∨ (p4117) := by
  classical
  tauto

theorem initial26133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2950)) ∨ (meaning t m 4117) := by
  have source := ElevenTheory.theory15389 (m.theta 0 2) (m.theta 0 3) (m.theta 0 5)
  exact rule26133 (meaning t m 2144) (meaning t m 2950) (meaning t m 4117) source

theorem rule26135 (p2027 p2246 p2373 p2387 p2459 p2542 p2651 p2744 p2778 p3366 p4347 p4902 : Prop) (h : (¬ p2373) ∨ (¬ p4347) ∨ (¬ p2387) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2542) ∨ (¬ p2744) ∨ (¬ p2778)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2373) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p4347) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory15391 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26135 (meaning t m 2027) (meaning t m 2246) (meaning t m 2373) (meaning t m 2387) (meaning t m 2459) (meaning t m 2542) (meaning t m 2651) (meaning t m 2744) (meaning t m 2778) (meaning t m 3366) (meaning t m 4347) (meaning t m 4902) source

theorem rule26138 (p2027 p2088 p2247 p2744 p4261 p4436 p5242 : Prop) (h : p2027 ∨ (¬ p4436) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2088) ∨ (¬ p4261) ∨ (¬ p5242)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p4261) ∨ (¬ p4436) ∨ (¬ p5242) := by
  classical
  tauto

theorem initial26138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4436)) ∨ (¬ (meaning t m 5242)) := by
  have source := ElevenTheory.theory15394 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 8 9)
  exact rule26138 (meaning t m 2027) (meaning t m 2088) (meaning t m 2247) (meaning t m 2744) (meaning t m 4261) (meaning t m 4436) (meaning t m 5242) source

theorem rule26139 (p2027 p2104 p2166 p2210 p2247 p2459 p2744 p3366 p4340 p4902 : Prop) (h : (¬ p2247) ∨ (¬ p2166) ∨ (¬ p2744) ∨ (¬ p2104) ∨ (¬ p2459) ∨ (¬ p4902) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3366) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p4340) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory15395 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26139 (meaning t m 2027) (meaning t m 2104) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2459) (meaning t m 2744) (meaning t m 3366) (meaning t m 4340) (meaning t m 4902) source

theorem rule26140 (p2027 p2156 p2247 p2744 p4172 p4173 p4874 : Prop) (h : (¬ p4173) ∨ (¬ p2744) ∨ (¬ p2247) ∨ (¬ p2156) ∨ (¬ p4874) ∨ (¬ p4172) ∨ p2027) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial26140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory15396 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 5 6)
  exact rule26140 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2744) (meaning t m 4172) (meaning t m 4173) (meaning t m 4874) source

theorem rule26141 (p2027 p2246 p2295 p2331 p2396 p2608 p2744 p3860 p3950 p4261 : Prop) (h : (¬ p2396) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p4261) ∨ (¬ p3950) ∨ (¬ p3860) ∨ (¬ p2295)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial26141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory15397 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule26141 (meaning t m 2027) (meaning t m 2246) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 2608) (meaning t m 2744) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) source

theorem rule26144 (p2027 p2246 p2295 p2331 p2396 p2608 p2744 p3548 p4366 p4668 : Prop) (h : (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4668) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p2608) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial26144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory15400 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26144 (meaning t m 2027) (meaning t m 2246) (meaning t m 2295) (meaning t m 2331) (meaning t m 2396) (meaning t m 2608) (meaning t m 2744) (meaning t m 3548) (meaning t m 4366) (meaning t m 4668) source

theorem rule26145 (p2027 p2246 p2331 p2608 p2744 p3256 p3548 p4133 p4341 p4347 p4366 : Prop) (h : (¬ p4133) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3548) ∨ (¬ p3256) ∨ (¬ p4366) ∨ (¬ p2608) ∨ (¬ p4347) ∨ (¬ p2246) ∨ (¬ p4341) ∨ (¬ p2331)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3256) ∨ (¬ p3548) ∨ (¬ p4133) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial26145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4341)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory15401 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26145 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2608) (meaning t m 2744) (meaning t m 3256) (meaning t m 3548) (meaning t m 4133) (meaning t m 4341) (meaning t m 4347) (meaning t m 4366) source

theorem rule26146 (p2027 p2246 p2608 p2744 p3286 p3506 p3555 p4034 p4444 p4948 p5059 : Prop) (h : p2027 ∨ (¬ p4034) ∨ (¬ p4948) ∨ (¬ p5059) ∨ (¬ p4444) ∨ (¬ p3506) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p2246) ∨ (¬ p3555)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial26146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory15402 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 9) (m.theta 4 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26146 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3286) (meaning t m 3506) (meaning t m 3555) (meaning t m 4034) (meaning t m 4444) (meaning t m 4948) (meaning t m 5059) source

theorem rule26147 (p2027 p2246 p2744 p3055 p3166 p3256 p3266 p3366 p3876 p4831 p5503 : Prop) (h : (¬ p3166) ∨ (¬ p3266) ∨ (¬ p5503) ∨ (¬ p4831) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p3366) ∨ (¬ p3055) ∨ (¬ p2246) ∨ (¬ p3256) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p3876) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial26147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory15403 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 8) (m.theta 4 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule26147 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 3055) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3366) (meaning t m 3876) (meaning t m 4831) (meaning t m 5503) source

theorem rule26148 (p2027 p2138 p2247 p2744 p3366 p3399 p3547 p3570 p3791 p4244 p5564 : Prop) (h : (¬ p4244) ∨ (¬ p5564) ∨ (¬ p3791) ∨ (¬ p3570) ∨ (¬ p3399) ∨ (¬ p2247) ∨ (¬ p3366) ∨ (¬ p2138) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3547)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3570) ∨ (¬ p3791) ∨ (¬ p4244) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial26148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory15404 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule26148 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3399) (meaning t m 3547) (meaning t m 3570) (meaning t m 3791) (meaning t m 4244) (meaning t m 5564) source

theorem rule26149 (p2027 p2138 p2247 p2744 p3366 p3449 p3692 p3694 p3979 p4318 p5122 : Prop) (h : (¬ p4318) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3694) ∨ (¬ p3979) ∨ (¬ p2138) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3979) ∨ (¬ p4318) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial26149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory15405 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26149 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3366) (meaning t m 3449) (meaning t m 3692) (meaning t m 3694) (meaning t m 3979) (meaning t m 4318) (meaning t m 5122) source

theorem rule26150 (p2027 p2138 p2246 p2331 p2744 p3323 p3366 p3461 p4244 p4831 p5660 : Prop) (h : (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p3323) ∨ (¬ p5660) ∨ (¬ p2246) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3461) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial26150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory15406 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 9 10)
  exact rule26150 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2331) (meaning t m 2744) (meaning t m 3323) (meaning t m 3366) (meaning t m 3461) (meaning t m 4244) (meaning t m 4831) (meaning t m 5660) source

theorem rule26152 (p1983 p2027 p2914 p3276 p3333 p3876 p4381 : Prop) (h : p2027 ∨ (¬ p3333) ∨ (¬ p3876) ∨ p2914 ∨ (¬ p3276) ∨ (¬ p1983) ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (p2914) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3876) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial26152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory15408 t (m.theta 2 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule26152 (meaning t m 1983) (meaning t m 2027) (meaning t m 2914) (meaning t m 3276) (meaning t m 3333) (meaning t m 3876) (meaning t m 4381) source

theorem rule26153 (p2027 p2331 p2363 p2589 p2668 p2850 p3905 p4697 p4786 p5160 : Prop) (h : (¬ p2850) ∨ (¬ p2589) ∨ (¬ p2363) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p2668) ∨ (¬ p2331) ∨ (¬ p4697) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p2850) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial26153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory15409 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule26153 (meaning t m 2027) (meaning t m 2331) (meaning t m 2363) (meaning t m 2589) (meaning t m 2668) (meaning t m 2850) (meaning t m 3905) (meaning t m 4697) (meaning t m 4786) (meaning t m 5160) source

theorem rule26155 (p2027 p2246 p2331 p2363 p2668 p2744 p3055 p3366 p3684 p4948 p5059 : Prop) (h : (¬ p2363) ∨ (¬ p3055) ∨ (¬ p2668) ∨ (¬ p2331) ∨ (¬ p4948) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p5059) ∨ p2027) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3684) ∨ (¬ p4948) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial26155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory15411 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule26155 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2744) (meaning t m 3055) (meaning t m 3366) (meaning t m 3684) (meaning t m 4948) (meaning t m 5059) source

theorem rule26157 (p2027 p2247 p2744 p3516 p3545 p3554 p3817 p4874 : Prop) (h : (¬ p3516) ∨ (¬ p2744) ∨ (¬ p3545) ∨ (¬ p3817) ∨ (¬ p3554) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4874)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3554) ∨ (¬ p3817) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial26157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3545)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory15413 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 1 7) (m.theta 7 9)
  exact rule26157 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3516) (meaning t m 3545) (meaning t m 3554) (meaning t m 3817) (meaning t m 4874) source

theorem rule26158 (p2027 p2264 p2459 p2744 p3027 p3055 p3366 p3584 p4137 p4604 : Prop) (h : (¬ p4604) ∨ (¬ p3366) ∨ (¬ p2459) ∨ (¬ p4137) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3027) ∨ (¬ p2264) ∨ (¬ p3055) ∨ (¬ p3584)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial26158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory15414 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule26158 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2744) (meaning t m 3027) (meaning t m 3055) (meaning t m 3366) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) source

theorem rule26159 (p2027 p2246 p2264 p2744 p2807 p3055 p3366 p3941 p4425 p5119 p5160 : Prop) (h : (¬ p5119) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p5160) ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2264) ∨ (¬ p3055) ∨ (¬ p4425) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3941) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial26159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory15415 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26159 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2744) (meaning t m 2807) (meaning t m 3055) (meaning t m 3366) (meaning t m 3941) (meaning t m 4425) (meaning t m 5119) (meaning t m 5160) source

theorem rule26161 (p2027 p2246 p2264 p2608 p2744 p2807 p3834 p3941 p4321 p5119 : Prop) (h : (¬ p2246) ∨ (¬ p3834) ∨ (¬ p4321) ∨ (¬ p3941) ∨ (¬ p5119) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3834) ∨ (¬ p3941) ∨ (¬ p4321) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial26161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory15417 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26161 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2608) (meaning t m 2744) (meaning t m 2807) (meaning t m 3834) (meaning t m 3941) (meaning t m 4321) (meaning t m 5119) source

theorem rule26166 (p2027 p2138 p2247 p2744 p3073 p3366 p3449 p3690 p4244 p4669 : Prop) (h : (¬ p3073) ∨ (¬ p2744) ∨ (¬ p4669) ∨ (¬ p3449) ∨ (¬ p2138) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p3366) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial26166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory15422 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule26166 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) source

theorem rule26169 (p2027 p2166 p2210 p2247 p2459 p2744 p3366 p3425 p3685 p4340 p4902 : Prop) (h : p2027 ∨ (¬ p4902) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4340) ∨ (¬ p3685) ∨ (¬ p2459)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory15425 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 7) (m.theta 2 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26169 (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2247) (meaning t m 2459) (meaning t m 2744) (meaning t m 3366) (meaning t m 3425) (meaning t m 3685) (meaning t m 4340) (meaning t m 4902) source

theorem rule26170 (p2027 p2122 p2247 p2313 p2518 p2744 p2778 p3366 p3379 p4358 p4596 : Prop) (h : (¬ p4596) ∨ (¬ p2313) ∨ (¬ p4358) ∨ (¬ p2122) ∨ (¬ p2247) ∨ (¬ p3366) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p2518) ∨ (¬ p2778)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2247) ∨ (¬ p2313) ∨ (¬ p2518) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4358) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial26170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory15426 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule26170 (meaning t m 2027) (meaning t m 2122) (meaning t m 2247) (meaning t m 2313) (meaning t m 2518) (meaning t m 2744) (meaning t m 2778) (meaning t m 3366) (meaning t m 3379) (meaning t m 4358) (meaning t m 4596) source

theorem rule26175 (p2027 p2246 p2608 p2744 p3166 p3256 p3548 p3692 p4366 p4902 : Prop) (h : (¬ p3166) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3256) ∨ (¬ p4366) ∨ (¬ p3548) ∨ (¬ p3692) ∨ (¬ p4902) ∨ (¬ p2608) ∨ p2027) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3548) ∨ (¬ p3692) ∨ (¬ p4366) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory15431 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26175 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3166) (meaning t m 3256) (meaning t m 3548) (meaning t m 3692) (meaning t m 4366) (meaning t m 4902) source

theorem rule26177 (p2027 p2230 p2246 p2299 p2440 p2663 p2744 p2780 p3343 p3366 p3822 p4451 p4668 : Prop) (h : (¬ p2230) ∨ (¬ p2440) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p2744) ∨ (¬ p2663) ∨ (¬ p2246) ∨ (¬ p3822) ∨ (¬ p3366) ∨ (¬ p2299) ∨ (¬ p4668) ∨ (¬ p2780) ∨ (¬ p4451)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2299) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4451) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial26177 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory15433 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26177 (meaning t m 2027) (meaning t m 2230) (meaning t m 2246) (meaning t m 2299) (meaning t m 2440) (meaning t m 2663) (meaning t m 2744) (meaning t m 2780) (meaning t m 3343) (meaning t m 3366) (meaning t m 3822) (meaning t m 4451) (meaning t m 4668) source

theorem rule26180 (p2027 p2246 p2651 p2744 p3276 p3343 p3366 p3425 p3659 p5123 p5558 : Prop) (h : (¬ p3366) ∨ (¬ p3343) ∨ (¬ p5123) ∨ (¬ p5558) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3276) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial26180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory15436 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26180 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 3276) (meaning t m 3343) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 5123) (meaning t m 5558) source

theorem rule26187 (p2027 p2246 p2284 p2744 p2946 p3125 p3366 p3551 p3657 p3670 p3820 p4381 p5271 : Prop) (h : (¬ p2744) ∨ (¬ p3125) ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p3820) ∨ (¬ p4381) ∨ (¬ p2946) ∨ (¬ p3551) ∨ (¬ p3670) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3657) ∨ (¬ p5271)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3657) ∨ (¬ p3670) ∨ (¬ p3820) ∨ (¬ p4381) ∨ (¬ p5271) := by
  classical
  tauto

theorem initial26187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5271)) := by
  have source := ElevenTheory.theory15443 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 9) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule26187 (meaning t m 2027) (meaning t m 2246) (meaning t m 2284) (meaning t m 2744) (meaning t m 2946) (meaning t m 3125) (meaning t m 3366) (meaning t m 3551) (meaning t m 3657) (meaning t m 3670) (meaning t m 3820) (meaning t m 4381) (meaning t m 5271) source

theorem rule26188 (p2027 p2248 p2313 p2901 p2946 p3246 p3309 p3923 p4138 p4668 p5015 : Prop) (h : p2027 ∨ (¬ p4138) ∨ (¬ p3309) ∨ (¬ p4668) ∨ (¬ p2901) ∨ (¬ p3923) ∨ (¬ p2248) ∨ (¬ p2313) ∨ (¬ p5015) ∨ (¬ p3246) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2313) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4138) ∨ (¬ p4668) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial26188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory15444 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 1 6) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule26188 (meaning t m 2027) (meaning t m 2248) (meaning t m 2313) (meaning t m 2901) (meaning t m 2946) (meaning t m 3246) (meaning t m 3309) (meaning t m 3923) (meaning t m 4138) (meaning t m 4668) (meaning t m 5015) source

theorem rule26189 (p2027 p2313 p2782 p3609 p3955 p4261 p4318 p4861 : Prop) (h : (¬ p4318) ∨ (¬ p3609) ∨ (¬ p4261) ∨ (¬ p3955) ∨ (¬ p4861) ∨ (¬ p2782) ∨ p2027 ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2782) ∨ (¬ p3609) ∨ (¬ p3955) ∨ (¬ p4261) ∨ (¬ p4318) ∨ (¬ p4861) := by
  classical
  tauto

theorem initial26189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2782)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4318)) ∨ (¬ (meaning t m 4861)) := by
  have source := ElevenTheory.theory15445 t (m.theta 0 6) (m.theta 1 8) (m.theta 2 6) (m.theta 2 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule26189 (meaning t m 2027) (meaning t m 2313) (meaning t m 2782) (meaning t m 3609) (meaning t m 3955) (meaning t m 4261) (meaning t m 4318) (meaning t m 4861) source

theorem rule26190 (p2470 p3346 p3358 : Prop) (h : (¬ p3346) ∨ (¬ p2470) ∨ (¬ p3358)) : (¬ p2470) ∨ (¬ p3346) ∨ (¬ p3358) := by
  classical
  tauto

theorem initial26190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3358)) := by
  have source := ElevenTheory.theory15446 (m.theta 0 4) (m.theta 4 8) (m.theta 4 9)
  exact rule26190 (meaning t m 2470) (meaning t m 3346) (meaning t m 3358) source

theorem rule26192 (p1990 p2027 p2563 p2622 p2630 p2657 p3237 p3286 p5175 : Prop) (h : (¬ p2630) ∨ p2622 ∨ p2027 ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p5175) ∨ (¬ p3237) ∨ (¬ p2657) ∨ (¬ p3286)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3237) ∨ (¬ p3286) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial26192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3237)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory15448 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule26192 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 3237) (meaning t m 3286) (meaning t m 5175) source

theorem rule26193 (p2230 p3346 p4449 : Prop) (h : (¬ p2230) ∨ (¬ p4449) ∨ (¬ p3346)) : (¬ p2230) ∨ (¬ p3346) ∨ (¬ p4449) := by
  classical
  tauto

theorem initial26193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4449)) := by
  have source := ElevenTheory.theory15449 (m.theta 0 4) (m.theta 4 5) (m.theta 4 9)
  exact rule26193 (meaning t m 2230) (meaning t m 3346) (meaning t m 4449) source

theorem rule26194 (p2027 p2246 p2608 p2744 p3286 p3506 p3591 p4026 p4396 p4444 p4669 : Prop) (h : (¬ p4669) ∨ (¬ p3591) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p2246) ∨ (¬ p3286) ∨ (¬ p2744) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4396) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial26194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory15450 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 3 9) (m.theta 6 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26194 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3286) (meaning t m 3506) (meaning t m 3591) (meaning t m 4026) (meaning t m 4396) (meaning t m 4444) (meaning t m 4669) source

theorem rule26195 (p2027 p2156 p2246 p2608 p2744 p2958 p3156 p3548 p3952 p4366 p4902 : Prop) (h : (¬ p4902) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3548) ∨ (¬ p2608) ∨ (¬ p4366) ∨ (¬ p2156) ∨ (¬ p3952) ∨ (¬ p3156) ∨ (¬ p2958) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3548) ∨ (¬ p3952) ∨ (¬ p4366) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial26195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory15451 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 7 8)
  exact rule26195 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2958) (meaning t m 3156) (meaning t m 3548) (meaning t m 3952) (meaning t m 4366) (meaning t m 4902) source

theorem rule26198 (p2534 p3073 p4370 : Prop) (h : (¬ p4370) ∨ (¬ p2534) ∨ (¬ p3073)) : (¬ p2534) ∨ (¬ p3073) ∨ (¬ p4370) := by
  classical
  tauto

theorem initial26198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4370)) := by
  have source := ElevenTheory.theory15454 (m.theta 1 8) (m.theta 4 8) (m.theta 8 9)
  exact rule26198 (meaning t m 2534) (meaning t m 3073) (meaning t m 4370) source

theorem rule26199 (p2027 p2156 p2246 p2363 p2608 p2668 p2744 p2958 p3745 p3860 p4286 p4370 p5118 : Prop) (h : (¬ p2608) ∨ (¬ p5118) ∨ (¬ p2363) ∨ (¬ p2958) ∨ (¬ p3860) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4370) ∨ p2027 ∨ (¬ p3745) ∨ (¬ p2668) ∨ (¬ p2156) ∨ (¬ p4286)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3745) ∨ (¬ p3860) ∨ (¬ p4286) ∨ (¬ p4370) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial26199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory15455 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26199 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2363) (meaning t m 2608) (meaning t m 2668) (meaning t m 2744) (meaning t m 2958) (meaning t m 3745) (meaning t m 3860) (meaning t m 4286) (meaning t m 4370) (meaning t m 5118) source

theorem rule26202 (p2088 p2481 p2528 : Prop) (h : (¬ p2528) ∨ (¬ p2481) ∨ p2088) : (p2088) ∨ (¬ p2481) ∨ (¬ p2528) := by
  classical
  tauto

theorem initial26202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2088) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2528)) := by
  have source := ElevenTheory.theory15458 (m.theta 0 8) (m.theta 4 8) (m.theta 8 9)
  exact rule26202 (meaning t m 2088) (meaning t m 2481) (meaning t m 2528) source

theorem rule26204 (p2027 p2156 p2246 p2476 p2744 p2901 p2958 p3366 p3641 p3876 p3905 p3952 p4647 : Prop) (h : (¬ p2744) ∨ (¬ p3366) ∨ (¬ p4647) ∨ (¬ p2901) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2958)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2958) ∨ (¬ p3366) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial26204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory15460 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7)
  exact rule26204 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2476) (meaning t m 2744) (meaning t m 2901) (meaning t m 2958) (meaning t m 3366) (meaning t m 3641) (meaning t m 3876) (meaning t m 3905) (meaning t m 3952) (meaning t m 4647) source

theorem rule26205 (p2027 p2246 p2744 p2901 p2946 p3055 p3246 p3366 p3644 p3876 p4668 : Prop) (h : (¬ p2901) ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p4668) ∨ (¬ p2744) ∨ (¬ p3246) ∨ (¬ p3876) ∨ (¬ p3644) ∨ p2027) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3246) ∨ (¬ p3366) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial26205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory15461 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule26205 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2901) (meaning t m 2946) (meaning t m 3055) (meaning t m 3246) (meaning t m 3366) (meaning t m 3644) (meaning t m 3876) (meaning t m 4668) source

theorem rule26208 (p2027 p2156 p2246 p2744 p2958 p3156 p3201 p3366 p3540 p3874 p3905 p3952 p4434 : Prop) (h : (¬ p3540) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p4434) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3952) ∨ (¬ p2246) ∨ (¬ p3905)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3366) ∨ (¬ p3540) ∨ (¬ p3874) ∨ (¬ p3905) ∨ (¬ p3952) ∨ (¬ p4434) := by
  classical
  tauto

theorem initial26208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4434)) := by
  have source := ElevenTheory.theory15464 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule26208 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2744) (meaning t m 2958) (meaning t m 3156) (meaning t m 3201) (meaning t m 3366) (meaning t m 3540) (meaning t m 3874) (meaning t m 3905) (meaning t m 3952) (meaning t m 4434) source

theorem rule26209 (p2027 p2088 p3570 p4348 p4590 p4990 : Prop) (h : (¬ p4990) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p4348) ∨ (¬ p3570) ∨ (¬ p4590)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3570) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p4990) := by
  classical
  tauto

theorem initial26209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 4990)) := by
  have source := ElevenTheory.theory15465 t (m.theta 0 7) (m.theta 0 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule26209 (meaning t m 2027) (meaning t m 2088) (meaning t m 3570) (meaning t m 4348) (meaning t m 4590) (meaning t m 4990) source

theorem rule26210 (p2027 p2246 p2274 p2284 p2476 p2744 p2946 p3347 p3641 p3876 p4257 p4712 : Prop) (h : (¬ p3641) ∨ (¬ p4712) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3876) ∨ (¬ p2476) ∨ (¬ p3347) ∨ (¬ p4257) ∨ (¬ p2946) ∨ (¬ p2274) ∨ (¬ p2744) ∨ (¬ p2246)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2476) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3347) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4257) ∨ (¬ p4712) := by
  classical
  tauto

theorem initial26210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4712)) := by
  have source := ElevenTheory.theory15466 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule26210 (meaning t m 2027) (meaning t m 2246) (meaning t m 2274) (meaning t m 2284) (meaning t m 2476) (meaning t m 2744) (meaning t m 2946) (meaning t m 3347) (meaning t m 3641) (meaning t m 3876) (meaning t m 4257) (meaning t m 4712) source

theorem rule26213 (p2027 p2246 p2579 p2744 p3166 p3366 p3506 p3822 p3905 p4107 p4390 p4444 p4669 p5111 : Prop) (h : (¬ p3905) ∨ (¬ p4669) ∨ (¬ p4107) ∨ (¬ p2744) ∨ (¬ p2579) ∨ (¬ p4390) ∨ (¬ p3366) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p5111) ∨ (¬ p2246) ∨ (¬ p3822) ∨ (¬ p3166) ∨ (¬ p3506)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2579) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4390) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p5111) := by
  classical
  tauto

theorem initial26213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5111)) := by
  have source := ElevenTheory.theory15469 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 8) (m.theta 3 9) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26213 (meaning t m 2027) (meaning t m 2246) (meaning t m 2579) (meaning t m 2744) (meaning t m 3166) (meaning t m 3366) (meaning t m 3506) (meaning t m 3822) (meaning t m 3905) (meaning t m 4107) (meaning t m 4390) (meaning t m 4444) (meaning t m 4669) (meaning t m 5111) source

theorem rule26214 (p2027 p2247 p2307 p2497 p2744 p3549 p4257 p5020 : Prop) (h : (¬ p2744) ∨ (¬ p2307) ∨ (¬ p2247) ∨ (¬ p4257) ∨ (¬ p3549) ∨ (¬ p5020) ∨ (¬ p2497) ∨ p2027) : (p2027) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2497) ∨ (¬ p2744) ∨ (¬ p3549) ∨ (¬ p4257) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial26214 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory15470 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7)
  exact rule26214 (meaning t m 2027) (meaning t m 2247) (meaning t m 2307) (meaning t m 2497) (meaning t m 2744) (meaning t m 3549) (meaning t m 4257) (meaning t m 5020) source

theorem rule26223 (p2027 p2264 p2476 p3389 p4383 p4653 : Prop) (h : (¬ p4383) ∨ (¬ p2476) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p4653)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial26223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory15479 t (m.theta 0 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule26223 (meaning t m 2027) (meaning t m 2264) (meaning t m 2476) (meaning t m 3389) (meaning t m 4383) (meaning t m 4653) source

theorem rule26224 (p2027 p2139 p2156 p2177 p2274 p2630 p2657 p3877 p4041 p4236 : Prop) (h : (¬ p3877) ∨ (¬ p2177) ∨ (¬ p2657) ∨ (¬ p2630) ∨ (¬ p2156) ∨ p2027 ∨ (¬ p4041) ∨ (¬ p2139) ∨ (¬ p4236) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial26224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory15480 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule26224 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 2177) (meaning t m 2274) (meaning t m 2630) (meaning t m 2657) (meaning t m 3877) (meaning t m 4041) (meaning t m 4236) source

theorem rule26229 (p2027 p2685 p3276 p3355 p3366 p3414 p3519 p4035 p4236 p4376 p4444 p5113 : Prop) (h : p2027 ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p5113) ∨ (¬ p2685) ∨ (¬ p4035) ∨ (¬ p4444) ∨ (¬ p3355) ∨ (¬ p3519) ∨ (¬ p3414) ∨ (¬ p3276)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3519) ∨ (¬ p4035) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4444) ∨ (¬ p5113) := by
  classical
  tauto

theorem initial26229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5113)) := by
  have source := ElevenTheory.theory15485 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26229 (meaning t m 2027) (meaning t m 2685) (meaning t m 3276) (meaning t m 3355) (meaning t m 3366) (meaning t m 3414) (meaning t m 3519) (meaning t m 4035) (meaning t m 4236) (meaning t m 4376) (meaning t m 4444) (meaning t m 5113) source

theorem rule26230 (p1982 p2027 p2459 p2622 p2881 p2951 p3051 p3136 : Prop) (h : p2027 ∨ (¬ p3051) ∨ p2622 ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p1982) ∨ (¬ p2881) ∨ (¬ p2459)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial26230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory15486 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule26230 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2622) (meaning t m 2881) (meaning t m 2951) (meaning t m 3051) (meaning t m 3136) source

theorem rule26233 (p2027 p2481 p2509 p2717 p2922 p3960 p5087 : Prop) (h : (¬ p2509) ∨ (¬ p5087) ∨ (¬ p2717) ∨ (¬ p2922) ∨ (¬ p2481) ∨ p2027 ∨ (¬ p3960)) : (p2027) ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2717) ∨ (¬ p2922) ∨ (¬ p3960) ∨ (¬ p5087) := by
  classical
  tauto

theorem initial26233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2481)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3960)) ∨ (¬ (meaning t m 5087)) := by
  have source := ElevenTheory.theory15489 t (m.theta 0 8) (m.theta 1 4) (m.theta 2 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule26233 (meaning t m 2027) (meaning t m 2481) (meaning t m 2509) (meaning t m 2717) (meaning t m 2922) (meaning t m 3960) (meaning t m 5087) source

theorem rule26241 (p1994 p2027 p2190 p2202 p2563 p2727 p3497 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p1994) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p3497) ∨ p2202 ∨ (¬ p2563) ∨ (¬ p2190)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2190) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial26241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory15497 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule26241 (meaning t m 1994) (meaning t m 2027) (meaning t m 2190) (meaning t m 2202) (meaning t m 2563) (meaning t m 2727) (meaning t m 3497) (meaning t m 3662) source

theorem rule26242 (p1994 p2027 p2148 p2220 p2727 p3497 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p1994) ∨ (¬ p2727) ∨ p2027 ∨ p2148 ∨ (¬ p3497) ∨ (¬ p2220)) : (¬ p1994) ∨ (p2027) ∨ (p2148) ∨ (¬ p2220) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial26242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory15498 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule26242 (meaning t m 1994) (meaning t m 2027) (meaning t m 2148) (meaning t m 2220) (meaning t m 2727) (meaning t m 3497) (meaning t m 3662) source

theorem rule26244 (p1994 p2027 p2202 p2373 p2727 p3497 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p1994) ∨ (¬ p2727) ∨ p2027 ∨ p2202 ∨ (¬ p3497) ∨ (¬ p2373)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p2727) ∨ (¬ p3497) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial26244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory15500 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule26244 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 2727) (meaning t m 3497) (meaning t m 3662) source

theorem rule26245 (p2027 p2246 p2528 p2608 p2651 p2744 p3083 p3817 p4366 p4669 : Prop) (h : (¬ p2744) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p4669) ∨ (¬ p4366) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3817)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial26245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory15501 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26245 (meaning t m 2027) (meaning t m 2246) (meaning t m 2528) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3083) (meaning t m 3817) (meaning t m 4366) (meaning t m 4669) source

theorem rule26249 (p2027 p2122 p2246 p2313 p2528 p2651 p2744 p2778 p3083 p3366 p3917 p4604 : Prop) (h : (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4604) ∨ (¬ p2778) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2778) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3917) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial26249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory15505 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule26249 (meaning t m 2027) (meaning t m 2122) (meaning t m 2246) (meaning t m 2313) (meaning t m 2528) (meaning t m 2651) (meaning t m 2744) (meaning t m 2778) (meaning t m 3083) (meaning t m 3366) (meaning t m 3917) (meaning t m 4604) source

theorem rule26250 (p2027 p2246 p2528 p2651 p2744 p2780 p3083 p3366 p3822 p4107 p4669 : Prop) (h : (¬ p2528) ∨ (¬ p4669) ∨ (¬ p3083) ∨ (¬ p4107) ∨ (¬ p3822) ∨ (¬ p2780) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial26250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory15506 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule26250 (meaning t m 2027) (meaning t m 2246) (meaning t m 2528) (meaning t m 2651) (meaning t m 2744) (meaning t m 2780) (meaning t m 3083) (meaning t m 3366) (meaning t m 3822) (meaning t m 4107) (meaning t m 4669) source

theorem rule26252 (p2027 p2177 p2311 p2386 p3551 p3564 p4624 : Prop) (h : (¬ p2177) ∨ (¬ p2386) ∨ p2027 ∨ (¬ p4624) ∨ (¬ p3564) ∨ (¬ p2311) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p3551) ∨ (¬ p3564) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial26252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory15508 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule26252 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2386) (meaning t m 3551) (meaning t m 3564) (meaning t m 4624) source

theorem rule26253 (p2027 p2246 p2264 p2459 p2744 p2807 p3379 p3860 p4257 p5118 p5693 : Prop) (h : (¬ p2459) ∨ (¬ p4257) ∨ (¬ p5118) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p5693)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p2807) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4257) ∨ (¬ p5118) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial26253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory15509 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 1 8) (m.theta 3 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule26253 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2459) (meaning t m 2744) (meaning t m 2807) (meaning t m 3379) (meaning t m 3860) (meaning t m 4257) (meaning t m 5118) (meaning t m 5693) source

theorem rule26254 (p3821 p3857 p3961 p4443 : Prop) (h : (¬ p4443) ∨ (¬ p3857) ∨ (¬ p3961) ∨ p3821) : (p3821) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial26254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3821) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3961)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory15510 (m.theta 0 7) (m.theta 0 8) (m.theta 7 9) (m.theta 8 9)
  exact rule26254 (meaning t m 3821) (meaning t m 3857) (meaning t m 3961) (meaning t m 4443) source

theorem rule26255 (p1982 p2027 p2363 p2774 p2819 p2842 p3055 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p3055) ∨ p2842 ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (p2842) ∨ (¬ p3055) := by
  classical
  tauto

theorem initial26255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) := by
  have source := ElevenTheory.theory15511 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8) (m.theta 8 9)
  exact rule26255 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2774) (meaning t m 2819) (meaning t m 2842) (meaning t m 3055) source

theorem rule26258 (p2027 p2295 p2774 p3425 p4471 p4843 : Prop) (h : (¬ p4471) ∨ (¬ p4843) ∨ (¬ p2774) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p4843) := by
  classical
  tauto

theorem initial26258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 4843)) := by
  have source := ElevenTheory.theory15514 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 3 6) (m.theta 6 7)
  exact rule26258 (meaning t m 2027) (meaning t m 2295) (meaning t m 2774) (meaning t m 3425) (meaning t m 4471) (meaning t m 4843) source

theorem rule26260 (p3192 p3358 p3875 : Prop) (h : (¬ p3875) ∨ (¬ p3358) ∨ p3192) : (p3192) ∨ (¬ p3358) ∨ (¬ p3875) := by
  classical
  tauto

theorem initial26260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3192) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3875)) := by
  have source := ElevenTheory.theory15516 (m.theta 4 7) (m.theta 4 8) (m.theta 4 9)
  exact rule26260 (meaning t m 3192) (meaning t m 3358) (meaning t m 3875) source

theorem rule26262 (p2027 p2870 p3516 p3691 p3694 p4132 p4668 : Prop) (h : (¬ p3691) ∨ (¬ p2870) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4668) ∨ p2027 ∨ (¬ p3516)) : (p2027) ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3694) ∨ (¬ p4132) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial26262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory15518 t (m.theta 0 7) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9)
  exact rule26262 (meaning t m 2027) (meaning t m 2870) (meaning t m 3516) (meaning t m 3691) (meaning t m 3694) (meaning t m 4132) (meaning t m 4668) source

theorem rule26263 (p2027 p2246 p2651 p2744 p2780 p3276 p3343 p3366 p3822 p4260 p4831 : Prop) (h : (¬ p2246) ∨ (¬ p2780) ∨ (¬ p4260) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4831) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3276) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial26263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory15519 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule26263 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 2780) (meaning t m 3276) (meaning t m 3343) (meaning t m 3366) (meaning t m 3822) (meaning t m 4260) (meaning t m 4831) source

theorem rule26268 (p2027 p2136 p2247 p2459 p2744 p3063 p3093 p3366 p3692 p4120 p4133 : Prop) (h : (¬ p2136) ∨ (¬ p3093) ∨ (¬ p4120) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p3063) ∨ (¬ p4133) ∨ (¬ p3692) ∨ (¬ p2744) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2459) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4133) := by
  classical
  tauto

theorem initial26268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4133)) := by
  have source := ElevenTheory.theory15524 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule26268 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2459) (meaning t m 2744) (meaning t m 3063) (meaning t m 3093) (meaning t m 3366) (meaning t m 3692) (meaning t m 4120) (meaning t m 4133) source

theorem rule26270 (p2744 p4281 p4376 : Prop) (h : (¬ p4281) ∨ (¬ p2744) ∨ p4376) : (¬ p2744) ∨ (¬ p4281) ∨ (p4376) := by
  classical
  tauto

theorem initial26270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 4281)) ∨ (meaning t m 4376) := by
  have source := ElevenTheory.theory15526 t (m.theta 1 2) (m.theta 1 3) (m.theta 1 4)
  exact rule26270 (meaning t m 2744) (meaning t m 4281) (meaning t m 4376) source

theorem rule26271 (p2027 p2136 p2246 p2331 p2363 p2668 p2744 p2870 p3366 p3556 p4385 p5059 : Prop) (h : (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2136) ∨ (¬ p5059) ∨ (¬ p4385) ∨ (¬ p3556)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p2870) ∨ (¬ p3366) ∨ (¬ p3556) ∨ (¬ p4385) ∨ (¬ p5059) := by
  classical
  tauto

theorem initial26271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5059)) := by
  have source := ElevenTheory.theory15527 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 8 9)
  exact rule26271 (meaning t m 2027) (meaning t m 2136) (meaning t m 2246) (meaning t m 2331) (meaning t m 2363) (meaning t m 2668) (meaning t m 2744) (meaning t m 2870) (meaning t m 3366) (meaning t m 3556) (meaning t m 4385) (meaning t m 5059) source

theorem rule26276 (p2027 p2138 p2246 p2331 p2668 p2744 p3366 p3979 p4322 p4385 p5119 : Prop) (h : (¬ p3366) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2668) ∨ (¬ p2331) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p2138) ∨ (¬ p3979) ∨ (¬ p5119) ∨ p2027) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3979) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial26276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory15532 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule26276 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2331) (meaning t m 2668) (meaning t m 2744) (meaning t m 3366) (meaning t m 3979) (meaning t m 4322) (meaning t m 4385) (meaning t m 5119) source

theorem rule26277 (p2027 p2246 p2608 p2744 p3166 p3256 p3266 p4366 p4442 p4831 : Prop) (h : p2027 ∨ (¬ p3266) ∨ (¬ p4442) ∨ (¬ p4366) ∨ (¬ p2246) ∨ (¬ p4831) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p4366) ∨ (¬ p4442) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial26277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory15533 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule26277 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 4366) (meaning t m 4442) (meaning t m 4831) source

theorem rule26282 (p2027 p2138 p2246 p2470 p2663 p2744 p3343 p3366 p3690 p4244 p4256 p4638 : Prop) (h : (¬ p4244) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p4256) ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p2138) ∨ (¬ p4638) ∨ (¬ p3343) ∨ (¬ p2470) ∨ (¬ p2663)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3343) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4256) ∨ (¬ p4638) := by
  classical
  tauto

theorem initial26282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4638)) := by
  have source := ElevenTheory.theory15538 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule26282 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2470) (meaning t m 2663) (meaning t m 2744) (meaning t m 3343) (meaning t m 3366) (meaning t m 3690) (meaning t m 4244) (meaning t m 4256) (meaning t m 4638) source

theorem rule26283 (p2027 p2138 p2246 p2744 p3166 p3256 p3266 p3366 p4244 p4831 p5660 : Prop) (h : (¬ p3166) ∨ (¬ p4831) ∨ (¬ p3256) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3266) ∨ (¬ p4244) ∨ (¬ p5660) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2138)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p4244) ∨ (¬ p4831) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial26283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory15539 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 8) (m.theta 5 7) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule26283 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2744) (meaning t m 3166) (meaning t m 3256) (meaning t m 3266) (meaning t m 3366) (meaning t m 4244) (meaning t m 4831) (meaning t m 5660) source

theorem rule26286 (p2027 p2246 p2528 p2651 p2744 p3083 p3461 p3645 p4032 p4322 p4604 p4874 : Prop) (h : (¬ p4874) ∨ (¬ p2744) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p4604) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p2528) ∨ (¬ p3645)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3461) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4604) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial26286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory15542 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26286 (meaning t m 2027) (meaning t m 2246) (meaning t m 2528) (meaning t m 2651) (meaning t m 2744) (meaning t m 3083) (meaning t m 3461) (meaning t m 3645) (meaning t m 4032) (meaning t m 4322) (meaning t m 4604) (meaning t m 4874) source

theorem rule26287 (p2528 p3256 p4346 : Prop) (h : (¬ p2528) ∨ (¬ p4346) ∨ p3256) : (¬ p2528) ∨ (p3256) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial26287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2528)) ∨ (meaning t m 3256) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory15543 (m.theta 3 8) (m.theta 4 8) (m.theta 8 9)
  exact rule26287 (meaning t m 2528) (meaning t m 3256) (meaning t m 4346) source

theorem rule26288 (p2027 p2138 p2247 p2744 p3083 p3366 p3379 p3487 p3570 p4244 p4420 : Prop) (h : (¬ p3083) ∨ (¬ p3487) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4420) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p3570) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3570) ∨ (¬ p4244) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial26288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory15544 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule26288 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3083) (meaning t m 3366) (meaning t m 3379) (meaning t m 3487) (meaning t m 3570) (meaning t m 4244) (meaning t m 4420) source

theorem rule26289 (p2027 p2247 p2744 p3055 p3073 p3366 p3449 p3584 p4137 p4604 : Prop) (h : (¬ p4137) ∨ (¬ p3055) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2744) ∨ (¬ p4604) ∨ (¬ p3073) ∨ (¬ p2247) ∨ (¬ p3366)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3073) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial26289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory15545 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 8 9)
  exact rule26289 (meaning t m 2027) (meaning t m 2247) (meaning t m 2744) (meaning t m 3055) (meaning t m 3073) (meaning t m 3366) (meaning t m 3449) (meaning t m 3584) (meaning t m 4137) (meaning t m 4604) source

theorem rule26295 (p2027 p2608 p2761 p3346 p3537 p3609 p4425 p4669 p5193 : Prop) (h : (¬ p3537) ∨ (¬ p4425) ∨ (¬ p3609) ∨ (¬ p2608) ∨ (¬ p4669) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p3346)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p4425) ∨ (¬ p4669) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial26295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory15551 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule26295 (meaning t m 2027) (meaning t m 2608) (meaning t m 2761) (meaning t m 3346) (meaning t m 3537) (meaning t m 3609) (meaning t m 4425) (meaning t m 4669) (meaning t m 5193) source

theorem rule26296 (p2870 p2901 p5051 : Prop) (h : (¬ p2901) ∨ (¬ p5051) ∨ p2870) : (p2870) ∨ (¬ p2901) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial26296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2870) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory15552 (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule26296 (meaning t m 2870) (meaning t m 2901) (meaning t m 5051) source

theorem rule26298 (p4373 p4752 p5370 : Prop) (h : (¬ p4373) ∨ (¬ p4752) ∨ p5370) : (¬ p4373) ∨ (¬ p4752) ∨ (p5370) := by
  classical
  tauto

theorem initial26298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4373)) ∨ (¬ (meaning t m 4752)) ∨ (meaning t m 5370) := by
  have source := ElevenTheory.theory15554 t (m.theta 2 3) (m.theta 2 4) (m.theta 2 8)
  exact rule26298 (meaning t m 4373) (meaning t m 4752) (meaning t m 5370) source

theorem rule26299 (p2027 p2437 p2563 p3952 p4646 p4700 : Prop) (h : (¬ p4646) ∨ (¬ p3952) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4700) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4646) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial26299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory15555 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule26299 (meaning t m 2027) (meaning t m 2437) (meaning t m 2563) (meaning t m 3952) (meaning t m 4646) (meaning t m 4700) source

theorem rule26300 (p2027 p2122 p2230 p2440 p3016 p3549 p3591 p5190 p5225 : Prop) (h : (¬ p3016) ∨ (¬ p5190) ∨ (¬ p3591) ∨ (¬ p5225) ∨ (¬ p2122) ∨ (¬ p3549) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p2440)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p5190) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial26300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 5190)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory15556 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule26300 (meaning t m 2027) (meaning t m 2122) (meaning t m 2230) (meaning t m 2440) (meaning t m 3016) (meaning t m 3549) (meaning t m 3591) (meaning t m 5190) (meaning t m 5225) source

end SunPrize.SMT
