import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory062
import SunPrize.Certificate.Theory063
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule36048 (p1988 p2027 p2284 p2388 p3105 p3680 p3758 : Prop) (h : (¬ p2284) ∨ (¬ p3758) ∨ p2388 ∨ (¬ p1988) ∨ (¬ p3680) ∨ p2027 ∨ (¬ p3105)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2284) ∨ (p2388) ∨ (¬ p3105) ∨ (¬ p3680) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial36048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory25304 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 9 10)
  exact rule36048 (meaning t m 1988) (meaning t m 2027) (meaning t m 2284) (meaning t m 2388) (meaning t m 3105) (meaning t m 3680) (meaning t m 3758) source

theorem rule36049 (p2027 p2299 p3537 p3588 p4169 p4559 p4804 : Prop) (h : (¬ p4804) ∨ (¬ p3588) ∨ (¬ p4559) ∨ (¬ p2299) ∨ (¬ p4169) ∨ p2027 ∨ (¬ p3537)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p4804) := by
  classical
  tauto

theorem initial36049 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4804)) := by
  have source := ElevenTheory.theory25305 t (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36049 (meaning t m 2027) (meaning t m 2299) (meaning t m 3537) (meaning t m 3588) (meaning t m 4169) (meaning t m 4559) (meaning t m 4804) source

theorem rule36051 (p2027 p2717 p2737 p3366 p3551 p3820 p4778 : Prop) (h : (¬ p3551) ∨ p2027 ∨ (¬ p3820) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4778) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial36051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory25307 t (m.theta 0 2) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule36051 (meaning t m 2027) (meaning t m 2717) (meaning t m 2737) (meaning t m 3366) (meaning t m 3551) (meaning t m 3820) (meaning t m 4778) source

theorem rule36053 (p2027 p2088 p2166 p3696 p4340 p4359 p4878 : Prop) (h : (¬ p3696) ∨ (¬ p2166) ∨ (¬ p4878) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2088) ∨ (¬ p4359)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2166) ∨ (¬ p3696) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p4878) := by
  classical
  tauto

theorem initial36053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) ∨ (¬ (meaning t m 4878)) := by
  have source := ElevenTheory.theory25309 t (m.theta 0 8) (m.theta 1 5) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule36053 (meaning t m 2027) (meaning t m 2088) (meaning t m 2166) (meaning t m 3696) (meaning t m 4340) (meaning t m 4359) (meaning t m 4878) source

theorem rule36057 (p2027 p2934 p3238 p3631 p4278 p4646 : Prop) (h : (¬ p3631) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2934) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3631) ∨ (¬ p4278) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial36057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory25313 t (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule36057 (meaning t m 2027) (meaning t m 2934) (meaning t m 3238) (meaning t m 3631) (meaning t m 4278) (meaning t m 4646) source

theorem rule36063 (p2027 p2137 p2187 p2748 p2839 p3051 p3365 p3568 p4154 p4204 p4405 p4734 : Prop) (h : (¬ p4734) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p2839) ∨ (¬ p4204) ∨ (¬ p2187) ∨ (¬ p2137) ∨ (¬ p2748) ∨ (¬ p4405)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2187) ∨ (¬ p2748) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4204) ∨ (¬ p4405) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial36063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory25319 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule36063 (meaning t m 2027) (meaning t m 2137) (meaning t m 2187) (meaning t m 2748) (meaning t m 2839) (meaning t m 3051) (meaning t m 3365) (meaning t m 3568) (meaning t m 4154) (meaning t m 4204) (meaning t m 4405) (meaning t m 4734) source

theorem rule36064 (p2027 p2318 p2499 p2922 p3575 p3822 p5222 : Prop) (h : (¬ p2499) ∨ (¬ p5222) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3822) ∨ (¬ p2318)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3575) ∨ (¬ p3822) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial36064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory25320 t (m.theta 0 7) (m.theta 1 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule36064 (meaning t m 2027) (meaning t m 2318) (meaning t m 2499) (meaning t m 2922) (meaning t m 3575) (meaning t m 3822) (meaning t m 5222) source

theorem rule36067 (p2417 p3516 p3575 : Prop) (h : (¬ p3516) ∨ (¬ p3575) ∨ p2417) : (p2417) ∨ (¬ p3516) ∨ (¬ p3575) := by
  classical
  tauto

theorem initial36067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2417) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) := by
  have source := ElevenTheory.theory25323 (m.theta 0 7) (m.theta 4 7) (m.theta 7 9)
  exact rule36067 (meaning t m 2417) (meaning t m 3516) (meaning t m 3575) source

theorem rule36069 (p1996 p2027 p2202 p2241 p2440 p3027 p3452 p4116 : Prop) (h : p2202 ∨ (¬ p2440) ∨ (¬ p1996) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p3027)) : (¬ p1996) ∨ (p2027) ∨ (p2202) ∨ (¬ p2241) ∨ (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3452) ∨ (¬ p4116) := by
  classical
  tauto

theorem initial36069 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) := by
  have source := ElevenTheory.theory25325 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule36069 (meaning t m 1996) (meaning t m 2027) (meaning t m 2202) (meaning t m 2241) (meaning t m 2440) (meaning t m 3027) (meaning t m 3452) (meaning t m 4116) source

theorem rule36070 (p2027 p2241 p2440 p3452 p4116 p4210 p4448 : Prop) (h : (¬ p2440) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p4448) ∨ (¬ p2241) ∨ (¬ p3452) ∨ (¬ p4210)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2440) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4210) ∨ (¬ p4448) := by
  classical
  tauto

theorem initial36070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4448)) := by
  have source := ElevenTheory.theory25326 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5)
  exact rule36070 (meaning t m 2027) (meaning t m 2241) (meaning t m 2440) (meaning t m 3452) (meaning t m 4116) (meaning t m 4210) (meaning t m 4448) source

theorem rule36072 (p3051 p4031 p4235 : Prop) (h : p4031 ∨ (¬ p3051) ∨ (¬ p4235)) : (¬ p3051) ∨ (p4031) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial36072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (meaning t m 4031) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory25328 (m.theta 0 5) (m.theta 4 5) (m.theta 5 7)
  exact rule36072 (meaning t m 3051) (meaning t m 4031) (meaning t m 4235) source

theorem rule36075 (p2027 p2241 p2750 p2839 p2870 p3246 p3860 p3950 p4261 : Prop) (h : (¬ p2750) ∨ (¬ p2839) ∨ (¬ p2241) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p3860) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2870)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial36075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory25331 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule36075 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2839) (meaning t m 2870) (meaning t m 3246) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) source

theorem rule36076 (p2027 p2132 p2241 p2750 p2753 p2870 p3032 p3246 p3553 p4366 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p3032) ∨ (¬ p3553) ∨ (¬ p3246) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p2750) ∨ (¬ p2241) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p2753)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2870) ∨ (¬ p3032) ∨ (¬ p3246) ∨ (¬ p3553) ∨ (¬ p4366) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial36076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory25332 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36076 (meaning t m 2027) (meaning t m 2132) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2870) (meaning t m 3032) (meaning t m 3246) (meaning t m 3553) (meaning t m 4366) (meaning t m 4668) source

theorem rule36078 (p2027 p3355 p3540 p4324 p4451 p5083 : Prop) (h : (¬ p3540) ∨ (¬ p5083) ∨ (¬ p4324) ∨ (¬ p4451) ∨ (¬ p3355) ∨ p2027) : (p2027) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p4324) ∨ (¬ p4451) ∨ (¬ p5083) := by
  classical
  tauto

theorem initial36078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 5083)) := by
  have source := ElevenTheory.theory25334 t (m.theta 0 4) (m.theta 2 7) (m.theta 4 7) (m.theta 4 9) (m.theta 7 9)
  exact rule36078 (meaning t m 2027) (meaning t m 3355) (meaning t m 3540) (meaning t m 4324) (meaning t m 4451) (meaning t m 5083) source

theorem rule36083 (p2027 p2139 p2881 p3051 p3365 p3941 p4035 p5119 p5284 : Prop) (h : (¬ p2139) ∨ (¬ p5119) ∨ (¬ p4035) ∨ (¬ p5284) ∨ (¬ p3365) ∨ (¬ p3941) ∨ (¬ p3051) ∨ (¬ p2881) ∨ p2027) : (p2027) ∨ (¬ p2139) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3365) ∨ (¬ p3941) ∨ (¬ p4035) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial36083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory25339 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36083 (meaning t m 2027) (meaning t m 2139) (meaning t m 2881) (meaning t m 3051) (meaning t m 3365) (meaning t m 3941) (meaning t m 4035) (meaning t m 5119) (meaning t m 5284) source

theorem rule36096 (p2027 p2132 p2245 p2509 p2619 p2657 p3146 p3487 p4286 p4733 p5118 : Prop) (h : (¬ p2245) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p4733) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p5118) ∨ (¬ p2509) ∨ (¬ p4286) ∨ (¬ p3487) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2245) ∨ (¬ p2509) ∨ (¬ p2619) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3487) ∨ (¬ p4286) ∨ (¬ p4733) ∨ (¬ p5118) := by
  classical
  tauto

theorem initial36096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5118)) := by
  have source := ElevenTheory.theory25352 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36096 (meaning t m 2027) (meaning t m 2132) (meaning t m 2245) (meaning t m 2509) (meaning t m 2619) (meaning t m 2657) (meaning t m 3146) (meaning t m 3487) (meaning t m 4286) (meaning t m 4733) (meaning t m 5118) source

theorem rule36098 (p2027 p2440 p2573 p3343 p3346 p4717 : Prop) (h : (¬ p3346) ∨ (¬ p2573) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2573) ∨ (¬ p3343) ∨ (¬ p3346) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial36098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory25354 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule36098 (meaning t m 2027) (meaning t m 2440) (meaning t m 2573) (meaning t m 3343) (meaning t m 3346) (meaning t m 4717) source

theorem rule36099 (p2027 p2608 p2761 p3019 p3359 p3516 p3543 p3591 p3918 p4337 p4444 p4697 p4793 : Prop) (h : (¬ p3516) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4793) ∨ (¬ p2761) ∨ (¬ p3359) ∨ (¬ p3019) ∨ (¬ p3543) ∨ (¬ p3918) ∨ (¬ p3591) ∨ (¬ p4697) ∨ (¬ p4337) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2761) ∨ (¬ p3019) ∨ (¬ p3359) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p3591) ∨ (¬ p3918) ∨ (¬ p4337) ∨ (¬ p4444) ∨ (¬ p4697) ∨ (¬ p4793) := by
  classical
  tauto

theorem initial36099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4697)) ∨ (¬ (meaning t m 4793)) := by
  have source := ElevenTheory.theory25355 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36099 (meaning t m 2027) (meaning t m 2608) (meaning t m 2761) (meaning t m 3019) (meaning t m 3359) (meaning t m 3516) (meaning t m 3543) (meaning t m 3591) (meaning t m 3918) (meaning t m 4337) (meaning t m 4444) (meaning t m 4697) (meaning t m 4793) source

theorem rule36100 (p4140 p4275 : Prop) (h : p4140 ∨ p4275) : (p4140) ∨ (p4275) := by
  classical
  tauto

theorem initial36100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4140) ∨ (meaning t m 4275) := by
  have source := ElevenTheory.theory25356 (m.theta 5 7) (m.theta 6 7)
  exact rule36100 (meaning t m 4140) (meaning t m 4275) source

theorem rule36105 (p2027 p2573 p2668 p3346 p3990 p4022 p4976 : Prop) (h : (¬ p2573) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p2668) ∨ (¬ p4976) ∨ p2027 ∨ (¬ p3346)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2668) ∨ (¬ p3346) ∨ (¬ p3990) ∨ (¬ p4022) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial36105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory25361 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9)
  exact rule36105 (meaning t m 2027) (meaning t m 2573) (meaning t m 2668) (meaning t m 3346) (meaning t m 3990) (meaning t m 4022) (meaning t m 4976) source

theorem rule36106 (p2027 p2440 p3019 p3918 p4053 p4337 p4717 p5514 : Prop) (h : (¬ p4337) ∨ (¬ p3918) ∨ (¬ p3019) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p5514) ∨ (¬ p2440) ∨ (¬ p4053)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3918) ∨ (¬ p4053) ∨ (¬ p4337) ∨ (¬ p4717) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial36106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3918)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory25362 t (m.theta 1 6) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 10)
  exact rule36106 (meaning t m 2027) (meaning t m 2440) (meaning t m 3019) (meaning t m 3918) (meaning t m 4053) (meaning t m 4337) (meaning t m 4717) (meaning t m 5514) source

theorem rule36109 (p1981 p2027 p2187 p2307 p2622 p3097 p3136 p3567 p4336 : Prop) (h : (¬ p3136) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3567) ∨ p2622 ∨ (¬ p1981) ∨ (¬ p2307) ∨ (¬ p4336)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2307) ∨ (p2622) ∨ (¬ p3097) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial36109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory25365 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36109 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2307) (meaning t m 2622) (meaning t m 3097) (meaning t m 3136) (meaning t m 3567) (meaning t m 4336) source

theorem rule36116 (p2027 p2220 p3556 p3644 p4042 p4277 : Prop) (h : p2027 ∨ (¬ p3556) ∨ (¬ p4277) ∨ (¬ p4042) ∨ (¬ p3644) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial36116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory25372 t (m.theta 0 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule36116 (meaning t m 2027) (meaning t m 2220) (meaning t m 3556) (meaning t m 3644) (meaning t m 4042) (meaning t m 4277) source

theorem rule36120 (p1982 p2027 p2156 p2187 p2363 p2622 p2951 p3136 : Prop) (h : (¬ p1982) ∨ p2622 ∨ (¬ p2156) ∨ (¬ p3136) ∨ (¬ p2951) ∨ (¬ p2187) ∨ p2027 ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (p2622) ∨ (¬ p2951) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial36120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory25376 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule36120 (meaning t m 1982) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 2622) (meaning t m 2951) (meaning t m 3136) source

theorem rule36121 (p2027 p2249 p2656 p2727 p2963 p3212 p3680 p3922 p3923 p4399 p5123 p5580 : Prop) (h : (¬ p3680) ∨ (¬ p2656) ∨ (¬ p3212) ∨ (¬ p4399) ∨ (¬ p3922) ∨ (¬ p2963) ∨ (¬ p2727) ∨ (¬ p3923) ∨ (¬ p5580) ∨ (¬ p2249) ∨ (¬ p5123) ∨ p2027) : (p2027) ∨ (¬ p2249) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2963) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial36121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2249)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory25377 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 5 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36121 (meaning t m 2027) (meaning t m 2249) (meaning t m 2656) (meaning t m 2727) (meaning t m 2963) (meaning t m 3212) (meaning t m 3680) (meaning t m 3922) (meaning t m 3923) (meaning t m 4399) (meaning t m 5123) (meaning t m 5580) source

theorem rule36133 (p2027 p2441 p2579 p3516 p4278 p4715 p5201 : Prop) (h : (¬ p4278) ∨ (¬ p2441) ∨ (¬ p5201) ∨ (¬ p4715) ∨ (¬ p3516) ∨ (¬ p2579) ∨ p2027) : (p2027) ∨ (¬ p2441) ∨ (¬ p2579) ∨ (¬ p3516) ∨ (¬ p4278) ∨ (¬ p4715) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial36133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4715)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory25389 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule36133 (meaning t m 2027) (meaning t m 2441) (meaning t m 2579) (meaning t m 3516) (meaning t m 4278) (meaning t m 4715) (meaning t m 5201) source

theorem rule36138 (p1982 p2027 p2622 p2685 p3032 p3276 p3516 p3543 p4444 p4636 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p2685) ∨ (¬ p3543) ∨ p2622 ∨ (¬ p3276) ∨ (¬ p3032) ∨ (¬ p3516) ∨ (¬ p4636) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2622) ∨ (¬ p2685) ∨ (¬ p3032) ∨ (¬ p3276) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4444) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial36138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory25394 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 4 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36138 (meaning t m 1982) (meaning t m 2027) (meaning t m 2622) (meaning t m 2685) (meaning t m 3032) (meaning t m 3276) (meaning t m 3516) (meaning t m 3543) (meaning t m 4444) (meaning t m 4636) source

theorem rule36139 (p2027 p2177 p2807 p3172 p3579 p4276 p4548 : Prop) (h : (¬ p3579) ∨ p2027 ∨ (¬ p4276) ∨ (¬ p2807) ∨ (¬ p4548) ∨ (¬ p2177) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4548) := by
  classical
  tauto

theorem initial36139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4548)) := by
  have source := ElevenTheory.theory25395 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36139 (meaning t m 2027) (meaning t m 2177) (meaning t m 2807) (meaning t m 3172) (meaning t m 3579) (meaning t m 4276) (meaning t m 4548) source

theorem rule36142 (p2027 p2140 p3434 p3556 p3587 p3690 : Prop) (h : (¬ p3556) ∨ (¬ p3690) ∨ (¬ p2140) ∨ (¬ p3587) ∨ p2027 ∨ (¬ p3434)) : (p2027) ∨ (¬ p2140) ∨ (¬ p3434) ∨ (¬ p3556) ∨ (¬ p3587) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial36142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2140)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory25398 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 9)
  exact rule36142 (meaning t m 2027) (meaning t m 2140) (meaning t m 3434) (meaning t m 3556) (meaning t m 3587) (meaning t m 3690) source

theorem rule36143 (p3542 p4353 p4800 : Prop) (h : (¬ p4800) ∨ (¬ p4353) ∨ p3542) : (p3542) ∨ (¬ p4353) ∨ (¬ p4800) := by
  classical
  tauto

theorem initial36143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3542) ∨ (¬ (meaning t m 4353)) ∨ (¬ (meaning t m 4800)) := by
  have source := ElevenTheory.theory25399 (m.theta 1 8) (m.theta 2 8) (m.theta 7 8)
  exact rule36143 (meaning t m 3542) (meaning t m 4353) (meaning t m 4800) source

theorem rule36147 (p2027 p2598 p2850 p2982 p3549 p3591 p4107 p4395 p4733 : Prop) (h : p2027 ∨ (¬ p4107) ∨ (¬ p2850) ∨ (¬ p4395) ∨ (¬ p2982) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p2598) ∨ (¬ p4733)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4733) := by
  classical
  tauto

theorem initial36147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4733)) := by
  have source := ElevenTheory.theory25403 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule36147 (meaning t m 2027) (meaning t m 2598) (meaning t m 2850) (meaning t m 2982) (meaning t m 3549) (meaning t m 3591) (meaning t m 4107) (meaning t m 4395) (meaning t m 4733) source

theorem rule36150 (p2027 p2396 p2761 p3571 p4321 p4556 p5357 : Prop) (h : (¬ p4556) ∨ (¬ p3571) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2396) ∨ (¬ p4321) ∨ (¬ p5357)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3571) ∨ (¬ p4321) ∨ (¬ p4556) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial36150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory25406 t (m.theta 1 7) (m.theta 1 9) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule36150 (meaning t m 2027) (meaning t m 2396) (meaning t m 2761) (meaning t m 3571) (meaning t m 4321) (meaning t m 4556) (meaning t m 5357) source

theorem rule36153 (p2027 p2230 p2440 p2663 p3172 p5008 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p5008) ∨ (¬ p2663) ∨ (¬ p3172)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3172) ∨ (¬ p5008) := by
  classical
  tauto

theorem initial36153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 5008)) := by
  have source := ElevenTheory.theory25409 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5)
  exact rule36153 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 3172) (meaning t m 5008) source

theorem rule36154 (p2248 p2663 p5190 : Prop) (h : (¬ p2663) ∨ (¬ p2248) ∨ p5190) : (¬ p2248) ∨ (¬ p2663) ∨ (p5190) := by
  classical
  tauto

theorem initial36154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2663)) ∨ (meaning t m 5190) := by
  have source := ElevenTheory.theory25410 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4)
  exact rule36154 (meaning t m 2248) (meaning t m 2663) (meaning t m 5190) source

theorem rule36156 (p2027 p2341 p2396 p3553 p3821 p4570 : Prop) (h : (¬ p3821) ∨ p2027 ∨ (¬ p4570) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3553)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3553) ∨ (¬ p3821) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial36156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory25412 t (m.theta 0 7) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36156 (meaning t m 2027) (meaning t m 2341) (meaning t m 2396) (meaning t m 3553) (meaning t m 3821) (meaning t m 4570) source

theorem rule36157 (p2027 p2299 p2313 p2598 p2850 p2982 p4348 p4450 p4733 p5015 : Prop) (h : (¬ p4450) ∨ (¬ p2850) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p4348) ∨ (¬ p2299) ∨ (¬ p4733) ∨ (¬ p5015) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4733) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial36157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory25413 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule36157 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2598) (meaning t m 2850) (meaning t m 2982) (meaning t m 4348) (meaning t m 4450) (meaning t m 4733) (meaning t m 5015) source

theorem rule36160 (p2020 p2027 p2341 p2396 p2997 p3821 p3941 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p2020) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3821) ∨ (¬ p3941)) : (¬ p2020) ∨ (p2027) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3821) ∨ (¬ p3941) := by
  classical
  tauto

theorem initial36160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3941)) := by
  have source := ElevenTheory.theory25416 t (m.theta 0 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule36160 (meaning t m 2020) (meaning t m 2027) (meaning t m 2341) (meaning t m 2396) (meaning t m 2997) (meaning t m 3821) (meaning t m 3941) source

theorem rule36164 (p2027 p2245 p2598 p2963 p3641 p3922 p4026 p4149 p4191 p4733 p5119 : Prop) (h : (¬ p2245) ∨ (¬ p5119) ∨ (¬ p4191) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p4149) ∨ (¬ p4733) ∨ (¬ p2963) ∨ p2027 ∨ (¬ p3922) ∨ (¬ p4026)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3641) ∨ (¬ p3922) ∨ (¬ p4026) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4733) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial36164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4733)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory25420 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36164 (meaning t m 2027) (meaning t m 2245) (meaning t m 2598) (meaning t m 2963) (meaning t m 3641) (meaning t m 3922) (meaning t m 4026) (meaning t m 4149) (meaning t m 4191) (meaning t m 4733) (meaning t m 5119) source

theorem rule36166 (p1985 p2027 p2656 p2688 p2727 p2870 p3212 p4385 p4399 : Prop) (h : (¬ p3212) ∨ p2688 ∨ p2027 ∨ (¬ p4399) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4385) ∨ (¬ p2870) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2656) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2870) ∨ (¬ p3212) ∨ (¬ p4385) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial36166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory25422 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 5 7) (m.theta 5 9)
  exact rule36166 (meaning t m 1985) (meaning t m 2027) (meaning t m 2656) (meaning t m 2688) (meaning t m 2727) (meaning t m 2870) (meaning t m 3212) (meaning t m 4385) (meaning t m 4399) source

theorem rule36169 (p2027 p2247 p2751 p3830 p3853 p4035 : Prop) (h : (¬ p2751) ∨ (¬ p2247) ∨ (¬ p3853) ∨ (¬ p3830) ∨ p2027 ∨ (¬ p4035)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial36169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory25425 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 2 3) (m.theta 3 9)
  exact rule36169 (meaning t m 2027) (meaning t m 2247) (meaning t m 2751) (meaning t m 3830) (meaning t m 3853) (meaning t m 4035) source

theorem rule36172 (p2005 p2027 p2241 p2727 p2873 p3016 p3555 : Prop) (h : (¬ p3016) ∨ (¬ p2005) ∨ (¬ p2727) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3555) ∨ p2873) : (¬ p2005) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (p2873) ∨ (¬ p3016) ∨ (¬ p3555) := by
  classical
  tauto

theorem initial36172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3555)) := by
  have source := ElevenTheory.theory25428 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 4 6)
  exact rule36172 (meaning t m 2005) (meaning t m 2027) (meaning t m 2241) (meaning t m 2727) (meaning t m 2873) (meaning t m 3016) (meaning t m 3555) source

theorem rule36178 (p2010 p2027 p2341 p2622 p2707 p2743 p3577 p3644 : Prop) (h : (¬ p2010) ∨ (¬ p2743) ∨ (¬ p3577) ∨ p2622 ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2341) ∨ (¬ p2707)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2341) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3577) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial36178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3577)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory25434 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule36178 (meaning t m 2010) (meaning t m 2027) (meaning t m 2341) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3577) (meaning t m 3644) source

theorem rule36179 (p1997 p2027 p2177 p2542 p2997 p3570 p3742 p4001 : Prop) (h : (¬ p2542) ∨ (¬ p1997) ∨ p2997 ∨ (¬ p3570) ∨ (¬ p4001) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3742)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2542) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial36179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory25435 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36179 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2542) (meaning t m 2997) (meaning t m 3570) (meaning t m 3742) (meaning t m 4001) source

theorem rule36180 (p2027 p2177 p2315 p3246 p3570 p3821 : Prop) (h : (¬ p2315) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3821) ∨ (¬ p3570) ∨ (¬ p3246)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2315) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial36180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory25436 t (m.theta 0 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36180 (meaning t m 2027) (meaning t m 2177) (meaning t m 2315) (meaning t m 3246) (meaning t m 3570) (meaning t m 3821) source

theorem rule36181 (p1998 p2027 p2264 p2688 p2807 p2952 p2992 : Prop) (h : p2027 ∨ (¬ p2264) ∨ (¬ p1998) ∨ p2688 ∨ (¬ p2992) ∨ (¬ p2807) ∨ (¬ p2952)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2688) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial36181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory25437 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule36181 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2688) (meaning t m 2807) (meaning t m 2952) (meaning t m 2992) source

theorem rule36184 (p1988 p2027 p2323 p2946 p3662 p3680 p3842 p4039 : Prop) (h : (¬ p4039) ∨ (¬ p3680) ∨ (¬ p3662) ∨ (¬ p3842) ∨ (¬ p1988) ∨ p2027 ∨ p2323 ∨ (¬ p2946)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3842) ∨ (¬ p4039) := by
  classical
  tauto

theorem initial36184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4039)) := by
  have source := ElevenTheory.theory25440 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule36184 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3662) (meaning t m 3680) (meaning t m 3842) (meaning t m 4039) source

theorem rule36187 (p1997 p2027 p2177 p2542 p2997 p3543 p3548 p3742 p4279 : Prop) (h : (¬ p3543) ∨ (¬ p3548) ∨ (¬ p4279) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3742) ∨ p2997 ∨ (¬ p1997) ∨ (¬ p2542)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2542) ∨ (p2997) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial36187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory25443 t (m.theta 0 7) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36187 (meaning t m 1997) (meaning t m 2027) (meaning t m 2177) (meaning t m 2542) (meaning t m 2997) (meaning t m 3543) (meaning t m 3548) (meaning t m 3742) (meaning t m 4279) source

theorem rule36189 (p2927 p3817 p4278 : Prop) (h : (¬ p2927) ∨ (¬ p4278) ∨ p3817) : (¬ p2927) ∨ (p3817) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2927)) ∨ (meaning t m 3817) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25445 (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule36189 (meaning t m 2927) (meaning t m 3817) (meaning t m 4278) source

theorem rule36191 (p1995 p2027 p2396 p2997 p3379 p3817 p4366 : Prop) (h : (¬ p3379) ∨ (¬ p1995) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p3817) ∨ p2997 ∨ (¬ p4366)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3379) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial36191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory25447 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule36191 (meaning t m 1995) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3379) (meaning t m 3817) (meaning t m 4366) source

theorem rule36192 (p3948 p4496 p4688 : Prop) (h : (¬ p4496) ∨ (¬ p3948) ∨ p4688) : (¬ p3948) ∨ (¬ p4496) ∨ (p4688) := by
  classical
  tauto

theorem initial36192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4496)) ∨ (meaning t m 4688) := by
  have source := ElevenTheory.theory25448 (m.theta 1 4) (m.theta 1 5) (m.theta 1 8)
  exact rule36192 (meaning t m 3948) (meaning t m 4496) (meaning t m 4688) source

theorem rule36193 (p1980 p2027 p2331 p2952 p3105 p3474 p4208 : Prop) (h : p3474 ∨ (¬ p3105) ∨ (¬ p2331) ∨ (¬ p1980) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4208)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3105) ∨ (p3474) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial36193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3105)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory25449 t (m.theta 0 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 9)
  exact rule36193 (meaning t m 1980) (meaning t m 2027) (meaning t m 2331) (meaning t m 2952) (meaning t m 3105) (meaning t m 3474) (meaning t m 4208) source

theorem rule36197 (p1998 p2997 p3527 p5142 : Prop) (h : p2997 ∨ (¬ p1998) ∨ (¬ p3527) ∨ p5142) : (¬ p1998) ∨ (p2997) ∨ (¬ p3527) ∨ (p5142) := by
  classical
  tauto

theorem initial36197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3527)) ∨ (meaning t m 5142) := by
  have source := ElevenTheory.theory25453 t (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36197 (meaning t m 1998) (meaning t m 2997) (meaning t m 3527) (meaning t m 5142) source

theorem rule36211 (p1980 p2027 p2331 p2545 p2952 p2992 p4111 : Prop) (h : (¬ p2992) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p1980) ∨ (¬ p4111) ∨ p2545) : (¬ p1980) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial36211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory25467 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule36211 (meaning t m 1980) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2952) (meaning t m 2992) (meaning t m 4111) source

theorem rule36213 (p2027 p2145 p2177 p2437 p2630 p2696 p3570 p3646 p4204 p4276 : Prop) (h : (¬ p3570) ∨ (¬ p2437) ∨ (¬ p2145) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4204) ∨ (¬ p4276) ∨ (¬ p3646) ∨ (¬ p2696) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4204) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial36213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory25469 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36213 (meaning t m 2027) (meaning t m 2145) (meaning t m 2177) (meaning t m 2437) (meaning t m 2630) (meaning t m 2696) (meaning t m 3570) (meaning t m 3646) (meaning t m 4204) (meaning t m 4276) source

theorem rule36219 (p1990 p2027 p2299 p2396 p2441 p2563 p2633 p4278 : Prop) (h : p2027 ∨ (¬ p1990) ∨ (¬ p2563) ∨ p2633 ∨ (¬ p2299) ∨ (¬ p4278) ∨ (¬ p2396) ∨ (¬ p2441)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2441) ∨ (¬ p2563) ∨ (p2633) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25475 t (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36219 (meaning t m 1990) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2441) (meaning t m 2563) (meaning t m 2633) (meaning t m 4278) source

theorem rule36220 (p2027 p2619 p3969 p4371 p4512 p4875 p5693 : Prop) (h : (¬ p4371) ∨ (¬ p4875) ∨ (¬ p4512) ∨ (¬ p5693) ∨ (¬ p3969) ∨ (¬ p2619) ∨ p2027) : (p2027) ∨ (¬ p2619) ∨ (¬ p3969) ∨ (¬ p4371) ∨ (¬ p4512) ∨ (¬ p4875) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial36220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4875)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory25476 t (m.theta 1 5) (m.theta 1 6) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10)
  exact rule36220 (meaning t m 2027) (meaning t m 2619) (meaning t m 3969) (meaning t m 4371) (meaning t m 4512) (meaning t m 4875) (meaning t m 5693) source

theorem rule36221 (p2027 p2299 p2396 p2534 p4420 p4443 : Prop) (h : (¬ p2396) ∨ (¬ p4443) ∨ (¬ p2299) ∨ p2027 ∨ (¬ p4420) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p4420) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial36221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 4420)) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory25477 t (m.theta 4 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule36221 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2534) (meaning t m 4420) (meaning t m 4443) source

theorem rule36224 (p1996 p2027 p2247 p2685 p2688 p3830 p3853 p4035 : Prop) (h : (¬ p3830) ∨ p2688 ∨ (¬ p3853) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p2247) ∨ (¬ p1996) ∨ (¬ p4035)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2685) ∨ (p2688) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial36224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory25480 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9)
  exact rule36224 (meaning t m 1996) (meaning t m 2027) (meaning t m 2247) (meaning t m 2685) (meaning t m 2688) (meaning t m 3830) (meaning t m 3853) (meaning t m 4035) source

theorem rule36227 (p1982 p2027 p2622 p2630 p2657 p3166 p3256 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p3256) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p2630) ∨ p2622) : (¬ p1982) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial36227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory25483 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule36227 (meaning t m 1982) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 3166) (meaning t m 3256) source

theorem rule36229 (p3399 p3830 p5357 : Prop) (h : (¬ p5357) ∨ (¬ p3830) ∨ p3399) : (p3399) ∨ (¬ p3830) ∨ (¬ p5357) := by
  classical
  tauto

theorem initial36229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3399) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 5357)) := by
  have source := ElevenTheory.theory25485 (m.theta 0 1) (m.theta 1 7) (m.theta 1 9)
  exact rule36229 (meaning t m 3399) (meaning t m 3830) (meaning t m 5357) source

theorem rule36231 (p3821 p3834 p5206 p5362 : Prop) (h : (¬ p5206) ∨ (¬ p3821) ∨ (¬ p5362) ∨ p3834) : (¬ p3821) ∨ (p3834) ∨ (¬ p5206) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial36231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3821)) ∨ (meaning t m 3834) ∨ (¬ (meaning t m 5206)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory25487 (m.theta 0 1) (m.theta 0 7) (m.theta 1 9) (m.theta 7 9)
  exact rule36231 (meaning t m 3821) (meaning t m 3834) (meaning t m 5206) (meaning t m 5362) source

theorem rule36241 (p3858 p4967 p5315 p5590 p5600 : Prop) (h : (¬ p3858) ∨ (¬ p5590) ∨ (¬ p5315) ∨ (¬ p4967) ∨ p5600) : (¬ p3858) ∨ (¬ p4967) ∨ (¬ p5315) ∨ (¬ p5590) ∨ (p5600) := by
  classical
  tauto

theorem initial36241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3858)) ∨ (¬ (meaning t m 4967)) ∨ (¬ (meaning t m 5315)) ∨ (¬ (meaning t m 5590)) ∨ (meaning t m 5600) := by
  have source := ElevenTheory.theory25497 (m.theta 0 8) (m.theta 1 8) (m.theta 2 8) (m.theta 3 8) (m.theta 8 10)
  exact rule36241 (meaning t m 3858) (meaning t m 4967) (meaning t m 5315) (meaning t m 5590) (meaning t m 5600) source

theorem rule36242 (p2000 p2027 p2476 p2766 p3979 p4286 p4347 : Prop) (h : p2027 ∨ (¬ p4286) ∨ (¬ p2476) ∨ (¬ p3979) ∨ (¬ p4347) ∨ p2766 ∨ (¬ p2000)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2476) ∨ (p2766) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial36242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory25498 t (m.theta 0 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36242 (meaning t m 2000) (meaning t m 2027) (meaning t m 2476) (meaning t m 2766) (meaning t m 3979) (meaning t m 4286) (meaning t m 4347) source

theorem rule36243 (p2027 p2145 p2696 p3005 p3646 p3744 p4009 p4191 p5119 : Prop) (h : (¬ p4009) ∨ (¬ p5119) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p2145) ∨ (¬ p3005) ∨ (¬ p2696) ∨ (¬ p3744) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3005) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4009) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial36243 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory25499 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36243 (meaning t m 2027) (meaning t m 2145) (meaning t m 2696) (meaning t m 3005) (meaning t m 3646) (meaning t m 3744) (meaning t m 4009) (meaning t m 4191) (meaning t m 5119) source

theorem rule36244 (p2027 p2145 p2651 p2810 p2951 p3136 p4117 : Prop) (h : p2027 ∨ (¬ p2145) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4117) ∨ (¬ p2651) ∨ (¬ p2951)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial36244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory25500 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5)
  exact rule36244 (meaning t m 2027) (meaning t m 2145) (meaning t m 2651) (meaning t m 2810) (meaning t m 2951) (meaning t m 3136) (meaning t m 4117) source

theorem rule36245 (p2027 p2145 p2598 p3641 p3646 p3744 p4149 p4191 p5119 : Prop) (h : (¬ p3646) ∨ (¬ p2145) ∨ (¬ p5119) ∨ (¬ p3641) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p2598) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial36245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory25501 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36245 (meaning t m 2027) (meaning t m 2145) (meaning t m 2598) (meaning t m 3641) (meaning t m 3646) (meaning t m 3744) (meaning t m 4149) (meaning t m 4191) (meaning t m 5119) source

theorem rule36247 (p2027 p2352 p2387 p2577 p3422 p4727 : Prop) (h : (¬ p2387) ∨ (¬ p3422) ∨ (¬ p2577) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p4727)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3422) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial36247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory25503 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule36247 (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2577) (meaning t m 3422) (meaning t m 4727) source

theorem rule36249 (p1995 p2027 p2509 p2766 p3979 p4286 p4347 : Prop) (h : (¬ p2509) ∨ (¬ p1995) ∨ (¬ p4286) ∨ (¬ p3979) ∨ p2027 ∨ (¬ p4347) ∨ p2766) : (¬ p1995) ∨ (p2027) ∨ (¬ p2509) ∨ (p2766) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial36249 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory25505 t (m.theta 1 4) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36249 (meaning t m 1995) (meaning t m 2027) (meaning t m 2509) (meaning t m 2766) (meaning t m 3979) (meaning t m 4286) (meaning t m 4347) source

theorem rule36250 (p2005 p2027 p2396 p2997 p3016 p3742 p4278 : Prop) (h : (¬ p3016) ∨ (¬ p2005) ∨ p2997 ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3742)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25506 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule36250 (meaning t m 2005) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3016) (meaning t m 3742) (meaning t m 4278) source

theorem rule36251 (p2005 p2027 p2396 p2493 p2928 p2997 p4278 : Prop) (h : (¬ p2005) ∨ (¬ p2493) ∨ p2997 ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2928)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (p2997) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25507 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule36251 (meaning t m 2005) (meaning t m 2027) (meaning t m 2396) (meaning t m 2493) (meaning t m 2928) (meaning t m 2997) (meaning t m 4278) source

theorem rule36258 (p2027 p2241 p2992 p3115 p3266 p3946 p4191 p4450 p5021 : Prop) (h : (¬ p5021) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3266) ∨ (¬ p4450) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial36258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory25514 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36258 (meaning t m 2027) (meaning t m 2241) (meaning t m 2992) (meaning t m 3115) (meaning t m 3266) (meaning t m 3946) (meaning t m 4191) (meaning t m 4450) (meaning t m 5021) source

theorem rule36261 (p2027 p2241 p2387 p2992 p4272 p4347 p4444 p5021 p5400 : Prop) (h : (¬ p4347) ∨ (¬ p5400) ∨ (¬ p4444) ∨ (¬ p2387) ∨ (¬ p5021) ∨ (¬ p2241) ∨ (¬ p2992) ∨ p2027 ∨ (¬ p4272)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2387) ∨ (¬ p2992) ∨ (¬ p4272) ∨ (¬ p4347) ∨ (¬ p4444) ∨ (¬ p5021) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial36261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4272)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5021)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory25517 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule36261 (meaning t m 2027) (meaning t m 2241) (meaning t m 2387) (meaning t m 2992) (meaning t m 4272) (meaning t m 4347) (meaning t m 4444) (meaning t m 5021) (meaning t m 5400) source

theorem rule36262 (p2027 p3016 p3727 p4700 p4717 p5740 : Prop) (h : (¬ p4700) ∨ (¬ p3727) ∨ (¬ p4717) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p5740)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3727) ∨ (¬ p4700) ∨ (¬ p4717) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial36262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory25518 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 10)
  exact rule36262 (meaning t m 2027) (meaning t m 3016) (meaning t m 3727) (meaning t m 4700) (meaning t m 4717) (meaning t m 5740) source

theorem rule36263 (p1982 p2027 p2210 p2247 p2688 p3146 p3156 p4282 : Prop) (h : p2027 ∨ p2688 ∨ (¬ p2247) ∨ (¬ p1982) ∨ (¬ p2210) ∨ (¬ p4282) ∨ (¬ p3146) ∨ (¬ p3156)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial36263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory25519 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule36263 (meaning t m 1982) (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 3146) (meaning t m 3156) (meaning t m 4282) source

theorem rule36264 (p2027 p3830 p3860 p4352 p4993 p5118 p5580 : Prop) (h : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p4352) ∨ (¬ p4993) ∨ (¬ p3830)) : (p2027) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4993) ∨ (¬ p5118) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial36264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4352)) ∨ (¬ (meaning t m 4993)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory25520 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36264 (meaning t m 2027) (meaning t m 3830) (meaning t m 3860) (meaning t m 4352) (meaning t m 4993) (meaning t m 5118) (meaning t m 5580) source

theorem rule36265 (p3990 p4191 p5117 p5580 : Prop) (h : (¬ p5117) ∨ (¬ p3990) ∨ (¬ p5580) ∨ p4191) : (¬ p3990) ∨ (p4191) ∨ (¬ p5117) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial36265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3990)) ∨ (meaning t m 4191) ∨ (¬ (meaning t m 5117)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory25521 (m.theta 6 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36265 (meaning t m 3990) (meaning t m 4191) (meaning t m 5117) (meaning t m 5580) source

theorem rule36268 (p2027 p2210 p2891 p3325 p3860 p4556 p4993 : Prop) (h : (¬ p3860) ∨ (¬ p4556) ∨ (¬ p2210) ∨ (¬ p3325) ∨ (¬ p4993) ∨ p2027 ∨ (¬ p2891)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3325) ∨ (¬ p3860) ∨ (¬ p4556) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial36268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory25524 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8)
  exact rule36268 (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3325) (meaning t m 3860) (meaning t m 4556) (meaning t m 4993) source

theorem rule36270 (p3576 p3817 p4324 : Prop) (h : (¬ p3576) ∨ (¬ p3817) ∨ p4324) : (¬ p3576) ∨ (¬ p3817) ∨ (p4324) := by
  classical
  tauto

theorem initial36270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3817)) ∨ (meaning t m 4324) := by
  have source := ElevenTheory.theory25526 (m.theta 1 7) (m.theta 2 7) (m.theta 7 9)
  exact rule36270 (meaning t m 3576) (meaning t m 3817) (meaning t m 4324) source

theorem rule36272 (p2027 p2230 p2387 p2663 p2778 p2819 p3276 p3917 p4322 p4397 p4449 p4786 : Prop) (h : (¬ p2387) ∨ (¬ p2819) ∨ p2027 ∨ (¬ p4397) ∨ (¬ p3276) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p3917) ∨ (¬ p2663) ∨ (¬ p2230) ∨ (¬ p4786) ∨ (¬ p2778)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2387) ∨ (¬ p2663) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4322) ∨ (¬ p4397) ∨ (¬ p4449) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial36272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4397)) ∨ (¬ (meaning t m 4449)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory25528 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 2 6) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule36272 (meaning t m 2027) (meaning t m 2230) (meaning t m 2387) (meaning t m 2663) (meaning t m 2778) (meaning t m 2819) (meaning t m 3276) (meaning t m 3917) (meaning t m 4322) (meaning t m 4397) (meaning t m 4449) (meaning t m 4786) source

theorem rule36274 (p2027 p2122 p2230 p2246 p2313 p2663 p2744 p3146 p3156 p3204 p3879 p3917 p3953 p4604 : Prop) (h : (¬ p2313) ∨ (¬ p2122) ∨ (¬ p2663) ∨ p2027 ∨ (¬ p3917) ∨ (¬ p3204) ∨ (¬ p3953) ∨ (¬ p3879) ∨ (¬ p2230) ∨ (¬ p3156) ∨ (¬ p2246) ∨ (¬ p4604) ∨ (¬ p2744) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2230) ∨ (¬ p2246) ∨ (¬ p2313) ∨ (¬ p2663) ∨ (¬ p2744) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3879) ∨ (¬ p3917) ∨ (¬ p3953) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial36274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory25530 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8) (m.theta 6 7) (m.theta 6 9) (m.theta 8 9)
  exact rule36274 (meaning t m 2027) (meaning t m 2122) (meaning t m 2230) (meaning t m 2246) (meaning t m 2313) (meaning t m 2663) (meaning t m 2744) (meaning t m 3146) (meaning t m 3156) (meaning t m 3204) (meaning t m 3879) (meaning t m 3917) (meaning t m 3953) (meaning t m 4604) source

theorem rule36291 (p2027 p2145 p2299 p2651 p2810 p3005 p3097 p3646 p4117 p4550 : Prop) (h : (¬ p4550) ∨ (¬ p2145) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p2651) ∨ (¬ p4117) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p2299) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial36291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory25547 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule36291 (meaning t m 2027) (meaning t m 2145) (meaning t m 2299) (meaning t m 2651) (meaning t m 2810) (meaning t m 3005) (meaning t m 3097) (meaning t m 3646) (meaning t m 4117) (meaning t m 4550) source

theorem rule36296 (p2027 p2246 p2608 p2744 p3286 p3506 p3817 p4366 p4444 p4669 : Prop) (h : (¬ p3506) ∨ (¬ p3817) ∨ (¬ p4444) ∨ (¬ p2744) ∨ (¬ p4669) ∨ p2027 ∨ (¬ p3286) ∨ (¬ p2246) ∨ (¬ p4366) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4444) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25552 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36296 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 3286) (meaning t m 3506) (meaning t m 3817) (meaning t m 4366) (meaning t m 4444) (meaning t m 4669) source

theorem rule36306 (p1994 p2027 p2440 p2764 p3646 p3744 p4031 p4191 : Prop) (h : p2027 ∨ (¬ p1994) ∨ (¬ p4191) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p2440) ∨ (¬ p3744) ∨ p2764) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2764) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4031) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial36306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory25562 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule36306 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2764) (meaning t m 3646) (meaning t m 3744) (meaning t m 4031) (meaning t m 4191) source

theorem rule36308 (p2027 p2717 p3551 p3582 p3587 p3742 p4279 p4753 : Prop) (h : (¬ p3551) ∨ (¬ p3582) ∨ (¬ p4279) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p4753) ∨ (¬ p3587) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3582) ∨ (¬ p3587) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial36308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory25564 t (m.theta 0 7) (m.theta 2 4) (m.theta 2 5) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule36308 (meaning t m 2027) (meaning t m 2717) (meaning t m 3551) (meaning t m 3582) (meaning t m 3587) (meaning t m 3742) (meaning t m 4279) (meaning t m 4753) source

theorem rule36316 (p2027 p2311 p2386 p2717 p3551 p3574 p4753 p5085 : Prop) (h : (¬ p2386) ∨ (¬ p3551) ∨ (¬ p2311) ∨ (¬ p2717) ∨ (¬ p5085) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4753) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial36316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4753)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory25572 t (m.theta 0 6) (m.theta 0 7) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 7 8)
  exact rule36316 (meaning t m 2027) (meaning t m 2311) (meaning t m 2386) (meaning t m 2717) (meaning t m 3551) (meaning t m 3574) (meaning t m 4753) (meaning t m 5085) source

theorem rule36319 (p2027 p2230 p2630 p3519 p3879 p4315 p4814 : Prop) (h : (¬ p2230) ∨ (¬ p3519) ∨ (¬ p3879) ∨ (¬ p4814) ∨ (¬ p4315) ∨ (¬ p2630) ∨ p2027) : (p2027) ∨ (¬ p2230) ∨ (¬ p2630) ∨ (¬ p3519) ∨ (¬ p3879) ∨ (¬ p4315) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial36319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory25575 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule36319 (meaning t m 2027) (meaning t m 2230) (meaning t m 2630) (meaning t m 3519) (meaning t m 3879) (meaning t m 4315) (meaning t m 4814) source

theorem rule36320 (p2027 p2248 p2619 p2946 p3146 p3548 p4316 p4366 p5118 p5558 : Prop) (h : (¬ p2619) ∨ (¬ p3548) ∨ (¬ p5558) ∨ (¬ p2946) ∨ (¬ p4366) ∨ p2027 ∨ (¬ p5118) ∨ (¬ p2248) ∨ (¬ p4316) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2619) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3548) ∨ (¬ p4316) ∨ (¬ p4366) ∨ (¬ p5118) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial36320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5118)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory25576 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 2 5) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36320 (meaning t m 2027) (meaning t m 2248) (meaning t m 2619) (meaning t m 2946) (meaning t m 3146) (meaning t m 3548) (meaning t m 4316) (meaning t m 4366) (meaning t m 5118) (meaning t m 5558) source

theorem rule36323 (p3571 p3690 p3817 : Prop) (h : (¬ p3817) ∨ (¬ p3571) ∨ p3690) : (¬ p3571) ∨ (p3690) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial36323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3571)) ∨ (meaning t m 3690) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory25579 (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule36323 (meaning t m 3571) (meaning t m 3690) (meaning t m 3817) source

theorem rule36326 (p2027 p2341 p3570 p3631 p3821 p4914 : Prop) (h : (¬ p4914) ∨ (¬ p3570) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3570) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4914) := by
  classical
  tauto

theorem initial36326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4914)) := by
  have source := ElevenTheory.theory25582 t (m.theta 0 7) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36326 (meaning t m 2027) (meaning t m 2341) (meaning t m 3570) (meaning t m 3631) (meaning t m 3821) (meaning t m 4914) source

theorem rule36327 (p1984 p2027 p2766 p3266 p3591 p4026 p4191 : Prop) (h : (¬ p4026) ∨ (¬ p1984) ∨ (¬ p4191) ∨ (¬ p3591) ∨ p2027 ∨ p2766 ∨ (¬ p3266)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial36327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory25583 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36327 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3591) (meaning t m 4026) (meaning t m 4191) source

theorem rule36331 (p1997 p2027 p2299 p2396 p2633 p3690 p4110 p4204 : Prop) (h : (¬ p4110) ∨ (¬ p1997) ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2396) ∨ p2027 ∨ (¬ p4204) ∨ (¬ p3690)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3690) ∨ (¬ p4110) ∨ (¬ p4204) := by
  classical
  tauto

theorem initial36331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4204)) := by
  have source := ElevenTheory.theory25587 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36331 (meaning t m 1997) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3690) (meaning t m 4110) (meaning t m 4204) source

theorem rule36333 (p2027 p2598 p2839 p3365 p3585 p5052 : Prop) (h : (¬ p3365) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p5052) ∨ (¬ p3585) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2839) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial36333 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory25589 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule36333 (meaning t m 2027) (meaning t m 2598) (meaning t m 2839) (meaning t m 3365) (meaning t m 3585) (meaning t m 5052) source

theorem rule36335 (p2027 p2608 p3097 p3537 p3609 p3646 p4107 p4524 p4669 : Prop) (h : p2027 ∨ (¬ p2608) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p3609) ∨ (¬ p3537) ∨ (¬ p3097) ∨ (¬ p4524) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3097) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4524) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4524)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25591 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule36335 (meaning t m 2027) (meaning t m 2608) (meaning t m 3097) (meaning t m 3537) (meaning t m 3609) (meaning t m 3646) (meaning t m 4107) (meaning t m 4524) (meaning t m 4669) source

theorem rule36337 (p1994 p2027 p2177 p2311 p2386 p2462 p3551 p3574 p4107 : Prop) (h : (¬ p3574) ∨ (¬ p3551) ∨ p2027 ∨ (¬ p2311) ∨ (¬ p2386) ∨ p2462 ∨ (¬ p1994) ∨ (¬ p4107) ∨ (¬ p2177)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2386) ∨ (p2462) ∨ (¬ p3551) ∨ (¬ p3574) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial36337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2386)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory25593 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36337 (meaning t m 1994) (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2386) (meaning t m 2462) (meaning t m 3551) (meaning t m 3574) (meaning t m 4107) source

theorem rule36338 (p2027 p2958 p3767 p4035 p4207 p4790 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p3767) ∨ (¬ p2958) ∨ (¬ p4035) ∨ (¬ p4790) ∨ (¬ p4207) ∨ p2027) : (p2027) ∨ (¬ p2958) ∨ (¬ p3767) ∨ (¬ p4035) ∨ (¬ p4207) ∨ (¬ p4790) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial36338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4207)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory25594 t (m.theta 0 3) (m.theta 0 5) (m.theta 0 9) (m.theta 2 3) (m.theta 3 9) (m.theta 9 10)
  exact rule36338 (meaning t m 2027) (meaning t m 2958) (meaning t m 3767) (meaning t m 4035) (meaning t m 4207) (meaning t m 4790) (meaning t m 5284) source

theorem rule36341 (p2027 p2248 p2928 p3286 p3452 p3506 p4278 p4322 p4395 : Prop) (h : (¬ p3286) ∨ (¬ p2248) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p3506) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4395) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2928) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3506) ∨ (¬ p4278) ∨ (¬ p4322) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial36341 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory25597 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule36341 (meaning t m 2027) (meaning t m 2248) (meaning t m 2928) (meaning t m 3286) (meaning t m 3452) (meaning t m 3506) (meaning t m 4278) (meaning t m 4322) (meaning t m 4395) source

theorem rule36348 (p2027 p2598 p2850 p3425 p4106 p4644 : Prop) (h : (¬ p3425) ∨ (¬ p2850) ∨ (¬ p2598) ∨ (¬ p4644) ∨ p2027 ∨ (¬ p4106)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3425) ∨ (¬ p4106) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial36348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory25604 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 4 7)
  exact rule36348 (meaning t m 2027) (meaning t m 2598) (meaning t m 2850) (meaning t m 3425) (meaning t m 4106) (meaning t m 4644) source

theorem rule36350 (p2027 p2696 p2753 p3506 p3645 p3646 p3755 p3989 p4877 p5123 p5580 : Prop) (h : (¬ p3645) ∨ (¬ p3646) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p5580) ∨ (¬ p5123) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p2753) ∨ (¬ p3506) ∨ (¬ p3755)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3506) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p3989) ∨ (¬ p4877) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial36350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory25606 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 9) (m.theta 5 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36350 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3506) (meaning t m 3645) (meaning t m 3646) (meaning t m 3755) (meaning t m 3989) (meaning t m 4877) (meaning t m 5123) (meaning t m 5580) source

theorem rule36351 (p1997 p2027 p2323 p2542 p2630 p3286 p4035 : Prop) (h : p2323 ∨ (¬ p2630) ∨ p2027 ∨ (¬ p4035) ∨ (¬ p1997) ∨ (¬ p2542) ∨ (¬ p3286)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p3286) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial36351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory25607 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5)
  exact rule36351 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2542) (meaning t m 2630) (meaning t m 3286) (meaning t m 4035) source

theorem rule36352 (p2247 p3037 p3399 p3848 p4661 : Prop) (h : (¬ p3037) ∨ (¬ p4661) ∨ (¬ p2247) ∨ (¬ p3399) ∨ (¬ p3848)) : (¬ p2247) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3848) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial36352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory25608 (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 3 9)
  exact rule36352 (meaning t m 2247) (meaning t m 3037) (meaning t m 3399) (meaning t m 3848) (meaning t m 4661) source

theorem rule36356 (p2027 p2136 p2247 p2449 p2744 p3037 p3366 p3399 p3646 p3950 p3989 p4347 : Prop) (h : (¬ p2744) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p2136) ∨ (¬ p2449) ∨ (¬ p3950) ∨ (¬ p2247) ∨ (¬ p3646) ∨ (¬ p3037) ∨ (¬ p3989) ∨ (¬ p4347)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2449) ∨ (¬ p2744) ∨ (¬ p3037) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3646) ∨ (¬ p3950) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial36356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory25612 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule36356 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2449) (meaning t m 2744) (meaning t m 3037) (meaning t m 3366) (meaning t m 3399) (meaning t m 3646) (meaning t m 3950) (meaning t m 3989) (meaning t m 4347) source

theorem rule36364 (p2027 p2230 p2440 p2579 p4375 p4390 p4753 : Prop) (h : (¬ p2579) ∨ p2027 ∨ (¬ p4390) ∨ (¬ p2440) ∨ (¬ p4375) ∨ (¬ p4753) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p4375) ∨ (¬ p4390) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial36364 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory25620 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule36364 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2579) (meaning t m 4375) (meaning t m 4390) (meaning t m 4753) source

theorem rule36367 (p1994 p2027 p2230 p2440 p2764 p3346 p4322 p4947 : Prop) (h : p2764 ∨ (¬ p2230) ∨ (¬ p3346) ∨ (¬ p4947) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2764) ∨ (¬ p3346) ∨ (¬ p4322) ∨ (¬ p4947) := by
  classical
  tauto

theorem initial36367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4947)) := by
  have source := ElevenTheory.theory25623 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule36367 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2764) (meaning t m 3346) (meaning t m 4322) (meaning t m 4947) source

theorem rule36368 (p2027 p2696 p2787 p3115 p3136 p3266 p3946 p4191 p4450 : Prop) (h : (¬ p3946) ∨ (¬ p4450) ∨ (¬ p3136) ∨ (¬ p2696) ∨ (¬ p3266) ∨ (¬ p2787) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3266) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4450) := by
  classical
  tauto

theorem initial36368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2787)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4450)) := by
  have source := ElevenTheory.theory25624 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36368 (meaning t m 2027) (meaning t m 2696) (meaning t m 2787) (meaning t m 3115) (meaning t m 3136) (meaning t m 3266) (meaning t m 3946) (meaning t m 4191) (meaning t m 4450) source

theorem rule36370 (p2027 p2230 p2440 p3343 p3591 p3923 p4332 p4347 p5190 : Prop) (h : (¬ p3591) ∨ (¬ p3343) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p4332) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3923) ∨ (¬ p5190)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3343) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4332) ∨ (¬ p4347) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial36370 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory25626 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 6 8) (m.theta 8 9)
  exact rule36370 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 3343) (meaning t m 3591) (meaning t m 3923) (meaning t m 4332) (meaning t m 4347) (meaning t m 5190) source

theorem rule36372 (p2027 p2417 p3556 p3690 p3741 p4533 : Prop) (h : (¬ p2417) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p4533) ∨ (¬ p3741)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3556) ∨ (¬ p3690) ∨ (¬ p3741) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial36372 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3741)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory25628 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule36372 (meaning t m 2027) (meaning t m 2417) (meaning t m 3556) (meaning t m 3690) (meaning t m 3741) (meaning t m 4533) source

theorem rule36375 (p1983 p2027 p2230 p2233 p2417 p2437 p2440 : Prop) (h : (¬ p2440) ∨ (¬ p2230) ∨ p2027 ∨ p2233 ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2440) := by
  classical
  tauto

theorem initial36375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) := by
  have source := ElevenTheory.theory25631 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule36375 (meaning t m 1983) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2417) (meaning t m 2437) (meaning t m 2440) source

theorem rule36376 (p2027 p2470 p2663 p2761 p3343 p3425 p4256 p4638 p4786 p5228 p5387 : Prop) (h : (¬ p2470) ∨ (¬ p4256) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p5387) ∨ (¬ p2663) ∨ (¬ p4786) ∨ (¬ p5228) ∨ (¬ p2761) ∨ (¬ p4638) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2761) ∨ (¬ p3343) ∨ (¬ p3425) ∨ (¬ p4256) ∨ (¬ p4638) ∨ (¬ p4786) ∨ (¬ p5228) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial36376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 5228)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory25632 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 7) (m.theta 2 9) (m.theta 3 4) (m.theta 4 8) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule36376 (meaning t m 2027) (meaning t m 2470) (meaning t m 2663) (meaning t m 2761) (meaning t m 3343) (meaning t m 3425) (meaning t m 4256) (meaning t m 4638) (meaning t m 4786) (meaning t m 5228) (meaning t m 5387) source

theorem rule36377 (p2027 p2417 p3016 p3821 p4112 p4155 p4708 : Prop) (h : p2027 ∨ (¬ p4155) ∨ (¬ p3016) ∨ (¬ p4708) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4112)) : (p2027) ∨ (¬ p2417) ∨ (¬ p3016) ∨ (¬ p3821) ∨ (¬ p4112) ∨ (¬ p4155) ∨ (¬ p4708) := by
  classical
  tauto

theorem initial36377 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4112)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4708)) := by
  have source := ElevenTheory.theory25633 t (m.theta 0 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule36377 (meaning t m 2027) (meaning t m 2417) (meaning t m 3016) (meaning t m 3821) (meaning t m 4112) (meaning t m 4155) (meaning t m 4708) source

theorem rule36383 (p1982 p2027 p2248 p2313 p2633 p2946 p3146 p3156 p3434 p3659 p4107 p5015 : Prop) (h : (¬ p3434) ∨ (¬ p4107) ∨ p2027 ∨ p2633 ∨ (¬ p2313) ∨ (¬ p3659) ∨ (¬ p2248) ∨ (¬ p5015) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p2946) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2248) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p4107) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial36383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory25639 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 6) (m.theta 2 7) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule36383 (meaning t m 1982) (meaning t m 2027) (meaning t m 2248) (meaning t m 2313) (meaning t m 2633) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3434) (meaning t m 3659) (meaning t m 4107) (meaning t m 5015) source

theorem rule36384 (p2027 p3016 p3878 p3998 p4109 p4238 p4717 p5600 : Prop) (h : (¬ p4109) ∨ (¬ p4238) ∨ (¬ p5600) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p3998) ∨ (¬ p4717) ∨ p2027) : (p2027) ∨ (¬ p3016) ∨ (¬ p3878) ∨ (¬ p3998) ∨ (¬ p4109) ∨ (¬ p4238) ∨ (¬ p4717) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial36384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3878)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4238)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory25640 t (m.theta 0 5) (m.theta 0 8) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 6) (m.theta 8 10)
  exact rule36384 (meaning t m 2027) (meaning t m 3016) (meaning t m 3878) (meaning t m 3998) (meaning t m 4109) (meaning t m 4238) (meaning t m 4717) (meaning t m 5600) source

theorem rule36386 (p1985 p2027 p2202 p2341 p2922 p3238 p3570 p3575 : Prop) (h : (¬ p2341) ∨ p2202 ∨ (¬ p3575) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (p2202) ∨ (¬ p2341) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3570) ∨ (¬ p3575) := by
  classical
  tauto

theorem initial36386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3575)) := by
  have source := ElevenTheory.theory25642 t (m.theta 0 7) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule36386 (meaning t m 1985) (meaning t m 2027) (meaning t m 2202) (meaning t m 2341) (meaning t m 2922) (meaning t m 3238) (meaning t m 3570) (meaning t m 3575) source

theorem rule36387 (p1985 p2027 p2766 p3570 p4181 p4347 p4993 p5558 : Prop) (h : p2766 ∨ (¬ p4181) ∨ (¬ p1985) ∨ (¬ p3570) ∨ (¬ p4347) ∨ (¬ p4993) ∨ p2027 ∨ (¬ p5558)) : (¬ p1985) ∨ (p2027) ∨ (p2766) ∨ (¬ p3570) ∨ (¬ p4181) ∨ (¬ p4347) ∨ (¬ p4993) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial36387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4993)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory25643 t (m.theta 1 8) (m.theta 5 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36387 (meaning t m 1985) (meaning t m 2027) (meaning t m 2766) (meaning t m 3570) (meaning t m 4181) (meaning t m 4347) (meaning t m 4993) (meaning t m 5558) source

theorem rule36388 (p3979 p4181 p4993 : Prop) (h : (¬ p4181) ∨ (¬ p4993) ∨ p3979) : (p3979) ∨ (¬ p4181) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial36388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3979) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory25644 (m.theta 1 8) (m.theta 6 8) (m.theta 8 10)
  exact rule36388 (meaning t m 3979) (meaning t m 4181) (meaning t m 4993) source

theorem rule36390 (p3192 p3359 p3742 : Prop) (h : (¬ p3192) ∨ (¬ p3359) ∨ p3742) : (¬ p3192) ∨ (¬ p3359) ∨ (p3742) := by
  classical
  tauto

theorem initial36390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3359)) ∨ (meaning t m 3742) := by
  have source := ElevenTheory.theory25646 (m.theta 3 4) (m.theta 4 7) (m.theta 4 9)
  exact rule36390 (meaning t m 3192) (meaning t m 3359) (meaning t m 3742) source

theorem rule36391 (p2027 p2274 p2396 p3989 p4138 p4668 : Prop) (h : (¬ p4668) ∨ (¬ p4138) ∨ (¬ p2396) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2274)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4668) := by
  classical
  tauto

theorem initial36391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4668)) := by
  have source := ElevenTheory.theory25647 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule36391 (meaning t m 2027) (meaning t m 2274) (meaning t m 2396) (meaning t m 3989) (meaning t m 4138) (meaning t m 4668) source

theorem rule36399 (p2027 p2685 p2753 p2946 p3379 p3549 p3591 p4117 p4315 p4570 p5216 : Prop) (h : (¬ p3549) ∨ (¬ p3591) ∨ (¬ p3379) ∨ (¬ p5216) ∨ (¬ p2753) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p4570) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4315)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2753) ∨ (¬ p2946) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4570) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial36399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory25655 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7)
  exact rule36399 (meaning t m 2027) (meaning t m 2685) (meaning t m 2753) (meaning t m 2946) (meaning t m 3379) (meaning t m 3549) (meaning t m 3591) (meaning t m 4117) (meaning t m 4315) (meaning t m 4570) (meaning t m 5216) source

theorem rule36400 (p2027 p2241 p2449 p3027 p3055 p3584 p4137 p4625 p4736 : Prop) (h : (¬ p4625) ∨ (¬ p3027) ∨ (¬ p2241) ∨ (¬ p4736) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2449) ∨ (¬ p3055) ∨ (¬ p4137)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4625) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial36400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory25656 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9)
  exact rule36400 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3055) (meaning t m 3584) (meaning t m 4137) (meaning t m 4625) (meaning t m 4736) source

theorem rule36403 (p2027 p2668 p2696 p2753 p2797 p3379 p3549 p3591 p4405 p5216 : Prop) (h : (¬ p2668) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3549) ∨ (¬ p2753) ∨ (¬ p5216) ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p4405) ∨ (¬ p2797)) : (p2027) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4405) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial36403 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory25659 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36403 (meaning t m 2027) (meaning t m 2668) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3379) (meaning t m 3549) (meaning t m 3591) (meaning t m 4405) (meaning t m 5216) source

theorem rule36405 (p2027 p2230 p2440 p2780 p3343 p3822 p4107 p4395 p4419 p4952 : Prop) (h : (¬ p2780) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p4419) ∨ (¬ p2440) ∨ (¬ p2230) ∨ (¬ p4952) ∨ (¬ p4395) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4952) := by
  classical
  tauto

theorem initial36405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4952)) := by
  have source := ElevenTheory.theory25661 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule36405 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2780) (meaning t m 3343) (meaning t m 3822) (meaning t m 4107) (meaning t m 4395) (meaning t m 4419) (meaning t m 4952) source

theorem rule36408 (p2027 p2241 p2449 p3027 p3346 p3461 p4425 p4625 p5193 : Prop) (h : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3346) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p5193) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial36408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory25664 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule36408 (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3346) (meaning t m 3461) (meaning t m 4425) (meaning t m 4625) (meaning t m 5193) source

theorem rule36413 (p2027 p2230 p2780 p3276 p3822 p4107 p4322 p4395 p4419 p4449 : Prop) (h : (¬ p3822) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p4419) ∨ (¬ p2230) ∨ (¬ p4395) ∨ (¬ p3276) ∨ (¬ p2780) ∨ (¬ p4449) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3276) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4419) ∨ (¬ p4449) := by
  classical
  tauto

theorem initial36413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4449)) := by
  have source := ElevenTheory.theory25669 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule36413 (meaning t m 2027) (meaning t m 2230) (meaning t m 2780) (meaning t m 3276) (meaning t m 3822) (meaning t m 4107) (meaning t m 4322) (meaning t m 4395) (meaning t m 4419) (meaning t m 4449) source

theorem rule36414 (p2027 p2449 p2696 p2742 p3027 p3583 p4322 p4385 p4394 p4625 p4737 p5252 : Prop) (h : (¬ p5252) ∨ (¬ p4394) ∨ (¬ p4385) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p2449) ∨ (¬ p4625) ∨ (¬ p4322) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3583) ∨ (¬ p4737)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3583) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4394) ∨ (¬ p4625) ∨ (¬ p4737) ∨ (¬ p5252) := by
  classical
  tauto

theorem initial36414 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4394)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4737)) ∨ (¬ (meaning t m 5252)) := by
  have source := ElevenTheory.theory25670 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 7) (m.theta 5 9) (m.theta 6 10) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule36414 (meaning t m 2027) (meaning t m 2449) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3583) (meaning t m 4322) (meaning t m 4385) (meaning t m 4394) (meaning t m 4625) (meaning t m 4737) (meaning t m 5252) source

theorem rule36425 (p2027 p2246 p2608 p2744 p2946 p3156 p3834 p3969 p4321 p5119 : Prop) (h : p2027 ∨ (¬ p3834) ∨ (¬ p5119) ∨ (¬ p4321) ∨ (¬ p3156) ∨ (¬ p3969) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3834) ∨ (¬ p3969) ∨ (¬ p4321) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial36425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory25681 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36425 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2744) (meaning t m 2946) (meaning t m 3156) (meaning t m 3834) (meaning t m 3969) (meaning t m 4321) (meaning t m 5119) source

theorem rule36426 (p2011 p2027 p2299 p2396 p2633 p2761 p4322 : Prop) (h : p2633 ∨ (¬ p2396) ∨ (¬ p2299) ∨ (¬ p2011) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p2761)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2761) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial36426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory25682 t (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule36426 (meaning t m 2011) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 2761) (meaning t m 4322) source

theorem rule36429 (p2027 p2210 p2598 p2753 p3641 p3860 p4149 p4261 p4877 p5122 : Prop) (h : (¬ p3860) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p4149) ∨ (¬ p2210) ∨ (¬ p4877) ∨ (¬ p5122) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3641)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p3641) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p4261) ∨ (¬ p4877) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial36429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory25685 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 8) (m.theta 2 4) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36429 (meaning t m 2027) (meaning t m 2210) (meaning t m 2598) (meaning t m 2753) (meaning t m 3641) (meaning t m 3860) (meaning t m 4149) (meaning t m 4261) (meaning t m 4877) (meaning t m 5122) source

theorem rule36432 (p2027 p2470 p3346 p3609 p4440 p5375 : Prop) (h : (¬ p3346) ∨ (¬ p5375) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p3609) ∨ (¬ p4440)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3346) ∨ (¬ p3609) ∨ (¬ p4440) ∨ (¬ p5375) := by
  classical
  tauto

theorem initial36432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4440)) ∨ (¬ (meaning t m 5375)) := by
  have source := ElevenTheory.theory25688 t (m.theta 0 4) (m.theta 2 8) (m.theta 4 8) (m.theta 4 9) (m.theta 8 9)
  exact rule36432 (meaning t m 2027) (meaning t m 2470) (meaning t m 3346) (meaning t m 3609) (meaning t m 4440) (meaning t m 5375) source

theorem rule36433 (p3821 p4278 p4279 : Prop) (h : (¬ p3821) ∨ (¬ p4279) ∨ p4278) : (¬ p3821) ∨ (p4278) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial36433 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3821)) ∨ (meaning t m 4278) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory25689 (m.theta 0 7) (m.theta 4 7) (m.theta 7 9)
  exact rule36433 (meaning t m 3821) (meaning t m 4278) (meaning t m 4279) source

theorem rule36434 (p1985 p2027 p2264 p2323 p2663 p3355 p3359 p3570 p3580 : Prop) (h : (¬ p3580) ∨ p2323 ∨ (¬ p3570) ∨ (¬ p2663) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p2264)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2663) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial36434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory25690 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8)
  exact rule36434 (meaning t m 1985) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2663) (meaning t m 3355) (meaning t m 3359) (meaning t m 3570) (meaning t m 3580) source

theorem rule36443 (p2027 p2299 p3549 p3591 p4588 p5242 : Prop) (h : (¬ p4588) ∨ (¬ p3591) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p5242)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4588) ∨ (¬ p5242) := by
  classical
  tauto

theorem initial36443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4588)) ∨ (¬ (meaning t m 5242)) := by
  have source := ElevenTheory.theory25699 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule36443 (meaning t m 2027) (meaning t m 2299) (meaning t m 3549) (meaning t m 3591) (meaning t m 4588) (meaning t m 5242) source

theorem rule36444 (p2027 p2177 p2696 p3115 p3136 p3551 p4107 p4395 p5260 : Prop) (h : (¬ p4107) ∨ (¬ p3115) ∨ (¬ p3551) ∨ (¬ p5260) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p4395) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2696) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5260) := by
  classical
  tauto

theorem initial36444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5260)) := by
  have source := ElevenTheory.theory25700 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36444 (meaning t m 2027) (meaning t m 2177) (meaning t m 2696) (meaning t m 3115) (meaning t m 3136) (meaning t m 3551) (meaning t m 4107) (meaning t m 4395) (meaning t m 5260) source

theorem rule36448 (p1995 p2027 p3379 p3498 p3860 p4149 p5693 : Prop) (h : (¬ p1995) ∨ (¬ p4149) ∨ (¬ p5693) ∨ (¬ p3379) ∨ (¬ p3860) ∨ p3498 ∨ p2027) : (¬ p1995) ∨ (p2027) ∨ (¬ p3379) ∨ (p3498) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial36448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory25704 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 8) (m.theta 8 10)
  exact rule36448 (meaning t m 1995) (meaning t m 2027) (meaning t m 3379) (meaning t m 3498) (meaning t m 3860) (meaning t m 4149) (meaning t m 5693) source

theorem rule36450 (p4136 p4782 p5052 : Prop) (h : (¬ p4136) ∨ (¬ p5052) ∨ p4782) : (¬ p4136) ∨ (p4782) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial36450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4136)) ∨ (meaning t m 4782) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory25706 t (m.theta 2 3) (m.theta 2 5) (m.theta 2 7)
  exact rule36450 (meaning t m 4136) (meaning t m 4782) (meaning t m 5052) source

theorem rule36455 (p1976 p2027 p2764 p3055 p3876 p4278 p4381 : Prop) (h : (¬ p3055) ∨ (¬ p1976) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p4278) ∨ p2764 ∨ (¬ p4381)) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial36455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory25711 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule36455 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3055) (meaning t m 3876) (meaning t m 4278) (meaning t m 4381) source

theorem rule36457 (p1996 p2027 p2509 p2922 p3498 p3516 p3575 p3947 : Prop) (h : p3498 ∨ p2027 ∨ (¬ p3575) ∨ (¬ p1996) ∨ (¬ p3947) ∨ (¬ p2922) ∨ (¬ p3516) ∨ (¬ p2509)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2509) ∨ (¬ p2922) ∨ (p3498) ∨ (¬ p3516) ∨ (¬ p3575) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial36457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2922)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory25713 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 9)
  exact rule36457 (meaning t m 1996) (meaning t m 2027) (meaning t m 2509) (meaning t m 2922) (meaning t m 3498) (meaning t m 3516) (meaning t m 3575) (meaning t m 3947) source

theorem rule36462 (p2027 p2246 p2331 p2608 p2668 p2744 p3860 p3979 p4261 p5122 : Prop) (h : (¬ p2331) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p2246) ∨ (¬ p3979) ∨ (¬ p3860) ∨ (¬ p2608) ∨ (¬ p5122) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3860) ∨ (¬ p3979) ∨ (¬ p4261) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial36462 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory25718 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36462 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2608) (meaning t m 2668) (meaning t m 2744) (meaning t m 3860) (meaning t m 3979) (meaning t m 4261) (meaning t m 5122) source

theorem rule36465 (p2027 p2493 p2982 p4202 p4363 p4717 : Prop) (h : (¬ p2982) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p4363) ∨ (¬ p4202) ∨ (¬ p4717)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2982) ∨ (¬ p4202) ∨ (¬ p4363) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial36465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4363)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory25721 t (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule36465 (meaning t m 2027) (meaning t m 2493) (meaning t m 2982) (meaning t m 4202) (meaning t m 4363) (meaning t m 4717) source

theorem rule36467 (p2027 p3367 p3389 p3583 p3698 p3759 p4646 : Prop) (h : (¬ p3389) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p4646) ∨ (¬ p3367) ∨ p2027) : (p2027) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3759) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial36467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory25723 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7)
  exact rule36467 (meaning t m 2027) (meaning t m 3367) (meaning t m 3389) (meaning t m 3583) (meaning t m 3698) (meaning t m 3759) (meaning t m 4646) source

theorem rule36468 (p2027 p2299 p2313 p2417 p2598 p2785 p2922 p3590 p3688 p4668 p4737 : Prop) (h : p2027 ∨ (¬ p4668) ∨ (¬ p2299) ∨ (¬ p2417) ∨ (¬ p2313) ∨ (¬ p3688) ∨ (¬ p2922) ∨ (¬ p2598) ∨ (¬ p3590) ∨ (¬ p4737) ∨ (¬ p2785)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2785) ∨ (¬ p2922) ∨ (¬ p3590) ∨ (¬ p3688) ∨ (¬ p4668) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial36468 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4668)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory25724 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36468 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2417) (meaning t m 2598) (meaning t m 2785) (meaning t m 2922) (meaning t m 3590) (meaning t m 3688) (meaning t m 4668) (meaning t m 4737) source

theorem rule36469 (p1995 p2027 p2177 p2997 p3379 p3548 p4366 : Prop) (h : (¬ p3548) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p1995) ∨ (¬ p4366) ∨ p2997 ∨ (¬ p3379)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3379) ∨ (¬ p3548) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial36469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory25725 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8)
  exact rule36469 (meaning t m 1995) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3379) (meaning t m 3548) (meaning t m 4366) source

theorem rule36470 (p2027 p2829 p2850 p3238 p3475 p4257 p4845 : Prop) (h : (¬ p4257) ∨ (¬ p3475) ∨ (¬ p2850) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p4845) ∨ (¬ p3238)) : (p2027) ∨ (¬ p2829) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3475) ∨ (¬ p4257) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial36470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory25726 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5)
  exact rule36470 (meaning t m 2027) (meaning t m 2829) (meaning t m 2850) (meaning t m 3238) (meaning t m 3475) (meaning t m 4257) (meaning t m 4845) source

theorem rule36472 (p2437 p3683 p3876 : Prop) (h : (¬ p3876) ∨ (¬ p2437) ∨ (¬ p3683)) : (¬ p2437) ∨ (¬ p3683) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial36472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory25728 (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule36472 (meaning t m 2437) (meaning t m 3683) (meaning t m 3876) source

theorem rule36473 (p1975 p2027 p2252 p2295 p2622 p2641 p2952 p3136 : Prop) (h : (¬ p2641) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p2952) ∨ (¬ p1975) ∨ p2622 ∨ (¬ p3136)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2295) ∨ (p2622) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial36473 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory25729 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 6 7)
  exact rule36473 (meaning t m 1975) (meaning t m 2027) (meaning t m 2252) (meaning t m 2295) (meaning t m 2622) (meaning t m 2641) (meaning t m 2952) (meaning t m 3136) source

theorem rule36476 (p2027 p2717 p3347 p3487 p3551 p4315 p4701 p4781 p5197 : Prop) (h : (¬ p4701) ∨ (¬ p3487) ∨ (¬ p5197) ∨ (¬ p4781) ∨ (¬ p3347) ∨ (¬ p4315) ∨ p2027 ∨ (¬ p3551) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3347) ∨ (¬ p3487) ∨ (¬ p3551) ∨ (¬ p4315) ∨ (¬ p4701) ∨ (¬ p4781) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial36476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4701)) ∨ (¬ (meaning t m 4781)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory25732 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 5) (m.theta 7 8)
  exact rule36476 (meaning t m 2027) (meaning t m 2717) (meaning t m 3347) (meaning t m 3487) (meaning t m 3551) (meaning t m 4315) (meaning t m 4701) (meaning t m 4781) (meaning t m 5197) source

theorem rule36478 (p1976 p2027 p2633 p3055 p3367 p3588 p3644 p4106 : Prop) (h : p2633 ∨ (¬ p1976) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p3055) ∨ (¬ p4106) ∨ (¬ p3588)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3644) ∨ (¬ p4106) := by
  classical
  tauto

theorem initial36478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4106)) := by
  have source := ElevenTheory.theory25734 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule36478 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 3055) (meaning t m 3367) (meaning t m 3588) (meaning t m 3644) (meaning t m 4106) source

theorem rule36479 (p2027 p2246 p2264 p2807 p3645 p3646 p3744 p3941 p4191 p4959 p5119 : Prop) (h : (¬ p3645) ∨ (¬ p5119) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p4191) ∨ (¬ p4959) ∨ (¬ p3646) ∨ (¬ p2807) ∨ (¬ p3941) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3941) ∨ (¬ p4191) ∨ (¬ p4959) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial36479 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4959)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory25735 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 7) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36479 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2807) (meaning t m 3645) (meaning t m 3646) (meaning t m 3744) (meaning t m 3941) (meaning t m 4191) (meaning t m 4959) (meaning t m 5119) source

theorem rule36481 (p2027 p2177 p2311 p2608 p2839 p3105 p3551 p4107 p4395 p5021 : Prop) (h : p2027 ∨ (¬ p2177) ∨ (¬ p3551) ∨ (¬ p2839) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p2311) ∨ (¬ p3105) ∨ (¬ p5021) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2608) ∨ (¬ p2839) ∨ (¬ p3105) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5021) := by
  classical
  tauto

theorem initial36481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5021)) := by
  have source := ElevenTheory.theory25737 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36481 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2608) (meaning t m 2839) (meaning t m 3105) (meaning t m 3551) (meaning t m 4107) (meaning t m 4395) (meaning t m 5021) source

theorem rule36482 (p2027 p2449 p2881 p3553 p4277 p4278 : Prop) (h : (¬ p4278) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p2449) ∨ (¬ p4277) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2881) ∨ (¬ p3553) ∨ (¬ p4277) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25738 t (m.theta 3 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36482 (meaning t m 2027) (meaning t m 2449) (meaning t m 2881) (meaning t m 3553) (meaning t m 4277) (meaning t m 4278) source

theorem rule36483 (p2027 p2177 p2449 p3553 p4276 p4278 : Prop) (h : (¬ p4278) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p4276) ∨ (¬ p2449) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2449) ∨ (¬ p3553) ∨ (¬ p4276) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial36483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory25739 t (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36483 (meaning t m 2027) (meaning t m 2177) (meaning t m 2449) (meaning t m 3553) (meaning t m 4276) (meaning t m 4278) source

theorem rule36485 (p1984 p2027 p2417 p2633 p2926 p3452 p3644 p3817 : Prop) (h : (¬ p3817) ∨ (¬ p2417) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3644) ∨ p2633 ∨ (¬ p2926)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2417) ∨ (p2633) ∨ (¬ p2926) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial36485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory25741 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule36485 (meaning t m 1984) (meaning t m 2027) (meaning t m 2417) (meaning t m 2633) (meaning t m 2926) (meaning t m 3452) (meaning t m 3644) (meaning t m 3817) source

theorem rule36488 (p2027 p2139 p2156 p3055 p3156 p3644 p3876 p3952 p4133 p4441 : Prop) (h : (¬ p3644) ∨ (¬ p4441) ∨ (¬ p4133) ∨ (¬ p3876) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p2139) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p3952)) : (p2027) ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p3952) ∨ (¬ p4133) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial36488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2139)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory25744 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 7 8)
  exact rule36488 (meaning t m 2027) (meaning t m 2139) (meaning t m 2156) (meaning t m 3055) (meaning t m 3156) (meaning t m 3644) (meaning t m 3876) (meaning t m 3952) (meaning t m 4133) (meaning t m 4441) source

theorem rule36490 (p2187 p2588 p3955 p4203 : Prop) (h : (¬ p3955) ∨ (¬ p4203) ∨ (¬ p2588) ∨ (¬ p2187)) : (¬ p2187) ∨ (¬ p2588) ∨ (¬ p3955) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial36490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory25746 (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule36490 (meaning t m 2187) (meaning t m 2588) (meaning t m 3955) (meaning t m 4203) source

theorem rule36491 (p2027 p2743 p3363 p3527 p3551 p3687 p4752 p5197 : Prop) (h : (¬ p5197) ∨ (¬ p3527) ∨ (¬ p2743) ∨ (¬ p3551) ∨ (¬ p3687) ∨ p2027 ∨ (¬ p3363) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2743) ∨ (¬ p3363) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3687) ∨ (¬ p4752) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial36491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory25747 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 7 8)
  exact rule36491 (meaning t m 2027) (meaning t m 2743) (meaning t m 3363) (meaning t m 3527) (meaning t m 3551) (meaning t m 3687) (meaning t m 4752) (meaning t m 5197) source

theorem rule36493 (p3371 p4496 p5316 : Prop) (h : (¬ p3371) ∨ (¬ p4496) ∨ p5316) : (¬ p3371) ∨ (¬ p4496) ∨ (p5316) := by
  classical
  tauto

theorem initial36493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 4496)) ∨ (meaning t m 5316) := by
  have source := ElevenTheory.theory25749 (m.theta 1 2) (m.theta 1 5) (m.theta 1 8)
  exact rule36493 (meaning t m 3371) (meaning t m 4496) (meaning t m 5316) source

theorem rule36494 (p1981 p2027 p3474 p3537 p3583 p3609 p4347 : Prop) (h : (¬ p3609) ∨ (¬ p4347) ∨ (¬ p1981) ∨ p2027 ∨ (¬ p3583) ∨ p3474 ∨ (¬ p3537)) : (¬ p1981) ∨ (p2027) ∨ (p3474) ∨ (¬ p3537) ∨ (¬ p3583) ∨ (¬ p3609) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial36494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory25750 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule36494 (meaning t m 1981) (meaning t m 2027) (meaning t m 3474) (meaning t m 3537) (meaning t m 3583) (meaning t m 3609) (meaning t m 4347) source

theorem rule36498 (p1984 p2027 p2299 p2622 p2743 p2780 p2839 p3609 p3692 p3822 p3873 p4744 p4902 : Prop) (h : (¬ p2743) ∨ p2622 ∨ (¬ p3692) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3873) ∨ (¬ p3822) ∨ (¬ p2839) ∨ (¬ p4744) ∨ (¬ p1984) ∨ (¬ p4902) ∨ (¬ p3609)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (¬ p2839) ∨ (¬ p3609) ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p4744) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial36498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4744)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory25754 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 2 8) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule36498 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2622) (meaning t m 2743) (meaning t m 2780) (meaning t m 2839) (meaning t m 3609) (meaning t m 3692) (meaning t m 3822) (meaning t m 3873) (meaning t m 4744) (meaning t m 4902) source

theorem rule36500 (p3083 p3683 p3874 : Prop) (h : (¬ p3683) ∨ (¬ p3083) ∨ (¬ p3874)) : (¬ p3083) ∨ (¬ p3683) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial36500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory25756 (m.theta 2 4) (m.theta 3 4) (m.theta 4 8)
  exact rule36500 (meaning t m 3083) (meaning t m 3683) (meaning t m 3874) source

theorem rule36501 (p2027 p2313 p2449 p2807 p4107 p4583 : Prop) (h : p2027 ∨ (¬ p4107) ∨ (¬ p2807) ∨ (¬ p2449) ∨ (¬ p4583) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p4107) ∨ (¬ p4583) := by
  classical
  tauto

theorem initial36501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4583)) := by
  have source := ElevenTheory.theory25757 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule36501 (meaning t m 2027) (meaning t m 2313) (meaning t m 2449) (meaning t m 2807) (meaning t m 4107) (meaning t m 4583) source

theorem rule36503 (p1988 p2027 p2622 p2743 p3276 p3355 p3367 p3759 : Prop) (h : p2622 ∨ (¬ p2743) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p3759) ∨ (¬ p1988) ∨ (¬ p3355)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial36503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory25759 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 9) (m.theta 9 10)
  exact rule36503 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3276) (meaning t m 3355) (meaning t m 3367) (meaning t m 3759) source

theorem rule36511 (p2027 p3587 p4253 p4320 p5053 p5660 : Prop) (h : (¬ p5660) ∨ p2027 ∨ (¬ p5053) ∨ (¬ p3587) ∨ (¬ p4253) ∨ (¬ p4320)) : (p2027) ∨ (¬ p3587) ∨ (¬ p4253) ∨ (¬ p4320) ∨ (¬ p5053) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial36511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5053)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory25767 t (m.theta 2 5) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 7 10)
  exact rule36511 (meaning t m 2027) (meaning t m 3587) (meaning t m 4253) (meaning t m 4320) (meaning t m 5053) (meaning t m 5660) source

theorem rule36513 (p2027 p2246 p2341 p2751 p3553 p3572 p4104 : Prop) (h : (¬ p4104) ∨ (¬ p2751) ∨ (¬ p2246) ∨ (¬ p3572) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p3553)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2341) ∨ (¬ p2751) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4104) := by
  classical
  tauto

theorem initial36513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4104)) := by
  have source := ElevenTheory.theory25769 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule36513 (meaning t m 2027) (meaning t m 2246) (meaning t m 2341) (meaning t m 2751) (meaning t m 3553) (meaning t m 3572) (meaning t m 4104) source

theorem rule36516 (p3550 p4384 p4438 : Prop) (h : (¬ p3550) ∨ (¬ p4438) ∨ p4384) : (¬ p3550) ∨ (p4384) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial36516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3550)) ∨ (meaning t m 4384) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory25772 t (m.theta 4 8) (m.theta 6 8) (m.theta 7 8)
  exact rule36516 (meaning t m 3550) (meaning t m 4384) (meaning t m 4438) source

theorem rule36520 (p1992 p2027 p2764 p3583 p3744 p3758 p4191 : Prop) (h : p2764 ∨ (¬ p3744) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p4191) ∨ (¬ p3583) ∨ (¬ p3758)) : (¬ p1992) ∨ (p2027) ∨ (p2764) ∨ (¬ p3583) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial36520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory25776 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule36520 (meaning t m 1992) (meaning t m 2027) (meaning t m 2764) (meaning t m 3583) (meaning t m 3744) (meaning t m 3758) (meaning t m 4191) source

theorem rule36521 (p2027 p2860 p2934 p3379 p3527 p3644 p3646 p4244 p4277 p4524 : Prop) (h : (¬ p4277) ∨ (¬ p4244) ∨ (¬ p3379) ∨ (¬ p2934) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p4524) ∨ (¬ p3644) ∨ (¬ p3527) ∨ (¬ p3646)) : (p2027) ∨ (¬ p2860) ∨ (¬ p2934) ∨ (¬ p3379) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4524) := by
  classical
  tauto

theorem initial36521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4524)) := by
  have source := ElevenTheory.theory25777 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 1 7) (m.theta 2 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule36521 (meaning t m 2027) (meaning t m 2860) (meaning t m 2934) (meaning t m 3379) (meaning t m 3527) (meaning t m 3644) (meaning t m 3646) (meaning t m 4244) (meaning t m 4277) (meaning t m 4524) source

theorem rule36523 (p2891 p2901 p4282 : Prop) (h : (¬ p2901) ∨ (¬ p4282) ∨ p2891) : (p2891) ∨ (¬ p2901) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial36523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2891) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory25779 (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule36523 (meaning t m 2891) (meaning t m 2901) (meaning t m 4282) source

theorem rule36532 (p1985 p2027 p2323 p2417 p2437 p2651 p3690 : Prop) (h : (¬ p2651) ∨ (¬ p2417) ∨ (¬ p3690) ∨ p2323 ∨ (¬ p2437) ∨ p2027 ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial36532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory25788 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule36532 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3690) source

theorem rule36533 (p2027 p2136 p2247 p2417 p2744 p2933 p3366 p3399 p3461 p4032 p4625 p5030 p5387 : Prop) (h : (¬ p2136) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p3399) ∨ (¬ p2417) ∨ (¬ p2247) ∨ (¬ p2933) ∨ (¬ p3366) ∨ (¬ p5030) ∨ (¬ p5387) ∨ (¬ p3461) ∨ (¬ p2744) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2417) ∨ (¬ p2744) ∨ (¬ p2933) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3461) ∨ (¬ p4032) ∨ (¬ p4625) ∨ (¬ p5030) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial36533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5030)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory25789 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 9) (m.theta 4 7) (m.theta 5 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule36533 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2417) (meaning t m 2744) (meaning t m 2933) (meaning t m 3366) (meaning t m 3399) (meaning t m 3461) (meaning t m 4032) (meaning t m 4625) (meaning t m 5030) (meaning t m 5387) source

theorem rule36540 (p2027 p2589 p3093 p3319 p3347 p3690 p3954 p4235 p4621 p5216 : Prop) (h : (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3690) ∨ (¬ p3347) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p5216) ∨ (¬ p4621) ∨ (¬ p3319) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3690) ∨ (¬ p3954) ∨ (¬ p4235) ∨ (¬ p4621) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial36540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory25796 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9)
  exact rule36540 (meaning t m 2027) (meaning t m 2589) (meaning t m 3093) (meaning t m 3319) (meaning t m 3347) (meaning t m 3690) (meaning t m 3954) (meaning t m 4235) (meaning t m 4621) (meaning t m 5216) source

theorem rule36542 (p2027 p2138 p2246 p2651 p2744 p3083 p3366 p4149 p4322 p4385 p5119 : Prop) (h : (¬ p2744) ∨ (¬ p3366) ∨ (¬ p5119) ∨ (¬ p2246) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p4322) ∨ (¬ p2138) ∨ (¬ p4149) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p4149) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial36542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory25798 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36542 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 3083) (meaning t m 3366) (meaning t m 4149) (meaning t m 4322) (meaning t m 4385) (meaning t m 5119) source

theorem rule36551 (p2027 p2104 p2248 p2449 p2807 p3537 p3588 p3690 p3873 p4898 : Prop) (h : (¬ p2807) ∨ (¬ p3873) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p4898) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p3588) ∨ (¬ p3537) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2248) ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p3690) ∨ (¬ p3873) ∨ (¬ p4898) := by
  classical
  tauto

theorem initial36551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4898)) := by
  have source := ElevenTheory.theory25807 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule36551 (meaning t m 2027) (meaning t m 2104) (meaning t m 2248) (meaning t m 2449) (meaning t m 2807) (meaning t m 3537) (meaning t m 3588) (meaning t m 3690) (meaning t m 3873) (meaning t m 4898) source

theorem rule36552 (p2027 p2248 p2437 p2651 p2911 p3688 p3954 p4358 p4503 : Prop) (h : (¬ p4503) ∨ (¬ p3688) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4358) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial36552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory25808 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 8) (m.theta 7 8)
  exact rule36552 (meaning t m 2027) (meaning t m 2248) (meaning t m 2437) (meaning t m 2651) (meaning t m 2911) (meaning t m 3688) (meaning t m 3954) (meaning t m 4358) (meaning t m 4503) source

theorem rule36564 (p2027 p2246 p2717 p2744 p2958 p3212 p3366 p3506 p3551 p3820 p4040 p4191 p4324 p4621 : Prop) (h : (¬ p3212) ∨ (¬ p3506) ∨ (¬ p2958) ∨ (¬ p4621) ∨ (¬ p4040) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p4324) ∨ (¬ p2744) ∨ (¬ p2717) ∨ (¬ p2246) ∨ (¬ p4191) ∨ (¬ p3820) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2717) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p3366) ∨ (¬ p3506) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4040) ∨ (¬ p4191) ∨ (¬ p4324) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial36564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory25820 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 9) (m.theta 5 9) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule36564 (meaning t m 2027) (meaning t m 2246) (meaning t m 2717) (meaning t m 2744) (meaning t m 2958) (meaning t m 3212) (meaning t m 3366) (meaning t m 3506) (meaning t m 3551) (meaning t m 3820) (meaning t m 4040) (meaning t m 4191) (meaning t m 4324) (meaning t m 4621) source

theorem rule36567 (p2027 p3201 p3569 p3684 p4320 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p3201) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4320) ∨ p2027) : (p2027) ∨ (¬ p3201) ∨ (¬ p3569) ∨ (¬ p3684) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial36567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory25823 t (m.theta 2 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule36567 (meaning t m 2027) (meaning t m 3201) (meaning t m 3569) (meaning t m 3684) (meaning t m 4320) (meaning t m 4702) source

theorem rule36569 (p2027 p2248 p2417 p2437 p2651 p3688 p3917 p3954 p4625 : Prop) (h : (¬ p2248) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3917) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p3688) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial36569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory25825 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 7) (m.theta 6 9) (m.theta 7 9)
  exact rule36569 (meaning t m 2027) (meaning t m 2248) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4625) source

theorem rule36570 (p1998 p2027 p2114 p2437 p2651 p2737 p2811 p2911 : Prop) (h : (¬ p1998) ∨ (¬ p2911) ∨ p2114 ∨ (¬ p2651) ∨ (¬ p2437) ∨ (¬ p2811) ∨ p2027 ∨ (¬ p2737)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2911) := by
  classical
  tauto

theorem initial36570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2911)) := by
  have source := ElevenTheory.theory25826 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule36570 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2437) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 2911) source

theorem rule36573 (p1979 p2027 p2396 p2992 p2996 p2997 p3947 : Prop) (h : (¬ p1979) ∨ p2997 ∨ (¬ p2396) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2996)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (p2997) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial36573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory25829 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule36573 (meaning t m 1979) (meaning t m 2027) (meaning t m 2396) (meaning t m 2992) (meaning t m 2996) (meaning t m 2997) (meaning t m 3947) source

theorem rule36574 (p2027 p2246 p2608 p2651 p2744 p3276 p3343 p3860 p4353 p5123 p5612 : Prop) (h : p2027 ∨ (¬ p2246) ∨ (¬ p3343) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2651) ∨ (¬ p3276) ∨ (¬ p3860) ∨ (¬ p5123) ∨ (¬ p4353) ∨ (¬ p5612)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p3860) ∨ (¬ p4353) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial36574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4353)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory25830 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 2 8) (m.theta 3 4) (m.theta 4 9) (m.theta 8 10) (m.theta 9 10)
  exact rule36574 (meaning t m 2027) (meaning t m 2246) (meaning t m 2608) (meaning t m 2651) (meaning t m 2744) (meaning t m 3276) (meaning t m 3343) (meaning t m 3860) (meaning t m 4353) (meaning t m 5123) (meaning t m 5612) source

theorem rule36576 (p2027 p2246 p2651 p2744 p3016 p3366 p3425 p3888 p4324 p4381 p5250 : Prop) (h : (¬ p4381) ∨ (¬ p4324) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p3425) ∨ (¬ p2246) ∨ (¬ p3888) ∨ (¬ p5250) ∨ (¬ p2651)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3888) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5250) := by
  classical
  tauto

theorem initial36576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5250)) := by
  have source := ElevenTheory.theory25832 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule36576 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2744) (meaning t m 3016) (meaning t m 3366) (meaning t m 3425) (meaning t m 3888) (meaning t m 4324) (meaning t m 4381) (meaning t m 5250) source

theorem rule36577 (p2027 p2386 p2437 p2779 p3574 p4358 p4501 p4710 : Prop) (h : (¬ p2386) ∨ (¬ p4501) ∨ (¬ p2437) ∨ (¬ p3574) ∨ (¬ p4358) ∨ (¬ p2779) ∨ (¬ p4710) ∨ p2027) : (p2027) ∨ (¬ p2386) ∨ (¬ p2437) ∨ (¬ p2779) ∨ (¬ p3574) ∨ (¬ p4358) ∨ (¬ p4501) ∨ (¬ p4710) := by
  classical
  tauto

theorem initial36577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2779)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4501)) ∨ (¬ (meaning t m 4710)) := by
  have source := ElevenTheory.theory25833 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8)
  exact rule36577 (meaning t m 2027) (meaning t m 2386) (meaning t m 2437) (meaning t m 2779) (meaning t m 3574) (meaning t m 4358) (meaning t m 4501) (meaning t m 4710) source

theorem rule36578 (p1976 p2027 p2766 p2780 p2829 p4242 p4347 p4857 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p1976) ∨ (¬ p4347) ∨ (¬ p2829) ∨ (¬ p4857) ∨ (¬ p4242) ∨ (¬ p2780)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p4242) ∨ (¬ p4347) ∨ (¬ p4857) := by
  classical
  tauto

theorem initial36578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4857)) := by
  have source := ElevenTheory.theory25834 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule36578 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 2780) (meaning t m 2829) (meaning t m 4242) (meaning t m 4347) (meaning t m 4857) source

theorem rule36584 (p2027 p2246 p2363 p2749 p2807 p3005 p3347 p3572 p3646 p3692 p3904 p3988 p4771 p5216 : Prop) (h : (¬ p3347) ∨ (¬ p5216) ∨ (¬ p3988) ∨ (¬ p2363) ∨ (¬ p2749) ∨ (¬ p3904) ∨ (¬ p3005) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3692) ∨ (¬ p3646) ∨ (¬ p4771) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2363) ∨ (¬ p2749) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3347) ∨ (¬ p3572) ∨ (¬ p3646) ∨ (¬ p3692) ∨ (¬ p3904) ∨ (¬ p3988) ∨ (¬ p4771) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial36584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4771)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory25840 t (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule36584 (meaning t m 2027) (meaning t m 2246) (meaning t m 2363) (meaning t m 2749) (meaning t m 2807) (meaning t m 3005) (meaning t m 3347) (meaning t m 3572) (meaning t m 3646) (meaning t m 3692) (meaning t m 3904) (meaning t m 3988) (meaning t m 4771) (meaning t m 5216) source

theorem rule36586 (p2027 p2417 p2437 p2651 p3146 p3657 p3877 p4118 p4790 p4905 : Prop) (h : (¬ p2417) ∨ (¬ p2651) ∨ (¬ p4790) ∨ (¬ p3877) ∨ (¬ p2437) ∨ (¬ p3657) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p3146) ∨ (¬ p4118)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p3146) ∨ (¬ p3657) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4790) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial36586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4790)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory25842 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule36586 (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 2651) (meaning t m 3146) (meaning t m 3657) (meaning t m 3877) (meaning t m 4118) (meaning t m 4790) (meaning t m 4905) source

theorem rule36587 (p2027 p2396 p3027 p3848 p4570 p4656 : Prop) (h : p2027 ∨ (¬ p4570) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p4656) ∨ (¬ p3848)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3848) ∨ (¬ p4570) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial36587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory25843 t (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 6 7) (m.theta 7 9)
  exact rule36587 (meaning t m 2027) (meaning t m 2396) (meaning t m 3027) (meaning t m 3848) (meaning t m 4570) (meaning t m 4656) source

theorem rule36597 (p3016 p3083 p3573 : Prop) (h : (¬ p3083) ∨ (¬ p3573) ∨ p3016) : (p3016) ∨ (¬ p3083) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial36597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3016) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory25853 (m.theta 3 4) (m.theta 4 6) (m.theta 4 8)
  exact rule36597 (meaning t m 3016) (meaning t m 3083) (meaning t m 3573) source

theorem rule36599 (p1986 p2027 p2114 p2387 p2598 p2778 p2819 p2829 : Prop) (h : (¬ p1986) ∨ (¬ p2598) ∨ p2027 ∨ p2114 ∨ (¬ p2819) ∨ (¬ p2387) ∨ (¬ p2778) ∨ (¬ p2829)) : (¬ p1986) ∨ (p2027) ∨ (p2114) ∨ (¬ p2387) ∨ (¬ p2598) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial36599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory25855 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8)
  exact rule36599 (meaning t m 1986) (meaning t m 2027) (meaning t m 2114) (meaning t m 2387) (meaning t m 2598) (meaning t m 2778) (meaning t m 2819) (meaning t m 2829) source

theorem rule36600 (p2027 p2241 p2299 p2579 p2588 p2992 p3156 p4902 p5193 : Prop) (h : (¬ p4902) ∨ (¬ p2992) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p3156) ∨ (¬ p2241) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p4902) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial36600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4902)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory25856 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule36600 (meaning t m 2027) (meaning t m 2241) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2992) (meaning t m 3156) (meaning t m 4902) (meaning t m 5193) source

theorem rule36602 (p2027 p2156 p2246 p2744 p2958 p3115 p3366 p3425 p3659 p3952 p4330 p4348 p5045 : Prop) (h : (¬ p3952) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p3366) ∨ (¬ p3659) ∨ (¬ p2958) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p3425) ∨ (¬ p4330) ∨ (¬ p5045) ∨ (¬ p4348) ∨ (¬ p3115)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3952) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial36602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory25858 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule36602 (meaning t m 2027) (meaning t m 2156) (meaning t m 2246) (meaning t m 2744) (meaning t m 2958) (meaning t m 3115) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 3952) (meaning t m 4330) (meaning t m 4348) (meaning t m 5045) source

theorem rule36603 (p1982 p2027 p2528 p2819 p3586 p3979 p4286 : Prop) (h : p2027 ∨ p3586 ∨ (¬ p2819) ∨ (¬ p1982) ∨ (¬ p2528) ∨ (¬ p4286) ∨ (¬ p3979)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (¬ p2819) ∨ (p3586) ∨ (¬ p3979) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial36603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 3586) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory25859 t (m.theta 2 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule36603 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2819) (meaning t m 3586) (meaning t m 3979) (meaning t m 4286) source

theorem rule36609 (p1984 p2027 p2409 p2493 p3584 p3585 p3954 : Prop) (h : (¬ p3584) ∨ (¬ p2493) ∨ p2409 ∨ p2027 ∨ (¬ p3954) ∨ (¬ p1984) ∨ (¬ p3585)) : (¬ p1984) ∨ (p2027) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial36609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory25865 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6)
  exact rule36609 (meaning t m 1984) (meaning t m 2027) (meaning t m 2409) (meaning t m 2493) (meaning t m 3584) (meaning t m 3585) (meaning t m 3954) source

theorem rule36613 (p2027 p2248 p2528 p2651 p3083 p3688 p3917 p3954 p4604 : Prop) (h : (¬ p2248) ∨ (¬ p3954) ∨ (¬ p3083) ∨ (¬ p3688) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p4604) ∨ (¬ p2528) ∨ (¬ p3917)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial36613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory25869 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 9)
  exact rule36613 (meaning t m 2027) (meaning t m 2248) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4604) source

theorem rule36614 (p2027 p2667 p2745 p4019 p4154 p4197 p4781 p4805 p5590 : Prop) (h : (¬ p2667) ∨ (¬ p4197) ∨ (¬ p4781) ∨ p2027 ∨ (¬ p4805) ∨ (¬ p4154) ∨ (¬ p2745) ∨ (¬ p5590) ∨ (¬ p4019)) : (p2027) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p4019) ∨ (¬ p4154) ∨ (¬ p4197) ∨ (¬ p4781) ∨ (¬ p4805) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial36614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2667)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4781)) ∨ (¬ (meaning t m 4805)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory25870 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8) (m.theta 3 6) (m.theta 8 10)
  exact rule36614 (meaning t m 2027) (meaning t m 2667) (meaning t m 2745) (meaning t m 4019) (meaning t m 4154) (meaning t m 4197) (meaning t m 4781) (meaning t m 4805) (meaning t m 5590) source

theorem rule36615 (p1990 p2027 p2323 p2563 p2651 p2810 p3136 p4241 : Prop) (h : (¬ p2563) ∨ p2323 ∨ (¬ p1990) ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p2810)) : (¬ p1990) ∨ (p2027) ∨ (p2323) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial36615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory25871 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule36615 (meaning t m 1990) (meaning t m 2027) (meaning t m 2323) (meaning t m 2563) (meaning t m 2651) (meaning t m 2810) (meaning t m 3136) (meaning t m 4241) source

theorem rule36616 (p2027 p2707 p2743 p2774 p3425 p4845 : Prop) (h : (¬ p4845) ∨ p2027 ∨ (¬ p2774) ∨ (¬ p2743) ∨ (¬ p2707) ∨ (¬ p3425)) : (p2027) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial36616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory25872 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 2 7)
  exact rule36616 (meaning t m 2027) (meaning t m 2707) (meaning t m 2743) (meaning t m 2774) (meaning t m 3425) (meaning t m 4845) source

theorem rule36617 (p2027 p2315 p3461 p3821 p4187 p4381 : Prop) (h : (¬ p2315) ∨ (¬ p4187) ∨ (¬ p3821) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p4381)) : (p2027) ∨ (¬ p2315) ∨ (¬ p3461) ∨ (¬ p3821) ∨ (¬ p4187) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial36617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2315)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory25873 t (m.theta 0 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule36617 (meaning t m 2027) (meaning t m 2315) (meaning t m 3461) (meaning t m 3821) (meaning t m 4187) (meaning t m 4381) source

theorem rule36618 (p1978 p2027 p2997 p3483 p3646 p3744 p3822 : Prop) (h : (¬ p1978) ∨ p2997 ∨ (¬ p3483) ∨ (¬ p3646) ∨ (¬ p3822) ∨ p2027 ∨ (¬ p3744)) : (¬ p1978) ∨ (p2027) ∨ (p2997) ∨ (¬ p3483) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial36618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory25874 t (m.theta 0 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule36618 (meaning t m 1978) (meaning t m 2027) (meaning t m 2997) (meaning t m 3483) (meaning t m 3646) (meaning t m 3744) (meaning t m 3822) source

theorem rule36620 (p2027 p2563 p2598 p2753 p2850 p3093 p3486 p3555 p4555 p4870 : Prop) (h : (¬ p4555) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p2563) ∨ (¬ p3555) ∨ (¬ p3093) ∨ (¬ p2598) ∨ (¬ p4870) ∨ (¬ p2850) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3093) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p4555) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial36620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4555)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory25876 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule36620 (meaning t m 2027) (meaning t m 2563) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 3093) (meaning t m 3486) (meaning t m 3555) (meaning t m 4555) (meaning t m 4870) source

theorem rule36623 (p2027 p2138 p2246 p2528 p2651 p2744 p3083 p3366 p3690 p4244 p4669 : Prop) (h : p2027 ∨ (¬ p3366) ∨ (¬ p4244) ∨ (¬ p2246) ∨ (¬ p2138) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p4669) ∨ (¬ p3690) ∨ (¬ p2651) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2246) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3366) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial36623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory25879 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule36623 (meaning t m 2027) (meaning t m 2138) (meaning t m 2246) (meaning t m 2528) (meaning t m 2651) (meaning t m 2744) (meaning t m 3083) (meaning t m 3366) (meaning t m 3690) (meaning t m 4244) (meaning t m 4669) source

theorem rule36625 (p1982 p2027 p2699 p2761 p3399 p3631 p4444 : Prop) (h : p2699 ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p1982) ∨ (¬ p4444) ∨ (¬ p2761)) : (¬ p1982) ∨ (p2027) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial36625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory25881 t (m.theta 0 1) (m.theta 1 7) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule36625 (meaning t m 1982) (meaning t m 2027) (meaning t m 2699) (meaning t m 2761) (meaning t m 3399) (meaning t m 3631) (meaning t m 4444) source

theorem rule36626 (p2027 p2187 p2192 p2210 p2254 p2437 p2655 p3540 p4256 p4384 : Prop) (h : (¬ p3540) ∨ (¬ p2655) ∨ (¬ p2187) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p2192) ∨ (¬ p2254) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p2437)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2437) ∨ (¬ p2655) ∨ (¬ p3540) ∨ (¬ p4256) ∨ (¬ p4384) := by
  classical
  tauto

theorem initial36626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) := by
  have source := ElevenTheory.theory25882 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule36626 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2254) (meaning t m 2437) (meaning t m 2655) (meaning t m 3540) (meaning t m 4256) (meaning t m 4384) source

theorem rule36628 (p2027 p2246 p2331 p2744 p3323 p3366 p3425 p3461 p3659 p5123 p5558 : Prop) (h : (¬ p3659) ∨ (¬ p3366) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p2246) ∨ (¬ p5123) ∨ (¬ p3425) ∨ (¬ p2744) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p5558)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2744) ∨ (¬ p3323) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p3659) ∨ (¬ p5123) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial36628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory25884 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule36628 (meaning t m 2027) (meaning t m 2246) (meaning t m 2331) (meaning t m 2744) (meaning t m 3323) (meaning t m 3366) (meaning t m 3425) (meaning t m 3461) (meaning t m 3659) (meaning t m 5123) (meaning t m 5558) source

end SunPrize.SMT
