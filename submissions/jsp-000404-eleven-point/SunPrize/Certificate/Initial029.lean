import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory014
import SunPrize.Certificate.Theory015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule14058 (p1995 p2027 p2230 p2462 p3238 p3540 p4278 : Prop) (h : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3540) ∨ p2027 ∨ p2462 ∨ (¬ p1995) ∨ (¬ p4278)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (p2462) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory3698 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule14058 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2462) (meaning t m 3238) (meaning t m 3540) (meaning t m 4278) source

theorem rule14059 (p1975 p2027 p2274 p2323 p2331 p3323 p3744 : Prop) (h : p2323 ∨ (¬ p1975) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3744)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial14059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory3699 t (m.theta 0 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14059 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2323) (meaning t m 2331) (meaning t m 3323) (meaning t m 3744) source

theorem rule14060 (p1980 p3128 p3568 p4620 : Prop) (h : p3128 ∨ (¬ p1980) ∨ p4620 ∨ (¬ p3568)) : (¬ p1980) ∨ (p3128) ∨ (¬ p3568) ∨ (p4620) := by
  classical
  tauto

theorem initial14060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3568)) ∨ (meaning t m 4620) := by
  have source := ElevenTheory.theory3700 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14060 (meaning t m 1980) (meaning t m 3128) (meaning t m 3568) (meaning t m 4620) source

theorem rule14061 (p1976 p2027 p2534 p2766 p2810 p3365 p4256 : Prop) (h : (¬ p1976) ∨ p2766 ∨ (¬ p3365) ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p4256)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial14061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory3701 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule14061 (meaning t m 1976) (meaning t m 2027) (meaning t m 2534) (meaning t m 2766) (meaning t m 2810) (meaning t m 3365) (meaning t m 4256) source

theorem rule14062 (p1976 p2027 p2766 p3365 p3553 p3572 p4348 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p1976) ∨ (¬ p3553) ∨ (¬ p3365) ∨ (¬ p4348) ∨ (¬ p3572)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14062 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3702 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14062 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) (meaning t m 4348) source

theorem rule14064 (p1976 p2027 p2766 p3055 p3584 p3956 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p1976) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p3956) ∨ p2766 ∨ (¬ p3055)) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3704 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14064 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3055) (meaning t m 3584) (meaning t m 3956) (meaning t m 4347) source

theorem rule14065 (p1977 p2027 p2202 p2573 p2589 p3574 p4111 : Prop) (h : (¬ p2589) ∨ (¬ p1977) ∨ (¬ p2573) ∨ (¬ p3574) ∨ p2027 ∨ (¬ p4111) ∨ p2202) : (¬ p1977) ∨ (p2027) ∨ (p2202) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3705 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule14065 (meaning t m 1977) (meaning t m 2027) (meaning t m 2202) (meaning t m 2573) (meaning t m 2589) (meaning t m 3574) (meaning t m 4111) source

theorem rule14066 (p1982 p2027 p2241 p2699 p2992 p3146 p3156 : Prop) (h : (¬ p3146) ∨ (¬ p1982) ∨ p2027 ∨ p2699 ∨ (¬ p3156) ∨ (¬ p2241) ∨ (¬ p2992)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial14066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory3706 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule14066 (meaning t m 1982) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2992) (meaning t m 3146) (meaning t m 3156) source

theorem rule14067 (p1992 p2027 p2997 p3097 p3585 p3684 p4110 : Prop) (h : (¬ p1992) ∨ (¬ p3585) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3684) ∨ p2997) : (¬ p1992) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3707 t (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14067 (meaning t m 1992) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3585) (meaning t m 3684) (meaning t m 4110) source

theorem rule14071 (p2318 p4140 p4283 : Prop) (h : p2318 ∨ (¬ p4140) ∨ (¬ p4283)) : (p2318) ∨ (¬ p4140) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial14071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2318) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory3711 (m.theta 0 7) (m.theta 5 7) (m.theta 6 7)
  exact rule14071 (meaning t m 2318) (meaning t m 4140) (meaning t m 4283) source

theorem rule14072 (p1991 p2027 p2169 p2440 p2657 p3989 p4110 : Prop) (h : (¬ p4110) ∨ (¬ p3989) ∨ p2027 ∨ p2169 ∨ (¬ p2440) ∨ (¬ p1991) ∨ (¬ p2657)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3712 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule14072 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2440) (meaning t m 2657) (meaning t m 3989) (meaning t m 4110) source

theorem rule14073 (p1975 p2027 p2156 p2187 p2295 p2323 p2958 p3324 : Prop) (h : p2323 ∨ p2027 ∨ (¬ p2958) ∨ (¬ p3324) ∨ (¬ p1975) ∨ (¬ p2295) ∨ (¬ p2187) ∨ (¬ p2156)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2295) ∨ (p2323) ∨ (¬ p2958) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial14073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory3713 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14073 (meaning t m 1975) (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2295) (meaning t m 2323) (meaning t m 2958) (meaning t m 3324) source

theorem rule14074 (p1992 p2027 p2588 p2741 p2997 p3564 p4037 p4111 p4194 : Prop) (h : (¬ p2588) ∨ (¬ p4194) ∨ (¬ p4037) ∨ (¬ p4111) ∨ p2997 ∨ (¬ p1992) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2741)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2741) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4111) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial14074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2741)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory3714 t (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14074 (meaning t m 1992) (meaning t m 2027) (meaning t m 2588) (meaning t m 2741) (meaning t m 2997) (meaning t m 3564) (meaning t m 4037) (meaning t m 4111) (meaning t m 4194) source

theorem rule14075 (p1992 p2027 p2764 p3584 p3585 p4137 p4191 : Prop) (h : (¬ p3585) ∨ p2764 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p4191) ∨ (¬ p3584) ∨ (¬ p4137)) : (¬ p1992) ∨ (p2027) ∨ (p2764) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14075 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory3715 t (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14075 (meaning t m 1992) (meaning t m 2027) (meaning t m 2764) (meaning t m 3584) (meaning t m 3585) (meaning t m 4137) (meaning t m 4191) source

theorem rule14076 (p1988 p2027 p2166 p2210 p2699 p3146 p3266 : Prop) (h : p2699 ∨ (¬ p1988) ∨ (¬ p2210) ∨ p2027 ∨ (¬ p3266) ∨ (¬ p3146) ∨ (¬ p2166)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3146) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial14076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory3716 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14076 (meaning t m 1988) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2699) (meaning t m 3146) (meaning t m 3266) source

theorem rule14078 (p1992 p2027 p2588 p2651 p2741 p2963 p2997 p4111 p4389 : Prop) (h : (¬ p4111) ∨ (¬ p1992) ∨ (¬ p4389) ∨ p2027 ∨ (¬ p2741) ∨ (¬ p2588) ∨ (¬ p2963) ∨ (¬ p2651) ∨ p2997) : (¬ p1992) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p4111) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial14078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory3718 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule14078 (meaning t m 1992) (meaning t m 2027) (meaning t m 2588) (meaning t m 2651) (meaning t m 2741) (meaning t m 2963) (meaning t m 2997) (meaning t m 4111) (meaning t m 4389) source

theorem rule14079 (p1990 p2148 p3051 p4555 : Prop) (h : p4555 ∨ p2148 ∨ (¬ p3051) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2148) ∨ (¬ p3051) ∨ (p4555) := by
  classical
  tauto

theorem initial14079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3051)) ∨ (meaning t m 4555) := by
  have source := ElevenTheory.theory3719 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14079 (meaning t m 1990) (meaning t m 2148) (meaning t m 3051) (meaning t m 4555) source

theorem rule14080 (p2027 p2946 p3425 p4117 p4315 p4778 : Prop) (h : (¬ p4778) ∨ (¬ p4315) ∨ (¬ p4117) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial14080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory3720 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 5)
  exact rule14080 (meaning t m 2027) (meaning t m 2946) (meaning t m 3425) (meaning t m 4117) (meaning t m 4315) (meaning t m 4778) source

theorem rule14081 (p1992 p2027 p2542 p2589 p2914 p3363 p3585 p3742 : Prop) (h : (¬ p1992) ∨ p2914 ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3363)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (p2914) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial14081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory3721 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule14081 (meaning t m 1992) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2914) (meaning t m 3363) (meaning t m 3585) (meaning t m 3742) source

theorem rule14082 (p1982 p2027 p2187 p2192 p2210 p2363 p2699 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (¬ p2187) ∨ p2699) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2363) ∨ (p2699) := by
  classical
  tauto

theorem initial14082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory3722 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14082 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2363) (meaning t m 2699) source

theorem rule14083 (p1992 p2027 p2202 p2563 p2743 p2952 p3361 p3952 : Prop) (h : (¬ p3361) ∨ (¬ p3952) ∨ p2202 ∨ (¬ p2952) ∨ (¬ p1992) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p2743)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial14083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory3723 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule14083 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2743) (meaning t m 2952) (meaning t m 3361) (meaning t m 3952) source

theorem rule14084 (p1992 p2027 p2440 p2657 p2743 p2765 p3361 p4110 : Prop) (h : (¬ p3361) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p2743) ∨ (¬ p2657) ∨ (¬ p4110) ∨ p2765) : (¬ p1992) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2743) ∨ (p2765) ∨ (¬ p3361) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3724 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule14084 (meaning t m 1992) (meaning t m 2027) (meaning t m 2440) (meaning t m 2657) (meaning t m 2743) (meaning t m 2765) (meaning t m 3361) (meaning t m 4110) source

theorem rule14085 (p1992 p2027 p2743 p2766 p3361 p3414 p3553 p4348 : Prop) (h : (¬ p3414) ∨ (¬ p3361) ∨ (¬ p1992) ∨ (¬ p3553) ∨ (¬ p2743) ∨ p2027 ∨ (¬ p4348) ∨ p2766) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2766) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3725 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14085 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2766) (meaning t m 3361) (meaning t m 3414) (meaning t m 3553) (meaning t m 4348) source

theorem rule14087 (p1992 p2027 p2633 p2696 p2743 p3425 p3659 : Prop) (h : (¬ p1992) ∨ p2027 ∨ p2633 ∨ (¬ p3659) ∨ (¬ p3425) ∨ (¬ p2743) ∨ (¬ p2696)) : (¬ p1992) ∨ (p2027) ∨ (p2633) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial14087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory3727 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule14087 (meaning t m 1992) (meaning t m 2027) (meaning t m 2633) (meaning t m 2696) (meaning t m 2743) (meaning t m 3425) (meaning t m 3659) source

theorem rule14088 (p1992 p2027 p2563 p2938 p3363 p3585 p3646 p3904 p4235 : Prop) (h : (¬ p3363) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p1992) ∨ p2938 ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p2563)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3728 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14088 (meaning t m 1992) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 3363) (meaning t m 3585) (meaning t m 3646) (meaning t m 3904) (meaning t m 4235) source

theorem rule14089 (p1994 p2027 p2598 p2622 p3201 p3365 p3742 : Prop) (h : (¬ p2598) ∨ (¬ p1994) ∨ (¬ p3201) ∨ (¬ p3365) ∨ p2027 ∨ p2622 ∨ (¬ p3742)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p3201) ∨ (¬ p3365) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial14089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory3729 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule14089 (meaning t m 1994) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 3201) (meaning t m 3365) (meaning t m 3742) source

theorem rule14090 (p1992 p2027 p2553 p2598 p3008 p3425 p3585 p4471 : Prop) (h : (¬ p2598) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3585) ∨ p3008 ∨ (¬ p4471) ∨ (¬ p3425) ∨ (¬ p2553)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2598) ∨ (p3008) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial14090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory3730 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7)
  exact rule14090 (meaning t m 1992) (meaning t m 2027) (meaning t m 2553) (meaning t m 2598) (meaning t m 3008) (meaning t m 3425) (meaning t m 3585) (meaning t m 4471) source

theorem rule14091 (p1992 p2027 p2387 p2598 p2766 p2778 p3585 p4347 : Prop) (h : (¬ p2598) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2778) ∨ (¬ p4347) ∨ p2766 ∨ (¬ p2387)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p2778) ∨ (¬ p3585) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3731 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 6 8) (m.theta 8 9)
  exact rule14091 (meaning t m 1992) (meaning t m 2027) (meaning t m 2387) (meaning t m 2598) (meaning t m 2766) (meaning t m 2778) (meaning t m 3585) (meaning t m 4347) source

theorem rule14093 (p1992 p2027 p2352 p2387 p2588 p2785 p2997 p3688 : Prop) (h : (¬ p3688) ∨ (¬ p2387) ∨ p2997 ∨ (¬ p2785) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2352) ∨ (¬ p2588)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2785) ∨ (p2997) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial14093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory3733 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14093 (meaning t m 1992) (meaning t m 2027) (meaning t m 2352) (meaning t m 2387) (meaning t m 2588) (meaning t m 2785) (meaning t m 2997) (meaning t m 3688) source

theorem rule14095 (p1992 p2027 p2104 p2534 p2598 p2766 p3585 p5369 : Prop) (h : (¬ p3585) ∨ (¬ p2104) ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2598) ∨ (¬ p2534) ∨ (¬ p5369) ∨ p2766) : (¬ p1992) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2534) ∨ (¬ p2598) ∨ (p2766) ∨ (¬ p3585) ∨ (¬ p5369) := by
  classical
  tauto

theorem initial14095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 5369)) := by
  have source := ElevenTheory.theory3735 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 4 8) (m.theta 8 9)
  exact rule14095 (meaning t m 1992) (meaning t m 2027) (meaning t m 2104) (meaning t m 2534) (meaning t m 2598) (meaning t m 2766) (meaning t m 3585) (meaning t m 5369) source

theorem rule14097 (p1976 p2027 p2870 p3055 p3474 p3684 p4235 : Prop) (h : (¬ p3684) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3055) ∨ (¬ p4235) ∨ p3474 ∨ (¬ p2870)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2870) ∨ (¬ p3055) ∨ (p3474) ∨ (¬ p3684) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3055)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3737 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule14097 (meaning t m 1976) (meaning t m 2027) (meaning t m 2870) (meaning t m 3055) (meaning t m 3474) (meaning t m 3684) (meaning t m 4235) source

theorem rule14098 (p1976 p2027 p2462 p2810 p3365 p3742 p4278 : Prop) (h : p2462 ∨ p2027 ∨ (¬ p4278) ∨ (¬ p3365) ∨ (¬ p2810) ∨ (¬ p3742) ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory3738 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule14098 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2810) (meaning t m 3365) (meaning t m 3742) (meaning t m 4278) source

theorem rule14099 (p1995 p2027 p2499 p2914 p3019 p3323 p3742 p4137 : Prop) (h : p2027 ∨ p2914 ∨ (¬ p2499) ∨ (¬ p1995) ∨ (¬ p3742) ∨ (¬ p4137) ∨ (¬ p3019) ∨ (¬ p3323)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (p2914) ∨ (¬ p3019) ∨ (¬ p3323) ∨ (¬ p3742) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial14099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory3739 t (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9)
  exact rule14099 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2914) (meaning t m 3019) (meaning t m 3323) (meaning t m 3742) (meaning t m 4137) source

theorem rule14100 (p1990 p2027 p2202 p2440 p3016 p3564 p3744 : Prop) (h : p2027 ∨ p2202 ∨ (¬ p3564) ∨ (¬ p2440) ∨ (¬ p3744) ∨ (¬ p1990) ∨ (¬ p3016)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial14100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory3740 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule14100 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3016) (meaning t m 3564) (meaning t m 3744) source

theorem rule14102 (p1976 p2027 p2440 p2810 p2938 p3365 p4235 : Prop) (h : p2027 ∨ (¬ p2440) ∨ (¬ p3365) ∨ (¬ p1976) ∨ (¬ p2810) ∨ p2938 ∨ (¬ p4235)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2440) ∨ (¬ p2810) ∨ (p2938) ∨ (¬ p3365) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3742 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule14102 (meaning t m 1976) (meaning t m 2027) (meaning t m 2440) (meaning t m 2810) (meaning t m 2938) (meaning t m 3365) (meaning t m 4235) source

theorem rule14106 (p1976 p2027 p2138 p2563 p2938 p3758 p4235 : Prop) (h : p2027 ∨ p2938 ∨ (¬ p1976) ∨ (¬ p4235) ∨ (¬ p2138) ∨ (¬ p3758) ∨ (¬ p2563)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p3758) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3746 t (m.theta 0 2) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14106 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2563) (meaning t m 2938) (meaning t m 3758) (meaning t m 4235) source

theorem rule14107 (p1990 p2027 p2156 p2901 p3497 p3556 p3578 : Prop) (h : p2027 ∨ (¬ p1990) ∨ (¬ p2901) ∨ (¬ p3497) ∨ p3578 ∨ (¬ p3556) ∨ (¬ p2156)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (p3578) := by
  classical
  tauto

theorem initial14107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) ∨ (meaning t m 3578) := by
  have source := ElevenTheory.theory3747 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule14107 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2901) (meaning t m 3497) (meaning t m 3556) (meaning t m 3578) source

theorem rule14110 (p1976 p2027 p2138 p2839 p2914 p3585 p3876 : Prop) (h : p2914 ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2839) ∨ (¬ p3876) ∨ (¬ p2138) ∨ (¬ p3585)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (p2914) ∨ (¬ p3585) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial14110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory3750 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7)
  exact rule14110 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2839) (meaning t m 2914) (meaning t m 3585) (meaning t m 3876) source

theorem rule14118 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p5518) ∨ (((¬ p5518) ∨ (¬ p3893) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5520))) := by
  classical
  tauto

theorem initial14118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5518) ∨ (meaning t m 6134) := by
  exact rule14118 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule14119 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p3893) ∨ (((¬ p5518) ∨ (¬ p3893) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5520))) := by
  classical
  tauto

theorem initial14119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3893) ∨ (meaning t m 6134) := by
  exact rule14119 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule14120 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p3888) ∨ (((¬ p5518) ∨ (¬ p3893) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5520))) := by
  classical
  tauto

theorem initial14120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3888) ∨ (meaning t m 6134) := by
  exact rule14120 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule14121 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p5519) ∨ (((¬ p5518) ∨ (¬ p3893) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5520))) := by
  classical
  tauto

theorem initial14121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5519) ∨ (meaning t m 6134) := by
  exact rule14121 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule14122 (p3888 p3893 p5518 p5519 p5520 : Prop) : (p5520) ∨ (((¬ p5518) ∨ (¬ p3893) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5520))) := by
  classical
  tauto

theorem initial14122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5520) ∨ (meaning t m 6134) := by
  exact rule14122 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule14123 (p3888 p3893 p5518 p5519 p5520 : Prop) : (¬ p3888) ∨ (¬ p3893) ∨ (¬ p5518) ∨ (¬ p5519) ∨ (¬ p5520) ∨ (¬ ((¬ p5518) ∨ (¬ p3893) ∨ (¬ p3888) ∨ (¬ p5519) ∨ (¬ p5520))) := by
  classical
  tauto

theorem initial14123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 3893)) ∨ (¬ (meaning t m 5518)) ∨ (¬ (meaning t m 5519)) ∨ (¬ (meaning t m 5520)) ∨ (¬ (meaning t m 6134)) := by
  exact rule14123 (meaning t m 3888) (meaning t m 3893) (meaning t m 5518) (meaning t m 5519) (meaning t m 5520)

theorem rule14131 (p3892 p5523 p5524 p5525 p5526 : Prop) : (p3892) ∨ (((¬ p5524) ∨ (¬ p3892) ∨ (¬ p5523) ∨ (¬ p5525) ∨ (¬ p5526))) := by
  classical
  tauto

theorem initial14131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3892) ∨ (meaning t m 6136) := by
  exact rule14131 (meaning t m 3892) (meaning t m 5523) (meaning t m 5524) (meaning t m 5525) (meaning t m 5526)

theorem rule14138 (p3901 p5528 p5529 p5530 p5531 : Prop) : (p3901) ∨ (((¬ p5528) ∨ (¬ p5529) ∨ (¬ p3901) ∨ (¬ p5530) ∨ (¬ p5531))) := by
  classical
  tauto

theorem initial14138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3901) ∨ (meaning t m 6137) := by
  exact rule14138 (meaning t m 3901) (meaning t m 5528) (meaning t m 5529) (meaning t m 5530) (meaning t m 5531)

theorem rule14144 (p6136 p6137 : Prop) : (¬ ((¬ p6136) ∨ (¬ p6137))) ∨ (¬ p6136) ∨ (¬ p6137) := by
  classical
  tauto

theorem initial14144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6135)) ∨ (¬ (meaning t m 6136)) ∨ (¬ (meaning t m 6137)) := by
  exact rule14144 (meaning t m 6136) (meaning t m 6137)

theorem rule14145 (p5521 p6135 : Prop) (h : (p5521 ↔ p6135)) : (¬ p5521) ∨ (p6135) := by
  classical
  tauto

theorem initial14145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5521)) ∨ (meaning t m 6135) := by
  have source := ElevenTheory.theory3754 t (m.theta 3 10) (m.theta 3 4) (m.theta 4 10)
  exact rule14145 (meaning t m 5521) (meaning t m 6135) source

theorem rule14148 (p1992 p2027 p2169 p2363 p2534 p3573 p3584 p3585 : Prop) (h : (¬ p3573) ∨ (¬ p1992) ∨ (¬ p3585) ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3584) ∨ (¬ p2534) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3584) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial14148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory3756 t (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14148 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2534) (meaning t m 3573) (meaning t m 3584) (meaning t m 3585) source

theorem rule14149 (p2534 p3990 p4157 p4345 : Prop) (h : (¬ p4157) ∨ (¬ p2534) ∨ (¬ p3990) ∨ (¬ p4345)) : (¬ p2534) ∨ (¬ p3990) ∨ (¬ p4157) ∨ (¬ p4345) := by
  classical
  tauto

theorem initial14149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3990)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4345)) := by
  have source := ElevenTheory.theory3757 (m.theta 4 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule14149 (meaning t m 2534) (meaning t m 3990) (meaning t m 4157) (meaning t m 4345) source

theorem rule14152 (p4118 p4351 p4352 p5074 : Prop) (h : (¬ p5074) ∨ (¬ p4118) ∨ (¬ p4351) ∨ (¬ p4352)) : (¬ p4118) ∨ (¬ p4351) ∨ (¬ p4352) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial14152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4351)) ∨ (¬ (meaning t m 4352)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory3760 (m.theta 1 8) (m.theta 1 9) (m.theta 3 8) (m.theta 8 9)
  exact rule14152 (meaning t m 4118) (meaning t m 4351) (meaning t m 4352) (meaning t m 5074) source

theorem rule14153 (p2004 p2027 p2427 p2765 p3246 p3817 p4110 : Prop) (h : (¬ p3817) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p4110) ∨ p2765 ∨ (¬ p2004) ∨ (¬ p2427)) : (¬ p2004) ∨ (p2027) ∨ (¬ p2427) ∨ (p2765) ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory3761 t (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 9)
  exact rule14153 (meaning t m 2004) (meaning t m 2027) (meaning t m 2427) (meaning t m 2765) (meaning t m 3246) (meaning t m 3817) (meaning t m 4110) source

theorem rule14155 (p1975 p2027 p2241 p2553 p2699 p2727 p3016 : Prop) (h : (¬ p2553) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3016) ∨ p2699 ∨ (¬ p2727) ∨ (¬ p2241)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2553) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial14155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory3763 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule14155 (meaning t m 1975) (meaning t m 2027) (meaning t m 2241) (meaning t m 2553) (meaning t m 2699) (meaning t m 2727) (meaning t m 3016) source

theorem rule14156 (p1977 p2027 p2938 p2957 p3105 p3662 p4032 p4244 : Prop) (h : p2938 ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2957) ∨ (¬ p4032) ∨ (¬ p4244) ∨ (¬ p3105)) : (¬ p1977) ∨ (p2027) ∨ (p2938) ∨ (¬ p2957) ∨ (¬ p3105) ∨ (¬ p3662) ∨ (¬ p4032) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial14156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory3764 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9)
  exact rule14156 (meaning t m 1977) (meaning t m 2027) (meaning t m 2938) (meaning t m 2957) (meaning t m 3105) (meaning t m 3662) (meaning t m 4032) (meaning t m 4244) source

theorem rule14158 (p1997 p2938 p4948 p5104 : Prop) (h : (¬ p1997) ∨ p5104 ∨ p2938 ∨ (¬ p4948)) : (¬ p1997) ∨ (p2938) ∨ (¬ p4948) ∨ (p5104) := by
  classical
  tauto

theorem initial14158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4948)) ∨ (meaning t m 5104) := by
  have source := ElevenTheory.theory3766 t (m.theta 4 5) (m.theta 5 7) (m.theta 5 9)
  exact rule14158 (meaning t m 1997) (meaning t m 2938) (meaning t m 4948) (meaning t m 5104) source

theorem rule14159 (p1977 p2027 p2589 p2662 p2997 p3097 p4110 p4111 : Prop) (h : p2997 ∨ (¬ p3097) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2662) ∨ (¬ p4111) ∨ (¬ p2589)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3767 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14159 (meaning t m 1977) (meaning t m 2027) (meaning t m 2589) (meaning t m 2662) (meaning t m 2997) (meaning t m 3097) (meaning t m 4110) (meaning t m 4111) source

theorem rule14160 (p1975 p2027 p2122 p2611 p2696 p2743 p2829 : Prop) (h : (¬ p1975) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829) ∨ p2027 ∨ (¬ p2122)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial14160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory3768 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule14160 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2611) (meaning t m 2696) (meaning t m 2743) (meaning t m 2829) source

theorem rule14161 (p1975 p2027 p2295 p2611 p2774 p3483 p4037 : Prop) (h : (¬ p1975) ∨ p2611 ∨ (¬ p2295) ∨ (¬ p3483) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p4037)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3483) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial14161 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory3769 t (m.theta 0 2) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14161 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2774) (meaning t m 3483) (meaning t m 4037) source

theorem rule14163 (p1977 p2027 p2651 p2963 p3128 p4037 p4111 : Prop) (h : (¬ p2651) ∨ p3128 ∨ p2027 ∨ (¬ p4037) ∨ (¬ p2963) ∨ (¬ p4111) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (p3128) ∨ (¬ p4037) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14163 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3771 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9)
  exact rule14163 (meaning t m 1977) (meaning t m 2027) (meaning t m 2651) (meaning t m 2963) (meaning t m 3128) (meaning t m 4037) (meaning t m 4111) source

theorem rule14166 (p4329 p5534 p5535 p5536 p5537 : Prop) : (p4329) ∨ (((¬ p5535) ∨ (¬ p4329) ∨ (¬ p5534) ∨ (¬ p5536) ∨ (¬ p5537))) := by
  classical
  tauto

theorem initial14166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4329) ∨ (meaning t m 6139) := by
  exact rule14166 (meaning t m 4329) (meaning t m 5534) (meaning t m 5535) (meaning t m 5536) (meaning t m 5537)

theorem rule14171 (p3914 p5539 p5540 p5541 p5542 : Prop) : (p5539) ∨ (((¬ p5539) ∨ (¬ p5540) ∨ (¬ p3914) ∨ (¬ p5541) ∨ (¬ p5542))) := by
  classical
  tauto

theorem initial14171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5539) ∨ (meaning t m 6140) := by
  exact rule14171 (meaning t m 3914) (meaning t m 5539) (meaning t m 5540) (meaning t m 5541) (meaning t m 5542)

theorem rule14172 (p3914 p5539 p5540 p5541 p5542 : Prop) : (p5540) ∨ (((¬ p5539) ∨ (¬ p5540) ∨ (¬ p3914) ∨ (¬ p5541) ∨ (¬ p5542))) := by
  classical
  tauto

theorem initial14172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5540) ∨ (meaning t m 6140) := by
  exact rule14172 (meaning t m 3914) (meaning t m 5539) (meaning t m 5540) (meaning t m 5541) (meaning t m 5542)

theorem rule14173 (p3914 p5539 p5540 p5541 p5542 : Prop) : (p3914) ∨ (((¬ p5539) ∨ (¬ p5540) ∨ (¬ p3914) ∨ (¬ p5541) ∨ (¬ p5542))) := by
  classical
  tauto

theorem initial14173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3914) ∨ (meaning t m 6140) := by
  exact rule14173 (meaning t m 3914) (meaning t m 5539) (meaning t m 5540) (meaning t m 5541) (meaning t m 5542)

theorem rule14179 (p6139 p6140 : Prop) : (¬ ((¬ p6139) ∨ (¬ p6140))) ∨ (¬ p6139) ∨ (¬ p6140) := by
  classical
  tauto

theorem initial14179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6138)) ∨ (¬ (meaning t m 6139)) ∨ (¬ (meaning t m 6140)) := by
  exact rule14179 (meaning t m 6139) (meaning t m 6140)

theorem rule14180 (p5532 p6138 : Prop) (h : (p5532 ↔ p6138)) : (¬ p5532) ∨ (p6138) := by
  classical
  tauto

theorem initial14180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5532)) ∨ (meaning t m 6138) := by
  have source := ElevenTheory.theory3773 t (m.theta 2 10) (m.theta 2 6) (m.theta 6 10)
  exact rule14180 (meaning t m 5532) (meaning t m 6138) source

theorem rule14182 (p2002 p2027 p2914 p3016 p3742 p3888 p4329 : Prop) (h : (¬ p2002) ∨ p2914 ∨ p2027 ∨ (¬ p4329) ∨ (¬ p3016) ∨ (¬ p3888) ∨ (¬ p3742)) : (¬ p2002) ∨ (p2027) ∨ (p2914) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3888) ∨ (¬ p4329) := by
  classical
  tauto

theorem initial14182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 4329)) := by
  have source := ElevenTheory.theory3774 t (m.theta 2 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 10)
  exact rule14182 (meaning t m 2002) (meaning t m 2027) (meaning t m 2914) (meaning t m 3016) (meaning t m 3742) (meaning t m 3888) (meaning t m 4329) source

theorem rule14183 (p2000 p2027 p2169 p2579 p3737 p3989 p5514 : Prop) (h : (¬ p2000) ∨ (¬ p5514) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p3737) ∨ (¬ p2579) ∨ p2169) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2579) ∨ (¬ p3737) ∨ (¬ p3989) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial14183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory3775 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 8)
  exact rule14183 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2579) (meaning t m 3737) (meaning t m 3989) (meaning t m 5514) source

theorem rule14184 (p1995 p2027 p2764 p3238 p3744 p4110 p4191 : Prop) (h : p2027 ∨ (¬ p1995) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p3238) ∨ (¬ p4191) ∨ p2764) : (¬ p1995) ∨ (p2027) ∨ (p2764) ∨ (¬ p3238) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14184 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory3776 t (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14184 (meaning t m 1995) (meaning t m 2027) (meaning t m 2764) (meaning t m 3238) (meaning t m 3744) (meaning t m 4110) (meaning t m 4191) source

theorem rule14185 (p2000 p2027 p2169 p2579 p3125 p3989 p4137 : Prop) (h : (¬ p2000) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2579) ∨ p2169 ∨ (¬ p4137) ∨ (¬ p3125)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2579) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial14185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory3777 t (m.theta 0 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule14185 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2579) (meaning t m 3125) (meaning t m 3989) (meaning t m 4137) source

theorem rule14186 (p1990 p2027 p2608 p2699 p2819 p2829 p3989 : Prop) (h : (¬ p2819) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2829) ∨ p2699 ∨ (¬ p3989) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial14186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory3778 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 8)
  exact rule14186 (meaning t m 1990) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2819) (meaning t m 2829) (meaning t m 3989) source

theorem rule14187 (p1991 p2027 p2657 p2766 p3574 p3956 p4347 : Prop) (h : (¬ p2657) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p3956) ∨ p2766 ∨ (¬ p3574) ∨ (¬ p1991)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2657) ∨ (p2766) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3779 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14187 (meaning t m 1991) (meaning t m 2027) (meaning t m 2657) (meaning t m 2766) (meaning t m 3574) (meaning t m 3956) (meaning t m 4347) source

theorem rule14189 (p1983 p2027 p2132 p2274 p2396 p2611 p2860 : Prop) (h : p2611 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p2132) ∨ (¬ p1983) ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (p2611) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial14189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory3781 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule14189 (meaning t m 1983) (meaning t m 2027) (meaning t m 2132) (meaning t m 2274) (meaning t m 2396) (meaning t m 2611) (meaning t m 2860) source

theorem rule14190 (p1985 p2027 p2287 p2870 p3323 p3744 p3758 : Prop) (h : p2287 ∨ (¬ p3758) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p1985) ∨ (¬ p2870) ∨ (¬ p3744)) : (¬ p1985) ∨ (p2027) ∨ (p2287) ∨ (¬ p2870) ∨ (¬ p3323) ∨ (¬ p3744) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial14190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory3782 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule14190 (meaning t m 1985) (meaning t m 2027) (meaning t m 2287) (meaning t m 2870) (meaning t m 3323) (meaning t m 3744) (meaning t m 3758) source

theorem rule14191 (p1975 p2027 p2295 p2696 p2699 p2743 p2829 p3589 p4328 : Prop) (h : (¬ p3589) ∨ (¬ p2829) ∨ p2699 ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2696) ∨ (¬ p1975) ∨ (¬ p2295) ∨ (¬ p4328)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p4328) := by
  classical
  tauto

theorem initial14191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4328)) := by
  have source := ElevenTheory.theory3783 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule14191 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2696) (meaning t m 2699) (meaning t m 2743) (meaning t m 2829) (meaning t m 3589) (meaning t m 4328) source

theorem rule14192 (p1985 p2027 p2132 p2611 p2860 p2901 p3952 : Prop) (h : p2611 ∨ (¬ p2860) ∨ (¬ p1985) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2132)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2860) ∨ (¬ p2901) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial14192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory3784 t (m.theta 0 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14192 (meaning t m 1985) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2860) (meaning t m 2901) (meaning t m 3952) source

theorem rule14194 (p1977 p2027 p2633 p2946 p3414 p3553 p3662 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p3662) ∨ p2633 ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3553)) : (¬ p1977) ∨ (p2027) ∨ (p2633) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial14194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory3786 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule14194 (meaning t m 1977) (meaning t m 2027) (meaning t m 2633) (meaning t m 2946) (meaning t m 3414) (meaning t m 3553) (meaning t m 3662) source

theorem rule14195 (p1983 p2027 p2299 p2396 p2699 p3399 p3527 : Prop) (h : p2027 ∨ (¬ p2299) ∨ p2699 ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p1983) ∨ (¬ p2396)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial14195 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory3787 t (m.theta 0 1) (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14195 (meaning t m 1983) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2699) (meaning t m 3399) (meaning t m 3527) source

theorem rule14196 (p1998 p2027 p2437 p2611 p2630 p2696 p2911 : Prop) (h : (¬ p1998) ∨ p2027 ∨ (¬ p2696) ∨ p2611 ∨ (¬ p2630) ∨ (¬ p2437) ∨ (¬ p2911)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2437) ∨ (p2611) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2911) := by
  classical
  tauto

theorem initial14196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2911)) := by
  have source := ElevenTheory.theory3788 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule14196 (meaning t m 1998) (meaning t m 2027) (meaning t m 2437) (meaning t m 2611) (meaning t m 2630) (meaning t m 2696) (meaning t m 2911) source

theorem rule14200 (p2027 p2651 p2737 p2811 p3583 p4316 p4701 : Prop) (h : (¬ p4316) ∨ (¬ p2651) ∨ (¬ p4701) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3583) ∨ p2027) : (p2027) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3583) ∨ (¬ p4316) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial14200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory3792 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5)
  exact rule14200 (meaning t m 2027) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 3583) (meaning t m 4316) (meaning t m 4701) source

theorem rule14201 (p1984 p2027 p2928 p3008 p3201 p3452 p3584 : Prop) (h : (¬ p3201) ∨ (¬ p3452) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2928) ∨ (¬ p3584) ∨ p3008) : (¬ p1984) ∨ (p2027) ∨ (¬ p2928) ∨ (p3008) ∨ (¬ p3201) ∨ (¬ p3452) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial14201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2928)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory3793 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule14201 (meaning t m 1984) (meaning t m 2027) (meaning t m 2928) (meaning t m 3008) (meaning t m 3201) (meaning t m 3452) (meaning t m 3584) source

theorem rule14202 (p1975 p2027 p2274 p2323 p2542 p2563 p2651 : Prop) (h : p2323 ∨ (¬ p2563) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2542) ∨ p2027 ∨ (¬ p2651)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2323) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) := by
  classical
  tauto

theorem initial14202 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2651)) := by
  have source := ElevenTheory.theory3794 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14202 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2323) (meaning t m 2542) (meaning t m 2563) (meaning t m 2651) source

theorem rule14203 (p1998 p2027 p2177 p2417 p2842 p3422 p3920 p4107 : Prop) (h : (¬ p2177) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p4107) ∨ p2842 ∨ (¬ p3422) ∨ (¬ p3920)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2417) ∨ (p2842) ∨ (¬ p3422) ∨ (¬ p3920) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial14203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory3795 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14203 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2417) (meaning t m 2842) (meaning t m 3422) (meaning t m 3920) (meaning t m 4107) source

theorem rule14204 (p1976 p2027 p2138 p2765 p3156 p3694 p3952 : Prop) (h : (¬ p3952) ∨ (¬ p1976) ∨ (¬ p2138) ∨ p2027 ∨ p2765 ∨ (¬ p3156) ∨ (¬ p3694)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2765) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial14204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory3796 t (m.theta 0 2) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule14204 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2765) (meaning t m 3156) (meaning t m 3694) (meaning t m 3952) source

theorem rule14208 (p1992 p2027 p2138 p2696 p2743 p2765 p3758 : Prop) (h : (¬ p3758) ∨ p2765 ∨ (¬ p2743) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p1992) ∨ (¬ p2696)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (p2765) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial14208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory3800 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule14208 (meaning t m 1992) (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2743) (meaning t m 2765) (meaning t m 3758) source

theorem rule14209 (p1981 p2027 p2608 p2699 p2819 p3309 p3822 p4869 : Prop) (h : (¬ p1981) ∨ p2699 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p3822) ∨ (¬ p4869) ∨ (¬ p2819) ∨ (¬ p3309)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2819) ∨ (¬ p3309) ∨ (¬ p3822) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial14209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory3801 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14209 (meaning t m 1981) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2819) (meaning t m 3309) (meaning t m 3822) (meaning t m 4869) source

theorem rule14210 (p1998 p2027 p2122 p2177 p2608 p2699 p2829 : Prop) (h : (¬ p2177) ∨ (¬ p1998) ∨ (¬ p2829) ∨ p2699 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2122)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2829) := by
  classical
  tauto

theorem initial14210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2829)) := by
  have source := ElevenTheory.theory3802 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule14210 (meaning t m 1998) (meaning t m 2027) (meaning t m 2122) (meaning t m 2177) (meaning t m 2608) (meaning t m 2699) (meaning t m 2829) source

theorem rule14211 (p1998 p2027 p2177 p2241 p2295 p2641 p2699 : Prop) (h : (¬ p1998) ∨ p2027 ∨ p2699 ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2295) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (p2699) := by
  classical
  tauto

theorem initial14211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory3803 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule14211 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2241) (meaning t m 2295) (meaning t m 2641) (meaning t m 2699) source

theorem rule14212 (p1998 p2027 p2253 p2264 p2331 p2699 p3027 p4154 : Prop) (h : (¬ p1998) ∨ (¬ p2264) ∨ p2699 ∨ (¬ p3027) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p2331) ∨ (¬ p2253)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2264) ∨ (¬ p2331) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial14212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory3804 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 8)
  exact rule14212 (meaning t m 1998) (meaning t m 2027) (meaning t m 2253) (meaning t m 2264) (meaning t m 2331) (meaning t m 2699) (meaning t m 3027) (meaning t m 4154) source

theorem rule14213 (p1981 p2027 p2323 p2352 p2663 p3016 p3389 p3742 : Prop) (h : p2323 ∨ (¬ p3742) ∨ (¬ p2352) ∨ (¬ p3016) ∨ (¬ p2663) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p3389)) : (¬ p1981) ∨ (p2027) ∨ (p2323) ∨ (¬ p2352) ∨ (¬ p2663) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial14213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory3805 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 8)
  exact rule14213 (meaning t m 1981) (meaning t m 2027) (meaning t m 2323) (meaning t m 2352) (meaning t m 2663) (meaning t m 3016) (meaning t m 3389) (meaning t m 3742) source

theorem rule14217 (p1996 p2027 p2241 p2396 p2699 p3309 p3947 p4759 : Prop) (h : p2699 ∨ (¬ p1996) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4759) ∨ (¬ p3947) ∨ (¬ p2396) ∨ (¬ p3309)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2396) ∨ (p2699) ∨ (¬ p3309) ∨ (¬ p3947) ∨ (¬ p4759) := by
  classical
  tauto

theorem initial14217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4759)) := by
  have source := ElevenTheory.theory3809 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule14217 (meaning t m 1996) (meaning t m 2027) (meaning t m 2241) (meaning t m 2396) (meaning t m 2699) (meaning t m 3309) (meaning t m 3947) (meaning t m 4759) source

theorem rule14218 (p1988 p2027 p2396 p2611 p2761 p2774 p3309 p3918 : Prop) (h : (¬ p3918) ∨ p2611 ∨ (¬ p2774) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3309) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2396) ∨ (p2611) ∨ (¬ p2761) ∨ (¬ p2774) ∨ (¬ p3309) ∨ (¬ p3918) := by
  classical
  tauto

theorem initial14218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3918)) := by
  have source := ElevenTheory.theory3810 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule14218 (meaning t m 1988) (meaning t m 2027) (meaning t m 2396) (meaning t m 2611) (meaning t m 2761) (meaning t m 2774) (meaning t m 3309) (meaning t m 3918) source

theorem rule14219 (p1995 p2027 p2230 p2764 p3238 p3346 p4425 : Prop) (h : (¬ p3346) ∨ p2027 ∨ p2764 ∨ (¬ p4425) ∨ (¬ p3238) ∨ (¬ p2230) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (p2764) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial14219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory3811 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule14219 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2764) (meaning t m 3238) (meaning t m 3346) (meaning t m 4425) source

theorem rule14220 (p1988 p2027 p2241 p2449 p2699 p2761 p3027 : Prop) (h : p2699 ∨ (¬ p1988) ∨ (¬ p2241) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2449)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p3027) := by
  classical
  tauto

theorem initial14220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3027)) := by
  have source := ElevenTheory.theory3812 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule14220 (meaning t m 1988) (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2699) (meaning t m 2761) (meaning t m 3027) source

theorem rule14221 (p1977 p2027 p2938 p3005 p4315 p4320 p4360 : Prop) (h : (¬ p1977) ∨ p2938 ∨ (¬ p4320) ∨ (¬ p4360) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p4315)) : (¬ p1977) ∨ (p2027) ∨ (p2938) ∨ (¬ p3005) ∨ (¬ p4315) ∨ (¬ p4320) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial14221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory3813 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 7)
  exact rule14221 (meaning t m 1977) (meaning t m 2027) (meaning t m 2938) (meaning t m 3005) (meaning t m 4315) (meaning t m 4320) (meaning t m 4360) source

theorem rule14222 (p1995 p2027 p2230 p2476 p2545 p3083 p3238 : Prop) (h : (¬ p2476) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p1995) ∨ (¬ p3083) ∨ p2545 ∨ (¬ p3238)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (p2545) ∨ (¬ p3083) ∨ (¬ p3238) := by
  classical
  tauto

theorem initial14222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3238)) := by
  have source := ElevenTheory.theory3814 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule14222 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2545) (meaning t m 3083) (meaning t m 3238) source

theorem rule14226 (p2010 p2027 p2608 p3201 p3367 p3623 p4366 : Prop) (h : (¬ p2608) ∨ p2027 ∨ p3623 ∨ (¬ p3367) ∨ (¬ p4366) ∨ (¬ p2010) ∨ (¬ p3201)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (p3623) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial14226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory3818 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7)
  exact rule14226 (meaning t m 2010) (meaning t m 2027) (meaning t m 2608) (meaning t m 3201) (meaning t m 3367) (meaning t m 3623) (meaning t m 4366) source

theorem rule14228 (p1994 p2027 p2727 p2938 p2996 p3246 p3947 : Prop) (h : p2938 ∨ (¬ p1994) ∨ (¬ p2727) ∨ (¬ p3246) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2996)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2727) ∨ (p2938) ∨ (¬ p2996) ∨ (¬ p3246) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial14228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory3820 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14228 (meaning t m 1994) (meaning t m 2027) (meaning t m 2727) (meaning t m 2938) (meaning t m 2996) (meaning t m 3246) (meaning t m 3947) source

theorem rule14231 (p1995 p2027 p3008 p3238 p3584 p3609 p3697 p3857 p4031 p4354 : Prop) (h : (¬ p3238) ∨ (¬ p3584) ∨ (¬ p4354) ∨ p3008 ∨ (¬ p3857) ∨ (¬ p3697) ∨ (¬ p4031) ∨ (¬ p3609) ∨ (¬ p1995) ∨ p2027) : (¬ p1995) ∨ (p2027) ∨ (p3008) ∨ (¬ p3238) ∨ (¬ p3584) ∨ (¬ p3609) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4031) ∨ (¬ p4354) := by
  classical
  tauto

theorem initial14231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3609)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4354)) := by
  have source := ElevenTheory.theory3823 t (m.theta 0 5) (m.theta 0 8) (m.theta 1 4) (m.theta 2 4) (m.theta 2 8) (m.theta 4 5) (m.theta 4 6) (m.theta 8 9)
  exact rule14231 (meaning t m 1995) (meaning t m 2027) (meaning t m 3008) (meaning t m 3238) (meaning t m 3584) (meaning t m 3609) (meaning t m 3697) (meaning t m 3857) (meaning t m 4031) (meaning t m 4354) source

theorem rule14233 (p3032 p3947 p5362 p5363 : Prop) (h : (¬ p5363) ∨ (¬ p3032) ∨ (¬ p5362) ∨ (¬ p3947)) : (¬ p3032) ∨ (¬ p3947) ∨ (¬ p5362) ∨ (¬ p5363) := by
  classical
  tauto

theorem initial14233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 5362)) ∨ (¬ (meaning t m 5363)) := by
  have source := ElevenTheory.theory3825 (m.theta 1 7) (m.theta 1 9) (m.theta 3 7) (m.theta 7 9)
  exact rule14233 (meaning t m 3032) (meaning t m 3947) (meaning t m 5362) (meaning t m 5363) source

theorem rule14236 (p1975 p2027 p2323 p2331 p2668 p3309 p3923 : Prop) (h : p2323 ∨ (¬ p2668) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p3923) ∨ (¬ p2331)) : (¬ p1975) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3309) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial14236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory3828 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14236 (meaning t m 1975) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2668) (meaning t m 3309) (meaning t m 3923) source

theorem rule14239 (p1995 p2027 p2187 p2386 p2387 p2499 p2997 p3097 : Prop) (h : (¬ p2386) ∨ p2997 ∨ (¬ p2499) ∨ (¬ p3097) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p1995) ∨ (¬ p2187)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2386) ∨ (¬ p2387) ∨ (¬ p2499) ∨ (p2997) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial14239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory3831 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14239 (meaning t m 1995) (meaning t m 2027) (meaning t m 2187) (meaning t m 2386) (meaning t m 2387) (meaning t m 2499) (meaning t m 2997) (meaning t m 3097) source

theorem rule14240 (p1997 p2027 p2766 p3266 p3744 p4110 p4191 : Prop) (h : p2027 ∨ p2766 ∨ (¬ p4110) ∨ (¬ p1997) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p3266)) : (¬ p1997) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory3832 t (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14240 (meaning t m 1997) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3744) (meaning t m 4110) (meaning t m 4191) source

theorem rule14242 (p1983 p2027 p2241 p2699 p3027 p3506 p4381 p4661 : Prop) (h : p2027 ∨ (¬ p1983) ∨ (¬ p4381) ∨ (¬ p3506) ∨ (¬ p4661) ∨ (¬ p2241) ∨ p2699 ∨ (¬ p3027)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3506) ∨ (¬ p4381) ∨ (¬ p4661) := by
  classical
  tauto

theorem initial14242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4661)) := by
  have source := ElevenTheory.theory3834 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 3 9) (m.theta 7 9) (m.theta 9 10)
  exact rule14242 (meaning t m 1983) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3027) (meaning t m 3506) (meaning t m 4381) (meaning t m 4661) source

theorem rule14245 (p1995 p2027 p2169 p2230 p2579 p3096 p3238 p3989 : Prop) (h : (¬ p1995) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p3238) ∨ p2169 ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096)) : (¬ p1995) ∨ (p2027) ∨ (p2169) ∨ (¬ p2230) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial14245 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory3837 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule14245 (meaning t m 1995) (meaning t m 2027) (meaning t m 2169) (meaning t m 2230) (meaning t m 2579) (meaning t m 3096) (meaning t m 3238) (meaning t m 3989) source

theorem rule14253 (p3931 p5550 p5551 p5552 p5553 : Prop) : (p5550) ∨ (((¬ p5550) ∨ (¬ p5551) ∨ (¬ p3931) ∨ (¬ p5552) ∨ (¬ p5553))) := by
  classical
  tauto

theorem initial14253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5550) ∨ (meaning t m 6143) := by
  exact rule14253 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule14254 (p3931 p5550 p5551 p5552 p5553 : Prop) : (p5551) ∨ (((¬ p5550) ∨ (¬ p5551) ∨ (¬ p3931) ∨ (¬ p5552) ∨ (¬ p5553))) := by
  classical
  tauto

theorem initial14254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5551) ∨ (meaning t m 6143) := by
  exact rule14254 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule14255 (p3931 p5550 p5551 p5552 p5553 : Prop) : (p3931) ∨ (((¬ p5550) ∨ (¬ p5551) ∨ (¬ p3931) ∨ (¬ p5552) ∨ (¬ p5553))) := by
  classical
  tauto

theorem initial14255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3931) ∨ (meaning t m 6143) := by
  exact rule14255 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule14256 (p3931 p5550 p5551 p5552 p5553 : Prop) : (p5552) ∨ (((¬ p5550) ∨ (¬ p5551) ∨ (¬ p3931) ∨ (¬ p5552) ∨ (¬ p5553))) := by
  classical
  tauto

theorem initial14256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5552) ∨ (meaning t m 6143) := by
  exact rule14256 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule14257 (p3931 p5550 p5551 p5552 p5553 : Prop) : (p5553) ∨ (((¬ p5550) ∨ (¬ p5551) ∨ (¬ p3931) ∨ (¬ p5552) ∨ (¬ p5553))) := by
  classical
  tauto

theorem initial14257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5553) ∨ (meaning t m 6143) := by
  exact rule14257 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule14258 (p3931 p5550 p5551 p5552 p5553 : Prop) : (¬ p3931) ∨ (¬ p5550) ∨ (¬ p5551) ∨ (¬ p5552) ∨ (¬ p5553) ∨ (¬ ((¬ p5550) ∨ (¬ p5551) ∨ (¬ p3931) ∨ (¬ p5552) ∨ (¬ p5553))) := by
  classical
  tauto

theorem initial14258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 5550)) ∨ (¬ (meaning t m 5551)) ∨ (¬ (meaning t m 5552)) ∨ (¬ (meaning t m 5553)) ∨ (¬ (meaning t m 6143)) := by
  exact rule14258 (meaning t m 3931) (meaning t m 5550) (meaning t m 5551) (meaning t m 5552) (meaning t m 5553)

theorem rule14265 (p5556 p5557 p5558 p5559 p5560 : Prop) : (p5558) ∨ (((¬ p5557) ∨ (¬ p5558) ∨ (¬ p5556) ∨ (¬ p5559) ∨ (¬ p5560))) := by
  classical
  tauto

theorem initial14265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5558) ∨ (meaning t m 6145) := by
  exact rule14265 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule14267 (p5556 p5557 p5558 p5559 p5560 : Prop) : (p5559) ∨ (((¬ p5557) ∨ (¬ p5558) ∨ (¬ p5556) ∨ (¬ p5559) ∨ (¬ p5560))) := by
  classical
  tauto

theorem initial14267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5559) ∨ (meaning t m 6145) := by
  exact rule14267 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule14268 (p5556 p5557 p5558 p5559 p5560 : Prop) : (p5560) ∨ (((¬ p5557) ∨ (¬ p5558) ∨ (¬ p5556) ∨ (¬ p5559) ∨ (¬ p5560))) := by
  classical
  tauto

theorem initial14268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5560) ∨ (meaning t m 6145) := by
  exact rule14268 (meaning t m 5556) (meaning t m 5557) (meaning t m 5558) (meaning t m 5559) (meaning t m 5560)

theorem rule14272 (p3941 p5562 p5563 p5564 p5565 : Prop) : (p3941) ∨ (((¬ p5562) ∨ (¬ p5563) ∨ (¬ p3941) ∨ (¬ p5564) ∨ (¬ p5565))) := by
  classical
  tauto

theorem initial14272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3941) ∨ (meaning t m 6146) := by
  exact rule14272 (meaning t m 3941) (meaning t m 5562) (meaning t m 5563) (meaning t m 5564) (meaning t m 5565)

theorem rule14278 (p6145 p6146 : Prop) : (¬ ((¬ p6145) ∨ (¬ p6146))) ∨ (¬ p6145) ∨ (¬ p6146) := by
  classical
  tauto

theorem initial14278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6144)) ∨ (¬ (meaning t m 6145)) ∨ (¬ (meaning t m 6146)) := by
  exact rule14278 (meaning t m 6145) (meaning t m 6146)

theorem rule14279 (p5554 p6144 : Prop) (h : (p5554 ↔ p6144)) : (¬ p5554) ∨ (p6144) := by
  classical
  tauto

theorem initial14279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5554)) ∨ (meaning t m 6144) := by
  have source := ElevenTheory.theory3840 t (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule14279 (meaning t m 5554) (meaning t m 6144) source

theorem rule14281 (p2020 p3941 p3944 p5559 : Prop) (h : p3944 ∨ p5559 ∨ (¬ p3941) ∨ (¬ p2020)) : (¬ p2020) ∨ (¬ p3941) ∨ (p3944) ∨ (p5559) := by
  classical
  tauto

theorem initial14281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (¬ (meaning t m 3941)) ∨ (meaning t m 3944) ∨ (meaning t m 5559) := by
  have source := ElevenTheory.theory3841 t (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule14281 (meaning t m 2020) (meaning t m 3941) (meaning t m 3944) (meaning t m 5559) source

theorem rule14282 (p1976 p2027 p2138 p2766 p3266 p4322 p4385 : Prop) (h : (¬ p1976) ∨ (¬ p4385) ∨ (¬ p4322) ∨ (¬ p2138) ∨ p2027 ∨ p2766 ∨ (¬ p3266)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4385) := by
  classical
  tauto

theorem initial14282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4385)) := by
  have source := ElevenTheory.theory3842 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14282 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2766) (meaning t m 3266) (meaning t m 4322) (meaning t m 4385) source

theorem rule14283 (p1992 p2027 p2166 p2210 p2699 p3583 p3694 : Prop) (h : (¬ p1992) ∨ (¬ p2210) ∨ p2699 ∨ p2027 ∨ (¬ p2166) ∨ (¬ p3694) ∨ (¬ p3583)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3583) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial14283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory3843 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5) (m.theta 5 8)
  exact rule14283 (meaning t m 1992) (meaning t m 2027) (meaning t m 2166) (meaning t m 2210) (meaning t m 2699) (meaning t m 3583) (meaning t m 3694) source

theorem rule14285 (p2578 p4036 p4038 p4137 : Prop) (h : (¬ p4038) ∨ (¬ p2578) ∨ (¬ p4036) ∨ (¬ p4137)) : (¬ p2578) ∨ (¬ p4036) ∨ (¬ p4038) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial14285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 4036)) ∨ (¬ (meaning t m 4038)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory3845 (m.theta 0 6) (m.theta 0 9) (m.theta 4 6) (m.theta 6 9)
  exact rule14285 (meaning t m 2578) (meaning t m 4036) (meaning t m 4038) (meaning t m 4137) source

theorem rule14288 (p1997 p2027 p2241 p2699 p2901 p2992 p4235 : Prop) (h : (¬ p2241) ∨ p2027 ∨ p2699 ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p4235) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory3848 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 7)
  exact rule14288 (meaning t m 1997) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2901) (meaning t m 2992) (meaning t m 4235) source

theorem rule14289 (p1982 p2027 p2241 p2264 p2459 p2699 p3027 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2264) ∨ (¬ p1982) ∨ (¬ p2459) ∨ (¬ p3027) ∨ (¬ p2241)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (p2699) ∨ (¬ p3027) := by
  classical
  tauto

theorem initial14289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) := by
  have source := ElevenTheory.theory3849 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14289 (meaning t m 1982) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2459) (meaning t m 2699) (meaning t m 3027) source

theorem rule14290 (p1988 p2027 p2459 p2699 p3266 p3399 p3527 : Prop) (h : (¬ p3527) ∨ p2699 ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3266) ∨ (¬ p2459) ∨ (¬ p3399)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2459) ∨ (p2699) ∨ (¬ p3266) ∨ (¬ p3399) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial14290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory3850 t (m.theta 0 1) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14290 (meaning t m 1988) (meaning t m 2027) (meaning t m 2459) (meaning t m 2699) (meaning t m 3266) (meaning t m 3399) (meaning t m 3527) source

theorem rule14291 (p1982 p2027 p2459 p3399 p3527 p3591 p3818 : Prop) (h : (¬ p2459) ∨ p3818 ∨ (¬ p1982) ∨ (¬ p3399) ∨ (¬ p3527) ∨ p2027 ∨ (¬ p3591)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3591) ∨ (p3818) := by
  classical
  tauto

theorem initial14291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3591)) ∨ (meaning t m 3818) := by
  have source := ElevenTheory.theory3851 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14291 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 3399) (meaning t m 3527) (meaning t m 3591) (meaning t m 3818) source

theorem rule14292 (p1983 p2027 p2449 p2699 p3399 p3527 p3553 : Prop) (h : (¬ p2449) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3527) ∨ p2699 ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2449) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial14292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory3852 t (m.theta 0 1) (m.theta 1 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14292 (meaning t m 1983) (meaning t m 2027) (meaning t m 2449) (meaning t m 2699) (meaning t m 3399) (meaning t m 3527) (meaning t m 3553) source

theorem rule14293 (p1983 p2027 p2699 p3246 p3399 p3527 p3570 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p1983) ∨ (¬ p3246)) : (¬ p1983) ∨ (p2027) ∨ (p2699) ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial14293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory3853 t (m.theta 0 1) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14293 (meaning t m 1983) (meaning t m 2027) (meaning t m 2699) (meaning t m 3246) (meaning t m 3399) (meaning t m 3527) (meaning t m 3570) source

theorem rule14295 (p1986 p2027 p2352 p3008 p3367 p3688 p4358 : Prop) (h : (¬ p4358) ∨ p3008 ∨ (¬ p3688) ∨ (¬ p1986) ∨ (¬ p3367) ∨ (¬ p2352) ∨ p2027) : (¬ p1986) ∨ (p2027) ∨ (¬ p2352) ∨ (p3008) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial14295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory3855 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 8)
  exact rule14295 (meaning t m 1986) (meaning t m 2027) (meaning t m 2352) (meaning t m 3008) (meaning t m 3367) (meaning t m 3688) (meaning t m 4358) source

theorem rule14296 (p2027 p2780 p3471 p3549 p4475 p4867 : Prop) (h : (¬ p3471) ∨ (¬ p3549) ∨ p2027 ∨ (¬ p4475) ∨ (¬ p4867) ∨ (¬ p2780)) : (p2027) ∨ (¬ p2780) ∨ (¬ p3471) ∨ (¬ p3549) ∨ (¬ p4475) ∨ (¬ p4867) := by
  classical
  tauto

theorem initial14296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4475)) ∨ (¬ (meaning t m 4867)) := by
  have source := ElevenTheory.theory3856 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7)
  exact rule14296 (meaning t m 2027) (meaning t m 2780) (meaning t m 3471) (meaning t m 3549) (meaning t m 4475) (meaning t m 4867) source

theorem rule14297 (p2015 p2611 p2774 p4867 : Prop) (h : (¬ p2015) ∨ (¬ p2774) ∨ p4867 ∨ p2611) : (¬ p2015) ∨ (p2611) ∨ (¬ p2774) ∨ (p4867) := by
  classical
  tauto

theorem initial14297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (meaning t m 4867) := by
  have source := ElevenTheory.theory3857 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 6)
  exact rule14297 (meaning t m 2015) (meaning t m 2611) (meaning t m 2774) (meaning t m 4867) source

theorem rule14299 (p1975 p2027 p2765 p2951 p3051 p3246 p3952 p4107 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p1975) ∨ (¬ p3952) ∨ (¬ p2951) ∨ (¬ p4107) ∨ (¬ p3246) ∨ (¬ p3051)) : (¬ p1975) ∨ (p2027) ∨ (p2765) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3952) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial14299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory3859 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule14299 (meaning t m 1975) (meaning t m 2027) (meaning t m 2765) (meaning t m 2951) (meaning t m 3051) (meaning t m 3246) (meaning t m 3952) (meaning t m 4107) source

theorem rule14302 (p1992 p2027 p2274 p2743 p2765 p3568 p4195 : Prop) (h : (¬ p2274) ∨ (¬ p1992) ∨ (¬ p4195) ∨ p2765 ∨ (¬ p3568) ∨ (¬ p2743) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2743) ∨ (p2765) ∨ (¬ p3568) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial14302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory3862 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule14302 (meaning t m 1992) (meaning t m 2027) (meaning t m 2274) (meaning t m 2743) (meaning t m 2765) (meaning t m 3568) (meaning t m 4195) source

theorem rule14303 (p1976 p2027 p2997 p3097 p3365 p3952 p4315 : Prop) (h : (¬ p1976) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4315) ∨ p2997) : (¬ p1976) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial14303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory3863 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14303 (meaning t m 1976) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3365) (meaning t m 3952) (meaning t m 4315) source

theorem rule14304 (p1995 p2388 p3238 p4705 : Prop) (h : (¬ p3238) ∨ (¬ p1995) ∨ p2388 ∨ p4705) : (¬ p1995) ∨ (p2388) ∨ (¬ p3238) ∨ (p4705) := by
  classical
  tauto

theorem initial14304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 3238)) ∨ (meaning t m 4705) := by
  have source := ElevenTheory.theory3864 t (m.theta 1 4) (m.theta 3 5) (m.theta 4 5)
  exact rule14304 (meaning t m 1995) (meaning t m 2388) (meaning t m 3238) (meaning t m 4705) source

theorem rule14305 (p1982 p2027 p2274 p2313 p2363 p2765 p3063 p3204 : Prop) (h : (¬ p2313) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2363) ∨ (¬ p3204) ∨ p2765 ∨ (¬ p3063)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2363) ∨ (p2765) ∨ (¬ p3063) ∨ (¬ p3204) := by
  classical
  tauto

theorem initial14305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3204)) := by
  have source := ElevenTheory.theory3865 t (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule14305 (meaning t m 1982) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2363) (meaning t m 2765) (meaning t m 3063) (meaning t m 3204) source

theorem rule14306 (p2780 p3365 p4841 : Prop) (h : (¬ p3365) ∨ (¬ p4841) ∨ p2780) : (p2780) ∨ (¬ p3365) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial14306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2780) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory3866 (m.theta 0 2) (m.theta 2 3) (m.theta 2 6)
  exact rule14306 (meaning t m 2780) (meaning t m 3365) (meaning t m 4841) source

theorem rule14307 (p2005 p2027 p2230 p2476 p2493 p3238 p3498 : Prop) (h : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p2493) ∨ p2027 ∨ p3498 ∨ (¬ p2476) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (p3498) := by
  classical
  tauto

theorem initial14307 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (meaning t m 3498) := by
  have source := ElevenTheory.theory3867 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8)
  exact rule14307 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2493) (meaning t m 3238) (meaning t m 3498) source

theorem rule14308 (p2027 p2499 p2797 p2810 p3984 p4811 : Prop) (h : (¬ p2810) ∨ p2027 ∨ (¬ p3984) ∨ (¬ p4811) ∨ (¬ p2797) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial14308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory3868 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule14308 (meaning t m 2027) (meaning t m 2499) (meaning t m 2797) (meaning t m 2810) (meaning t m 3984) (meaning t m 4811) source

theorem rule14309 (p1992 p2027 p2766 p3570 p3583 p4244 p4348 : Prop) (h : (¬ p1992) ∨ (¬ p3583) ∨ (¬ p4348) ∨ (¬ p4244) ∨ p2027 ∨ p2766 ∨ (¬ p3570)) : (¬ p1992) ∨ (p2027) ∨ (p2766) ∨ (¬ p3570) ∨ (¬ p3583) ∨ (¬ p4244) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3869 t (m.theta 1 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14309 (meaning t m 1992) (meaning t m 2027) (meaning t m 2766) (meaning t m 3570) (meaning t m 3583) (meaning t m 4244) (meaning t m 4348) source

theorem rule14312 (p1998 p2027 p2264 p2323 p2651 p3027 p4111 : Prop) (h : p2027 ∨ (¬ p1998) ∨ p2323 ∨ (¬ p4111) ∨ (¬ p3027) ∨ (¬ p2651) ∨ (¬ p2264)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p3027) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory3872 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8)
  exact rule14312 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2323) (meaning t m 2651) (meaning t m 3027) (meaning t m 4111) source

theorem rule14313 (p1981 p2027 p2241 p2352 p2699 p2727 p3016 : Prop) (h : (¬ p2352) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p1981) ∨ p2699 ∨ p2027) : (¬ p1981) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2352) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial14313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory3873 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule14313 (meaning t m 1981) (meaning t m 2027) (meaning t m 2241) (meaning t m 2352) (meaning t m 2699) (meaning t m 2727) (meaning t m 3016) source

theorem rule14316 (p1983 p2027 p2241 p2417 p2437 p2699 p2727 : Prop) (h : (¬ p2241) ∨ (¬ p2727) ∨ p2699 ∨ (¬ p2437) ∨ p2027 ∨ (¬ p1983) ∨ (¬ p2417)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (p2699) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial14316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory3876 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule14316 (meaning t m 1983) (meaning t m 2027) (meaning t m 2241) (meaning t m 2417) (meaning t m 2437) (meaning t m 2699) (meaning t m 2727) source

theorem rule14319 (p2005 p2027 p2187 p2387 p2765 p3654 p4137 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p3654) ∨ (¬ p2005) ∨ (¬ p4137) ∨ (¬ p2187) ∨ (¬ p2387)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2387) ∨ (p2765) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial14319 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory3879 t (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule14319 (meaning t m 2005) (meaning t m 2027) (meaning t m 2187) (meaning t m 2387) (meaning t m 2765) (meaning t m 3654) (meaning t m 4137) source

theorem rule14322 (p1992 p2027 p2132 p2169 p2780 p3583 p4358 : Prop) (h : (¬ p2132) ∨ p2169 ∨ (¬ p1992) ∨ (¬ p2780) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p4358)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2132) ∨ (p2169) ∨ (¬ p2780) ∨ (¬ p3583) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial14322 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory3882 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 6 8)
  exact rule14322 (meaning t m 1992) (meaning t m 2027) (meaning t m 2132) (meaning t m 2169) (meaning t m 2780) (meaning t m 3583) (meaning t m 4358) source

theorem rule14323 (p1975 p2027 p2274 p2459 p2633 p3989 p4347 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p1975) ∨ (¬ p2459) ∨ (¬ p4347) ∨ (¬ p2274) ∨ (¬ p3989)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3883 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14323 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2459) (meaning t m 2633) (meaning t m 3989) (meaning t m 4347) source

theorem rule14324 (p2015 p2027 p2352 p2493 p2699 p3379 p3923 : Prop) (h : p2699 ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p3923) ∨ (¬ p2015)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2493) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial14324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory3884 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule14324 (meaning t m 2015) (meaning t m 2027) (meaning t m 2352) (meaning t m 2493) (meaning t m 2699) (meaning t m 3379) (meaning t m 3923) source

theorem rule14325 (p2005 p2027 p2406 p2440 p2699 p3016 p3379 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2005) ∨ (¬ p3379) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3016)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (p2699) ∨ (¬ p3016) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial14325 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3885 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule14325 (meaning t m 2005) (meaning t m 2027) (meaning t m 2406) (meaning t m 2440) (meaning t m 2699) (meaning t m 3016) (meaning t m 3379) source

theorem rule14328 (p1990 p2027 p2148 p2307 p2962 p3063 p3549 p3989 : Prop) (h : (¬ p3549) ∨ p2148 ∨ (¬ p2962) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3063) ∨ (¬ p3989) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (p2148) ∨ (¬ p2307) ∨ (¬ p2962) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial14328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory3888 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14328 (meaning t m 1990) (meaning t m 2027) (meaning t m 2148) (meaning t m 2307) (meaning t m 2962) (meaning t m 3063) (meaning t m 3549) (meaning t m 3989) source

theorem rule14329 (p1981 p2027 p2187 p2406 p2563 p2699 p3379 : Prop) (h : p2027 ∨ (¬ p1981) ∨ (¬ p3379) ∨ (¬ p2406) ∨ (¬ p2563) ∨ p2699 ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (p2699) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial14329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory3889 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule14329 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2406) (meaning t m 2563) (meaning t m 2699) (meaning t m 3379) source

theorem rule14330 (p1992 p2027 p2104 p2132 p2766 p3583 p3692 p4740 : Prop) (h : (¬ p2132) ∨ (¬ p2104) ∨ (¬ p4740) ∨ p2027 ∨ (¬ p3692) ∨ p2766 ∨ (¬ p1992) ∨ (¬ p3583)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2104) ∨ (¬ p2132) ∨ (p2766) ∨ (¬ p3583) ∨ (¬ p3692) ∨ (¬ p4740) := by
  classical
  tauto

theorem initial14330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4740)) := by
  have source := ElevenTheory.theory3890 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule14330 (meaning t m 1992) (meaning t m 2027) (meaning t m 2104) (meaning t m 2132) (meaning t m 2766) (meaning t m 3583) (meaning t m 3692) (meaning t m 4740) source

theorem rule14331 (p1979 p2688 p2751 p2811 p2946 : Prop) (h : (¬ p1979) ∨ p2688 ∨ (¬ p2946) ∨ p2751 ∨ (¬ p2811)) : (¬ p1979) ∨ (p2688) ∨ (p2751) ∨ (¬ p2811) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial14331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2688) ∨ (meaning t m 2751) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory3891 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule14331 (meaning t m 1979) (meaning t m 2688) (meaning t m 2751) (meaning t m 2811) (meaning t m 2946) source

theorem rule14332 (p2005 p2027 p2241 p2295 p2588 p2641 p2699 : Prop) (h : p2027 ∨ (¬ p2295) ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p2005) ∨ (¬ p2588) ∨ p2699) : (¬ p2005) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (p2699) := by
  classical
  tauto

theorem initial14332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) := by
  have source := ElevenTheory.theory3892 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule14332 (meaning t m 2005) (meaning t m 2027) (meaning t m 2241) (meaning t m 2295) (meaning t m 2588) (meaning t m 2641) (meaning t m 2699) source

theorem rule14334 (p1989 p2027 p2191 p2545 p2657 p2946 p3156 : Prop) (h : (¬ p2657) ∨ p2545 ∨ (¬ p1989) ∨ (¬ p2191) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3156)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2191) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial14334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory3894 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule14334 (meaning t m 1989) (meaning t m 2027) (meaning t m 2191) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) (meaning t m 3156) source

theorem rule14336 (p1987 p2027 p2138 p2696 p2766 p3692 p3694 : Prop) (h : (¬ p2138) ∨ p2027 ∨ p2766 ∨ (¬ p3694) ∨ (¬ p1987) ∨ (¬ p3692) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (p2766) ∨ (¬ p3692) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial14336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory3896 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8) (m.theta 8 9)
  exact rule14336 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2766) (meaning t m 3692) (meaning t m 3694) source

theorem rule14337 (p3694 p4335 p4385 : Prop) (h : (¬ p4335) ∨ (¬ p3694) ∨ p4385) : (¬ p3694) ∨ (¬ p4335) ∨ (p4385) := by
  classical
  tauto

theorem initial14337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4335)) ∨ (meaning t m 4385) := by
  have source := ElevenTheory.theory3897 (m.theta 2 5) (m.theta 5 8) (m.theta 5 9)
  exact rule14337 (meaning t m 3694) (meaning t m 4335) (meaning t m 4385) source

theorem rule14338 (p1992 p2027 p2307 p2545 p2797 p2810 p3549 p3567 p3953 : Prop) (h : (¬ p1992) ∨ (¬ p3567) ∨ (¬ p3549) ∨ (¬ p2810) ∨ (¬ p2797) ∨ (¬ p2307) ∨ p2545 ∨ p2027 ∨ (¬ p3953)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2307) ∨ (p2545) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p3953) := by
  classical
  tauto

theorem initial14338 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3953)) := by
  have source := ElevenTheory.theory3898 t (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 7)
  exact rule14338 (meaning t m 1992) (meaning t m 2027) (meaning t m 2307) (meaning t m 2545) (meaning t m 2797) (meaning t m 2810) (meaning t m 3549) (meaning t m 3567) (meaning t m 3953) source

theorem rule14339 (p2651 p2952 p3413 : Prop) (h : (¬ p3413) ∨ (¬ p2952) ∨ (¬ p2651)) : (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial14339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory3899 (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule14339 (meaning t m 2651) (meaning t m 2952) (meaning t m 3413) source

theorem rule14343 (p1990 p2027 p2166 p2563 p2699 p3379 p3880 p3948 : Prop) (h : (¬ p3379) ∨ (¬ p1990) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p2166) ∨ p2699 ∨ (¬ p3880) ∨ (¬ p3948)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2563) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3880) ∨ (¬ p3948) := by
  classical
  tauto

theorem initial14343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3948)) := by
  have source := ElevenTheory.theory3903 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule14343 (meaning t m 1990) (meaning t m 2027) (meaning t m 2166) (meaning t m 2563) (meaning t m 2699) (meaning t m 3379) (meaning t m 3880) (meaning t m 3948) source

theorem rule14347 (p1987 p2027 p2462 p2946 p3414 p3690 p3699 p4315 : Prop) (h : p2462 ∨ (¬ p4315) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3699) ∨ (¬ p3690) ∨ (¬ p2946) ∨ (¬ p3414)) : (¬ p1987) ∨ (p2027) ∨ (p2462) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3690) ∨ (¬ p3699) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial14347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory3907 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14347 (meaning t m 1987) (meaning t m 2027) (meaning t m 2462) (meaning t m 2946) (meaning t m 3414) (meaning t m 3690) (meaning t m 3699) (meaning t m 4315) source

theorem rule14348 (p1979 p2027 p2598 p2699 p2737 p3136 p3585 p3589 : Prop) (h : (¬ p3136) ∨ (¬ p3589) ∨ p2699 ∨ (¬ p1979) ∨ (¬ p2737) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p3585)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3136) ∨ (¬ p3585) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial14348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory3908 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule14348 (meaning t m 1979) (meaning t m 2027) (meaning t m 2598) (meaning t m 2699) (meaning t m 2737) (meaning t m 3136) (meaning t m 3585) (meaning t m 3589) source

theorem rule14350 (p1989 p2027 p2210 p2459 p2633 p3544 p3692 p3906 p4366 : Prop) (h : (¬ p4366) ∨ (¬ p2210) ∨ (¬ p1989) ∨ p2633 ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p3906) ∨ (¬ p3544)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3544) ∨ (¬ p3692) ∨ (¬ p3906) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial14350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory3910 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 1 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14350 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2459) (meaning t m 2633) (meaning t m 3544) (meaning t m 3692) (meaning t m 3906) (meaning t m 4366) source

theorem rule14352 (p1998 p2027 p2114 p2363 p2383 p2584 p3367 p3759 p4348 : Prop) (h : p2114 ∨ (¬ p3759) ∨ (¬ p3367) ∨ (¬ p1998) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2584) ∨ (¬ p2383)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory3912 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 2) (m.theta 2 4) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14352 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2363) (meaning t m 2383) (meaning t m 2584) (meaning t m 3367) (meaning t m 3759) (meaning t m 4348) source

theorem rule14354 (p1998 p2027 p2598 p2699 p2707 p2911 p3585 p3589 p3658 : Prop) (h : (¬ p1998) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2911) ∨ (¬ p3589) ∨ p2027 ∨ p2699 ∨ (¬ p3658) ∨ (¬ p3585)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2598) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2911) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3658) := by
  classical
  tauto

theorem initial14354 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3658)) := by
  have source := ElevenTheory.theory3914 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule14354 (meaning t m 1998) (meaning t m 2027) (meaning t m 2598) (meaning t m 2699) (meaning t m 2707) (meaning t m 2911) (meaning t m 3585) (meaning t m 3589) (meaning t m 3658) source

theorem rule14356 (p2005 p2027 p2331 p2545 p2657 p2668 p3956 : Prop) (h : (¬ p2005) ∨ (¬ p2331) ∨ (¬ p2657) ∨ p2545 ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2668)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial14356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory3916 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 8)
  exact rule14356 (meaning t m 2005) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 2668) (meaning t m 3956) source

theorem rule14373 (p1985 p2027 p2323 p2437 p2651 p2911 p3570 : Prop) (h : (¬ p2911) ∨ (¬ p1985) ∨ (¬ p2437) ∨ p2027 ∨ p2323 ∨ (¬ p3570) ∨ (¬ p2651)) : (¬ p1985) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial14373 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory3933 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule14373 (meaning t m 1985) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2651) (meaning t m 2911) (meaning t m 3570) source

theorem rule14378 (p1975 p2027 p2295 p2383 p2860 p3324 p3474 p3743 : Prop) (h : (¬ p3743) ∨ (¬ p2383) ∨ (¬ p1975) ∨ (¬ p2295) ∨ (¬ p3324) ∨ p2027 ∨ p3474 ∨ (¬ p2860)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2860) ∨ (¬ p3324) ∨ (p3474) ∨ (¬ p3743) := by
  classical
  tauto

theorem initial14378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3324)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3743)) := by
  have source := ElevenTheory.theory3938 t (m.theta 0 6) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14378 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2383) (meaning t m 2860) (meaning t m 3324) (meaning t m 3474) (meaning t m 3743) source

theorem rule14379 (p1975 p2027 p2202 p2295 p2383 p2584 p2589 p3324 : Prop) (h : p2202 ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p3324) ∨ (¬ p2295) ∨ (¬ p2589) ∨ (¬ p1975) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial14379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory3939 t (m.theta 0 4) (m.theta 0 6) (m.theta 3 6) (m.theta 4 5) (m.theta 6 7) (m.theta 6 8)
  exact rule14379 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2295) (meaning t m 2383) (meaning t m 2584) (meaning t m 2589) (meaning t m 3324) source

theorem rule14380 (p1975 p2027 p2295 p2352 p2842 p3324 p3422 : Prop) (h : p2842 ∨ (¬ p2352) ∨ (¬ p2295) ∨ (¬ p1975) ∨ (¬ p3324) ∨ p2027 ∨ (¬ p3422)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2352) ∨ (p2842) ∨ (¬ p3324) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial14380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory3940 t (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14380 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2352) (meaning t m 2842) (meaning t m 3324) (meaning t m 3422) source

theorem rule14383 (p1981 p2027 p2295 p2313 p2383 p2641 p2688 : Prop) (h : (¬ p2383) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p1981) ∨ p2688 ∨ (¬ p2295) ∨ (¬ p2641)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2641) ∨ (p2688) := by
  classical
  tauto

theorem initial14383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2688) := by
  have source := ElevenTheory.theory3943 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14383 (meaning t m 1981) (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 2383) (meaning t m 2641) (meaning t m 2688) source

theorem rule14384 (p1981 p2027 p2323 p2946 p3146 p3156 p4347 : Prop) (h : p2323 ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p4347) ∨ (¬ p3146) ∨ (¬ p3156)) : (¬ p1981) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory3944 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14384 (meaning t m 1981) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 4347) source

theorem rule14387 (p1992 p2027 p2608 p2766 p3659 p4348 p4366 p4424 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p4348) ∨ (¬ p3659) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4366) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial14387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory3947 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14387 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2766) (meaning t m 3659) (meaning t m 4348) (meaning t m 4366) (meaning t m 4424) source

theorem rule14389 (p1996 p2027 p2202 p2417 p3201 p3684 p3947 : Prop) (h : (¬ p3684) ∨ p2202 ∨ (¬ p1996) ∨ (¬ p3947) ∨ (¬ p2417) ∨ (¬ p3201) ∨ p2027) : (¬ p1996) ∨ (p2027) ∨ (p2202) ∨ (¬ p2417) ∨ (¬ p3201) ∨ (¬ p3684) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial14389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory3949 t (m.theta 2 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule14389 (meaning t m 1996) (meaning t m 2027) (meaning t m 2202) (meaning t m 2417) (meaning t m 3201) (meaning t m 3684) (meaning t m 3947) source

theorem rule14391 (p4199 p4201 p5568 p5569 p5570 : Prop) : (p5568) ∨ (((¬ p4199) ∨ (¬ p5568) ∨ (¬ p4201) ∨ (¬ p5569) ∨ (¬ p5570))) := by
  classical
  tauto

theorem initial14391 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5568) ∨ (meaning t m 6148) := by
  exact rule14391 (meaning t m 4199) (meaning t m 4201) (meaning t m 5568) (meaning t m 5569) (meaning t m 5570)

theorem rule14398 (p3969 p5572 p5573 p5574 p5575 : Prop) : (p3969) ∨ (((¬ p5572) ∨ (¬ p5573) ∨ (¬ p3969) ∨ (¬ p5574) ∨ (¬ p5575))) := by
  classical
  tauto

theorem initial14398 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3969) ∨ (meaning t m 6149) := by
  exact rule14398 (meaning t m 3969) (meaning t m 5572) (meaning t m 5573) (meaning t m 5574) (meaning t m 5575)

theorem rule14404 (p6148 p6149 : Prop) : (¬ ((¬ p6148) ∨ (¬ p6149))) ∨ (¬ p6148) ∨ (¬ p6149) := by
  classical
  tauto

theorem initial14404 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6147)) ∨ (¬ (meaning t m 6148)) ∨ (¬ (meaning t m 6149)) := by
  exact rule14404 (meaning t m 6148) (meaning t m 6149)

theorem rule14405 (p5566 p6147 : Prop) (h : (p5566 ↔ p6147)) : (¬ p5566) ∨ (p6147) := by
  classical
  tauto

theorem initial14405 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5566)) ∨ (meaning t m 6147) := by
  have source := ElevenTheory.theory3950 t (m.theta 5 10) (m.theta 5 8) (m.theta 8 10)
  exact rule14405 (meaning t m 5566) (meaning t m 6147) source

theorem rule14409 (p5578 p5579 p5580 p5581 p5582 : Prop) : (p5580) ∨ (((¬ p5579) ∨ (¬ p5580) ∨ (¬ p5578) ∨ (¬ p5581) ∨ (¬ p5582))) := by
  classical
  tauto

theorem initial14409 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5580) ∨ (meaning t m 6151) := by
  exact rule14409 (meaning t m 5578) (meaning t m 5579) (meaning t m 5580) (meaning t m 5581) (meaning t m 5582)

theorem rule14416 (p3979 p5584 p5585 p5586 p5587 : Prop) : (p3979) ∨ (((¬ p5584) ∨ (¬ p5585) ∨ (¬ p3979) ∨ (¬ p5586) ∨ (¬ p5587))) := by
  classical
  tauto

theorem initial14416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3979) ∨ (meaning t m 6152) := by
  exact rule14416 (meaning t m 3979) (meaning t m 5584) (meaning t m 5585) (meaning t m 5586) (meaning t m 5587)

theorem rule14422 (p6151 p6152 : Prop) : (¬ ((¬ p6151) ∨ (¬ p6152))) ∨ (¬ p6151) ∨ (¬ p6152) := by
  classical
  tauto

theorem initial14422 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6150)) ∨ (¬ (meaning t m 6151)) ∨ (¬ (meaning t m 6152)) := by
  exact rule14422 (meaning t m 6151) (meaning t m 6152)

theorem rule14423 (p5576 p6150 : Prop) (h : (p5576 ↔ p6150)) : (¬ p5576) ∨ (p6150) := by
  classical
  tauto

theorem initial14423 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5576)) ∨ (meaning t m 6150) := by
  have source := ElevenTheory.theory3952 t (m.theta 6 10) (m.theta 6 8) (m.theta 8 10)
  exact rule14423 (meaning t m 5576) (meaning t m 6150) source

theorem rule14425 (p1988 p3266 p3982 p5118 : Prop) (h : p3982 ∨ p5118 ∨ (¬ p3266) ∨ (¬ p1988)) : (¬ p1988) ∨ (¬ p3266) ∨ (p3982) ∨ (p5118) := by
  classical
  tauto

theorem initial14425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (¬ (meaning t m 3266)) ∨ (meaning t m 3982) ∨ (meaning t m 5118) := by
  have source := ElevenTheory.theory3953 t (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule14425 (meaning t m 1988) (meaning t m 3266) (meaning t m 3982) (meaning t m 5118) source

theorem rule14426 (p1975 p2027 p2274 p2284 p2611 p2696 p3136 : Prop) (h : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p1975) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3136) ∨ p2027) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial14426 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory3954 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14426 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2611) (meaning t m 2696) (meaning t m 3136) source

theorem rule14427 (p1975 p2027 p2274 p2611 p2797 p2946 p3986 p4117 p4315 : Prop) (h : p2611 ∨ (¬ p3986) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p4117) ∨ (¬ p2797)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2611) ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3986) ∨ (¬ p4117) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial14427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory3955 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule14427 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2611) (meaning t m 2797) (meaning t m 2946) (meaning t m 3986) (meaning t m 4117) (meaning t m 4315) source

theorem rule14428 (p1994 p2027 p2323 p2383 p2630 p3324 p3987 p4195 : Prop) (h : (¬ p3324) ∨ (¬ p2630) ∨ (¬ p2383) ∨ (¬ p3987) ∨ p2027 ∨ p2323 ∨ (¬ p4195) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2323) ∨ (¬ p2383) ∨ (¬ p2630) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial14428 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory3956 t (m.theta 0 3) (m.theta 0 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule14428 (meaning t m 1994) (meaning t m 2027) (meaning t m 2323) (meaning t m 2383) (meaning t m 2630) (meaning t m 3324) (meaning t m 3987) (meaning t m 4195) source

theorem rule14429 (p2000 p2027 p2633 p3333 p3346 p3644 p3876 : Prop) (h : (¬ p3644) ∨ (¬ p2000) ∨ (¬ p3333) ∨ (¬ p3876) ∨ (¬ p3346) ∨ p2027 ∨ p2633) : (¬ p2000) ∨ (p2027) ∨ (p2633) ∨ (¬ p3333) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial14429 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory3957 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 9) (m.theta 7 8)
  exact rule14429 (meaning t m 2000) (meaning t m 2027) (meaning t m 2633) (meaning t m 3333) (meaning t m 3346) (meaning t m 3644) (meaning t m 3876) source

theorem rule14430 (p1988 p2027 p2284 p2323 p2946 p3125 p3461 : Prop) (h : (¬ p3125) ∨ p2323 ∨ p2027 ∨ (¬ p3461) ∨ (¬ p2284) ∨ (¬ p1988) ∨ (¬ p2946)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial14430 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory3958 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14430 (meaning t m 1988) (meaning t m 2027) (meaning t m 2284) (meaning t m 2323) (meaning t m 2946) (meaning t m 3125) (meaning t m 3461) source

theorem rule14431 (p1988 p2027 p2323 p2946 p3146 p3156 p3266 : Prop) (h : (¬ p3156) ∨ (¬ p1988) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2946) ∨ p2323 ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial14431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory3959 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14431 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3266) source

theorem rule14432 (p1975 p2027 p2323 p2383 p2449 p3324 p3987 p4107 p4156 : Prop) (h : p2323 ∨ (¬ p3324) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p2449) ∨ (¬ p3987) ∨ (¬ p2383) ∨ (¬ p1975) ∨ (¬ p4156)) : (¬ p1975) ∨ (p2027) ∨ (p2323) ∨ (¬ p2383) ∨ (¬ p2449) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4107) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial14432 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory3960 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule14432 (meaning t m 1975) (meaning t m 2027) (meaning t m 2323) (meaning t m 2383) (meaning t m 2449) (meaning t m 3324) (meaning t m 3987) (meaning t m 4107) (meaning t m 4156) source

theorem rule14435 (p1975 p2027 p2622 p2707 p2743 p3434 p4107 : Prop) (h : (¬ p3434) ∨ (¬ p2707) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p4107) ∨ p2622 ∨ (¬ p2743)) : (¬ p1975) ∨ (p2027) ∨ (p2622) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p3434) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial14435 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory3963 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule14435 (meaning t m 1975) (meaning t m 2027) (meaning t m 2622) (meaning t m 2707) (meaning t m 2743) (meaning t m 3434) (meaning t m 4107) source

theorem rule14436 (p1999 p2027 p2210 p2247 p2284 p2688 p3125 p4282 : Prop) (h : p2688 ∨ (¬ p3125) ∨ (¬ p1999) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2284) ∨ (¬ p4282) ∨ (¬ p2210)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2284) ∨ (p2688) ∨ (¬ p3125) ∨ (¬ p4282) := by
  classical
  tauto

theorem initial14436 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4282)) := by
  have source := ElevenTheory.theory3964 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9)
  exact rule14436 (meaning t m 1999) (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2284) (meaning t m 2688) (meaning t m 3125) (meaning t m 4282) source

theorem rule14440 (p1994 p2027 p2622 p2743 p3201 p3367 p3742 : Prop) (h : (¬ p2743) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3367) ∨ p2622 ∨ (¬ p3201) ∨ (¬ p3742)) : (¬ p1994) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3201) ∨ (¬ p3367) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial14440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory3968 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule14440 (meaning t m 1994) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3201) (meaning t m 3367) (meaning t m 3742) source

theorem rule14441 (p1975 p2027 p2114 p2274 p2284 p2737 p2811 p2946 : Prop) (h : p2027 ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p2284) ∨ (¬ p2274) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (p2114) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial14441 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory3969 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14441 (meaning t m 1975) (meaning t m 2027) (meaning t m 2114) (meaning t m 2274) (meaning t m 2284) (meaning t m 2737) (meaning t m 2811) (meaning t m 2946) source

theorem rule14446 (p2020 p2027 p2611 p2696 p3136 p3156 p3969 : Prop) (h : (¬ p2020) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p3136) ∨ p2611 ∨ (¬ p3156)) : (¬ p2020) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3969) := by
  classical
  tauto

theorem initial14446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3969)) := by
  have source := ElevenTheory.theory3974 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10)
  exact rule14446 (meaning t m 2020) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 3136) (meaning t m 3156) (meaning t m 3969) source

theorem rule14455 (p1982 p2027 p2323 p2533 p2946 p3156 p3680 p4444 : Prop) (h : p2323 ∨ (¬ p1982) ∨ (¬ p2533) ∨ (¬ p2946) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p4444)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2533) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3680) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory3983 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14455 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2533) (meaning t m 2946) (meaning t m 3156) (meaning t m 3680) (meaning t m 4444) source

theorem rule14456 (p1975 p2027 p2274 p3622 p3670 p3744 p4191 : Prop) (h : p3622 ∨ (¬ p1975) ∨ (¬ p3670) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p3744)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p3622) ∨ (¬ p3670) ∨ (¬ p3744) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14456 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 3622) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory3984 t (m.theta 2 9) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule14456 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 3622) (meaning t m 3670) (meaning t m 3744) (meaning t m 4191) source

theorem rule14460 (p1994 p2027 p3008 p3434 p3584 p3742 p4278 p5085 : Prop) (h : (¬ p5085) ∨ p3008 ∨ (¬ p4278) ∨ (¬ p3434) ∨ (¬ p3742) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3584)) : (¬ p1994) ∨ (p2027) ∨ (p3008) ∨ (¬ p3434) ∨ (¬ p3584) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial14460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory3988 t (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule14460 (meaning t m 1994) (meaning t m 2027) (meaning t m 3008) (meaning t m 3434) (meaning t m 3584) (meaning t m 3742) (meaning t m 4278) (meaning t m 5085) source

theorem rule14465 (p2008 p2027 p2417 p2579 p3008 p3389 p4324 : Prop) (h : (¬ p4324) ∨ (¬ p2008) ∨ (¬ p2579) ∨ p3008 ∨ (¬ p2417) ∨ p2027 ∨ (¬ p3389)) : (¬ p2008) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2579) ∨ (p3008) ∨ (¬ p3389) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial14465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory3993 t (m.theta 0 4) (m.theta 2 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule14465 (meaning t m 2008) (meaning t m 2027) (meaning t m 2417) (meaning t m 2579) (meaning t m 3008) (meaning t m 3389) (meaning t m 4324) source

theorem rule14469 (p1994 p2027 p2202 p3434 p3684 p3742 p4278 p5085 : Prop) (h : (¬ p5085) ∨ p2202 ∨ p2027 ∨ (¬ p3684) ∨ (¬ p1994) ∨ (¬ p4278) ∨ (¬ p3742) ∨ (¬ p3434)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p3434) ∨ (¬ p3684) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial14469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory3997 t (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule14469 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 3434) (meaning t m 3684) (meaning t m 3742) (meaning t m 4278) (meaning t m 5085) source

theorem rule14470 (p2020 p2964 p3276 p5119 : Prop) (h : p2964 ∨ (¬ p2020) ∨ p5119 ∨ (¬ p3276)) : (¬ p2020) ∨ (p2964) ∨ (¬ p3276) ∨ (p5119) := by
  classical
  tauto

theorem initial14470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (meaning t m 5119) := by
  have source := ElevenTheory.theory3998 t (m.theta 4 9) (m.theta 8 10) (m.theta 9 10)
  exact rule14470 (meaning t m 2020) (meaning t m 2964) (meaning t m 3276) (meaning t m 5119) source

theorem rule14475 (p4309 p4310 p5590 p5591 p5592 : Prop) : (p5590) ∨ (((¬ p4309) ∨ (¬ p4310) ∨ (¬ p5591) ∨ (¬ p5590) ∨ (¬ p5592))) := by
  classical
  tauto

theorem initial14475 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5590) ∨ (meaning t m 6154) := by
  exact rule14475 (meaning t m 4309) (meaning t m 4310) (meaning t m 5590) (meaning t m 5591) (meaning t m 5592)

theorem rule14482 (p3998 p4284 p4285 p5594 p5595 : Prop) : (p3998) ∨ (((¬ p5595) ∨ (¬ p5594) ∨ (¬ p4285) ∨ (¬ p4284) ∨ (¬ p3998))) := by
  classical
  tauto

theorem initial14482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3998) ∨ (meaning t m 6155) := by
  exact rule14482 (meaning t m 3998) (meaning t m 4284) (meaning t m 4285) (meaning t m 5594) (meaning t m 5595)

end SunPrize.SMT
