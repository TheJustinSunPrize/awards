import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory017
import SunPrize.Certificate.Theory018
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule15618 (p1984 p2027 p2169 p3564 p3591 p3956 p4026 : Prop) (h : p2169 ∨ (¬ p3956) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3564) ∨ (¬ p3591) ∨ (¬ p4026)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p3564) ∨ (¬ p3591) ∨ (¬ p3956) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial15618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory4986 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15618 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 3564) (meaning t m 3591) (meaning t m 3956) (meaning t m 4026) source

theorem rule15620 (p1984 p2027 p2588 p2997 p3584 p3585 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p2588) ∨ (¬ p3585) ∨ (¬ p3584) ∨ (¬ p1984) ∨ p2027 ∨ p2997) : (¬ p1984) ∨ (p2027) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4988 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule15620 (meaning t m 1984) (meaning t m 2027) (meaning t m 2588) (meaning t m 2997) (meaning t m 3584) (meaning t m 3585) (meaning t m 3954) source

theorem rule15621 (p1992 p2027 p2169 p2499 p2608 p3452 p3956 : Prop) (h : p2169 ∨ (¬ p3956) ∨ (¬ p2608) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p1992) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2499) ∨ (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4989 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8)
  exact rule15621 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2499) (meaning t m 2608) (meaning t m 3452) (meaning t m 3956) source

theorem rule15622 (p1982 p2027 p2459 p2688 p2881 p2951 p2992 p3051 : Prop) (h : (¬ p2459) ∨ (¬ p1982) ∨ p2688 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p2951) ∨ (¬ p2881)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (p2688) ∨ (¬ p2881) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) := by
  classical
  tauto

theorem initial15622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) := by
  have source := ElevenTheory.theory4990 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15622 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2688) (meaning t m 2881) (meaning t m 2951) (meaning t m 2992) (meaning t m 3051) source

theorem rule15623 (p1983 p2027 p2264 p2688 p3027 p3516 p3551 : Prop) (h : (¬ p1983) ∨ p2027 ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p3027) ∨ (¬ p2264) ∨ p2688) : (¬ p1983) ∨ (p2027) ∨ (¬ p2264) ∨ (p2688) ∨ (¬ p3027) ∨ (¬ p3516) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial15623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory4991 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15623 (meaning t m 1983) (meaning t m 2027) (meaning t m 2264) (meaning t m 2688) (meaning t m 3027) (meaning t m 3516) (meaning t m 3551) source

theorem rule15625 (p1994 p2027 p2202 p2373 p2651 p2952 p3497 : Prop) (h : (¬ p1994) ∨ (¬ p2373) ∨ p2202 ∨ (¬ p2952) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p2651)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial15625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory4993 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule15625 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 2651) (meaning t m 2952) (meaning t m 3497) source

theorem rule15626 (p1988 p2027 p2622 p2761 p2951 p3051 p3136 p3246 : Prop) (h : p2622 ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (p2622) ∨ (¬ p2761) ∨ (¬ p2951) ∨ (¬ p3051) ∨ (¬ p3136) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial15626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory4994 t (m.theta 0 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15626 (meaning t m 1988) (meaning t m 2027) (meaning t m 2622) (meaning t m 2761) (meaning t m 2951) (meaning t m 3051) (meaning t m 3136) (meaning t m 3246) source

theorem rule15627 (p2000 p2027 p2169 p2499 p3222 p3346 p3956 : Prop) (h : (¬ p3956) ∨ (¬ p2499) ∨ p2169 ∨ p2027 ∨ (¬ p3346) ∨ (¬ p2000) ∨ (¬ p3222)) : (¬ p2000) ∨ (p2027) ∨ (p2169) ∨ (¬ p2499) ∨ (¬ p3222) ∨ (¬ p3346) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15627 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4995 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 8)
  exact rule15627 (meaning t m 2000) (meaning t m 2027) (meaning t m 2169) (meaning t m 2499) (meaning t m 3222) (meaning t m 3346) (meaning t m 3956) source

theorem rule15630 (p1982 p2027 p2459 p2499 p2588 p2997 p3051 p3156 p3452 p4042 p4320 p4521 : Prop) (h : (¬ p2459) ∨ (¬ p4042) ∨ (¬ p1982) ∨ (¬ p3156) ∨ (¬ p4320) ∨ (¬ p2499) ∨ p2997 ∨ (¬ p2588) ∨ (¬ p4521) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p3452)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4042) ∨ (¬ p4320) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial15630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory4998 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15630 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2499) (meaning t m 2588) (meaning t m 2997) (meaning t m 3051) (meaning t m 3156) (meaning t m 3452) (meaning t m 4042) (meaning t m 4320) (meaning t m 4521) source

theorem rule15631 (p1982 p2027 p2202 p2373 p2459 p3969 p5558 : Prop) (h : (¬ p2373) ∨ p2027 ∨ (¬ p1982) ∨ p2202 ∨ (¬ p2459) ∨ (¬ p3969) ∨ (¬ p5558)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p2459) ∨ (¬ p3969) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial15631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory4999 t (m.theta 4 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule15631 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 2459) (meaning t m 3969) (meaning t m 5558) source

theorem rule15632 (p1988 p2027 p2688 p2992 p3146 p3156 p3266 : Prop) (h : p2027 ∨ (¬ p1988) ∨ p2688 ∨ (¬ p3146) ∨ (¬ p2992) ∨ (¬ p3266) ∨ (¬ p3156)) : (¬ p1988) ∨ (p2027) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial15632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory5000 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15632 (meaning t m 1988) (meaning t m 2027) (meaning t m 2688) (meaning t m 2992) (meaning t m 3146) (meaning t m 3156) (meaning t m 3266) source

theorem rule15635 (p1978 p3360 p3556 p4990 : Prop) (h : (¬ p3556) ∨ p3360 ∨ (¬ p1978) ∨ p4990) : (¬ p1978) ∨ (p3360) ∨ (¬ p3556) ∨ (p4990) := by
  classical
  tauto

theorem initial15635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 3360) ∨ (¬ (meaning t m 3556)) ∨ (meaning t m 4990) := by
  have source := ElevenTheory.theory5003 t (m.theta 0 5) (m.theta 0 7) (m.theta 5 7)
  exact rule15635 (meaning t m 1978) (meaning t m 3360) (meaning t m 3556) (meaning t m 4990) source

theorem rule15636 (p1975 p2027 p2169 p2295 p3564 p3956 p4037 : Prop) (h : (¬ p1975) ∨ p2169 ∨ p2027 ∨ (¬ p3956) ∨ (¬ p2295) ∨ (¬ p3564) ∨ (¬ p4037)) : (¬ p1975) ∨ (p2027) ∨ (p2169) ∨ (¬ p2295) ∨ (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5004 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule15636 (meaning t m 1975) (meaning t m 2027) (meaning t m 2169) (meaning t m 2295) (meaning t m 3564) (meaning t m 3956) (meaning t m 4037) source

theorem rule15638 (p1990 p2027 p2202 p2307 p2373 p2962 p3097 p4120 : Prop) (h : (¬ p3097) ∨ (¬ p1990) ∨ (¬ p2962) ∨ (¬ p4120) ∨ (¬ p2373) ∨ p2202 ∨ p2027 ∨ (¬ p2307)) : (¬ p1990) ∨ (p2027) ∨ (p2202) ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial15638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory5006 t (m.theta 0 5) (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule15638 (meaning t m 1990) (meaning t m 2027) (meaning t m 2202) (meaning t m 2307) (meaning t m 2373) (meaning t m 2962) (meaning t m 3097) (meaning t m 4120) source

theorem rule15643 (p1979 p2027 p2462 p3868 p4278 p4320 p5660 : Prop) (h : p2462 ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3868) ∨ (¬ p4320) ∨ (¬ p1979) ∨ (¬ p5660)) : (¬ p1979) ∨ (p2027) ∨ (p2462) ∨ (¬ p3868) ∨ (¬ p4278) ∨ (¬ p4320) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial15643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory5011 t (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 10) (m.theta 7 9)
  exact rule15643 (meaning t m 1979) (meaning t m 2027) (meaning t m 2462) (meaning t m 3868) (meaning t m 4278) (meaning t m 4320) (meaning t m 5660) source

theorem rule15644 (p1990 p2027 p2284 p2528 p3497 p3498 p3692 : Prop) (h : (¬ p2284) ∨ (¬ p3692) ∨ p3498 ∨ (¬ p2528) ∨ (¬ p1990) ∨ (¬ p3497) ∨ p2027) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (p3498) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial15644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory5012 t (m.theta 3 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule15644 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2528) (meaning t m 3497) (meaning t m 3498) (meaning t m 3692) source

theorem rule15645 (p2951 p3051 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p3051) ∨ (¬ p2951)) : (¬ p2951) ∨ (¬ p3051) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory5013 (m.theta 0 5) (m.theta 3 5) (m.theta 5 7)
  exact rule15645 (meaning t m 2951) (meaning t m 3051) (meaning t m 4320) source

theorem rule15646 (p1983 p2027 p2622 p2807 p2952 p3136 p3246 p4333 : Prop) (h : (¬ p2952) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p3136) ∨ (¬ p1983) ∨ (¬ p4333) ∨ p2622 ∨ (¬ p2807)) : (¬ p1983) ∨ (p2027) ∨ (p2622) ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3246) ∨ (¬ p4333) := by
  classical
  tauto

theorem initial15646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4333)) := by
  have source := ElevenTheory.theory5014 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule15646 (meaning t m 1983) (meaning t m 2027) (meaning t m 2622) (meaning t m 2807) (meaning t m 2952) (meaning t m 3136) (meaning t m 3246) (meaning t m 4333) source

theorem rule15647 (p2247 p3031 p3399 : Prop) (h : (¬ p2247) ∨ (¬ p3399) ∨ (¬ p3031)) : (¬ p2247) ∨ (¬ p3031) ∨ (¬ p3399) := by
  classical
  tauto

theorem initial15647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3399)) := by
  have source := ElevenTheory.theory5015 (m.theta 0 1) (m.theta 1 3) (m.theta 1 7)
  exact rule15647 (meaning t m 2247) (meaning t m 3031) (meaning t m 3399) source

theorem rule15648 (p1984 p2027 p2177 p2997 p3588 p3659 p3954 : Prop) (h : (¬ p3588) ∨ (¬ p2177) ∨ (¬ p3659) ∨ (¬ p1984) ∨ (¬ p3954) ∨ p2997 ∨ p2027) : (¬ p1984) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5016 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule15648 (meaning t m 1984) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) source

theorem rule15652 (p1990 p2027 p2284 p3051 p3578 p4120 p4320 : Prop) (h : (¬ p4120) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4320) ∨ p3578 ∨ (¬ p1990) ∨ (¬ p2284)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p3051) ∨ (p3578) ∨ (¬ p4120) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3051)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory5020 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule15652 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 3051) (meaning t m 3578) (meaning t m 4120) (meaning t m 4320) source

theorem rule15653 (p1990 p2027 p2156 p2202 p2911 p3556 p3570 p3741 : Prop) (h : (¬ p1990) ∨ p2027 ∨ (¬ p3556) ∨ p2202 ∨ (¬ p2156) ∨ (¬ p3570) ∨ (¬ p2911) ∨ (¬ p3741)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (p2202) ∨ (¬ p2911) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3741) := by
  classical
  tauto

theorem initial15653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3741)) := by
  have source := ElevenTheory.theory5021 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule15653 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2202) (meaning t m 2911) (meaning t m 3556) (meaning t m 3570) (meaning t m 3741) source

theorem rule15657 (p1982 p2027 p2688 p2992 p3115 p3680 p4444 : Prop) (h : p2027 ∨ (¬ p1982) ∨ p2688 ∨ (¬ p2992) ∨ (¬ p3680) ∨ (¬ p4444) ∨ (¬ p3115)) : (¬ p1982) ∨ (p2027) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial15657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5025 t (m.theta 1 3) (m.theta 3 5) (m.theta 5 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15657 (meaning t m 1982) (meaning t m 2027) (meaning t m 2688) (meaning t m 2992) (meaning t m 3115) (meaning t m 3680) (meaning t m 4444) source

theorem rule15658 (p1976 p2027 p2136 p2766 p3941 p4120 p4348 p5568 : Prop) (h : (¬ p3941) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2136) ∨ (¬ p4120) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p5568)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2136) ∨ (p2766) ∨ (¬ p3941) ∨ (¬ p4120) ∨ (¬ p4348) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial15658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory5026 t (m.theta 0 2) (m.theta 0 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule15658 (meaning t m 1976) (meaning t m 2027) (meaning t m 2136) (meaning t m 2766) (meaning t m 3941) (meaning t m 4120) (meaning t m 4348) (meaning t m 5568) source

theorem rule15659 (p1984 p2027 p2499 p3452 p3956 p3982 p5580 : Prop) (h : p3982 ∨ (¬ p5580) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2499) ∨ (¬ p3452)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (p3982) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial15659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3956)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory5027 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 10)
  exact rule15659 (meaning t m 1984) (meaning t m 2027) (meaning t m 2499) (meaning t m 3452) (meaning t m 3956) (meaning t m 3982) (meaning t m 5580) source

theorem rule15661 (p2001 p2027 p2114 p2241 p2992 p3156 p3954 : Prop) (h : (¬ p2241) ∨ p2114 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p2001) ∨ (¬ p3156)) : (¬ p2001) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5029 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 8)
  exact rule15661 (meaning t m 2001) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2992) (meaning t m 3156) (meaning t m 3954) source

theorem rule15668 (p1986 p2027 p2138 p2202 p2427 p2598 p4244 : Prop) (h : (¬ p2598) ∨ p2027 ∨ (¬ p2427) ∨ p2202 ∨ (¬ p2138) ∨ (¬ p4244) ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2138) ∨ (p2202) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial15668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory5036 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule15668 (meaning t m 1986) (meaning t m 2027) (meaning t m 2138) (meaning t m 2202) (meaning t m 2427) (meaning t m 2598) (meaning t m 4244) source

theorem rule15670 (p1992 p2027 p2169 p2608 p3555 p3989 p4173 : Prop) (h : p2169 ∨ (¬ p4173) ∨ (¬ p3555) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p1992) ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p3989) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial15670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory5038 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15670 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2608) (meaning t m 3555) (meaning t m 3989) (meaning t m 4173) source

theorem rule15671 (p1988 p2027 p2098 p2622 p3256 p3266 p3365 p4967 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2098) ∨ (¬ p4967) ∨ p2622 ∨ (¬ p3256) ∨ (¬ p3266)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2098) ∨ (p2622) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial15671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory5039 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 8 9) (m.theta 9 10)
  exact rule15671 (meaning t m 1988) (meaning t m 2027) (meaning t m 2098) (meaning t m 2622) (meaning t m 3256) (meaning t m 3266) (meaning t m 3365) (meaning t m 4967) source

theorem rule15674 (p1984 p2027 p2764 p3555 p3744 p4173 p4191 : Prop) (h : p2764 ∨ (¬ p3555) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p3744) ∨ (¬ p4173)) : (¬ p1984) ∨ (p2027) ∨ (p2764) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5042 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15674 (meaning t m 1984) (meaning t m 2027) (meaning t m 2764) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) (meaning t m 4191) source

theorem rule15675 (p1975 p2027 p2295 p2633 p3246 p3570 p4037 p4396 : Prop) (h : (¬ p4396) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p4037) ∨ (¬ p1975) ∨ (¬ p3570) ∨ p2633) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial15675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory5043 t (m.theta 3 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule15675 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 4037) (meaning t m 4396) source

theorem rule15676 (p1984 p2027 p2462 p2911 p2926 p3452 p3548 p4278 : Prop) (h : (¬ p3548) ∨ (¬ p1984) ∨ (¬ p3452) ∨ p2462 ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2911) ∨ (¬ p2926)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3452) ∨ (¬ p3548) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5044 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15676 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2911) (meaning t m 2926) (meaning t m 3452) (meaning t m 3548) (meaning t m 4278) source

theorem rule15677 (p1984 p2027 p3486 p3555 p3623 p3631 p3690 : Prop) (h : p2027 ∨ (¬ p3690) ∨ (¬ p3555) ∨ (¬ p1984) ∨ (¬ p3486) ∨ p3623 ∨ (¬ p3631)) : (¬ p1984) ∨ (p2027) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (p3623) ∨ (¬ p3631) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial15677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory5045 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule15677 (meaning t m 1984) (meaning t m 2027) (meaning t m 3486) (meaning t m 3555) (meaning t m 3623) (meaning t m 3631) (meaning t m 3690) source

theorem rule15679 (p1994 p2027 p2230 p2440 p2499 p3128 p3519 p4137 : Prop) (h : (¬ p2499) ∨ (¬ p3519) ∨ (¬ p2230) ∨ (¬ p4137) ∨ p2027 ∨ p3128 ∨ (¬ p1994) ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2499) ∨ (p3128) ∨ (¬ p3519) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory5047 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule15679 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2499) (meaning t m 3128) (meaning t m 3519) (meaning t m 4137) source

theorem rule15682 (p1988 p2027 p2132 p2622 p3105 p3365 p3680 : Prop) (h : (¬ p2132) ∨ (¬ p1988) ∨ p2622 ∨ (¬ p3105) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p3365)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2132) ∨ (p2622) ∨ (¬ p3105) ∨ (¬ p3365) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial15682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory5050 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 9) (m.theta 9 10)
  exact rule15682 (meaning t m 1988) (meaning t m 2027) (meaning t m 2132) (meaning t m 2622) (meaning t m 3105) (meaning t m 3365) (meaning t m 3680) source

theorem rule15685 (p2774 p3055 p5220 : Prop) (h : (¬ p5220) ∨ (¬ p3055) ∨ (¬ p2774)) : (¬ p2774) ∨ (¬ p3055) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial15685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory5053 (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule15685 (meaning t m 2774) (meaning t m 3055) (meaning t m 5220) source

theorem rule15687 (p1979 p2027 p2169 p2553 p3097 p3952 p3956 : Prop) (h : (¬ p3952) ∨ p2169 ∨ (¬ p3956) ∨ (¬ p2553) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (p2169) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial15687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory5055 t (m.theta 3 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15687 (meaning t m 1979) (meaning t m 2027) (meaning t m 2169) (meaning t m 2553) (meaning t m 3097) (meaning t m 3952) (meaning t m 3956) source

theorem rule15688 (p1990 p2027 p2114 p2220 p2284 p2737 p2811 p2958 p3497 : Prop) (h : (¬ p3497) ∨ (¬ p2220) ∨ (¬ p2958) ∨ (¬ p2811) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p1990) ∨ p2114 ∨ (¬ p2737)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3497) := by
  classical
  tauto

theorem initial15688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3497)) := by
  have source := ElevenTheory.theory5056 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule15688 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2220) (meaning t m 2284) (meaning t m 2737) (meaning t m 2811) (meaning t m 2958) (meaning t m 3497) source

theorem rule15689 (p1986 p2027 p2138 p2166 p2598 p2873 p3694 : Prop) (h : p2873 ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2598) ∨ (¬ p3694) ∨ (¬ p1986)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2166) ∨ (¬ p2598) ∨ (p2873) ∨ (¬ p3694) := by
  classical
  tauto

theorem initial15689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3694)) := by
  have source := ElevenTheory.theory5057 t (m.theta 0 2) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 5 8)
  exact rule15689 (meaning t m 1986) (meaning t m 2027) (meaning t m 2138) (meaning t m 2166) (meaning t m 2598) (meaning t m 2873) (meaning t m 3694) source

theorem rule15692 (p1995 p2027 p3128 p3379 p3555 p3744 p4173 : Prop) (h : p3128 ∨ (¬ p3555) ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (p3128) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial15692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory5060 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 5 6) (m.theta 6 9)
  exact rule15692 (meaning t m 1995) (meaning t m 2027) (meaning t m 3128) (meaning t m 3379) (meaning t m 3555) (meaning t m 3744) (meaning t m 4173) source

theorem rule15693 (p1984 p2027 p3128 p3583 p3744 p3758 p3954 : Prop) (h : (¬ p3744) ∨ (¬ p1984) ∨ p3128 ∨ p2027 ∨ (¬ p3758) ∨ (¬ p3954) ∨ (¬ p3583)) : (¬ p1984) ∨ (p2027) ∨ (p3128) ∨ (¬ p3583) ∨ (¬ p3744) ∨ (¬ p3758) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5061 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 9)
  exact rule15693 (meaning t m 1984) (meaning t m 2027) (meaning t m 3128) (meaning t m 3583) (meaning t m 3744) (meaning t m 3758) (meaning t m 3954) source

theorem rule15700 (p1987 p2027 p2169 p2589 p2696 p3905 p3989 p4110 : Prop) (h : (¬ p1987) ∨ p2169 ∨ (¬ p2589) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p3905) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3905) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5068 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15700 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2589) (meaning t m 2696) (meaning t m 3905) (meaning t m 3989) (meaning t m 4110) source

theorem rule15701 (p1994 p2027 p2630 p2911 p2914 p3553 p3572 : Prop) (h : (¬ p1994) ∨ (¬ p2630) ∨ p2914 ∨ (¬ p2911) ∨ (¬ p3553) ∨ p2027 ∨ (¬ p3572)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial15701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory5069 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule15701 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2911) (meaning t m 2914) (meaning t m 3553) (meaning t m 3572) source

theorem rule15705 (p2000 p2027 p2462 p2589 p3097 p4107 p4110 : Prop) (h : (¬ p4107) ∨ (¬ p2589) ∨ (¬ p4110) ∨ p2027 ∨ (¬ p2000) ∨ (¬ p3097) ∨ p2462) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2589) ∨ (¬ p3097) ∨ (¬ p4107) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5073 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule15705 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2589) (meaning t m 3097) (meaning t m 4107) (meaning t m 4110) source

theorem rule15709 (p3177 p4378 p4403 : Prop) (h : (¬ p4378) ∨ (¬ p3177) ∨ p4403) : (¬ p3177) ∨ (¬ p4378) ∨ (p4403) := by
  classical
  tauto

theorem initial15709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 4378)) ∨ (meaning t m 4403) := by
  have source := ElevenTheory.theory5077 (m.theta 0 8) (m.theta 3 8) (m.theta 7 8)
  exact rule15709 (meaning t m 3177) (meaning t m 4378) (meaning t m 4403) source

theorem rule15711 (p2000 p2027 p2589 p2911 p2914 p3570 p4235 : Prop) (h : (¬ p3570) ∨ (¬ p2000) ∨ (¬ p2589) ∨ (¬ p4235) ∨ p2027 ∨ p2914 ∨ (¬ p2911)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2911) ∨ (p2914) ∨ (¬ p3570) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15711 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory5079 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule15711 (meaning t m 2000) (meaning t m 2027) (meaning t m 2589) (meaning t m 2911) (meaning t m 2914) (meaning t m 3570) (meaning t m 4235) source

theorem rule15714 (p2005 p2027 p2114 p2598 p2737 p3365 p3422 : Prop) (h : (¬ p3422) ∨ p2027 ∨ p2114 ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2598) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial15714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory5082 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 6)
  exact rule15714 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2598) (meaning t m 2737) (meaning t m 3365) (meaning t m 3422) source

theorem rule15716 (p1980 p2169 p3989 p4564 : Prop) (h : (¬ p1980) ∨ (¬ p3989) ∨ p2169 ∨ p4564) : (¬ p1980) ∨ (p2169) ∨ (¬ p3989) ∨ (p4564) := by
  classical
  tauto

theorem initial15716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3989)) ∨ (meaning t m 4564) := by
  have source := ElevenTheory.theory5084 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15716 (meaning t m 1980) (meaning t m 2169) (meaning t m 3989) (meaning t m 4564) source

theorem rule15717 (p1980 p2027 p3146 p3309 p3568 p3578 p4261 p4371 : Prop) (h : (¬ p1980) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p4371) ∨ (¬ p3146) ∨ p3578 ∨ (¬ p4261)) : (¬ p1980) ∨ (p2027) ∨ (¬ p3146) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (p3578) ∨ (¬ p4261) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial15717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3568)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory5085 t (m.theta 1 6) (m.theta 1 8) (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 8 9)
  exact rule15717 (meaning t m 1980) (meaning t m 2027) (meaning t m 3146) (meaning t m 3309) (meaning t m 3568) (meaning t m 3578) (meaning t m 4261) (meaning t m 4371) source

theorem rule15718 (p2015 p2027 p2169 p2589 p3093 p3989 p4108 p4110 : Prop) (h : (¬ p2589) ∨ (¬ p4108) ∨ p2169 ∨ (¬ p4110) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p2015) ∨ (¬ p3093)) : (¬ p2015) ∨ (p2027) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3989) ∨ (¬ p4108) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5086 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15718 (meaning t m 2015) (meaning t m 2027) (meaning t m 2169) (meaning t m 2589) (meaning t m 3093) (meaning t m 3989) (meaning t m 4108) (meaning t m 4110) source

theorem rule15719 (p2000 p2027 p2462 p2579 p3016 p3742 p4278 : Prop) (h : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p4278) ∨ p2462 ∨ (¬ p3742)) : (¬ p2000) ∨ (p2027) ∨ (p2462) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5087 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule15719 (meaning t m 2000) (meaning t m 2027) (meaning t m 2462) (meaning t m 2579) (meaning t m 3016) (meaning t m 3742) (meaning t m 4278) source

theorem rule15720 (p1982 p2027 p2088 p2110 p2169 p3324 p3365 p4195 : Prop) (h : (¬ p3324) ∨ p2169 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2088) ∨ (¬ p4195) ∨ (¬ p3365) ∨ (¬ p2110)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2110) ∨ (p2169) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial15720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2110)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory5088 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule15720 (meaning t m 1982) (meaning t m 2027) (meaning t m 2088) (meaning t m 2110) (meaning t m 2169) (meaning t m 3324) (meaning t m 3365) (meaning t m 4195) source

theorem rule15741 (p2000 p2027 p2406 p2509 p2589 p2881 p2938 p4383 : Prop) (h : (¬ p2000) ∨ p2938 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4383) ∨ (¬ p2589) ∨ (¬ p2509) ∨ (¬ p2406)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2589) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial15741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory5093 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule15741 (meaning t m 2000) (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 2589) (meaning t m 2881) (meaning t m 2938) (meaning t m 4383) source

theorem rule15746 (p1983 p2027 p2114 p2341 p2449 p2737 p2811 p3553 p4104 : Prop) (h : (¬ p4104) ∨ (¬ p2737) ∨ p2027 ∨ p2114 ∨ (¬ p2449) ∨ (¬ p2811) ∨ (¬ p3553) ∨ (¬ p1983) ∨ (¬ p2341)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2341) ∨ (¬ p2449) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3553) ∨ (¬ p4104) := by
  classical
  tauto

theorem initial15746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4104)) := by
  have source := ElevenTheory.theory5098 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15746 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2341) (meaning t m 2449) (meaning t m 2737) (meaning t m 2811) (meaning t m 3553) (meaning t m 4104) source

theorem rule15747 (p1976 p2027 p2589 p2850 p3096 p3128 p3584 p3744 p3905 : Prop) (h : p3128 ∨ (¬ p3096) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p3905) ∨ (¬ p3584) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (p3128) ∨ (¬ p3584) ∨ (¬ p3744) ∨ (¬ p3905) := by
  classical
  tauto

theorem initial15747 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3096)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3905)) := by
  have source := ElevenTheory.theory5099 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule15747 (meaning t m 1976) (meaning t m 2027) (meaning t m 2589) (meaning t m 2850) (meaning t m 3096) (meaning t m 3128) (meaning t m 3584) (meaning t m 3744) (meaning t m 3905) source

theorem rule15758 (p2000 p2622 p2630 p2659 : Prop) (h : p2622 ∨ (¬ p2000) ∨ p2659 ∨ (¬ p2630)) : (¬ p2000) ∨ (p2622) ∨ (¬ p2630) ∨ (p2659) := by
  classical
  tauto

theorem initial15758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2659) := by
  have source := ElevenTheory.theory5110 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4)
  exact rule15758 (meaning t m 2000) (meaning t m 2622) (meaning t m 2630) (meaning t m 2659) source

theorem rule15764 (p2014 p2027 p2241 p2284 p2699 p2992 p3737 : Prop) (h : p2027 ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p2992) ∨ p2699 ∨ (¬ p2014) ∨ (¬ p3737)) : (¬ p2014) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p3737) := by
  classical
  tauto

theorem initial15764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2014)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3737)) := by
  have source := ElevenTheory.theory5116 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10)
  exact rule15764 (meaning t m 2014) (meaning t m 2027) (meaning t m 2241) (meaning t m 2284) (meaning t m 2699) (meaning t m 2992) (meaning t m 3737) source

theorem rule15766 (p5715 p5716 p5717 p5718 p5719 : Prop) : (p5717) ∨ (((¬ p5716) ∨ (¬ p5717) ∨ (¬ p5715) ∨ (¬ p5718) ∨ (¬ p5719))) := by
  classical
  tauto

theorem initial15766 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5717) ∨ (meaning t m 6187) := by
  exact rule15766 (meaning t m 5715) (meaning t m 5716) (meaning t m 5717) (meaning t m 5718) (meaning t m 5719)

theorem rule15773 (p4228 p5721 p5722 p5723 p5724 : Prop) : (p4228) ∨ (((¬ p5721) ∨ (¬ p5722) ∨ (¬ p4228) ∨ (¬ p5723) ∨ (¬ p5724))) := by
  classical
  tauto

theorem initial15773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4228) ∨ (meaning t m 6188) := by
  exact rule15773 (meaning t m 4228) (meaning t m 5721) (meaning t m 5722) (meaning t m 5723) (meaning t m 5724)

theorem rule15779 (p6187 p6188 : Prop) : (¬ ((¬ p6187) ∨ (¬ p6188))) ∨ (¬ p6187) ∨ (¬ p6188) := by
  classical
  tauto

theorem initial15779 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6186)) ∨ (¬ (meaning t m 6187)) ∨ (¬ (meaning t m 6188)) := by
  exact rule15779 (meaning t m 6187) (meaning t m 6188)

theorem rule15780 (p5713 p6186 : Prop) (h : (p5713 ↔ p6186)) : (¬ p5713) ∨ (p6186) := by
  classical
  tauto

theorem initial15780 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5713)) ∨ (meaning t m 6186) := by
  have source := ElevenTheory.theory5117 t (m.theta 3 10) (m.theta 3 6) (m.theta 6 10)
  exact rule15780 (meaning t m 5713) (meaning t m 6186) source

theorem rule15791 (p1995 p2027 p2169 p2542 p3096 p3238 p3574 p3989 : Prop) (h : (¬ p3096) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p1995) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2542) ∨ (¬ p3238)) : (¬ p1995) ∨ (p2027) ∨ (p2169) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3574) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial15791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory5127 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15791 (meaning t m 1995) (meaning t m 2027) (meaning t m 2169) (meaning t m 2542) (meaning t m 3096) (meaning t m 3238) (meaning t m 3574) (meaning t m 3989) source

theorem rule15793 (p1977 p2027 p2307 p3128 p3568 p3946 p4154 : Prop) (h : (¬ p3568) ∨ p3128 ∨ (¬ p3946) ∨ p2027 ∨ (¬ p4154) ∨ (¬ p1977) ∨ (¬ p2307)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2307) ∨ (p3128) ∨ (¬ p3568) ∨ (¬ p3946) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5129 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15793 (meaning t m 1977) (meaning t m 2027) (meaning t m 2307) (meaning t m 3128) (meaning t m 3568) (meaning t m 3946) (meaning t m 4154) source

theorem rule15795 (p1986 p2027 p2169 p3367 p3583 p3698 p3989 p4110 : Prop) (h : (¬ p3367) ∨ p2169 ∨ (¬ p3989) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p4110) ∨ (¬ p3698)) : (¬ p1986) ∨ (p2027) ∨ (p2169) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15795 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5131 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15795 (meaning t m 1986) (meaning t m 2027) (meaning t m 2169) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 3989) (meaning t m 4110) source

theorem rule15796 (p1994 p2027 p2169 p2651 p2952 p3952 p3989 : Prop) (h : p2027 ∨ (¬ p1994) ∨ (¬ p3952) ∨ p2169 ∨ (¬ p2651) ∨ (¬ p3989) ∨ (¬ p2952)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial15796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory5132 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15796 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2651) (meaning t m 2952) (meaning t m 3952) (meaning t m 3989) source

theorem rule15805 (p1986 p2027 p2462 p3016 p3584 p3742 p4278 : Prop) (h : (¬ p3584) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3742) ∨ (¬ p3016) ∨ p2462 ∨ (¬ p4278)) : (¬ p1986) ∨ (p2027) ∨ (p2462) ∨ (¬ p3016) ∨ (¬ p3584) ∨ (¬ p3742) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5141 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 9)
  exact rule15805 (meaning t m 1986) (meaning t m 2027) (meaning t m 2462) (meaning t m 3016) (meaning t m 3584) (meaning t m 3742) (meaning t m 4278) source

theorem rule15815 (p2000 p2027 p2299 p2589 p2633 p3097 p4110 : Prop) (h : (¬ p3097) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2000) ∨ p2633 ∨ (¬ p4110) ∨ (¬ p2299)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2589) ∨ (p2633) ∨ (¬ p3097) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5151 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15815 (meaning t m 2000) (meaning t m 2027) (meaning t m 2299) (meaning t m 2589) (meaning t m 2633) (meaning t m 3097) (meaning t m 4110) source

theorem rule15816 (p1987 p2027 p2542 p2589 p2655 p2881 p2938 p3361 p4256 p4383 : Prop) (h : p2938 ∨ (¬ p2655) ∨ (¬ p1987) ∨ (¬ p4383) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3361) ∨ (¬ p2589) ∨ (¬ p2542) ∨ (¬ p4256)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3361) ∨ (¬ p4256) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial15816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory5152 t (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule15816 (meaning t m 1987) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 2655) (meaning t m 2881) (meaning t m 2938) (meaning t m 3361) (meaning t m 4256) (meaning t m 4383) source

theorem rule15817 (p2000 p2027 p2542 p2589 p3742 p3921 p3944 p4260 : Prop) (h : (¬ p2000) ∨ (¬ p2589) ∨ p2027 ∨ p3944 ∨ (¬ p4260) ∨ (¬ p3921) ∨ (¬ p2542) ∨ (¬ p3742)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (p3944) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial15817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3921)) ∨ (meaning t m 3944) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory5153 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 6 7) (m.theta 7 10)
  exact rule15817 (meaning t m 2000) (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 3742) (meaning t m 3921) (meaning t m 3944) (meaning t m 4260) source

theorem rule15818 (p2004 p2027 p2177 p2764 p3548 p4107 p4381 : Prop) (h : p2027 ∨ (¬ p2004) ∨ (¬ p3548) ∨ (¬ p4107) ∨ (¬ p2177) ∨ (¬ p4381) ∨ p2764) : (¬ p2004) ∨ (p2027) ∨ (¬ p2177) ∨ (p2764) ∨ (¬ p3548) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory5154 t (m.theta 1 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule15818 (meaning t m 2004) (meaning t m 2027) (meaning t m 2177) (meaning t m 2764) (meaning t m 3548) (meaning t m 4107) (meaning t m 4381) source

theorem rule15821 (p1992 p2027 p2169 p2307 p2387 p3688 p3822 : Prop) (h : (¬ p2307) ∨ p2169 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2387) ∨ (¬ p3822) ∨ (¬ p3688)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3688) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial15821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory5157 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15821 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2307) (meaning t m 2387) (meaning t m 3688) (meaning t m 3822) source

theorem rule15823 (p2010 p2027 p2169 p2589 p3389 p3989 p4110 : Prop) (h : (¬ p2589) ∨ p2169 ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2010) ∨ (¬ p3989) ∨ (¬ p3389)) : (¬ p2010) ∨ (p2027) ∨ (p2169) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial15823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5159 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8)
  exact rule15823 (meaning t m 2010) (meaning t m 2027) (meaning t m 2169) (meaning t m 2589) (meaning t m 3389) (meaning t m 3989) (meaning t m 4110) source

theorem rule15827 (p1979 p2027 p2622 p2992 p3166 p3365 p4117 p4360 : Prop) (h : (¬ p4117) ∨ (¬ p3365) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p4360) ∨ (¬ p2992) ∨ (¬ p1979) ∨ p2622) : (¬ p1979) ∨ (p2027) ∨ (p2622) ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p3365) ∨ (¬ p4117) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial15827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory5163 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8)
  exact rule15827 (meaning t m 1979) (meaning t m 2027) (meaning t m 2622) (meaning t m 2992) (meaning t m 3166) (meaning t m 3365) (meaning t m 4117) (meaning t m 4360) source

theorem rule15828 (p1983 p2027 p2997 p3096 p3097 p3461 p3564 p4381 : Prop) (h : (¬ p3461) ∨ (¬ p1983) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p4381) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3096)) : (¬ p1983) ∨ (p2027) ∨ (p2997) ∨ (¬ p3096) ∨ (¬ p3097) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial15828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory5164 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule15828 (meaning t m 1983) (meaning t m 2027) (meaning t m 2997) (meaning t m 3096) (meaning t m 3097) (meaning t m 3461) (meaning t m 3564) (meaning t m 4381) source

theorem rule15831 (p1986 p2027 p2299 p2633 p2780 p3366 p3367 p3822 : Prop) (h : (¬ p3822) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3367) ∨ (¬ p2780) ∨ p2633 ∨ (¬ p1986) ∨ (¬ p2299)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2780) ∨ (¬ p3366) ∨ (¬ p3367) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial15831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory5167 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule15831 (meaning t m 1986) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2780) (meaning t m 3366) (meaning t m 3367) (meaning t m 3822) source

theorem rule15832 (p1994 p2027 p2169 p2363 p2630 p2748 p4118 p4360 : Prop) (h : (¬ p2363) ∨ p2169 ∨ (¬ p2630) ∨ (¬ p1994) ∨ (¬ p4360) ∨ (¬ p2748) ∨ p2027 ∨ (¬ p4118)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2630) ∨ (¬ p2748) ∨ (¬ p4118) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial15832 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory5168 t (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule15832 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2630) (meaning t m 2748) (meaning t m 4118) (meaning t m 4360) source

theorem rule15833 (p1980 p2027 p2299 p2313 p2633 p3654 p4037 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2299) ∨ (¬ p4037) ∨ (¬ p3654) ∨ (¬ p1980)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (p2633) ∨ (¬ p3654) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5169 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule15833 (meaning t m 1980) (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2633) (meaning t m 3654) (meaning t m 4037) source

theorem rule15841 (p1975 p2027 p2166 p2295 p2533 p2873 p3680 p5274 p5284 : Prop) (h : p2873 ∨ (¬ p2166) ∨ (¬ p5274) ∨ (¬ p3680) ∨ (¬ p2533) ∨ p2027 ∨ (¬ p2295) ∨ (¬ p1975) ∨ (¬ p5284)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2295) ∨ (¬ p2533) ∨ (p2873) ∨ (¬ p3680) ∨ (¬ p5274) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial15841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2533)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 5274)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory5177 t (m.theta 1 5) (m.theta 3 6) (m.theta 3 9) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 9 10)
  exact rule15841 (meaning t m 1975) (meaning t m 2027) (meaning t m 2166) (meaning t m 2295) (meaning t m 2533) (meaning t m 2873) (meaning t m 3680) (meaning t m 5274) (meaning t m 5284) source

theorem rule15842 (p1979 p2027 p2114 p2210 p2891 p3954 p4320 : Prop) (h : (¬ p4320) ∨ p2114 ∨ p2027 ∨ (¬ p2891) ∨ (¬ p1979) ∨ (¬ p2210) ∨ (¬ p3954)) : (¬ p1979) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3954) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial15842 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory5178 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule15842 (meaning t m 1979) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2891) (meaning t m 3954) (meaning t m 4320) source

theorem rule15845 (p1987 p2027 p2313 p2577 p2662 p2810 p3128 p3309 p4026 : Prop) (h : p3128 ∨ (¬ p4026) ∨ (¬ p3309) ∨ (¬ p2577) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p2810) ∨ (¬ p2662) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p3128) ∨ (¬ p3309) ∨ (¬ p4026) := by
  classical
  tauto

theorem initial15845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4026)) := by
  have source := ElevenTheory.theory5181 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 6 7) (m.theta 6 9)
  exact rule15845 (meaning t m 1987) (meaning t m 2027) (meaning t m 2313) (meaning t m 2577) (meaning t m 2662) (meaning t m 2810) (meaning t m 3128) (meaning t m 3309) (meaning t m 4026) source

theorem rule15846 (p1982 p2027 p2622 p2743 p3537 p3670 p4444 p5344 : Prop) (h : (¬ p4444) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p3537) ∨ p2622 ∨ (¬ p5344) ∨ (¬ p3670) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2622) ∨ (¬ p2743) ∨ (¬ p3537) ∨ (¬ p3670) ∨ (¬ p4444) ∨ (¬ p5344) := by
  classical
  tauto

theorem initial15846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 5344)) := by
  have source := ElevenTheory.theory5182 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 2 9) (m.theta 8 9) (m.theta 9 10)
  exact rule15846 (meaning t m 1982) (meaning t m 2027) (meaning t m 2622) (meaning t m 2743) (meaning t m 3537) (meaning t m 3670) (meaning t m 4444) (meaning t m 5344) source

theorem rule15849 (p1975 p2027 p2307 p2387 p2611 p2774 p2819 : Prop) (h : p2611 ∨ (¬ p2387) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2819) ∨ (¬ p1975) ∨ (¬ p2774)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p2819) := by
  classical
  tauto

theorem initial15849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) := by
  have source := ElevenTheory.theory5185 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15849 (meaning t m 1975) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2611) (meaning t m 2774) (meaning t m 2819) source

theorem rule15850 (p1997 p2027 p2114 p2598 p2780 p2829 p2850 : Prop) (h : p2027 ∨ (¬ p1997) ∨ (¬ p2850) ∨ p2114 ∨ (¬ p2598) ∨ (¬ p2829) ∨ (¬ p2780)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p2850) := by
  classical
  tauto

theorem initial15850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2850)) := by
  have source := ElevenTheory.theory5186 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 5)
  exact rule15850 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2598) (meaning t m 2780) (meaning t m 2829) (meaning t m 2850) source

theorem rule15852 (p1990 p2027 p2295 p2331 p2388 p2952 p3097 : Prop) (h : (¬ p2952) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p1990) ∨ (¬ p3097) ∨ p2027 ∨ p2388) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial15852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory5188 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule15852 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 2331) (meaning t m 2388) (meaning t m 2952) (meaning t m 3097) source

theorem rule15854 (p1985 p2027 p2901 p2964 p3276 p4208 p4322 : Prop) (h : (¬ p4208) ∨ (¬ p1985) ∨ (¬ p4322) ∨ p2027 ∨ p2964 ∨ (¬ p3276) ∨ (¬ p2901)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2901) ∨ (p2964) ∨ (¬ p3276) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial15854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2901)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory5190 t (m.theta 3 5) (m.theta 4 9) (m.theta 5 7) (m.theta 5 9) (m.theta 9 10)
  exact rule15854 (meaning t m 1985) (meaning t m 2027) (meaning t m 2901) (meaning t m 2964) (meaning t m 3276) (meaning t m 4208) (meaning t m 4322) source

theorem rule15855 (p1994 p2027 p2169 p3568 p3868 p3920 p3956 p4194 p4260 : Prop) (h : p2169 ∨ (¬ p3920) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4260) ∨ (¬ p3868) ∨ (¬ p3568) ∨ (¬ p1994) ∨ (¬ p4194)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p3568) ∨ (¬ p3868) ∨ (¬ p3920) ∨ (¬ p3956) ∨ (¬ p4194) ∨ (¬ p4260) := by
  classical
  tauto

theorem initial15855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 3920)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4260)) := by
  have source := ElevenTheory.theory5191 t (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule15855 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 3568) (meaning t m 3868) (meaning t m 3920) (meaning t m 3956) (meaning t m 4194) (meaning t m 4260) source

theorem rule15856 (p2504 p3922 p3984 : Prop) (h : (¬ p3984) ∨ (¬ p3922) ∨ p2504) : (p2504) ∨ (¬ p3922) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial15856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2504) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory5192 (m.theta 1 6) (m.theta 3 6) (m.theta 4 6)
  exact rule15856 (meaning t m 2504) (meaning t m 3922) (meaning t m 3984) source

theorem rule15860 (p1991 p2027 p2588 p2963 p2997 p3888 p5717 : Prop) (h : p2997 ∨ (¬ p2963) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p3888) ∨ (¬ p1991) ∨ (¬ p5717)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3888) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial15860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory5196 t (m.theta 0 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 10) (m.theta 6 7)
  exact rule15860 (meaning t m 1991) (meaning t m 2027) (meaning t m 2588) (meaning t m 2963) (meaning t m 2997) (meaning t m 3888) (meaning t m 5717) source

theorem rule15866 (p1984 p2027 p2169 p2247 p3662 p3952 p3989 : Prop) (h : (¬ p3662) ∨ p2169 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial15866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory5202 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule15866 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2247) (meaning t m 3662) (meaning t m 3952) (meaning t m 3989) source

theorem rule15869 (p1988 p2027 p2388 p2449 p2761 p3027 p3662 : Prop) (h : (¬ p3662) ∨ (¬ p3027) ∨ p2388 ∨ (¬ p2761) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p2449)) : (¬ p1988) ∨ (p2027) ∨ (p2388) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p3027) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial15869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory5205 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15869 (meaning t m 1988) (meaning t m 2027) (meaning t m 2388) (meaning t m 2449) (meaning t m 2761) (meaning t m 3027) (meaning t m 3662) source

theorem rule15871 (p1987 p2027 p2264 p2355 p2696 p3425 p3659 : Prop) (h : (¬ p1987) ∨ p2355 ∨ (¬ p2264) ∨ (¬ p3659) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2264) ∨ (p2355) ∨ (¬ p2696) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial15871 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory5207 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule15871 (meaning t m 1987) (meaning t m 2027) (meaning t m 2264) (meaning t m 2355) (meaning t m 2696) (meaning t m 3425) (meaning t m 3659) source

theorem rule15873 (p1991 p2027 p2641 p2938 p2963 p3662 p3879 p4235 : Prop) (h : (¬ p4235) ∨ (¬ p1991) ∨ p2938 ∨ (¬ p3662) ∨ (¬ p2963) ∨ (¬ p2641) ∨ (¬ p3879) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (¬ p2641) ∨ (p2938) ∨ (¬ p2963) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial15873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory5209 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 7)
  exact rule15873 (meaning t m 1991) (meaning t m 2027) (meaning t m 2641) (meaning t m 2938) (meaning t m 2963) (meaning t m 3662) (meaning t m 3879) (meaning t m 4235) source

theorem rule15880 (p1984 p2027 p2247 p3128 p3662 p3744 p3952 : Prop) (h : (¬ p1984) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3662) ∨ p3128) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p3128) ∨ (¬ p3662) ∨ (¬ p3744) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial15880 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory5216 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9)
  exact rule15880 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 3128) (meaning t m 3662) (meaning t m 3744) (meaning t m 3952) source

theorem rule15882 (p1984 p2027 p2287 p2499 p3323 p3452 p4137 : Prop) (h : (¬ p1984) ∨ (¬ p3452) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p3323) ∨ p2287 ∨ (¬ p4137)) : (¬ p1984) ∨ (p2027) ∨ (p2287) ∨ (¬ p2499) ∨ (¬ p3323) ∨ (¬ p3452) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15882 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory5218 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule15882 (meaning t m 1984) (meaning t m 2027) (meaning t m 2287) (meaning t m 2499) (meaning t m 3323) (meaning t m 3452) (meaning t m 4137) source

theorem rule15884 (p1984 p2027 p2247 p2355 p2449 p4037 p4154 p4396 : Prop) (h : (¬ p4154) ∨ (¬ p4396) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4037) ∨ (¬ p1984) ∨ p2355 ∨ (¬ p2449)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2355) ∨ (¬ p2449) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial15884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory5220 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 9) (m.theta 7 9)
  exact rule15884 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2355) (meaning t m 2449) (meaning t m 4037) (meaning t m 4154) (meaning t m 4396) source

theorem rule15885 (p1984 p2027 p2247 p2764 p4037 p4154 p4191 : Prop) (h : p2027 ∨ (¬ p2247) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p1984) ∨ (¬ p4154) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2764) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial15885 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5221 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule15885 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2764) (meaning t m 4037) (meaning t m 4154) (meaning t m 4191) source

theorem rule15887 (p1984 p2027 p2247 p2765 p3125 p4037 p4154 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3125) ∨ (¬ p4037) ∨ p2765 ∨ (¬ p2247) ∨ (¬ p4154)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2765) ∨ (¬ p3125) ∨ (¬ p4037) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial15887 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5223 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule15887 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2765) (meaning t m 3125) (meaning t m 4037) (meaning t m 4154) source

theorem rule15893 (p1990 p2027 p2156 p2427 p2542 p2545 p3556 : Prop) (h : p2545 ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2156) ∨ (¬ p2542) ∨ (¬ p1990) ∨ (¬ p3556)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial15893 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory5229 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule15893 (meaning t m 1990) (meaning t m 2027) (meaning t m 2156) (meaning t m 2427) (meaning t m 2542) (meaning t m 2545) (meaning t m 3556) source

theorem rule15894 (p1984 p2027 p2247 p2766 p3324 p4154 p4347 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p1984) ∨ (¬ p2247) ∨ (¬ p4154)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2766) ∨ (¬ p3324) ∨ (¬ p4154) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial15894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory5230 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule15894 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2766) (meaning t m 3324) (meaning t m 4154) (meaning t m 4347) source

theorem rule15899 (p1984 p2027 p2462 p2743 p3572 p3947 p3954 : Prop) (h : p2462 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3954) ∨ (¬ p2743) ∨ (¬ p3947) ∨ (¬ p3572)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2743) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15899 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5235 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9)
  exact rule15899 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2743) (meaning t m 3572) (meaning t m 3947) (meaning t m 3954) source

theorem rule15903 (p1992 p2027 p2499 p2608 p3128 p3452 p4137 : Prop) (h : (¬ p1992) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p4137) ∨ p3128 ∨ (¬ p2608)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2608) ∨ (p3128) ∨ (¬ p3452) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial15903 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory5239 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 6) (m.theta 6 9)
  exact rule15903 (meaning t m 1992) (meaning t m 2027) (meaning t m 2499) (meaning t m 2608) (meaning t m 3128) (meaning t m 3452) (meaning t m 4137) source

theorem rule15906 (p1997 p2027 p2323 p2331 p2542 p2630 p4195 : Prop) (h : p2323 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p4195) ∨ (¬ p1997) ∨ (¬ p2630)) : (¬ p1997) ∨ (p2027) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial15906 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory5242 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5)
  exact rule15906 (meaning t m 1997) (meaning t m 2027) (meaning t m 2323) (meaning t m 2331) (meaning t m 2542) (meaning t m 2630) (meaning t m 4195) source

theorem rule15907 (p1998 p2027 p2323 p2449 p2651 p2685 p2810 p3657 : Prop) (h : (¬ p2449) ∨ p2323 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3657) ∨ (¬ p2810) ∨ (¬ p2685) ∨ (¬ p2651)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2449) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3657) := by
  classical
  tauto

theorem initial15907 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3657)) := by
  have source := ElevenTheory.theory5243 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15907 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2449) (meaning t m 2651) (meaning t m 2685) (meaning t m 2810) (meaning t m 3657) source

theorem rule15909 (p3819 p3905 p5201 : Prop) (h : (¬ p3819) ∨ (¬ p3905) ∨ p5201) : (¬ p3819) ∨ (¬ p3905) ∨ (p5201) := by
  classical
  tauto

theorem initial15909 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3819)) ∨ (¬ (meaning t m 3905)) ∨ (meaning t m 5201) := by
  have source := ElevenTheory.theory5245 (m.theta 0 2) (m.theta 0 4) (m.theta 0 7)
  exact rule15909 (meaning t m 3819) (meaning t m 3905) (meaning t m 5201) source

theorem rule15913 (p1989 p2027 p2210 p2499 p2588 p2997 p3452 : Prop) (h : (¬ p2499) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p1989) ∨ (¬ p2210)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial15913 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory5249 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 6) (m.theta 6 7)
  exact rule15913 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2499) (meaning t m 2588) (meaning t m 2997) (meaning t m 3452) source

theorem rule15914 (p1981 p3527 p3623 p4133 : Prop) (h : p4133 ∨ p3623 ∨ (¬ p3527) ∨ (¬ p1981)) : (¬ p1981) ∨ (¬ p3527) ∨ (p3623) ∨ (p4133) := by
  classical
  tauto

theorem initial15914 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (¬ (meaning t m 3527)) ∨ (meaning t m 3623) ∨ (meaning t m 4133) := by
  have source := ElevenTheory.theory5250 t (m.theta 1 7) (m.theta 6 8) (m.theta 7 8)
  exact rule15914 (meaning t m 1981) (meaning t m 3527) (meaning t m 3623) (meaning t m 4133) source

theorem rule15916 (p1988 p2027 p2114 p2449 p2685 p2737 p2761 : Prop) (h : p2114 ∨ (¬ p2737) ∨ (¬ p2685) ∨ (¬ p1988) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p2761) := by
  classical
  tauto

theorem initial15916 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2761)) := by
  have source := ElevenTheory.theory5252 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15916 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2449) (meaning t m 2685) (meaning t m 2737) (meaning t m 2761) source

theorem rule15917 (p1987 p2027 p2406 p2499 p2589 p2662 p2810 p3008 : Prop) (h : p3008 ∨ (¬ p2499) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2810) ∨ (¬ p2662) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (p3008) := by
  classical
  tauto

theorem initial15917 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2810)) ∨ (meaning t m 3008) := by
  have source := ElevenTheory.theory5253 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule15917 (meaning t m 1987) (meaning t m 2027) (meaning t m 2406) (meaning t m 2499) (meaning t m 2589) (meaning t m 2662) (meaning t m 2810) (meaning t m 3008) source

theorem rule15918 (p1982 p2027 p2114 p2264 p2459 p2737 p2807 p2811 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p2737) ∨ (¬ p1982) ∨ (¬ p2811) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2807)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) := by
  classical
  tauto

theorem initial15918 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) := by
  have source := ElevenTheory.theory5254 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9)
  exact rule15918 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2264) (meaning t m 2459) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) source

theorem rule15919 (p1988 p2027 p2114 p2761 p3399 p3631 p3954 : Prop) (h : (¬ p3399) ∨ (¬ p3954) ∨ p2027 ∨ p2114 ∨ (¬ p3631) ∨ (¬ p1988) ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15919 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5255 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule15919 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2761) (meaning t m 3399) (meaning t m 3631) (meaning t m 3954) source

theorem rule15920 (p1983 p2699 p3399 p3631 p3950 p4443 : Prop) (h : p2699 ∨ (¬ p3399) ∨ (¬ p1983) ∨ (¬ p3631) ∨ p3950 ∨ (¬ p4443)) : (¬ p1983) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (p3950) ∨ (¬ p4443) := by
  classical
  tauto

theorem initial15920 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (meaning t m 3950) ∨ (¬ (meaning t m 4443)) := by
  have source := ElevenTheory.theory5256 t (m.theta 0 1) (m.theta 1 7) (m.theta 7 9) (m.theta 8 9)
  exact rule15920 (meaning t m 1983) (meaning t m 2699) (meaning t m 3399) (meaning t m 3631) (meaning t m 3950) (meaning t m 4443) source

theorem rule15922 (p2000 p2027 p2542 p2553 p2589 p3008 p3568 p4194 : Prop) (h : (¬ p2589) ∨ (¬ p2000) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3568) ∨ p3008 ∨ (¬ p4194) ∨ (¬ p2542)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2589) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p4194) := by
  classical
  tauto

theorem initial15922 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4194)) := by
  have source := ElevenTheory.theory5258 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule15922 (meaning t m 2000) (meaning t m 2027) (meaning t m 2542) (meaning t m 2553) (meaning t m 2589) (meaning t m 3008) (meaning t m 3568) (meaning t m 4194) source

theorem rule15927 (p1983 p2027 p2427 p2598 p2611 p2850 p3246 : Prop) (h : (¬ p1983) ∨ p2611 ∨ (¬ p3246) ∨ p2027 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2427)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial15927 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory5263 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule15927 (meaning t m 1983) (meaning t m 2027) (meaning t m 2427) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 3246) source

theorem rule15930 (p1980 p2027 p2114 p3093 p3319 p3954 p4037 : Prop) (h : (¬ p3319) ∨ p2114 ∨ (¬ p1980) ∨ (¬ p4037) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3093)) : (¬ p1980) ∨ (p2027) ∨ (p2114) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3954) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15930 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5266 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 3 6) (m.theta 6 9)
  exact rule15930 (meaning t m 1980) (meaning t m 2027) (meaning t m 2114) (meaning t m 3093) (meaning t m 3319) (meaning t m 3954) (meaning t m 4037) source

theorem rule15931 (p1996 p2027 p2114 p3399 p3631 p3947 p3954 : Prop) (h : p2027 ∨ (¬ p3399) ∨ (¬ p1996) ∨ p2114 ∨ (¬ p3954) ∨ (¬ p3631) ∨ (¬ p3947)) : (¬ p1996) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3947) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15931 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5267 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 3 7) (m.theta 7 9)
  exact rule15931 (meaning t m 1996) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3631) (meaning t m 3947) (meaning t m 3954) source

theorem rule15932 (p2010 p2027 p2114 p2449 p2685 p2737 p4278 : Prop) (h : p2027 ∨ (¬ p4278) ∨ (¬ p2010) ∨ p2114 ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p2449)) : (¬ p2010) ∨ (p2027) ∨ (p2114) ∨ (¬ p2449) ∨ (¬ p2685) ∨ (¬ p2737) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial15932 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5268 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 4 7) (m.theta 7 9)
  exact rule15932 (meaning t m 2010) (meaning t m 2027) (meaning t m 2114) (meaning t m 2449) (meaning t m 2685) (meaning t m 2737) (meaning t m 4278) source

theorem rule15933 (p1983 p2027 p2114 p2210 p2891 p3246 p3954 : Prop) (h : (¬ p2210) ∨ p2114 ∨ (¬ p3954) ∨ (¬ p3246) ∨ (¬ p2891) ∨ (¬ p1983) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15933 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5269 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 7) (m.theta 7 9)
  exact rule15933 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2891) (meaning t m 3246) (meaning t m 3954) source

theorem rule15934 (p1998 p2027 p2611 p2696 p2881 p2901 p3136 : Prop) (h : (¬ p1998) ∨ (¬ p2696) ∨ (¬ p2901) ∨ p2611 ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3136)) : (¬ p1998) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2881) ∨ (¬ p2901) ∨ (¬ p3136) := by
  classical
  tauto

theorem initial15934 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3136)) := by
  have source := ElevenTheory.theory5270 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule15934 (meaning t m 1998) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2881) (meaning t m 2901) (meaning t m 3136) source

theorem rule15935 (p1990 p2027 p2114 p3063 p3093 p3954 p3989 : Prop) (h : p2114 ∨ (¬ p3093) ∨ (¬ p3063) ∨ (¬ p3954) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial15935 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory5271 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule15935 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 3063) (meaning t m 3093) (meaning t m 3954) (meaning t m 3989) source

theorem rule15937 (p1985 p2027 p2114 p3399 p3631 p3690 p3954 : Prop) (h : (¬ p3399) ∨ (¬ p1985) ∨ p2114 ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3690) ∨ (¬ p3631)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15937 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5273 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule15937 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3631) (meaning t m 3690) (meaning t m 3954) source

theorem rule15939 (p1991 p2027 p2187 p2963 p2997 p3097 p3324 : Prop) (h : (¬ p1991) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p2187) ∨ (¬ p3324)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3324) := by
  classical
  tauto

theorem initial15939 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3324)) := by
  have source := ElevenTheory.theory5275 t (m.theta 0 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15939 (meaning t m 1991) (meaning t m 2027) (meaning t m 2187) (meaning t m 2963) (meaning t m 2997) (meaning t m 3097) (meaning t m 3324) source

theorem rule15942 (p1980 p2027 p2114 p2797 p3037 p3399 p3572 p3954 : Prop) (h : p2027 ∨ (¬ p2797) ∨ (¬ p3954) ∨ p2114 ∨ (¬ p3399) ∨ (¬ p3037) ∨ (¬ p1980) ∨ (¬ p3572)) : (¬ p1980) ∨ (p2027) ∨ (p2114) ∨ (¬ p2797) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15942 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5278 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule15942 (meaning t m 1980) (meaning t m 2027) (meaning t m 2114) (meaning t m 2797) (meaning t m 3037) (meaning t m 3399) (meaning t m 3572) (meaning t m 3954) source

theorem rule15944 (p2003 p2027 p2299 p2588 p2633 p3564 p3946 : Prop) (h : (¬ p3946) ∨ (¬ p2003) ∨ (¬ p3564) ∨ p2027 ∨ (¬ p2588) ∨ p2633 ∨ (¬ p2299)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (p2633) ∨ (¬ p3564) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial15944 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory5280 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule15944 (meaning t m 2003) (meaning t m 2027) (meaning t m 2299) (meaning t m 2588) (meaning t m 2633) (meaning t m 3564) (meaning t m 3946) source

theorem rule15949 (p1980 p2148 p2156 p4564 : Prop) (h : p2148 ∨ p4564 ∨ (¬ p2156) ∨ (¬ p1980)) : (¬ p1980) ∨ (p2148) ∨ (¬ p2156) ∨ (p4564) := by
  classical
  tauto

theorem initial15949 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 4564) := by
  have source := ElevenTheory.theory5285 t (m.theta 0 5) (m.theta 3 6) (m.theta 5 6)
  exact rule15949 (meaning t m 1980) (meaning t m 2148) (meaning t m 2156) (meaning t m 4564) source

theorem rule15950 (p1994 p2027 p2651 p2963 p3008 p3564 p4037 : Prop) (h : (¬ p2963) ∨ (¬ p1994) ∨ (¬ p4037) ∨ p3008 ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3564)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (¬ p2963) ∨ (p3008) ∨ (¬ p3564) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15950 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5286 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9)
  exact rule15950 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2963) (meaning t m 3008) (meaning t m 3564) (meaning t m 4037) source

theorem rule15951 (p1981 p2027 p2383 p2588 p2997 p3564 p3946 : Prop) (h : (¬ p1981) ∨ (¬ p2383) ∨ (¬ p3564) ∨ (¬ p2588) ∨ p2027 ∨ p2997 ∨ (¬ p3946)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2383) ∨ (¬ p2588) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial15951 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory5287 t (m.theta 0 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule15951 (meaning t m 1981) (meaning t m 2027) (meaning t m 2383) (meaning t m 2588) (meaning t m 2997) (meaning t m 3564) (meaning t m 3946) source

theorem rule15953 (p1982 p2027 p2114 p2241 p3189 p3256 p3954 : Prop) (h : (¬ p3256) ∨ (¬ p3954) ∨ p2027 ∨ p2114 ∨ (¬ p3189) ∨ (¬ p2241) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15953 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5289 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 8) (m.theta 8 9)
  exact rule15953 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 3189) (meaning t m 3256) (meaning t m 3954) source

theorem rule15955 (p1983 p2997 p3631 p5142 : Prop) (h : (¬ p1983) ∨ p2997 ∨ (¬ p3631) ∨ p5142) : (¬ p1983) ∨ (p2997) ∨ (¬ p3631) ∨ (p5142) := by
  classical
  tauto

theorem initial15955 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3631)) ∨ (meaning t m 5142) := by
  have source := ElevenTheory.theory5291 t (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule15955 (meaning t m 1983) (meaning t m 2997) (meaning t m 3631) (meaning t m 5142) source

theorem rule15956 (p1983 p2027 p2114 p2241 p2449 p3027 p3954 : Prop) (h : (¬ p1983) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2449) ∨ (¬ p3954) ∨ p2114) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (¬ p3027) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial15956 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5292 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 7) (m.theta 7 9)
  exact rule15956 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2449) (meaning t m 3027) (meaning t m 3954) source

theorem rule15957 (p1981 p2027 p2383 p2997 p3097 p3125 p3946 : Prop) (h : (¬ p1981) ∨ (¬ p3946) ∨ (¬ p2383) ∨ p2997 ∨ p2027 ∨ (¬ p3125) ∨ (¬ p3097)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2383) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial15957 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory5293 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule15957 (meaning t m 1981) (meaning t m 2027) (meaning t m 2383) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3946) source

theorem rule15958 (p1980 p2027 p2881 p2938 p3564 p3581 p3644 p4037 : Prop) (h : p2938 ∨ (¬ p1980) ∨ (¬ p4037) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3644) ∨ (¬ p3581)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15958 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5294 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8)
  exact rule15958 (meaning t m 1980) (meaning t m 2027) (meaning t m 2881) (meaning t m 2938) (meaning t m 3564) (meaning t m 3581) (meaning t m 3644) (meaning t m 4037) source

theorem rule15965 (p1984 p2027 p2462 p2881 p3548 p3690 p4366 : Prop) (h : p2027 ∨ (¬ p4366) ∨ (¬ p3690) ∨ (¬ p1984) ∨ (¬ p3548) ∨ p2462 ∨ (¬ p2881)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3690) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial15965 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5301 t (m.theta 0 1) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule15965 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 2881) (meaning t m 3548) (meaning t m 3690) (meaning t m 4366) source

theorem rule15973 (p1976 p2027 p2462 p2780 p2829 p3588 p4324 : Prop) (h : p2462 ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p2780) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p4324)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial15973 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory5309 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 7 9)
  exact rule15973 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2780) (meaning t m 2829) (meaning t m 3588) (meaning t m 4324) source

theorem rule15976 (p1990 p2027 p2295 p3097 p3319 p3818 p4037 : Prop) (h : (¬ p4037) ∨ p2027 ∨ p3818 ∨ (¬ p2295) ∨ (¬ p3319) ∨ (¬ p1990) ∨ (¬ p3097)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p3097) ∨ (¬ p3319) ∨ (p3818) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15976 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3319)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5312 t (m.theta 1 6) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15976 (meaning t m 1990) (meaning t m 2027) (meaning t m 2295) (meaning t m 3097) (meaning t m 3319) (meaning t m 3818) (meaning t m 4037) source

theorem rule15977 (p1981 p2027 p2202 p2563 p2668 p3125 p4037 : Prop) (h : (¬ p3125) ∨ p2027 ∨ (¬ p4037) ∨ p2202 ∨ (¬ p1981) ∨ (¬ p2563) ∨ (¬ p2668)) : (¬ p1981) ∨ (p2027) ∨ (p2202) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3125) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial15977 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5313 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9)
  exact rule15977 (meaning t m 1981) (meaning t m 2027) (meaning t m 2202) (meaning t m 2563) (meaning t m 2668) (meaning t m 3125) (meaning t m 4037) source

theorem rule15979 (p1990 p2027 p2307 p2352 p2387 p3008 p3097 : Prop) (h : (¬ p1990) ∨ (¬ p2387) ∨ p2027 ∨ p3008 ∨ (¬ p3097) ∨ (¬ p2307) ∨ (¬ p2352)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (p3008) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial15979 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory5315 t (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule15979 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2352) (meaning t m 2387) (meaning t m 3008) (meaning t m 3097) source

theorem rule15980 (p1985 p2027 p2688 p2901 p3319 p3744 p3952 p4338 p4365 : Prop) (h : (¬ p2901) ∨ (¬ p3952) ∨ (¬ p1985) ∨ (¬ p3319) ∨ (¬ p4338) ∨ p2688 ∨ p2027 ∨ (¬ p4365) ∨ (¬ p3744)) : (¬ p1985) ∨ (p2027) ∨ (p2688) ∨ (¬ p2901) ∨ (¬ p3319) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4338) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial15980 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory5316 t (m.theta 1 3) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9)
  exact rule15980 (meaning t m 1985) (meaning t m 2027) (meaning t m 2688) (meaning t m 2901) (meaning t m 3319) (meaning t m 3744) (meaning t m 3952) (meaning t m 4338) (meaning t m 4365) source

theorem rule15982 (p2010 p2027 p2202 p2499 p2573 p2589 p2922 : Prop) (h : p2027 ∨ p2202 ∨ (¬ p2499) ∨ (¬ p2010) ∨ (¬ p2589) ∨ (¬ p2922) ∨ (¬ p2573)) : (¬ p2010) ∨ (p2027) ∨ (p2202) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2922) := by
  classical
  tauto

theorem initial15982 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2922)) := by
  have source := ElevenTheory.theory5318 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule15982 (meaning t m 2010) (meaning t m 2027) (meaning t m 2202) (meaning t m 2499) (meaning t m 2573) (meaning t m 2589) (meaning t m 2922) source

theorem rule15983 (p1975 p2027 p2274 p2688 p2951 p2962 p2992 p3654 p3744 : Prop) (h : (¬ p3654) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2962) ∨ p2688 ∨ (¬ p2951) ∨ (¬ p2992)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2688) ∨ (¬ p2951) ∨ (¬ p2962) ∨ (¬ p2992) ∨ (¬ p3654) ∨ (¬ p3744) := by
  classical
  tauto

theorem initial15983 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3744)) := by
  have source := ElevenTheory.theory5319 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15983 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2688) (meaning t m 2951) (meaning t m 2962) (meaning t m 2992) (meaning t m 3654) (meaning t m 3744) source

theorem rule15984 (p1975 p2027 p2299 p2911 p2964 p3346 p3389 : Prop) (h : (¬ p2911) ∨ (¬ p3389) ∨ p2964 ∨ p2027 ∨ (¬ p3346) ∨ (¬ p2299) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2911) ∨ (p2964) ∨ (¬ p3346) ∨ (¬ p3389) := by
  classical
  tauto

theorem initial15984 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2911)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) := by
  have source := ElevenTheory.theory5320 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8)
  exact rule15984 (meaning t m 1975) (meaning t m 2027) (meaning t m 2299) (meaning t m 2911) (meaning t m 2964) (meaning t m 3346) (meaning t m 3389) source

theorem rule15991 (p1992 p2027 p2462 p2608 p3486 p3555 p3690 : Prop) (h : (¬ p1992) ∨ (¬ p3555) ∨ p2027 ∨ p2462 ∨ (¬ p2608) ∨ (¬ p3690) ∨ (¬ p3486)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2608) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial15991 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory5327 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 5 7) (m.theta 7 9)
  exact rule15991 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2608) (meaning t m 3486) (meaning t m 3555) (meaning t m 3690) source

theorem rule15995 (p1987 p2027 p2588 p2667 p2997 p3564 p3946 p4195 : Prop) (h : (¬ p2588) ∨ (¬ p1987) ∨ (¬ p4195) ∨ (¬ p2667) ∨ (¬ p3946) ∨ (¬ p3564) ∨ p2027 ∨ p2997) : (¬ p1987) ∨ (p2027) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (p2997) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial15995 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2667)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory5331 t (m.theta 0 6) (m.theta 2 3) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule15995 (meaning t m 1987) (meaning t m 2027) (meaning t m 2588) (meaning t m 2667) (meaning t m 2997) (meaning t m 3564) (meaning t m 3946) (meaning t m 4195) source

theorem rule15997 (p1996 p2027 p2247 p2688 p3399 p3631 p3947 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3947) ∨ p2688 ∨ (¬ p1996) ∨ (¬ p3631)) : (¬ p1996) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial15997 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory5333 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 7) (m.theta 3 7) (m.theta 7 9)
  exact rule15997 (meaning t m 1996) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3399) (meaning t m 3631) (meaning t m 3947) source

theorem rule16000 (p1981 p2027 p2668 p2938 p2982 p4037 p4235 p5045 : Prop) (h : (¬ p2982) ∨ (¬ p5045) ∨ p2938 ∨ p2027 ∨ (¬ p1981) ∨ (¬ p4037) ∨ (¬ p4235) ∨ (¬ p2668)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2668) ∨ (p2938) ∨ (¬ p2982) ∨ (¬ p4037) ∨ (¬ p4235) ∨ (¬ p5045) := by
  classical
  tauto

theorem initial16000 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 5045)) := by
  have source := ElevenTheory.theory5336 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 6 8) (m.theta 6 9)
  exact rule16000 (meaning t m 1981) (meaning t m 2027) (meaning t m 2668) (meaning t m 2938) (meaning t m 2982) (meaning t m 4037) (meaning t m 4235) (meaning t m 5045) source

theorem rule16001 (p1979 p2027 p2114 p3093 p3136 p3922 p3954 p4195 : Prop) (h : (¬ p3136) ∨ p2027 ∨ (¬ p1979) ∨ (¬ p4195) ∨ (¬ p3093) ∨ p2114 ∨ (¬ p3922) ∨ (¬ p3954)) : (¬ p1979) ∨ (p2027) ∨ (p2114) ∨ (¬ p3093) ∨ (¬ p3136) ∨ (¬ p3922) ∨ (¬ p3954) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial16001 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory5337 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6)
  exact rule16001 (meaning t m 1979) (meaning t m 2027) (meaning t m 2114) (meaning t m 3093) (meaning t m 3136) (meaning t m 3922) (meaning t m 3954) (meaning t m 4195) source

theorem rule16002 (p2015 p2027 p2383 p2764 p3923 p3946 p4381 p4396 : Prop) (h : (¬ p4381) ∨ p2764 ∨ (¬ p3946) ∨ (¬ p3923) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p2015) ∨ (¬ p4396)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2383) ∨ (p2764) ∨ (¬ p3923) ∨ (¬ p3946) ∨ (¬ p4381) ∨ (¬ p4396) := by
  classical
  tauto

theorem initial16002 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4396)) := by
  have source := ElevenTheory.theory5338 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule16002 (meaning t m 2015) (meaning t m 2027) (meaning t m 2383) (meaning t m 2764) (meaning t m 3923) (meaning t m 3946) (meaning t m 4381) (meaning t m 4396) source

theorem rule16003 (p2000 p2027 p2764 p3540 p3644 p4348 p4444 : Prop) (h : p2764 ∨ (¬ p2000) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p4444) ∨ (¬ p4348) ∨ (¬ p3540)) : (¬ p2000) ∨ (p2027) ∨ (p2764) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16003 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5339 t (m.theta 0 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16003 (meaning t m 2000) (meaning t m 2027) (meaning t m 2764) (meaning t m 3540) (meaning t m 3644) (meaning t m 4348) (meaning t m 4444) source

theorem rule16005 (p1975 p2027 p2247 p2295 p2383 p2688 p3324 p5020 : Prop) (h : (¬ p3324) ∨ p2688 ∨ (¬ p2295) ∨ p2027 ∨ (¬ p5020) ∨ (¬ p2383) ∨ (¬ p1975) ∨ (¬ p2247)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (p2688) ∨ (¬ p3324) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial16005 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory5341 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16005 (meaning t m 1975) (meaning t m 2027) (meaning t m 2247) (meaning t m 2295) (meaning t m 2383) (meaning t m 2688) (meaning t m 3324) (meaning t m 5020) source

theorem rule16008 (p1981 p2027 p2114 p2668 p2737 p3483 p4037 p4426 : Prop) (h : (¬ p1981) ∨ (¬ p2668) ∨ (¬ p2737) ∨ p2114 ∨ p2027 ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4426)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2668) ∨ (¬ p2737) ∨ (¬ p3483) ∨ (¬ p4037) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial16008 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory5344 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 8) (m.theta 6 9)
  exact rule16008 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2668) (meaning t m 2737) (meaning t m 3483) (meaning t m 4037) (meaning t m 4426) source

theorem rule16013 (p1987 p2027 p2437 p2545 p2696 p3055 p3876 : Prop) (h : (¬ p1987) ∨ p2545 ∨ p2027 ∨ (¬ p3055) ∨ (¬ p2437) ∨ (¬ p2696) ∨ (¬ p3876)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2437) ∨ (p2545) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial16013 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory5349 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule16013 (meaning t m 1987) (meaning t m 2027) (meaning t m 2437) (meaning t m 2545) (meaning t m 2696) (meaning t m 3055) (meaning t m 3876) source

theorem rule16014 (p1982 p2027 p2202 p2341 p2437 p2440 p2459 p3575 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p3575) ∨ (¬ p2459) ∨ (¬ p2341) ∨ (¬ p2437) ∨ (¬ p2440) ∨ p2202) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2341) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2459) ∨ (¬ p3575) := by
  classical
  tauto

theorem initial16014 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3575)) := by
  have source := ElevenTheory.theory5350 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16014 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2341) (meaning t m 2437) (meaning t m 2440) (meaning t m 2459) (meaning t m 3575) source

theorem rule16015 (p1998 p2027 p2202 p2437 p2440 p2528 p3875 p4348 : Prop) (h : (¬ p2440) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p1998) ∨ (¬ p2437) ∨ (¬ p4348) ∨ p2202 ∨ (¬ p3875)) : (¬ p1998) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2528) ∨ (¬ p3875) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16015 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5351 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16015 (meaning t m 1998) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 2528) (meaning t m 3875) (meaning t m 4348) source

theorem rule16018 (p2015 p2027 p2202 p2437 p2440 p2927 p3093 p4366 : Prop) (h : (¬ p2015) ∨ p2027 ∨ p2202 ∨ (¬ p4366) ∨ (¬ p2437) ∨ (¬ p3093) ∨ (¬ p2440) ∨ (¬ p2927)) : (¬ p2015) ∨ (p2027) ∨ (p2202) ∨ (¬ p2437) ∨ (¬ p2440) ∨ (¬ p2927) ∨ (¬ p3093) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16018 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5354 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule16018 (meaning t m 2015) (meaning t m 2027) (meaning t m 2202) (meaning t m 2437) (meaning t m 2440) (meaning t m 2927) (meaning t m 3093) (meaning t m 4366) source

theorem rule16019 (p1977 p2027 p2202 p2241 p2440 p2498 p3016 p3591 : Prop) (h : p2202 ∨ (¬ p3591) ∨ (¬ p2241) ∨ (¬ p3016) ∨ (¬ p2440) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p2498)) : (¬ p1977) ∨ (p2027) ∨ (p2202) ∨ (¬ p2241) ∨ (¬ p2440) ∨ (¬ p2498) ∨ (¬ p3016) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial16019 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory5355 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16019 (meaning t m 1977) (meaning t m 2027) (meaning t m 2202) (meaning t m 2241) (meaning t m 2440) (meaning t m 2498) (meaning t m 3016) (meaning t m 3591) source

theorem rule16022 (p2001 p2027 p2210 p2619 p2699 p2891 p4244 : Prop) (h : p2699 ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2210) ∨ (¬ p4244) ∨ (¬ p2001) ∨ (¬ p2891)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2619) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial16022 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2619)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory5358 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 8)
  exact rule16022 (meaning t m 2001) (meaning t m 2027) (meaning t m 2210) (meaning t m 2619) (meaning t m 2699) (meaning t m 2891) (meaning t m 4244) source

theorem rule16024 (p1983 p2027 p2210 p2891 p3246 p3623 p4366 : Prop) (h : p2027 ∨ p3623 ∨ (¬ p1983) ∨ (¬ p3246) ∨ (¬ p2891) ∨ (¬ p4366) ∨ (¬ p2210)) : (¬ p1983) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (p3623) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16024 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (meaning t m 3623) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5360 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16024 (meaning t m 1983) (meaning t m 2027) (meaning t m 2210) (meaning t m 2891) (meaning t m 3246) (meaning t m 3623) (meaning t m 4366) source

theorem rule16026 (p2741 p3402 p4257 : Prop) (h : p4257 ∨ (¬ p3402) ∨ (¬ p2741)) : (¬ p2741) ∨ (¬ p3402) ∨ (p4257) := by
  classical
  tauto

theorem initial16026 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3402)) ∨ (meaning t m 4257) := by
  have source := ElevenTheory.theory5362 (m.theta 1 2) (m.theta 1 3) (m.theta 1 4)
  exact rule16026 (meaning t m 2741) (meaning t m 3402) (meaning t m 4257) source

theorem rule16027 (p1992 p2027 p2202 p2440 p2579 p2655 p2743 p3016 p3361 : Prop) (h : (¬ p1992) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2440) ∨ (¬ p3361) ∨ p2202 ∨ (¬ p2655) ∨ (¬ p2743) ∨ (¬ p2579)) : (¬ p1992) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2743) ∨ (¬ p3016) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial16027 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory5363 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16027 (meaning t m 1992) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2579) (meaning t m 2655) (meaning t m 2743) (meaning t m 3016) (meaning t m 3361) source

theorem rule16029 (p3246 p3571 p3631 : Prop) (h : (¬ p3571) ∨ (¬ p3246) ∨ p3631) : (¬ p3246) ∨ (¬ p3571) ∨ (p3631) := by
  classical
  tauto

theorem initial16029 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3571)) ∨ (meaning t m 3631) := by
  have source := ElevenTheory.theory5365 (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16029 (meaning t m 3246) (meaning t m 3571) (meaning t m 3631) source

theorem rule16031 (p4423 p5727 p5728 p5729 p5730 : Prop) : (p4423) ∨ (((¬ p5728) ∨ (¬ p4423) ∨ (¬ p5727) ∨ (¬ p5729) ∨ (¬ p5730))) := by
  classical
  tauto

theorem initial16031 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4423) ∨ (meaning t m 6190) := by
  exact rule16031 (meaning t m 4423) (meaning t m 5727) (meaning t m 5728) (meaning t m 5729) (meaning t m 5730)

theorem rule16038 (p4253 p5732 p5733 p5734 p5735 : Prop) : (p4253) ∨ (((¬ p5732) ∨ (¬ p5733) ∨ (¬ p4253) ∨ (¬ p5734) ∨ (¬ p5735))) := by
  classical
  tauto

theorem initial16038 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4253) ∨ (meaning t m 6191) := by
  exact rule16038 (meaning t m 4253) (meaning t m 5732) (meaning t m 5733) (meaning t m 5734) (meaning t m 5735)

theorem rule16044 (p6190 p6191 : Prop) : (¬ ((¬ p6190) ∨ (¬ p6191))) ∨ (¬ p6190) ∨ (¬ p6191) := by
  classical
  tauto

theorem initial16044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6189)) ∨ (¬ (meaning t m 6190)) ∨ (¬ (meaning t m 6191)) := by
  exact rule16044 (meaning t m 6190) (meaning t m 6191)

theorem rule16045 (p5725 p6189 : Prop) (h : (p5725 ↔ p6189)) : (¬ p5725) ∨ (p6189) := by
  classical
  tauto

theorem initial16045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5725)) ∨ (meaning t m 6189) := by
  have source := ElevenTheory.theory5366 t (m.theta 2 10) (m.theta 2 7) (m.theta 7 10)
  exact rule16045 (meaning t m 5725) (meaning t m 6189) source

theorem rule16048 (p1983 p2027 p2699 p3399 p3434 p3527 p3659 : Prop) (h : (¬ p1983) ∨ (¬ p3434) ∨ p2027 ∨ p2699 ∨ (¬ p3399) ∨ (¬ p3659) ∨ (¬ p3527)) : (¬ p1983) ∨ (p2027) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3434) ∨ (¬ p3527) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial16048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory5368 t (m.theta 0 1) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16048 (meaning t m 1983) (meaning t m 2027) (meaning t m 2699) (meaning t m 3399) (meaning t m 3434) (meaning t m 3527) (meaning t m 3659) source

theorem rule16056 (p2000 p2027 p2177 p2579 p2997 p3016 p3553 p4112 : Prop) (h : (¬ p2000) ∨ (¬ p3553) ∨ (¬ p2579) ∨ (¬ p4112) ∨ p2997 ∨ p2027 ∨ (¬ p3016) ∨ (¬ p2177)) : (¬ p2000) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2579) ∨ (p2997) ∨ (¬ p3016) ∨ (¬ p3553) ∨ (¬ p4112) := by
  classical
  tauto

theorem initial16056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4112)) := by
  have source := ElevenTheory.theory5376 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16056 (meaning t m 2000) (meaning t m 2027) (meaning t m 2177) (meaning t m 2579) (meaning t m 2997) (meaning t m 3016) (meaning t m 3553) (meaning t m 4112) source

theorem rule16059 (p1994 p2027 p2114 p2406 p2440 p3379 p3954 : Prop) (h : (¬ p2406) ∨ p2027 ∨ (¬ p1994) ∨ (¬ p3379) ∨ (¬ p2440) ∨ p2114 ∨ (¬ p3954)) : (¬ p1994) ∨ (p2027) ∨ (p2114) ∨ (¬ p2406) ∨ (¬ p2440) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5379 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5)
  exact rule16059 (meaning t m 1994) (meaning t m 2027) (meaning t m 2114) (meaning t m 2406) (meaning t m 2440) (meaning t m 3379) (meaning t m 3954) source

theorem rule16061 (p1983 p2027 p2114 p3707 p3830 p3954 p4381 : Prop) (h : (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p1983) ∨ p2027 ∨ p2114 ∨ (¬ p4381)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory5381 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 9) (m.theta 7 9) (m.theta 9 10)
  exact rule16061 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 3707) (meaning t m 3830) (meaning t m 3954) (meaning t m 4381) source

theorem rule16063 (p1983 p2938 p3631 p4911 : Prop) (h : (¬ p1983) ∨ p2938 ∨ (¬ p3631) ∨ p4911) : (¬ p1983) ∨ (p2938) ∨ (¬ p3631) ∨ (p4911) := by
  classical
  tauto

theorem initial16063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3631)) ∨ (meaning t m 4911) := by
  have source := ElevenTheory.theory5383 t (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16063 (meaning t m 1983) (meaning t m 2938) (meaning t m 3631) (meaning t m 4911) source

theorem rule16066 (p1995 p2027 p2169 p2247 p3324 p3379 p4154 : Prop) (h : p2169 ∨ p2027 ∨ (¬ p3324) ∨ (¬ p2247) ∨ (¬ p1995) ∨ (¬ p3379) ∨ (¬ p4154)) : (¬ p1995) ∨ (p2027) ∨ (p2169) ∨ (¬ p2247) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5386 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 6) (m.theta 6 8)
  exact rule16066 (meaning t m 1995) (meaning t m 2027) (meaning t m 2169) (meaning t m 2247) (meaning t m 3324) (meaning t m 3379) (meaning t m 4154) source

theorem rule16068 (p1985 p2027 p2114 p2132 p2870 p3055 p3367 : Prop) (h : (¬ p1985) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3055) ∨ p2114 ∨ p2027 ∨ (¬ p3367)) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2870) ∨ (¬ p3055) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial16068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory5388 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 7)
  exact rule16068 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2870) (meaning t m 3055) (meaning t m 3367) source

theorem rule16070 (p1997 p2027 p2114 p2210 p2972 p3954 p4948 : Prop) (h : p2114 ∨ (¬ p3954) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p4948)) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3954) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5390 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 4 5) (m.theta 5 9)
  exact rule16070 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2210) (meaning t m 2972) (meaning t m 3954) (meaning t m 4948) source

theorem rule16071 (p1991 p2027 p2963 p2997 p3097 p3125 p4037 : Prop) (h : (¬ p3125) ∨ (¬ p1991) ∨ p2997 ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4037)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2963) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial16071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5391 t (m.theta 0 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule16071 (meaning t m 1991) (meaning t m 2027) (meaning t m 2963) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 4037) source

theorem rule16072 (p1997 p2027 p2156 p2177 p2997 p3551 p4110 p4984 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p2156) ∨ (¬ p3551) ∨ (¬ p2177) ∨ (¬ p1997) ∨ (¬ p4984) ∨ (¬ p4110)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p4110) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial16072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory5392 t (m.theta 0 5) (m.theta 0 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16072 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2177) (meaning t m 2997) (meaning t m 3551) (meaning t m 4110) (meaning t m 4984) source

theorem rule16073 (p1983 p2027 p2114 p2417 p2922 p3379 p3954 : Prop) (h : (¬ p1983) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p3954) ∨ p2114 ∨ (¬ p3379)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5393 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 7) (m.theta 7 9)
  exact rule16073 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2417) (meaning t m 2922) (meaning t m 3379) (meaning t m 3954) source

theorem rule16076 (p2010 p2027 p2323 p2437 p2630 p2946 p4315 : Prop) (h : p2323 ∨ (¬ p4315) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2010) ∨ (¬ p2946)) : (¬ p2010) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2946) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5396 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule16076 (meaning t m 2010) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2630) (meaning t m 2946) (meaning t m 4315) source

theorem rule16077 (p1997 p2027 p2459 p2542 p2633 p3692 p3693 p3742 p4186 : Prop) (h : (¬ p1997) ∨ (¬ p2459) ∨ (¬ p4186) ∨ p2633 ∨ p2027 ∨ (¬ p3742) ∨ (¬ p2542) ∨ (¬ p3692) ∨ (¬ p3693)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p3693) ∨ (¬ p3742) ∨ (¬ p4186) := by
  classical
  tauto

theorem initial16077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4186)) := by
  have source := ElevenTheory.theory5397 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16077 (meaning t m 1997) (meaning t m 2027) (meaning t m 2459) (meaning t m 2542) (meaning t m 2633) (meaning t m 3692) (meaning t m 3693) (meaning t m 3742) (meaning t m 4186) source

theorem rule16078 (p1983 p2027 p2230 p2233 p3201 p3246 p3569 p3684 : Prop) (h : (¬ p1983) ∨ (¬ p3569) ∨ (¬ p3246) ∨ p2233 ∨ (¬ p3201) ∨ (¬ p2230) ∨ (¬ p3684) ∨ p2027) : (¬ p1983) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p3201) ∨ (¬ p3246) ∨ (¬ p3569) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial16078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory5398 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16078 (meaning t m 1983) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 3201) (meaning t m 3246) (meaning t m 3569) (meaning t m 3684) source

theorem rule16081 (p2015 p2027 p2187 p2764 p3744 p3923 p4191 : Prop) (h : (¬ p3744) ∨ (¬ p2015) ∨ p2027 ∨ p2764 ∨ (¬ p2187) ∨ (¬ p3923) ∨ (¬ p4191)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2187) ∨ (p2764) ∨ (¬ p3744) ∨ (¬ p3923) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5401 t (m.theta 1 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule16081 (meaning t m 2015) (meaning t m 2027) (meaning t m 2187) (meaning t m 2764) (meaning t m 3744) (meaning t m 3923) (meaning t m 4191) source

theorem rule16082 (p1997 p2027 p2230 p2476 p2534 p2764 p4444 : Prop) (h : p2027 ∨ (¬ p1997) ∨ (¬ p2230) ∨ (¬ p2534) ∨ (¬ p2476) ∨ p2764 ∨ (¬ p4444)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2764) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5402 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16082 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2476) (meaning t m 2534) (meaning t m 2764) (meaning t m 4444) source

theorem rule16086 (p1979 p2027 p2156 p2764 p3952 p4032 p4033 p4191 : Prop) (h : (¬ p1979) ∨ p2764 ∨ (¬ p2156) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p4033) ∨ (¬ p4032) ∨ (¬ p4191)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2156) ∨ (p2764) ∨ (¬ p3952) ∨ (¬ p4032) ∨ (¬ p4033) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5406 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule16086 (meaning t m 1979) (meaning t m 2027) (meaning t m 2156) (meaning t m 2764) (meaning t m 3952) (meaning t m 4032) (meaning t m 4033) (meaning t m 4191) source

theorem rule16091 (p1994 p2027 p2177 p2651 p2997 p3414 p3553 : Prop) (h : p2997 ∨ (¬ p3553) ∨ (¬ p2651) ∨ (¬ p1994) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3414)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2651) ∨ (p2997) ∨ (¬ p3414) ∨ (¬ p3553) := by
  classical
  tauto

theorem initial16091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3553)) := by
  have source := ElevenTheory.theory5411 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16091 (meaning t m 1994) (meaning t m 2027) (meaning t m 2177) (meaning t m 2651) (meaning t m 2997) (meaning t m 3414) (meaning t m 3553) source

theorem rule16092 (p1990 p2027 p2114 p2241 p2284 p2992 p3954 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p1990) ∨ (¬ p2241) ∨ (¬ p2284)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p2992) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5412 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6)
  exact rule16092 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2284) (meaning t m 2992) (meaning t m 3954) source

theorem rule16093 (p1990 p2027 p2220 p2284 p2938 p3497 p3556 : Prop) (h : p2027 ∨ p2938 ∨ (¬ p3556) ∨ (¬ p3497) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2284) ∨ (p2938) ∨ (¬ p3497) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial16093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory5413 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule16093 (meaning t m 1990) (meaning t m 2027) (meaning t m 2220) (meaning t m 2284) (meaning t m 2938) (meaning t m 3497) (meaning t m 3556) source

theorem rule16097 (p1997 p2027 p2114 p2192 p2210 p3954 p4110 : Prop) (h : (¬ p1997) ∨ (¬ p2210) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p4110) ∨ p2114) : (¬ p1997) ∨ (p2027) ∨ (p2114) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3954) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16097 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5417 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16097 (meaning t m 1997) (meaning t m 2027) (meaning t m 2114) (meaning t m 2192) (meaning t m 2210) (meaning t m 3954) (meaning t m 4110) source

theorem rule16098 (p2926 p3399 p3452 : Prop) (h : (¬ p3399) ∨ (¬ p3452) ∨ (¬ p2926)) : (¬ p2926) ∨ (¬ p3399) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial16098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory5418 (m.theta 0 1) (m.theta 1 4) (m.theta 1 7)
  exact rule16098 (meaning t m 2926) (meaning t m 3399) (meaning t m 3452) source

theorem rule16100 (p2007 p2027 p2114 p2241 p2727 p3083 p3954 : Prop) (h : p2027 ∨ (¬ p2007) ∨ (¬ p3083) ∨ (¬ p2241) ∨ (¬ p2727) ∨ p2114 ∨ (¬ p3954)) : (¬ p2007) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3083) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5420 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8)
  exact rule16100 (meaning t m 2007) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2727) (meaning t m 3083) (meaning t m 3954) source

theorem rule16101 (p2006 p2027 p2284 p2764 p3758 p4033 p4191 p4208 : Prop) (h : (¬ p2006) ∨ (¬ p4191) ∨ (¬ p4208) ∨ p2027 ∨ p2764 ∨ (¬ p4033) ∨ (¬ p3758) ∨ (¬ p2284)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2284) ∨ (p2764) ∨ (¬ p3758) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4208) := by
  classical
  tauto

theorem initial16101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4208)) := by
  have source := ElevenTheory.theory5421 t (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule16101 (meaning t m 2006) (meaning t m 2027) (meaning t m 2284) (meaning t m 2764) (meaning t m 3758) (meaning t m 4033) (meaning t m 4191) (meaning t m 4208) source

theorem rule16103 (p2010 p2027 p2114 p3399 p3631 p3954 p4278 : Prop) (h : p2114 ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p2010) ∨ (¬ p3954) ∨ (¬ p4278)) : (¬ p2010) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5423 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule16103 (meaning t m 2010) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3631) (meaning t m 3954) (meaning t m 4278) source

theorem rule16105 (p1985 p2027 p2409 p3399 p3452 p3527 p3570 : Prop) (h : p2027 ∨ (¬ p1985) ∨ p2409 ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3452)) : (¬ p1985) ∨ (p2027) ∨ (p2409) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3527) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial16105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory5425 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule16105 (meaning t m 1985) (meaning t m 2027) (meaning t m 2409) (meaning t m 3399) (meaning t m 3452) (meaning t m 3527) (meaning t m 3570) source

theorem rule16109 (p2003 p2027 p2387 p2553 p2668 p3008 p3568 : Prop) (h : (¬ p2003) ∨ p3008 ∨ p2027 ∨ (¬ p2553) ∨ (¬ p3568) ∨ (¬ p2387) ∨ (¬ p2668)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2553) ∨ (¬ p2668) ∨ (p3008) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial16109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory5429 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16109 (meaning t m 2003) (meaning t m 2027) (meaning t m 2387) (meaning t m 2553) (meaning t m 2668) (meaning t m 3008) (meaning t m 3568) source

theorem rule16112 (p1991 p2027 p2630 p2657 p2765 p3952 p4315 : Prop) (h : (¬ p2630) ∨ (¬ p1991) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p4315) ∨ p2765 ∨ (¬ p3952)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (p2765) ∨ (¬ p3952) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5432 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule16112 (meaning t m 1991) (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2765) (meaning t m 3952) (meaning t m 4315) source

theorem rule16115 (p1979 p2765 p4110 p4702 : Prop) (h : p2765 ∨ (¬ p4110) ∨ (¬ p1979) ∨ p4702) : (¬ p1979) ∨ (p2765) ∨ (¬ p4110) ∨ (p4702) := by
  classical
  tauto

theorem initial16115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4110)) ∨ (meaning t m 4702) := by
  have source := ElevenTheory.theory5435 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16115 (meaning t m 1979) (meaning t m 2765) (meaning t m 4110) (meaning t m 4702) source

theorem rule16116 (p1994 p2027 p2553 p2727 p3008 p3568 p4154 : Prop) (h : p3008 ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p1994) ∨ (¬ p4154) ∨ (¬ p2727)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2727) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5436 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule16116 (meaning t m 1994) (meaning t m 2027) (meaning t m 2553) (meaning t m 2727) (meaning t m 3008) (meaning t m 3568) (meaning t m 4154) source

theorem rule16117 (p1979 p2027 p2553 p2992 p3008 p3568 p4154 : Prop) (h : p3008 ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3568) ∨ (¬ p1979) ∨ (¬ p4154) ∨ (¬ p2992)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2553) ∨ (¬ p2992) ∨ (p3008) ∨ (¬ p3568) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial16117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2992)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory5437 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7)
  exact rule16117 (meaning t m 1979) (meaning t m 2027) (meaning t m 2553) (meaning t m 2992) (meaning t m 3008) (meaning t m 3568) (meaning t m 4154) source

theorem rule16118 (p1981 p2553 p3008 p4405 : Prop) (h : p3008 ∨ (¬ p1981) ∨ (¬ p2553) ∨ p4405) : (¬ p1981) ∨ (¬ p2553) ∨ (p3008) ∨ (p4405) := by
  classical
  tauto

theorem initial16118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (meaning t m 4405) := by
  have source := ElevenTheory.theory5438 t (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16118 (meaning t m 1981) (meaning t m 2553) (meaning t m 3008) (meaning t m 4405) source

theorem rule16119 (p1977 p2027 p2462 p2589 p2662 p3690 p4111 p4235 : Prop) (h : (¬ p2589) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p1977) ∨ (¬ p2662) ∨ (¬ p3690) ∨ p2462) : (¬ p1977) ∨ (p2027) ∨ (p2462) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p3690) ∨ (¬ p4111) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial16119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory5439 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule16119 (meaning t m 1977) (meaning t m 2027) (meaning t m 2462) (meaning t m 2589) (meaning t m 2662) (meaning t m 3690) (meaning t m 4111) (meaning t m 4235) source

theorem rule16123 (p1995 p2027 p2553 p3008 p3379 p3549 p3591 : Prop) (h : (¬ p2553) ∨ (¬ p1995) ∨ p3008 ∨ p2027 ∨ (¬ p3379) ∨ (¬ p3591) ∨ (¬ p3549)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial16123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory5443 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule16123 (meaning t m 1995) (meaning t m 2027) (meaning t m 2553) (meaning t m 3008) (meaning t m 3379) (meaning t m 3549) (meaning t m 3591) source

theorem rule16125 (p2000 p2027 p2373 p2462 p3690 p3904 p4120 p4235 : Prop) (h : (¬ p2000) ∨ (¬ p2373) ∨ (¬ p4120) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p3904) ∨ (¬ p3690) ∨ p2462) : (¬ p2000) ∨ (p2027) ∨ (¬ p2373) ∨ (p2462) ∨ (¬ p3690) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial16125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory5445 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 9)
  exact rule16125 (meaning t m 2000) (meaning t m 2027) (meaning t m 2373) (meaning t m 2462) (meaning t m 3690) (meaning t m 3904) (meaning t m 4120) (meaning t m 4235) source

theorem rule16127 (p1998 p2027 p2323 p2946 p3146 p3156 p4348 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p4348) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p1998) ∨ (¬ p3156)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5447 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16127 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 4348) source

theorem rule16128 (p1981 p2027 p2187 p3309 p3791 p3818 p4204 p5660 : Prop) (h : (¬ p1981) ∨ p3818 ∨ (¬ p3791) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p4204) ∨ (¬ p5660) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p3309) ∨ (¬ p3791) ∨ (p3818) ∨ (¬ p4204) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial16128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3791)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory5448 t (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule16128 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 3309) (meaning t m 3791) (meaning t m 3818) (meaning t m 4204) (meaning t m 5660) source

end SunPrize.SMT
