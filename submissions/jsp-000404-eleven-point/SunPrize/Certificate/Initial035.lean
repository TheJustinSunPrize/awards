import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory019
import SunPrize.Certificate.Theory020
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule16507 (p2002 p2027 p2545 p2641 p2668 p4111 p4358 : Prop) (h : (¬ p2002) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2641) ∨ p2545 ∨ (¬ p4358) ∨ (¬ p2668)) : (¬ p2002) ∨ (p2027) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4111) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial16507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory5811 t (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule16507 (meaning t m 2002) (meaning t m 2027) (meaning t m 2545) (meaning t m 2641) (meaning t m 2668) (meaning t m 4111) (meaning t m 4358) source

theorem rule16508 (p1987 p2027 p2187 p2997 p3097 p3324 p4195 : Prop) (h : (¬ p1987) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p2187) ∨ p2997 ∨ (¬ p3324) ∨ (¬ p3097)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2187) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3324) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial16508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory5812 t (m.theta 2 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16508 (meaning t m 1987) (meaning t m 2027) (meaning t m 2187) (meaning t m 2997) (meaning t m 3097) (meaning t m 3324) (meaning t m 4195) source

theorem rule16509 (p1987 p2027 p2169 p2946 p2963 p3745 p3989 p4315 : Prop) (h : (¬ p2963) ∨ (¬ p3989) ∨ p2169 ∨ (¬ p3745) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p2946)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p3989) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5813 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule16509 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2946) (meaning t m 2963) (meaning t m 3745) (meaning t m 3989) (meaning t m 4315) source

theorem rule16510 (p1997 p2027 p2545 p2641 p2850 p3584 p3984 p4111 : Prop) (h : (¬ p1997) ∨ p2545 ∨ (¬ p4111) ∨ (¬ p2641) ∨ (¬ p3584) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3984)) : (¬ p1997) ∨ (p2027) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2850) ∨ (¬ p3584) ∨ (¬ p3984) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial16510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory5814 t (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6)
  exact rule16510 (meaning t m 1997) (meaning t m 2027) (meaning t m 2545) (meaning t m 2641) (meaning t m 2850) (meaning t m 3584) (meaning t m 3984) (meaning t m 4111) source

theorem rule16512 (p1984 p2027 p2169 p2191 p2363 p3555 p3692 : Prop) (h : p2169 ∨ p2027 ∨ (¬ p2191) ∨ (¬ p1984) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p2363)) : (¬ p1984) ∨ (p2027) ∨ (p2169) ∨ (¬ p2191) ∨ (¬ p2363) ∨ (¬ p3555) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial16512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory5816 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16512 (meaning t m 1984) (meaning t m 2027) (meaning t m 2169) (meaning t m 2191) (meaning t m 2363) (meaning t m 3555) (meaning t m 3692) source

theorem rule16513 (p1997 p2027 p2534 p2850 p2938 p3146 p3747 p3874 : Prop) (h : p2938 ∨ (¬ p1997) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2534) ∨ (¬ p3874) ∨ (¬ p2850) ∨ (¬ p3747)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2534) ∨ (¬ p2850) ∨ (p2938) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial16513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2850)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory5817 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 7) (m.theta 5 8) (m.theta 8 9)
  exact rule16513 (meaning t m 1997) (meaning t m 2027) (meaning t m 2534) (meaning t m 2850) (meaning t m 2938) (meaning t m 3146) (meaning t m 3747) (meaning t m 3874) source

theorem rule16514 (p1998 p2027 p2611 p2911 p3434 p3471 p4278 : Prop) (h : (¬ p1998) ∨ p2611 ∨ (¬ p2911) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p3471)) : (¬ p1998) ∨ (p2027) ∨ (p2611) ∨ (¬ p2911) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5818 t (m.theta 0 2) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16514 (meaning t m 1998) (meaning t m 2027) (meaning t m 2611) (meaning t m 2911) (meaning t m 3434) (meaning t m 3471) (meaning t m 4278) source

theorem rule16516 (p1982 p2027 p2459 p2598 p2611 p2911 p3201 : Prop) (h : p2611 ∨ (¬ p2598) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p1982) ∨ (¬ p2911)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2459) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2911) ∨ (¬ p3201) := by
  classical
  tauto

theorem initial16516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) := by
  have source := ElevenTheory.theory5820 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule16516 (meaning t m 1982) (meaning t m 2027) (meaning t m 2459) (meaning t m 2598) (meaning t m 2611) (meaning t m 2911) (meaning t m 3201) source

theorem rule16517 (p1981 p2027 p2122 p2187 p2611 p2774 p3097 : Prop) (h : (¬ p1981) ∨ p2611 ∨ (¬ p2122) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2774) ∨ (¬ p3097)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2187) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3097) := by
  classical
  tauto

theorem initial16517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3097)) := by
  have source := ElevenTheory.theory5821 t (m.theta 0 2) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16517 (meaning t m 1981) (meaning t m 2027) (meaning t m 2122) (meaning t m 2187) (meaning t m 2611) (meaning t m 2774) (meaning t m 3097) source

theorem rule16518 (p1981 p2027 p2122 p2352 p2588 p2611 p2774 : Prop) (h : (¬ p1981) ∨ p2611 ∨ (¬ p2352) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2588)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2122) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (p2611) ∨ (¬ p2774) := by
  classical
  tauto

theorem initial16518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) := by
  have source := ElevenTheory.theory5822 t (m.theta 0 2) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16518 (meaning t m 1981) (meaning t m 2027) (meaning t m 2122) (meaning t m 2352) (meaning t m 2588) (meaning t m 2611) (meaning t m 2774) source

theorem rule16519 (p1998 p2027 p2545 p3189 p3256 p4111 p4348 : Prop) (h : (¬ p3256) ∨ p2545 ∨ (¬ p4348) ∨ (¬ p3189) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4111)) : (¬ p1998) ∨ (p2027) ∨ (p2545) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p4111) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial16519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory5823 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16519 (meaning t m 1998) (meaning t m 2027) (meaning t m 2545) (meaning t m 3189) (meaning t m 3256) (meaning t m 4111) (meaning t m 4348) source

theorem rule16520 (p1988 p2027 p2114 p2417 p2761 p3367 p3389 p3759 : Prop) (h : (¬ p1988) ∨ (¬ p2417) ∨ (¬ p3759) ∨ (¬ p3389) ∨ (¬ p3367) ∨ p2027 ∨ p2114 ∨ (¬ p2761)) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial16520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory5824 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16520 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2417) (meaning t m 2761) (meaning t m 3367) (meaning t m 3389) (meaning t m 3759) source

theorem rule16521 (p1981 p2027 p2114 p2774 p2819 p3055 p3367 : Prop) (h : (¬ p3367) ∨ (¬ p2774) ∨ (¬ p1981) ∨ p2027 ∨ p2114 ∨ (¬ p3055) ∨ (¬ p2819)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3055) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial16521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory5825 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8)
  exact rule16521 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2774) (meaning t m 2819) (meaning t m 3055) (meaning t m 3367) source

theorem rule16522 (p1984 p2027 p2138 p2766 p3758 p3873 p3989 p4347 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p3989) ∨ p2766 ∨ (¬ p2138) ∨ (¬ p3873) ∨ (¬ p4347) ∨ (¬ p3758)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2138) ∨ (p2766) ∨ (¬ p3758) ∨ (¬ p3873) ∨ (¬ p3989) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory5826 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16522 (meaning t m 1984) (meaning t m 2027) (meaning t m 2138) (meaning t m 2766) (meaning t m 3758) (meaning t m 3873) (meaning t m 3989) (meaning t m 4347) source

theorem rule16523 (p1979 p2027 p2545 p2641 p2946 p2963 p4111 : Prop) (h : p2027 ∨ p2545 ∨ (¬ p2963) ∨ (¬ p2946) ∨ (¬ p4111) ∨ (¬ p2641) ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial16523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory5827 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 6)
  exact rule16523 (meaning t m 1979) (meaning t m 2027) (meaning t m 2545) (meaning t m 2641) (meaning t m 2946) (meaning t m 2963) (meaning t m 4111) source

theorem rule16524 (p1997 p2027 p2545 p2657 p2946 p3115 p4948 : Prop) (h : (¬ p1997) ∨ p2027 ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p4948) ∨ (¬ p3115)) : (¬ p1997) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5828 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 9)
  exact rule16524 (meaning t m 1997) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) (meaning t m 3115) (meaning t m 4948) source

theorem rule16527 (p2027 p2274 p2774 p3425 p4471 p4889 : Prop) (h : (¬ p4471) ∨ (¬ p4889) ∨ p2027 ∨ (¬ p3425) ∨ (¬ p2274) ∨ (¬ p2774)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2774) ∨ (¬ p3425) ∨ (¬ p4471) ∨ (¬ p4889) := by
  classical
  tauto

theorem initial16527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4471)) ∨ (¬ (meaning t m 4889)) := by
  have source := ElevenTheory.theory5831 t (m.theta 0 2) (m.theta 2 6) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7)
  exact rule16527 (meaning t m 2027) (meaning t m 2274) (meaning t m 2774) (meaning t m 3425) (meaning t m 4471) (meaning t m 4889) source

theorem rule16529 (p2018 p2027 p2098 p2545 p2641 p2780 p4111 p4337 : Prop) (h : p2027 ∨ (¬ p2018) ∨ (¬ p4111) ∨ (¬ p2098) ∨ p2545 ∨ (¬ p4337) ∨ (¬ p2780) ∨ (¬ p2641)) : (¬ p2018) ∨ (p2027) ∨ (¬ p2098) ∨ (p2545) ∨ (¬ p2641) ∨ (¬ p2780) ∨ (¬ p4111) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial16529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2018)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory5833 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 6) (m.theta 2 8) (m.theta 3 4) (m.theta 3 6)
  exact rule16529 (meaning t m 2018) (meaning t m 2027) (meaning t m 2098) (meaning t m 2545) (meaning t m 2641) (meaning t m 2780) (meaning t m 4111) (meaning t m 4337) source

theorem rule16531 (p2001 p2027 p2114 p2132 p2619 p3055 p3367 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p2001) ∨ (¬ p3367) ∨ (¬ p3055) ∨ (¬ p2619) ∨ (¬ p2132)) : (¬ p2001) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p3055) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial16531 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory5835 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 8)
  exact rule16531 (meaning t m 2001) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2619) (meaning t m 3055) (meaning t m 3367) source

theorem rule16532 (p1987 p2027 p2696 p3055 p3367 p3437 p3588 : Prop) (h : (¬ p3367) ∨ (¬ p3588) ∨ p2027 ∨ p3437 ∨ (¬ p3055) ∨ (¬ p1987) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2696) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (p3437) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial16532 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 3437) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory5836 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7)
  exact rule16532 (meaning t m 1987) (meaning t m 2027) (meaning t m 2696) (meaning t m 3055) (meaning t m 3367) (meaning t m 3437) (meaning t m 3588) source

theorem rule16534 (p2006 p2027 p2132 p2396 p2997 p3425 p4324 : Prop) (h : (¬ p2006) ∨ (¬ p2132) ∨ (¬ p3425) ∨ p2027 ∨ (¬ p2396) ∨ p2997 ∨ (¬ p4324)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3425) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial16534 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory5838 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16534 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2396) (meaning t m 2997) (meaning t m 3425) (meaning t m 4324) source

theorem rule16538 (p1976 p2027 p2138 p2274 p2765 p3568 p4154 p4243 p4365 : Prop) (h : p2765 ∨ (¬ p1976) ∨ (¬ p2274) ∨ (¬ p4365) ∨ (¬ p2138) ∨ (¬ p4243) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p3568)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4243) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial16538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory5842 t (m.theta 0 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16538 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2274) (meaning t m 2765) (meaning t m 3568) (meaning t m 4154) (meaning t m 4243) (meaning t m 4365) source

theorem rule16540 (p1998 p2027 p2449 p2688 p2717 p3027 p3821 p3959 : Prop) (h : (¬ p3821) ∨ (¬ p2717) ∨ (¬ p3959) ∨ (¬ p2449) ∨ (¬ p1998) ∨ p2027 ∨ p2688 ∨ (¬ p3027)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2449) ∨ (p2688) ∨ (¬ p2717) ∨ (¬ p3027) ∨ (¬ p3821) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial16540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory5844 t (m.theta 0 7) (m.theta 1 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16540 (meaning t m 1998) (meaning t m 2027) (meaning t m 2449) (meaning t m 2688) (meaning t m 2717) (meaning t m 3027) (meaning t m 3821) (meaning t m 3959) source

theorem rule16541 (p1979 p2027 p2449 p2688 p2727 p3136 p3580 p4324 p4357 : Prop) (h : p2027 ∨ (¬ p1979) ∨ (¬ p2727) ∨ (¬ p3136) ∨ p2688 ∨ (¬ p3580) ∨ (¬ p2449) ∨ (¬ p4357) ∨ (¬ p4324)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2449) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3136) ∨ (¬ p3580) ∨ (¬ p4324) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial16541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory5845 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 7 9)
  exact rule16541 (meaning t m 1979) (meaning t m 2027) (meaning t m 2449) (meaning t m 2688) (meaning t m 2727) (meaning t m 3136) (meaning t m 3580) (meaning t m 4324) (meaning t m 4357) source

theorem rule16546 (p1984 p2027 p2247 p2997 p3097 p3662 p3952 : Prop) (h : (¬ p3097) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3662) ∨ p2997 ∨ (¬ p1984) ∨ (¬ p3952)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3662) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial16546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory5850 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule16546 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2997) (meaning t m 3097) (meaning t m 3662) (meaning t m 3952) source

theorem rule16548 (p2006 p2027 p2220 p2274 p2313 p2765 p3694 p4198 : Prop) (h : (¬ p3694) ∨ p2765 ∨ (¬ p2274) ∨ (¬ p2220) ∨ (¬ p2313) ∨ (¬ p4198) ∨ p2027 ∨ (¬ p2006)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p3694) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial16548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory5852 t (m.theta 0 5) (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule16548 (meaning t m 2006) (meaning t m 2027) (meaning t m 2220) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 3694) (meaning t m 4198) source

theorem rule16549 (p1981 p2027 p2114 p2122 p2352 p2588 p3367 p4375 : Prop) (h : (¬ p2588) ∨ (¬ p3367) ∨ p2114 ∨ (¬ p1981) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2352) ∨ (¬ p4375)) : (¬ p1981) ∨ (p2027) ∨ (p2114) ∨ (¬ p2122) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3367) ∨ (¬ p4375) := by
  classical
  tauto

theorem initial16549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4375)) := by
  have source := ElevenTheory.theory5853 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16549 (meaning t m 1981) (meaning t m 2027) (meaning t m 2114) (meaning t m 2122) (meaning t m 2352) (meaning t m 2588) (meaning t m 3367) (meaning t m 4375) source

theorem rule16550 (p2307 p3654 p4187 : Prop) (h : (¬ p4187) ∨ (¬ p2307) ∨ p3654) : (¬ p2307) ∨ (p3654) ∨ (¬ p4187) := by
  classical
  tauto

theorem initial16550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (meaning t m 3654) ∨ (¬ (meaning t m 4187)) := by
  have source := ElevenTheory.theory5854 (m.theta 0 6) (m.theta 6 7) (m.theta 6 9)
  exact rule16550 (meaning t m 2307) (meaning t m 3654) (meaning t m 4187) source

theorem rule16551 (p2005 p2027 p2114 p2588 p3055 p3367 p3471 p4475 : Prop) (h : p2027 ∨ (¬ p3367) ∨ (¬ p3055) ∨ p2114 ∨ (¬ p2005) ∨ (¬ p4475) ∨ (¬ p3471) ∨ (¬ p2588)) : (¬ p2005) ∨ (p2027) ∨ (p2114) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial16551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory5855 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7)
  exact rule16551 (meaning t m 2005) (meaning t m 2027) (meaning t m 2114) (meaning t m 2588) (meaning t m 3055) (meaning t m 3367) (meaning t m 3471) (meaning t m 4475) source

theorem rule16554 (p1984 p2027 p2191 p2192 p2766 p3369 p3646 p4347 p4506 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p3369) ∨ (¬ p4506) ∨ (¬ p2191) ∨ p2766) : (¬ p1984) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2192) ∨ (p2766) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial16554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory5858 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16554 (meaning t m 1984) (meaning t m 2027) (meaning t m 2191) (meaning t m 2192) (meaning t m 2766) (meaning t m 3369) (meaning t m 3646) (meaning t m 4347) (meaning t m 4506) source

theorem rule16555 (p1980 p2027 p2177 p2311 p2997 p3551 p3654 p4037 : Prop) (h : (¬ p3654) ∨ (¬ p2177) ∨ (¬ p3551) ∨ (¬ p1980) ∨ (¬ p2311) ∨ (¬ p4037) ∨ p2027 ∨ p2997) : (¬ p1980) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p3654) ∨ (¬ p4037) := by
  classical
  tauto

theorem initial16555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4037)) := by
  have source := ElevenTheory.theory5859 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule16555 (meaning t m 1980) (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2997) (meaning t m 3551) (meaning t m 3654) (meaning t m 4037) source

theorem rule16556 (p1999 p2027 p2657 p2688 p2727 p2797 p3323 p3361 : Prop) (h : p2688 ∨ (¬ p3361) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p1999) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2727)) : (¬ p1999) ∨ (p2027) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3361) := by
  classical
  tauto

theorem initial16556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3361)) := by
  have source := ElevenTheory.theory5860 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 9)
  exact rule16556 (meaning t m 1999) (meaning t m 2027) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 2797) (meaning t m 3323) (meaning t m 3361) source

theorem rule16558 (p1987 p2027 p2177 p2696 p2997 p3425 p3548 p3576 : Prop) (h : (¬ p1987) ∨ p2997 ∨ p2027 ∨ (¬ p3576) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p2177) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2696) ∨ (p2997) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3576) := by
  classical
  tauto

theorem initial16558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) := by
  have source := ElevenTheory.theory5862 t (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16558 (meaning t m 1987) (meaning t m 2027) (meaning t m 2177) (meaning t m 2696) (meaning t m 2997) (meaning t m 3425) (meaning t m 3548) (meaning t m 3576) source

theorem rule16559 (p1978 p2027 p2938 p2992 p2996 p3115 p3699 p4032 : Prop) (h : (¬ p2996) ∨ (¬ p1978) ∨ p2027 ∨ (¬ p3699) ∨ (¬ p4032) ∨ (¬ p2992) ∨ (¬ p3115) ∨ p2938) : (¬ p1978) ∨ (p2027) ∨ (p2938) ∨ (¬ p2992) ∨ (¬ p2996) ∨ (¬ p3115) ∨ (¬ p3699) ∨ (¬ p4032) := by
  classical
  tauto

theorem initial16559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4032)) := by
  have source := ElevenTheory.theory5863 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7) (m.theta 5 9)
  exact rule16559 (meaning t m 1978) (meaning t m 2027) (meaning t m 2938) (meaning t m 2992) (meaning t m 2996) (meaning t m 3115) (meaning t m 3699) (meaning t m 4032) source

theorem rule16566 (p1991 p2027 p2737 p2842 p2952 p3136 p3585 : Prop) (h : p2842 ∨ (¬ p1991) ∨ (¬ p2952) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3136)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2737) ∨ (p2842) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial16566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory5870 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule16566 (meaning t m 1991) (meaning t m 2027) (meaning t m 2737) (meaning t m 2842) (meaning t m 2952) (meaning t m 3136) (meaning t m 3585) source

theorem rule16567 (p1984 p2027 p2542 p2545 p3585 p3684 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p1984) ∨ p2545 ∨ (¬ p3684) ∨ (¬ p2542)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2542) ∨ (p2545) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5871 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule16567 (meaning t m 1984) (meaning t m 2027) (meaning t m 2542) (meaning t m 2545) (meaning t m 3585) (meaning t m 3684) (meaning t m 3954) source

theorem rule16568 (p2010 p2027 p2657 p2688 p2727 p3516 p4104 p4278 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2010) ∨ p2688 ∨ (¬ p3516) ∨ (¬ p4104) ∨ (¬ p4278)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3516) ∨ (¬ p4104) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16568 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5872 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule16568 (meaning t m 2010) (meaning t m 2027) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3516) (meaning t m 4104) (meaning t m 4278) source

theorem rule16569 (p1990 p2027 p2563 p2688 p2992 p3156 p3880 : Prop) (h : (¬ p3880) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p2992) ∨ (¬ p2563) ∨ p2688 ∨ (¬ p3156)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2688) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial16569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory5873 t (m.theta 1 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8)
  exact rule16569 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2688) (meaning t m 2992) (meaning t m 3156) (meaning t m 3880) source

theorem rule16571 (p1997 p2027 p2331 p2657 p2688 p2727 p3986 p4110 : Prop) (h : (¬ p1997) ∨ p2688 ∨ (¬ p4110) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2657) ∨ (¬ p3986)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p3986) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16571 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5875 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule16571 (meaning t m 1997) (meaning t m 2027) (meaning t m 2331) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 3986) (meaning t m 4110) source

theorem rule16572 (p2010 p2299 p2633 p4276 : Prop) (h : p2633 ∨ (¬ p2010) ∨ (¬ p2299) ∨ p4276) : (¬ p2010) ∨ (¬ p2299) ∨ (p2633) ∨ (p4276) := by
  classical
  tauto

theorem initial16572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (meaning t m 4276) := by
  have source := ElevenTheory.theory5876 t (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16572 (meaning t m 2010) (meaning t m 2299) (meaning t m 2633) (meaning t m 4276) source

theorem rule16574 (p2010 p2027 p2579 p2764 p3389 p4137 p4191 : Prop) (h : p2027 ∨ (¬ p4191) ∨ (¬ p4137) ∨ p2764 ∨ (¬ p2579) ∨ (¬ p2010) ∨ (¬ p3389)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2579) ∨ (p2764) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5878 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 7) (m.theta 6 9) (m.theta 9 10)
  exact rule16574 (meaning t m 2010) (meaning t m 2027) (meaning t m 2579) (meaning t m 2764) (meaning t m 3389) (meaning t m 4137) (meaning t m 4191) source

theorem rule16576 (p3984 p3986 p4203 : Prop) (h : (¬ p4203) ∨ (¬ p3984) ∨ p3986) : (¬ p3984) ∨ (p3986) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial16576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3984)) ∨ (meaning t m 3986) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory5880 (m.theta 3 6) (m.theta 4 6) (m.theta 5 6)
  exact rule16576 (meaning t m 3984) (meaning t m 3986) (meaning t m 4203) source

theorem rule16580 (p2470 p2579 p3573 : Prop) (h : (¬ p3573) ∨ (¬ p2579) ∨ (¬ p2470)) : (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3573) := by
  classical
  tauto

theorem initial16580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3573)) := by
  have source := ElevenTheory.theory5884 (m.theta 0 4) (m.theta 4 6) (m.theta 4 8)
  exact rule16580 (meaning t m 2470) (meaning t m 2579) (meaning t m 3573) source

theorem rule16581 (p1994 p2027 p2766 p3266 p3322 p3574 p3956 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p1994) ∨ (¬ p3322) ∨ p2027 ∨ (¬ p3574) ∨ p2766 ∨ (¬ p3956) ∨ (¬ p3266)) : (¬ p1994) ∨ (p2027) ∨ (p2766) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5885 t (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16581 (meaning t m 1994) (meaning t m 2027) (meaning t m 2766) (meaning t m 3266) (meaning t m 3322) (meaning t m 3574) (meaning t m 3956) (meaning t m 4191) source

theorem rule16582 (p1994 p2027 p2387 p2504 p2764 p3204 p3574 p4347 p4444 : Prop) (h : (¬ p3204) ∨ p2764 ∨ (¬ p2387) ∨ (¬ p4444) ∨ (¬ p4347) ∨ p2027 ∨ (¬ p2504) ∨ (¬ p1994) ∨ (¬ p3574)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2504) ∨ (p2764) ∨ (¬ p3204) ∨ (¬ p3574) ∨ (¬ p4347) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2504)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5886 t (m.theta 0 6) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16582 (meaning t m 1994) (meaning t m 2027) (meaning t m 2387) (meaning t m 2504) (meaning t m 2764) (meaning t m 3204) (meaning t m 3574) (meaning t m 4347) (meaning t m 4444) source

theorem rule16584 (p1976 p2027 p2299 p2396 p2633 p3425 p4324 : Prop) (h : (¬ p3425) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2396) ∨ p2633 ∨ (¬ p2299)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial16584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory5888 t (m.theta 0 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16584 (meaning t m 1976) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3425) (meaning t m 4324) source

theorem rule16585 (p1985 p2027 p2114 p2241 p2901 p2992 p3954 : Prop) (h : (¬ p1985) ∨ (¬ p2992) ∨ (¬ p2901) ∨ (¬ p2241) ∨ (¬ p3954) ∨ p2027 ∨ p2114) : (¬ p1985) ∨ (p2027) ∨ (p2114) ∨ (¬ p2241) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5889 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7)
  exact rule16585 (meaning t m 1985) (meaning t m 2027) (meaning t m 2114) (meaning t m 2241) (meaning t m 2901) (meaning t m 2992) (meaning t m 3954) source

theorem rule16588 (p1994 p2027 p2396 p2727 p2996 p2997 p3575 p4155 p4278 : Prop) (h : (¬ p1994) ∨ (¬ p2727) ∨ (¬ p3575) ∨ (¬ p2996) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p2396) ∨ p2997 ∨ (¬ p4155)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (p2997) ∨ (¬ p3575) ∨ (¬ p4155) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2996)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4155)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5892 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16588 (meaning t m 1994) (meaning t m 2027) (meaning t m 2396) (meaning t m 2727) (meaning t m 2996) (meaning t m 2997) (meaning t m 3575) (meaning t m 4155) (meaning t m 4278) source

theorem rule16589 (p1986 p2027 p2396 p2598 p2780 p2997 p3689 p4106 p4278 : Prop) (h : (¬ p2780) ∨ (¬ p1986) ∨ p2997 ∨ (¬ p4106) ∨ (¬ p2396) ∨ (¬ p3689) ∨ (¬ p4278) ∨ (¬ p2598) ∨ p2027) : (¬ p1986) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2598) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3689) ∨ (¬ p4106) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5893 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6) (m.theta 2 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16589 (meaning t m 1986) (meaning t m 2027) (meaning t m 2396) (meaning t m 2598) (meaning t m 2780) (meaning t m 2997) (meaning t m 3689) (meaning t m 4106) (meaning t m 4278) source

theorem rule16591 (p1994 p2027 p2202 p2373 p2573 p3574 p3904 p4120 : Prop) (h : (¬ p2573) ∨ p2027 ∨ (¬ p2373) ∨ p2202 ∨ (¬ p3574) ∨ (¬ p3904) ∨ (¬ p4120) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (p2202) ∨ (¬ p2373) ∨ (¬ p2573) ∨ (¬ p3574) ∨ (¬ p3904) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial16591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory5895 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule16591 (meaning t m 1994) (meaning t m 2027) (meaning t m 2202) (meaning t m 2373) (meaning t m 2573) (meaning t m 3574) (meaning t m 3904) (meaning t m 4120) source

theorem rule16593 (p1982 p2027 p2247 p2688 p3506 p3830 p3853 p4444 : Prop) (h : (¬ p3853) ∨ (¬ p2247) ∨ (¬ p3830) ∨ p2688 ∨ (¬ p3506) ∨ p2027 ∨ (¬ p4444) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3506) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3853)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5897 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16593 (meaning t m 1982) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3506) (meaning t m 3830) (meaning t m 3853) (meaning t m 4444) source

theorem rule16594 (p1982 p2027 p2299 p2396 p2633 p2761 p4444 : Prop) (h : p2027 ∨ (¬ p2396) ∨ (¬ p4444) ∨ (¬ p2761) ∨ p2633 ∨ (¬ p1982) ∨ (¬ p2299)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2761) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16594 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory5898 t (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16594 (meaning t m 1982) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 2761) (meaning t m 4444) source

theorem rule16595 (p1984 p2027 p2688 p2743 p2992 p3954 p4315 : Prop) (h : (¬ p2992) ∨ (¬ p4315) ∨ p2688 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3954) ∨ (¬ p2743)) : (¬ p1984) ∨ (p2027) ∨ (p2688) ∨ (¬ p2743) ∨ (¬ p2992) ∨ (¬ p3954) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory5899 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5)
  exact rule16595 (meaning t m 1984) (meaning t m 2027) (meaning t m 2688) (meaning t m 2743) (meaning t m 2992) (meaning t m 3954) (meaning t m 4315) source

theorem rule16597 (p1990 p2563 p3474 p4885 : Prop) (h : (¬ p1990) ∨ (¬ p2563) ∨ p3474 ∨ p4885) : (¬ p1990) ∨ (¬ p2563) ∨ (p3474) ∨ (p4885) := by
  classical
  tauto

theorem initial16597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 3474) ∨ (meaning t m 4885) := by
  have source := ElevenTheory.theory5901 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16597 (meaning t m 1990) (meaning t m 2563) (meaning t m 3474) (meaning t m 4885) source

theorem rule16602 (p1990 p2027 p2247 p2406 p2563 p2688 p3379 : Prop) (h : (¬ p1990) ∨ p2688 ∨ (¬ p2563) ∨ (¬ p2406) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3379)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2247) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (p2688) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial16602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory5906 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6)
  exact rule16602 (meaning t m 1990) (meaning t m 2027) (meaning t m 2247) (meaning t m 2406) (meaning t m 2563) (meaning t m 2688) (meaning t m 3379) source

theorem rule16603 (p1988 p2027 p2323 p2542 p2651 p2982 p3680 : Prop) (h : (¬ p2982) ∨ (¬ p2651) ∨ p2323 ∨ (¬ p2542) ∨ p2027 ∨ (¬ p1988) ∨ (¬ p3680)) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2982) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial16603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory5907 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule16603 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2542) (meaning t m 2651) (meaning t m 2982) (meaning t m 3680) source

theorem rule16604 (p1998 p2027 p2323 p2437 p2663 p2881 p3355 p3359 p3569 : Prop) (h : p2323 ∨ (¬ p2437) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3355) ∨ (¬ p2663) ∨ (¬ p3359) ∨ (¬ p3569)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2663) ∨ (¬ p2881) ∨ (¬ p3355) ∨ (¬ p3359) ∨ (¬ p3569) := by
  classical
  tauto

theorem initial16604 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3569)) := by
  have source := ElevenTheory.theory5908 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8)
  exact rule16604 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2663) (meaning t m 2881) (meaning t m 3355) (meaning t m 3359) (meaning t m 3569) source

theorem rule16605 (p1990 p2027 p2284 p2396 p2957 p2997 p3556 p3690 : Prop) (h : (¬ p2284) ∨ (¬ p2957) ∨ (¬ p1990) ∨ (¬ p3556) ∨ p2997 ∨ p2027 ∨ (¬ p2396) ∨ (¬ p3690)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2396) ∨ (¬ p2957) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial16605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2957)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory5909 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16605 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2396) (meaning t m 2957) (meaning t m 2997) (meaning t m 3556) (meaning t m 3690) source

theorem rule16610 (p2015 p2027 p2396 p2997 p3093 p3817 p4366 : Prop) (h : (¬ p2015) ∨ (¬ p3093) ∨ (¬ p3817) ∨ p2027 ∨ p2997 ∨ (¬ p2396) ∨ (¬ p4366)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3093) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5914 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16610 (meaning t m 2015) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3093) (meaning t m 3817) (meaning t m 4366) source

theorem rule16612 (p1988 p2027 p2210 p2247 p2688 p2972 p3680 : Prop) (h : (¬ p1988) ∨ p2027 ∨ p2688 ∨ (¬ p2247) ∨ (¬ p2210) ∨ (¬ p3680) ∨ (¬ p2972)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2972) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial16612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory5916 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 5 9) (m.theta 9 10)
  exact rule16612 (meaning t m 1988) (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 2972) (meaning t m 3680) source

theorem rule16613 (p1990 p2027 p2177 p2563 p2997 p3551 p4235 p4283 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p3551) ∨ (¬ p1990) ∨ (¬ p4283) ∨ (¬ p2177) ∨ (¬ p4235) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2563) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p4235) ∨ (¬ p4283) := by
  classical
  tauto

theorem initial16613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) := by
  have source := ElevenTheory.theory5917 t (m.theta 0 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16613 (meaning t m 1990) (meaning t m 2027) (meaning t m 2177) (meaning t m 2563) (meaning t m 2997) (meaning t m 3551) (meaning t m 4235) (meaning t m 4283) source

theorem rule16617 (p1998 p2027 p2396 p2997 p3821 p3998 p4590 p5558 : Prop) (h : (¬ p1998) ∨ (¬ p2396) ∨ p2997 ∨ (¬ p5558) ∨ (¬ p3821) ∨ (¬ p4590) ∨ p2027 ∨ (¬ p3998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3821) ∨ (¬ p3998) ∨ (¬ p4590) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial16617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory5921 t (m.theta 0 7) (m.theta 0 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 10)
  exact rule16617 (meaning t m 1998) (meaning t m 2027) (meaning t m 2396) (meaning t m 2997) (meaning t m 3821) (meaning t m 3998) (meaning t m 4590) (meaning t m 5558) source

theorem rule16619 (p2012 p2027 p2114 p2737 p2811 p3286 p3506 p4425 : Prop) (h : (¬ p2811) ∨ p2027 ∨ (¬ p3286) ∨ p2114 ∨ (¬ p2737) ∨ (¬ p4425) ∨ (¬ p2012) ∨ (¬ p3506)) : (¬ p2012) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3286) ∨ (¬ p3506) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial16619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory5923 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule16619 (meaning t m 2012) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2811) (meaning t m 3286) (meaning t m 3506) (meaning t m 4425) source

theorem rule16620 (p1988 p2027 p2323 p2651 p2810 p3506 p3755 : Prop) (h : p2323 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p1988) ∨ (¬ p3506) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (p2323) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3506) ∨ (¬ p3755) := by
  classical
  tauto

theorem initial16620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3755)) := by
  have source := ElevenTheory.theory5924 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 9 10)
  exact rule16620 (meaning t m 1988) (meaning t m 2027) (meaning t m 2323) (meaning t m 2651) (meaning t m 2810) (meaning t m 3506) (meaning t m 3755) source

theorem rule16623 (p1976 p2027 p2138 p2187 p2997 p3097 p4193 p4358 : Prop) (h : p2997 ∨ (¬ p1976) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p4193) ∨ (¬ p2187) ∨ (¬ p4358)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2187) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p4193) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial16623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory5927 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16623 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2187) (meaning t m 2997) (meaning t m 3097) (meaning t m 4193) (meaning t m 4358) source

theorem rule16624 (p2927 p3631 p4278 : Prop) (h : (¬ p3631) ∨ (¬ p4278) ∨ (¬ p2927)) : (¬ p2927) ∨ (¬ p3631) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5928 (m.theta 1 7) (m.theta 4 7) (m.theta 7 9)
  exact rule16624 (meaning t m 2927) (meaning t m 3631) (meaning t m 4278) source

theorem rule16625 (p1979 p2027 p2156 p2396 p2997 p3821 p3952 p4984 : Prop) (h : (¬ p3821) ∨ (¬ p4984) ∨ p2027 ∨ p2997 ∨ (¬ p2156) ∨ (¬ p1979) ∨ (¬ p3952) ∨ (¬ p2396)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2156) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3821) ∨ (¬ p3952) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial16625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory5929 t (m.theta 0 5) (m.theta 0 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16625 (meaning t m 1979) (meaning t m 2027) (meaning t m 2156) (meaning t m 2396) (meaning t m 2997) (meaning t m 3821) (meaning t m 3952) (meaning t m 4984) source

theorem rule16632 (p1994 p2027 p2247 p2688 p3222 p3359 p3379 : Prop) (h : (¬ p3379) ∨ (¬ p3359) ∨ p2688 ∨ p2027 ∨ (¬ p2247) ∨ (¬ p1994) ∨ (¬ p3222)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3222) ∨ (¬ p3359) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial16632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory5936 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 9)
  exact rule16632 (meaning t m 1994) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3222) (meaning t m 3359) (meaning t m 3379) source

theorem rule16635 (p1997 p2027 p2396 p2761 p2997 p4322 p4948 : Prop) (h : p2997 ∨ (¬ p1997) ∨ (¬ p4322) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4948)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (p2997) ∨ (¬ p4322) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2761)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory5939 t (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16635 (meaning t m 1997) (meaning t m 2027) (meaning t m 2396) (meaning t m 2761) (meaning t m 2997) (meaning t m 4322) (meaning t m 4948) source

theorem rule16636 (p1989 p2027 p2210 p2396 p2997 p3817 p4366 : Prop) (h : (¬ p4366) ∨ p2997 ∨ (¬ p3817) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p1989) ∨ (¬ p2210)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2396) ∨ (p2997) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5940 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16636 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2396) (meaning t m 2997) (meaning t m 3817) (meaning t m 4366) source

theorem rule16637 (p2005 p2027 p2247 p2688 p3016 p3232 p3359 p3830 : Prop) (h : (¬ p3232) ∨ p2688 ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p2005) ∨ (¬ p3359) ∨ (¬ p3016)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p3016) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3830) := by
  classical
  tauto

theorem initial16637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3232)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3830)) := by
  have source := ElevenTheory.theory5941 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 9) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9)
  exact rule16637 (meaning t m 2005) (meaning t m 2027) (meaning t m 2247) (meaning t m 2688) (meaning t m 3016) (meaning t m 3232) (meaning t m 3359) (meaning t m 3830) source

theorem rule16642 (p1989 p2027 p2210 p2938 p3246 p3817 p4366 : Prop) (h : (¬ p1989) ∨ (¬ p3817) ∨ p2027 ∨ (¬ p2210) ∨ p2938 ∨ (¬ p3246) ∨ (¬ p4366)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5946 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 9)
  exact rule16642 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2938) (meaning t m 3246) (meaning t m 3817) (meaning t m 4366) source

theorem rule16644 (p1979 p2027 p2148 p2860 p3051 p3694 p3747 p3952 : Prop) (h : (¬ p3051) ∨ p2148 ∨ (¬ p1979) ∨ (¬ p3694) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p3747) ∨ (¬ p2860)) : (¬ p1979) ∨ (p2027) ∨ (p2148) ∨ (¬ p2860) ∨ (¬ p3051) ∨ (¬ p3694) ∨ (¬ p3747) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial16644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory5948 t (m.theta 0 5) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule16644 (meaning t m 1979) (meaning t m 2027) (meaning t m 2148) (meaning t m 2860) (meaning t m 3051) (meaning t m 3694) (meaning t m 3747) (meaning t m 3952) source

theorem rule16647 (p1992 p2027 p2608 p2766 p3591 p3923 p4347 : Prop) (h : (¬ p1992) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3923) ∨ p2766 ∨ (¬ p2608) ∨ (¬ p3591)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2608) ∨ (p2766) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory5951 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16647 (meaning t m 1992) (meaning t m 2027) (meaning t m 2608) (meaning t m 2766) (meaning t m 3591) (meaning t m 3923) (meaning t m 4347) source

theorem rule16648 (p1994 p2027 p2440 p2766 p3646 p3989 p4031 p4347 : Prop) (h : (¬ p1994) ∨ (¬ p4031) ∨ p2027 ∨ p2766 ∨ (¬ p3646) ∨ (¬ p2440) ∨ (¬ p3989) ∨ (¬ p4347)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2440) ∨ (p2766) ∨ (¬ p3646) ∨ (¬ p3989) ∨ (¬ p4031) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory5952 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16648 (meaning t m 1994) (meaning t m 2027) (meaning t m 2440) (meaning t m 2766) (meaning t m 3646) (meaning t m 3989) (meaning t m 4031) (meaning t m 4347) source

theorem rule16651 (p1989 p2230 p2233 p4629 : Prop) (h : p4629 ∨ p2233 ∨ (¬ p2230) ∨ (¬ p1989)) : (¬ p1989) ∨ (¬ p2230) ∨ (p2233) ∨ (p4629) := by
  classical
  tauto

theorem initial16651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (meaning t m 4629) := by
  have source := ElevenTheory.theory5955 t (m.theta 0 4) (m.theta 1 5) (m.theta 4 5)
  exact rule16651 (meaning t m 1989) (meaning t m 2230) (meaning t m 2233) (meaning t m 4629) source

theorem rule16652 (p3193 p3487 p5175 p5176 : Prop) (h : (¬ p3487) ∨ (¬ p3193) ∨ (¬ p5175) ∨ (¬ p5176)) : (¬ p3193) ∨ (¬ p3487) ∨ (¬ p5175) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial16652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 5175)) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory5956 (m.theta 1 4) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9)
  exact rule16652 (meaning t m 3193) (meaning t m 3487) (meaning t m 5175) (meaning t m 5176) source

theorem rule16653 (p1994 p2027 p2177 p2440 p2997 p3556 p3570 p4031 : Prop) (h : p2997 ∨ (¬ p1994) ∨ (¬ p2440) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4031) ∨ (¬ p2177)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2440) ∨ (p2997) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4031) := by
  classical
  tauto

theorem initial16653 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4031)) := by
  have source := ElevenTheory.theory5957 t (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16653 (meaning t m 1994) (meaning t m 2027) (meaning t m 2177) (meaning t m 2440) (meaning t m 2997) (meaning t m 3556) (meaning t m 3570) (meaning t m 4031) source

theorem rule16654 (p2440 p2590 p3574 : Prop) (h : (¬ p2440) ∨ (¬ p2590) ∨ p3574) : (¬ p2440) ∨ (¬ p2590) ∨ (p3574) := by
  classical
  tauto

theorem initial16654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2590)) ∨ (meaning t m 3574) := by
  have source := ElevenTheory.theory5958 (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16654 (meaning t m 2440) (meaning t m 2590) (meaning t m 3574) source

theorem rule16655 (p1980 p2027 p2860 p2938 p3737 p4244 p5717 : Prop) (h : (¬ p3737) ∨ p2027 ∨ (¬ p4244) ∨ p2938 ∨ (¬ p1980) ∨ (¬ p5717) ∨ (¬ p2860)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2860) ∨ (p2938) ∨ (¬ p3737) ∨ (¬ p4244) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial16655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2860)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory5959 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 10)
  exact rule16655 (meaning t m 1980) (meaning t m 2027) (meaning t m 2860) (meaning t m 2938) (meaning t m 3737) (meaning t m 4244) (meaning t m 5717) source

theorem rule16657 (p1997 p2027 p2192 p2210 p2247 p2688 p4110 : Prop) (h : (¬ p1997) ∨ (¬ p4110) ∨ (¬ p2210) ∨ p2027 ∨ p2688 ∨ (¬ p2247) ∨ (¬ p2192)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16657 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory5961 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16657 (meaning t m 1997) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 4110) source

theorem rule16658 (p1996 p2148 p3051 p4280 : Prop) (h : (¬ p1996) ∨ p2148 ∨ p4280 ∨ (¬ p3051)) : (¬ p1996) ∨ (p2148) ∨ (¬ p3051) ∨ (p4280) := by
  classical
  tauto

theorem initial16658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 3051)) ∨ (meaning t m 4280) := by
  have source := ElevenTheory.theory5962 t (m.theta 0 5) (m.theta 3 7) (m.theta 5 7)
  exact rule16658 (meaning t m 1996) (meaning t m 2148) (meaning t m 3051) (meaning t m 4280) source

theorem rule16659 (p1994 p2027 p2252 p2396 p2727 p2997 p3414 p3740 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3740) ∨ (¬ p2252) ∨ (¬ p2396) ∨ p2997 ∨ p2027 ∨ (¬ p2727) ∨ (¬ p1994) ∨ (¬ p3414)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2727) ∨ (p2997) ∨ (¬ p3414) ∨ (¬ p3740) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16659 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3740)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory5963 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16659 (meaning t m 1994) (meaning t m 2027) (meaning t m 2252) (meaning t m 2396) (meaning t m 2727) (meaning t m 2997) (meaning t m 3414) (meaning t m 3740) (meaning t m 4278) source

theorem rule16660 (p2002 p2027 p2299 p2396 p2633 p2774 p3820 p3821 : Prop) (h : (¬ p2002) ∨ p2633 ∨ (¬ p3820) ∨ (¬ p2396) ∨ (¬ p2299) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p2774)) : (¬ p2002) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2774) ∨ (¬ p3820) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial16660 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory5964 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16660 (meaning t m 2002) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 2774) (meaning t m 3820) (meaning t m 3821) source

theorem rule16661 (p1984 p2027 p2299 p2633 p2780 p2829 p3588 p3873 p4471 : Prop) (h : p2633 ∨ (¬ p1984) ∨ (¬ p2780) ∨ (¬ p2299) ∨ (¬ p3588) ∨ (¬ p3873) ∨ p2027 ∨ (¬ p4471) ∨ (¬ p2829)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2780) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial16661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory5965 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16661 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2780) (meaning t m 2829) (meaning t m 3588) (meaning t m 3873) (meaning t m 4471) source

theorem rule16662 (p1984 p2027 p2299 p2633 p3688 p3822 p3954 : Prop) (h : p2633 ∨ (¬ p1984) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p3822)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory5966 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16662 (meaning t m 1984) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3688) (meaning t m 3822) (meaning t m 3954) source

theorem rule16665 (p1994 p2027 p2299 p2396 p2633 p3742 p3821 p4279 : Prop) (h : (¬ p2299) ∨ (¬ p3821) ∨ p2633 ∨ (¬ p4279) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p1994) ∨ (¬ p3742)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3742) ∨ (¬ p3821) ∨ (¬ p4279) := by
  classical
  tauto

theorem initial16665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4279)) := by
  have source := ElevenTheory.theory5969 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16665 (meaning t m 1994) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3742) (meaning t m 3821) (meaning t m 4279) source

theorem rule16667 (p1990 p2027 p2114 p2132 p2563 p2737 p3365 p3695 : Prop) (h : (¬ p1990) ∨ (¬ p2563) ∨ (¬ p2737) ∨ p2114 ∨ (¬ p2132) ∨ p2027 ∨ (¬ p3695) ∨ (¬ p3365)) : (¬ p1990) ∨ (p2027) ∨ (p2114) ∨ (¬ p2132) ∨ (¬ p2563) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3695) := by
  classical
  tauto

theorem initial16667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3695)) := by
  have source := ElevenTheory.theory5971 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16667 (meaning t m 1990) (meaning t m 2027) (meaning t m 2114) (meaning t m 2132) (meaning t m 2563) (meaning t m 2737) (meaning t m 3365) (meaning t m 3695) source

theorem rule16668 (p1997 p2027 p2542 p2651 p2737 p2811 p2842 p3585 : Prop) (h : p2027 ∨ (¬ p1997) ∨ (¬ p2737) ∨ (¬ p2651) ∨ p2842 ∨ (¬ p3585) ∨ (¬ p2542) ∨ (¬ p2811)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial16668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory5972 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule16668 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 2842) (meaning t m 3585) source

theorem rule16669 (p1990 p2027 p2169 p2284 p3497 p3979 p5568 : Prop) (h : (¬ p2284) ∨ (¬ p3497) ∨ p2027 ∨ (¬ p3979) ∨ p2169 ∨ (¬ p1990) ∨ (¬ p5568)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3979) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial16669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory5973 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10)
  exact rule16669 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2284) (meaning t m 3497) (meaning t m 3979) (meaning t m 5568) source

theorem rule16671 (p1982 p2027 p2528 p2611 p3166 p4009 p4117 p4286 : Prop) (h : p2611 ∨ (¬ p4117) ∨ p2027 ∨ (¬ p1982) ∨ (¬ p4286) ∨ (¬ p2528) ∨ (¬ p4009) ∨ (¬ p3166)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2528) ∨ (p2611) ∨ (¬ p3166) ∨ (¬ p4009) ∨ (¬ p4117) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial16671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory5975 t (m.theta 0 2) (m.theta 0 3) (m.theta 3 8) (m.theta 4 8) (m.theta 8 10) (m.theta 8 9)
  exact rule16671 (meaning t m 1982) (meaning t m 2027) (meaning t m 2528) (meaning t m 2611) (meaning t m 3166) (meaning t m 4009) (meaning t m 4117) (meaning t m 4286) source

theorem rule16674 (p1990 p2027 p2169 p2563 p3645 p3979 p4120 p4210 p5568 : Prop) (h : (¬ p3645) ∨ p2169 ∨ (¬ p3979) ∨ (¬ p4120) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p4210) ∨ (¬ p1990) ∨ (¬ p5568)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2563) ∨ (¬ p3645) ∨ (¬ p3979) ∨ (¬ p4120) ∨ (¬ p4210) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial16674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory5978 t (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 10)
  exact rule16674 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2563) (meaning t m 3645) (meaning t m 3979) (meaning t m 4120) (meaning t m 4210) (meaning t m 5568) source

theorem rule16676 (p2003 p2027 p2299 p2633 p3483 p3822 p3946 : Prop) (h : (¬ p2299) ∨ (¬ p2003) ∨ p2633 ∨ p2027 ∨ (¬ p3822) ∨ (¬ p3483) ∨ (¬ p3946)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial16676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory5980 t (m.theta 0 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule16676 (meaning t m 2003) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3483) (meaning t m 3822) (meaning t m 3946) source

theorem rule16677 (p1989 p2027 p2210 p2633 p3860 p3969 p4132 p5693 : Prop) (h : (¬ p3860) ∨ (¬ p1989) ∨ p2027 ∨ p2633 ∨ (¬ p2210) ∨ (¬ p5693) ∨ (¬ p3969) ∨ (¬ p4132)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2633) ∨ (¬ p3860) ∨ (¬ p3969) ∨ (¬ p4132) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial16677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory5981 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10)
  exact rule16677 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2633) (meaning t m 3860) (meaning t m 3969) (meaning t m 4132) (meaning t m 5693) source

theorem rule16678 (p1989 p2027 p2210 p2633 p3860 p3906 p3941 p5568 : Prop) (h : (¬ p3906) ∨ (¬ p1989) ∨ (¬ p3860) ∨ (¬ p2210) ∨ p2633 ∨ p2027 ∨ (¬ p3941) ∨ (¬ p5568)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2633) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p3941) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial16678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory5982 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10)
  exact rule16678 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2633) (meaning t m 3860) (meaning t m 3906) (meaning t m 3941) (meaning t m 5568) source

theorem rule16679 (p1979 p2027 p2299 p2951 p3097 p3646 p3982 p5558 : Prop) (h : p2951 ∨ p3982 ∨ (¬ p5558) ∨ (¬ p3646) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2299)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2299) ∨ (p2951) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (p3982) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial16679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2951) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (meaning t m 3982) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory5983 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule16679 (meaning t m 1979) (meaning t m 2027) (meaning t m 2299) (meaning t m 2951) (meaning t m 3097) (meaning t m 3646) (meaning t m 3982) (meaning t m 5558) source

theorem rule16681 (p1985 p2027 p2764 p3051 p3646 p3744 p4191 : Prop) (h : p2764 ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p1985) ∨ (¬ p3051)) : (¬ p1985) ∨ (p2027) ∨ (p2764) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory5985 t (m.theta 0 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9) (m.theta 9 10)
  exact rule16681 (meaning t m 1985) (meaning t m 2027) (meaning t m 2764) (meaning t m 3051) (meaning t m 3646) (meaning t m 3744) (meaning t m 4191) source

theorem rule16682 (p1982 p2027 p2373 p2598 p2611 p2850 p3146 : Prop) (h : (¬ p1982) ∨ p2611 ∨ (¬ p2598) ∨ (¬ p2850) ∨ p2027 ∨ (¬ p2373) ∨ (¬ p3146)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2373) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2850) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial16682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory5986 t (m.theta 0 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16682 (meaning t m 1982) (meaning t m 2027) (meaning t m 2373) (meaning t m 2598) (meaning t m 2611) (meaning t m 2850) (meaning t m 3146) source

theorem rule16684 (p1982 p2027 p2688 p2952 p2992 p3166 p3256 : Prop) (h : (¬ p2952) ∨ p2688 ∨ p2027 ∨ (¬ p2992) ∨ (¬ p3256) ∨ (¬ p3166) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2688) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3166) ∨ (¬ p3256) := by
  classical
  tauto

theorem initial16684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3256)) := by
  have source := ElevenTheory.theory5988 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule16684 (meaning t m 1982) (meaning t m 2027) (meaning t m 2688) (meaning t m 2952) (meaning t m 2992) (meaning t m 3166) (meaning t m 3256) source

theorem rule16685 (p1992 p2027 p2396 p2608 p2997 p3817 p4366 : Prop) (h : (¬ p2396) ∨ p2027 ∨ p2997 ∨ (¬ p4366) ∨ (¬ p1992) ∨ (¬ p2608) ∨ (¬ p3817)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (p2997) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial16685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory5989 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16685 (meaning t m 1992) (meaning t m 2027) (meaning t m 2396) (meaning t m 2608) (meaning t m 2997) (meaning t m 3817) (meaning t m 4366) source

theorem rule16686 (p2005 p2027 p2396 p2573 p2997 p3540 p3658 p4324 : Prop) (h : (¬ p4324) ∨ (¬ p2005) ∨ p2027 ∨ p2997 ∨ (¬ p3540) ∨ (¬ p3658) ∨ (¬ p2573) ∨ (¬ p2396)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2396) ∨ (¬ p2573) ∨ (p2997) ∨ (¬ p3540) ∨ (¬ p3658) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial16686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory5990 t (m.theta 0 4) (m.theta 2 7) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule16686 (meaning t m 2005) (meaning t m 2027) (meaning t m 2396) (meaning t m 2573) (meaning t m 2997) (meaning t m 3540) (meaning t m 3658) (meaning t m 4324) source

theorem rule16687 (p1988 p2027 p2406 p2589 p2688 p3276 p3355 p4281 : Prop) (h : p2688 ∨ p2027 ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4281) ∨ (¬ p1988) ∨ (¬ p2406) ∨ (¬ p2589)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (p2688) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial16687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory5991 t (m.theta 0 4) (m.theta 1 3) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule16687 (meaning t m 1988) (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2688) (meaning t m 3276) (meaning t m 3355) (meaning t m 4281) source

theorem rule16688 (p1989 p2027 p2177 p2210 p2997 p3570 p4366 p4909 : Prop) (h : (¬ p2177) ∨ (¬ p4909) ∨ p2997 ∨ (¬ p3570) ∨ (¬ p4366) ∨ (¬ p2210) ∨ (¬ p1989) ∨ p2027) : (¬ p1989) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2210) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p4366) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial16688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory5992 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16688 (meaning t m 1989) (meaning t m 2027) (meaning t m 2177) (meaning t m 2210) (meaning t m 2997) (meaning t m 3570) (meaning t m 4366) (meaning t m 4909) source

theorem rule16690 (p2247 p2749 p3954 : Prop) (h : (¬ p2247) ∨ (¬ p2749) ∨ p3954) : (¬ p2247) ∨ (¬ p2749) ∨ (p3954) := by
  classical
  tauto

theorem initial16690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2749)) ∨ (meaning t m 3954) := by
  have source := ElevenTheory.theory5994 (m.theta 0 1) (m.theta 1 2) (m.theta 1 3)
  exact rule16690 (meaning t m 2247) (meaning t m 2749) (meaning t m 3954) source

theorem rule16725 (p1998 p2027 p2114 p3449 p3954 p4181 p5558 : Prop) (h : (¬ p1998) ∨ (¬ p3954) ∨ p2114 ∨ p2027 ∨ (¬ p4181) ∨ (¬ p5558) ∨ (¬ p3449)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial16725 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory5997 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 7 8) (m.theta 8 10)
  exact rule16725 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 3449) (meaning t m 3954) (meaning t m 4181) (meaning t m 5558) source

theorem rule16727 (p1982 p2027 p2114 p2737 p2811 p2946 p3146 p3156 : Prop) (h : (¬ p1982) ∨ (¬ p2737) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ p2114 ∨ (¬ p2811) ∨ p2027) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial16727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory5999 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16727 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2737) (meaning t m 2811) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) source

theorem rule16729 (p1980 p2323 p2946 p4566 : Prop) (h : (¬ p1980) ∨ (¬ p2946) ∨ p2323 ∨ p4566) : (¬ p1980) ∨ (p2323) ∨ (¬ p2946) ∨ (p4566) := by
  classical
  tauto

theorem initial16729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 4566) := by
  have source := ElevenTheory.theory6001 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6)
  exact rule16729 (meaning t m 1980) (meaning t m 2323) (meaning t m 2946) (meaning t m 4566) source

theorem rule16730 (p1982 p2027 p2114 p2528 p2651 p2737 p2811 p3083 : Prop) (h : (¬ p3083) ∨ p2114 ∨ (¬ p2811) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p1982) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (p2114) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3083) := by
  classical
  tauto

theorem initial16730 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3083)) := by
  have source := ElevenTheory.theory6002 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 8) (m.theta 8 9)
  exact rule16730 (meaning t m 1982) (meaning t m 2027) (meaning t m 2114) (meaning t m 2528) (meaning t m 2651) (meaning t m 2737) (meaning t m 2811) (meaning t m 3083) source

theorem rule16735 (p2003 p2027 p2177 p2997 p3319 p3548 p3946 p4105 : Prop) (h : (¬ p2003) ∨ p2027 ∨ (¬ p3946) ∨ p2997 ∨ (¬ p3319) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p2177)) : (¬ p2003) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3319) ∨ (¬ p3548) ∨ (¬ p3946) ∨ (¬ p4105) := by
  classical
  tauto

theorem initial16735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4105)) := by
  have source := ElevenTheory.theory6007 t (m.theta 0 6) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule16735 (meaning t m 2003) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3319) (meaning t m 3548) (meaning t m 3946) (meaning t m 4105) source

theorem rule16736 (p1982 p2027 p2323 p2373 p2542 p2651 p3146 : Prop) (h : p2323 ∨ (¬ p1982) ∨ (¬ p2373) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2651) ∨ (¬ p2542)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3146) := by
  classical
  tauto

theorem initial16736 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3146)) := by
  have source := ElevenTheory.theory6008 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16736 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2373) (meaning t m 2542) (meaning t m 2651) (meaning t m 3146) source

theorem rule16737 (p1997 p2027 p2241 p2493 p2542 p2699 p3574 p4281 : Prop) (h : (¬ p2241) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p2542) ∨ (¬ p3574) ∨ (¬ p4281) ∨ (¬ p2493) ∨ p2699) : (¬ p1997) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2493) ∨ (¬ p2542) ∨ (p2699) ∨ (¬ p3574) ∨ (¬ p4281) := by
  classical
  tauto

theorem initial16737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4281)) := by
  have source := ElevenTheory.theory6009 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16737 (meaning t m 1997) (meaning t m 2027) (meaning t m 2241) (meaning t m 2493) (meaning t m 2542) (meaning t m 2699) (meaning t m 3574) (meaning t m 4281) source

theorem rule16739 (p2012 p2230 p2233 p4953 : Prop) (h : p2233 ∨ p4953 ∨ (¬ p2230) ∨ (¬ p2012)) : (¬ p2012) ∨ (¬ p2230) ∨ (p2233) ∨ (p4953) := by
  classical
  tauto

theorem initial16739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (meaning t m 4953) := by
  have source := ElevenTheory.theory6011 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 9)
  exact rule16739 (meaning t m 2012) (meaning t m 2230) (meaning t m 2233) (meaning t m 4953) source

theorem rule16741 (p1999 p3043 p3125 p5043 : Prop) (h : (¬ p1999) ∨ p3043 ∨ (¬ p3125) ∨ p5043) : (¬ p1999) ∨ (p3043) ∨ (¬ p3125) ∨ (p5043) := by
  classical
  tauto

theorem initial16741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3125)) ∨ (meaning t m 5043) := by
  have source := ElevenTheory.theory6013 t (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule16741 (meaning t m 1999) (meaning t m 3043) (meaning t m 3125) (meaning t m 5043) source

theorem rule16742 (p1990 p2027 p2598 p2611 p2839 p2860 p3585 : Prop) (h : (¬ p2598) ∨ (¬ p2839) ∨ p2027 ∨ p2611 ∨ (¬ p2860) ∨ (¬ p1990) ∨ (¬ p3585)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial16742 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory6014 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6)
  exact rule16742 (meaning t m 1990) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 2839) (meaning t m 2860) (meaning t m 3585) source

theorem rule16744 (p1985 p2027 p2427 p2542 p2611 p2696 p2727 p2742 : Prop) (h : p2611 ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p1985) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2542)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2427) ∨ (¬ p2542) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) := by
  classical
  tauto

theorem initial16744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2742)) := by
  have source := ElevenTheory.theory6016 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule16744 (meaning t m 1985) (meaning t m 2027) (meaning t m 2427) (meaning t m 2542) (meaning t m 2611) (meaning t m 2696) (meaning t m 2727) (meaning t m 2742) source

theorem rule16745 (p1994 p2598 p2611 p4753 : Prop) (h : (¬ p1994) ∨ p2611 ∨ (¬ p2598) ∨ p4753) : (¬ p1994) ∨ (¬ p2598) ∨ (p2611) ∨ (p4753) := by
  classical
  tauto

theorem initial16745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (meaning t m 4753) := by
  have source := ElevenTheory.theory6017 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4)
  exact rule16745 (meaning t m 1994) (meaning t m 2598) (meaning t m 2611) (meaning t m 4753) source

theorem rule16746 (p1997 p2027 p2284 p2696 p2699 p3136 p3589 p4110 : Prop) (h : (¬ p4110) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p1997) ∨ p2699 ∨ (¬ p3589) ∨ (¬ p3136)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p3136) ∨ (¬ p3589) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6018 t (m.theta 0 1) (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule16746 (meaning t m 1997) (meaning t m 2027) (meaning t m 2284) (meaning t m 2696) (meaning t m 2699) (meaning t m 3136) (meaning t m 3589) (meaning t m 4110) source

theorem rule16748 (p1990 p2027 p2545 p2563 p2657 p2958 p3212 p4948 : Prop) (h : p2027 ∨ (¬ p2657) ∨ p2545 ∨ (¬ p1990) ∨ (¬ p2563) ∨ (¬ p3212) ∨ (¬ p4948) ∨ (¬ p2958)) : (¬ p1990) ∨ (p2027) ∨ (p2545) ∨ (¬ p2563) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3212) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory6020 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9)
  exact rule16748 (meaning t m 1990) (meaning t m 2027) (meaning t m 2545) (meaning t m 2563) (meaning t m 2657) (meaning t m 2958) (meaning t m 3212) (meaning t m 4948) source

theorem rule16755 (p1982 p2027 p2363 p2611 p2641 p2668 p2696 p2742 : Prop) (h : (¬ p2668) ∨ p2611 ∨ (¬ p1982) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2742) ∨ (¬ p2641) ∨ (¬ p2363)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (p2611) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2742) := by
  classical
  tauto

theorem initial16755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) := by
  have source := ElevenTheory.theory6027 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule16755 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2611) (meaning t m 2641) (meaning t m 2668) (meaning t m 2696) (meaning t m 2742) source

theorem rule16762 (p1990 p2027 p2307 p2387 p2766 p3097 p4347 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p2387) ∨ (¬ p3097) ∨ (¬ p4347) ∨ (¬ p1990) ∨ (¬ p2307)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (p2766) ∨ (¬ p3097) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial16762 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory6034 t (m.theta 0 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule16762 (meaning t m 1990) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2766) (meaning t m 3097) (meaning t m 4347) source

theorem rule16767 (p1985 p2027 p2264 p2611 p2696 p2742 p3027 p3570 : Prop) (h : (¬ p2696) ∨ (¬ p3027) ∨ (¬ p1985) ∨ (¬ p2742) ∨ (¬ p2264) ∨ p2027 ∨ p2611 ∨ (¬ p3570)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2264) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3027) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial16767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory6039 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule16767 (meaning t m 1985) (meaning t m 2027) (meaning t m 2264) (meaning t m 2611) (meaning t m 2696) (meaning t m 2742) (meaning t m 3027) (meaning t m 3570) source

theorem rule16770 (p1982 p2027 p2611 p2696 p2742 p2992 p3146 p3156 : Prop) (h : (¬ p1982) ∨ (¬ p2742) ∨ p2611 ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2696) ∨ (¬ p2992)) : (¬ p1982) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3156) := by
  classical
  tauto

theorem initial16770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) := by
  have source := ElevenTheory.theory6042 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16770 (meaning t m 1982) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2742) (meaning t m 2992) (meaning t m 3146) (meaning t m 3156) source

theorem rule16772 (p1990 p2027 p2563 p2938 p3105 p4244 p4948 : Prop) (h : p2938 ∨ (¬ p4948) ∨ (¬ p4244) ∨ p2027 ∨ (¬ p3105) ∨ (¬ p1990) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p3105) ∨ (¬ p4244) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory6044 t (m.theta 2 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule16772 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 3105) (meaning t m 4244) (meaning t m 4948) source

theorem rule16773 (p2024 p2027 p2598 p2611 p3276 p3333 p5284 : Prop) (h : p2027 ∨ p2611 ∨ (¬ p3333) ∨ (¬ p2024) ∨ (¬ p2598) ∨ (¬ p5284) ∨ (¬ p3276)) : (¬ p2024) ∨ (p2027) ∨ (¬ p2598) ∨ (p2611) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial16773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2024)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory6045 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 9) (m.theta 4 9) (m.theta 9 10)
  exact rule16773 (meaning t m 2024) (meaning t m 2027) (meaning t m 2598) (meaning t m 2611) (meaning t m 3276) (meaning t m 3333) (meaning t m 5284) source

theorem rule16774 (p2005 p2027 p2406 p2699 p3379 p3422 p3684 : Prop) (h : p2699 ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p2005)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p3379) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial16774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory6046 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule16774 (meaning t m 2005) (meaning t m 2027) (meaning t m 2406) (meaning t m 2699) (meaning t m 3379) (meaning t m 3422) (meaning t m 3684) source

theorem rule16775 (p1990 p2027 p2406 p2563 p2842 p2928 p3201 : Prop) (h : (¬ p1990) ∨ (¬ p2563) ∨ (¬ p2406) ∨ p2027 ∨ (¬ p2928) ∨ p2842 ∨ (¬ p3201)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2563) ∨ (p2842) ∨ (¬ p2928) ∨ (¬ p3201) := by
  classical
  tauto

theorem initial16775 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3201)) := by
  have source := ElevenTheory.theory6047 t (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6)
  exact rule16775 (meaning t m 1990) (meaning t m 2027) (meaning t m 2406) (meaning t m 2563) (meaning t m 2842) (meaning t m 2928) (meaning t m 3201) source

theorem rule16776 (p1975 p2027 p2230 p2233 p2274 p3422 p3684 p4203 : Prop) (h : p2027 ∨ p2233 ∨ (¬ p2274) ∨ (¬ p1975) ∨ (¬ p2230) ∨ (¬ p4203) ∨ (¬ p3684) ∨ (¬ p3422)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2274) ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4203) := by
  classical
  tauto

theorem initial16776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4203)) := by
  have source := ElevenTheory.theory6048 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16776 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2274) (meaning t m 3422) (meaning t m 3684) (meaning t m 4203) source

theorem rule16778 (p1977 p2699 p3093 p4756 : Prop) (h : (¬ p3093) ∨ p2699 ∨ (¬ p1977) ∨ p4756) : (¬ p1977) ∨ (p2699) ∨ (¬ p3093) ∨ (p4756) := by
  classical
  tauto

theorem initial16778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (meaning t m 4756) := by
  have source := ElevenTheory.theory6050 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6)
  exact rule16778 (meaning t m 1977) (meaning t m 2699) (meaning t m 3093) (meaning t m 4756) source

theorem rule16781 (p1990 p2027 p2210 p2699 p2860 p2891 p4244 : Prop) (h : (¬ p2210) ∨ (¬ p1990) ∨ p2699 ∨ p2027 ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p2891)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2860) ∨ (¬ p2891) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial16781 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6053 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16781 (meaning t m 1990) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2860) (meaning t m 2891) (meaning t m 4244) source

theorem rule16782 (p2000 p2598 p2611 p4727 : Prop) (h : p2611 ∨ p4727 ∨ (¬ p2000) ∨ (¬ p2598)) : (¬ p2000) ∨ (¬ p2598) ∨ (p2611) ∨ (p4727) := by
  classical
  tauto

theorem initial16782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2611) ∨ (meaning t m 4727) := by
  have source := ElevenTheory.theory6054 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 4)
  exact rule16782 (meaning t m 2000) (meaning t m 2598) (meaning t m 2611) (meaning t m 4727) source

theorem rule16783 (p1992 p2027 p2476 p2534 p2764 p3363 p3585 p4444 : Prop) (h : (¬ p2476) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p3363) ∨ (¬ p1992) ∨ p2764 ∨ (¬ p3585) ∨ (¬ p4444)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (p2764) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16783 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6055 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16783 (meaning t m 1992) (meaning t m 2027) (meaning t m 2476) (meaning t m 2534) (meaning t m 2764) (meaning t m 3363) (meaning t m 3585) (meaning t m 4444) source

theorem rule16784 (p2001 p2027 p2098 p2622 p3256 p3365 p3692 p4967 : Prop) (h : p2027 ∨ (¬ p2001) ∨ (¬ p4967) ∨ (¬ p3256) ∨ (¬ p2098) ∨ (¬ p3692) ∨ (¬ p3365) ∨ p2622) : (¬ p2001) ∨ (p2027) ∨ (¬ p2098) ∨ (p2622) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p3692) ∨ (¬ p4967) := by
  classical
  tauto

theorem initial16784 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4967)) := by
  have source := ElevenTheory.theory6056 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule16784 (meaning t m 2001) (meaning t m 2027) (meaning t m 2098) (meaning t m 2622) (meaning t m 3256) (meaning t m 3365) (meaning t m 3692) (meaning t m 4967) source

theorem rule16786 (p2001 p2881 p2938 p4902 : Prop) (h : p4902 ∨ p2938 ∨ (¬ p2881) ∨ (¬ p2001)) : (¬ p2001) ∨ (¬ p2881) ∨ (p2938) ∨ (p4902) := by
  classical
  tauto

theorem initial16786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (meaning t m 4902) := by
  have source := ElevenTheory.theory6058 t (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule16786 (meaning t m 2001) (meaning t m 2881) (meaning t m 2938) (meaning t m 4902) source

theorem rule16787 (p1992 p2027 p2589 p2766 p3363 p3585 p3692 p3880 : Prop) (h : (¬ p2589) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3585) ∨ p2766 ∨ (¬ p3880) ∨ (¬ p3692) ∨ (¬ p3363)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2589) ∨ (p2766) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial16787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory6059 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule16787 (meaning t m 1992) (meaning t m 2027) (meaning t m 2589) (meaning t m 2766) (meaning t m 3363) (meaning t m 3585) (meaning t m 3692) (meaning t m 3880) source

theorem rule16788 (p1992 p2027 p2313 p2764 p2785 p3688 p4107 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p2785) ∨ (¬ p2313) ∨ (¬ p1992) ∨ (¬ p3688) ∨ (¬ p4107) ∨ p2027 ∨ p2764) : (¬ p1992) ∨ (p2027) ∨ (¬ p2313) ∨ (p2764) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4107) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6060 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16788 (meaning t m 1992) (meaning t m 2027) (meaning t m 2313) (meaning t m 2764) (meaning t m 2785) (meaning t m 3688) (meaning t m 4107) (meaning t m 4381) source

theorem rule16789 (p1987 p2027 p2132 p2611 p2641 p2749 p3583 p4195 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p3583) ∨ p2611 ∨ (¬ p4195) ∨ (¬ p2749) ∨ (¬ p2641) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3583) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial16789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory6061 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6)
  exact rule16789 (meaning t m 1987) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2641) (meaning t m 2749) (meaning t m 3583) (meaning t m 4195) source

theorem rule16790 (p1980 p2027 p2132 p2611 p2737 p2797 p3583 : Prop) (h : p2027 ∨ (¬ p2132) ∨ (¬ p3583) ∨ p2611 ∨ (¬ p1980) ∨ (¬ p2737) ∨ (¬ p2797)) : (¬ p1980) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial16790 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory6062 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 6)
  exact rule16790 (meaning t m 1980) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2737) (meaning t m 2797) (meaning t m 3583) source

theorem rule16791 (p2010 p2027 p2406 p2699 p3201 p3379 p3684 : Prop) (h : (¬ p3379) ∨ (¬ p2010) ∨ (¬ p3201) ∨ (¬ p2406) ∨ p2699 ∨ p2027 ∨ (¬ p3684)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial16791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory6063 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7)
  exact rule16791 (meaning t m 2010) (meaning t m 2027) (meaning t m 2406) (meaning t m 2699) (meaning t m 3201) (meaning t m 3379) (meaning t m 3684) source

theorem rule16792 (p1979 p2027 p2696 p2699 p2743 p2829 p3589 p3952 p4185 : Prop) (h : p2699 ∨ (¬ p2829) ∨ (¬ p1979) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p4185) ∨ (¬ p3589) ∨ (¬ p2743) ∨ (¬ p2696)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p3589) ∨ (¬ p3952) ∨ (¬ p4185) := by
  classical
  tauto

theorem initial16792 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4185)) := by
  have source := ElevenTheory.theory6064 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6)
  exact rule16792 (meaning t m 1979) (meaning t m 2027) (meaning t m 2696) (meaning t m 2699) (meaning t m 2743) (meaning t m 2829) (meaning t m 3589) (meaning t m 3952) (meaning t m 4185) source

theorem rule16793 (p1978 p2210 p2699 p4522 : Prop) (h : p2699 ∨ p4522 ∨ (¬ p2210) ∨ (¬ p1978)) : (¬ p1978) ∨ (¬ p2210) ∨ (p2699) ∨ (p4522) := by
  classical
  tauto

theorem initial16793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (meaning t m 4522) := by
  have source := ElevenTheory.theory6065 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 5)
  exact rule16793 (meaning t m 1978) (meaning t m 2210) (meaning t m 2699) (meaning t m 4522) source

theorem rule16796 (p1999 p2027 p2241 p2699 p2727 p3016 p3564 : Prop) (h : p2699 ∨ (¬ p1999) ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3564) ∨ p2027) : (¬ p1999) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3564) := by
  classical
  tauto

theorem initial16796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3564)) := by
  have source := ElevenTheory.theory6068 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9)
  exact rule16796 (meaning t m 1999) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2727) (meaning t m 3016) (meaning t m 3564) source

theorem rule16799 (p1992 p2027 p2633 p3246 p3570 p3588 p4324 : Prop) (h : (¬ p3570) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4324) ∨ (¬ p3246) ∨ p2633 ∨ (¬ p3588)) : (¬ p1992) ∨ (p2027) ∨ (p2633) ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p3588) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial16799 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory6071 t (m.theta 1 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16799 (meaning t m 1992) (meaning t m 2027) (meaning t m 2633) (meaning t m 3246) (meaning t m 3570) (meaning t m 3588) (meaning t m 4324) source

theorem rule16801 (p1982 p2027 p2323 p2528 p2573 p2663 p3083 p3574 : Prop) (h : (¬ p3083) ∨ p2323 ∨ (¬ p3574) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p1982) ∨ (¬ p2528)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p3083) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial16801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory6073 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 8 9)
  exact rule16801 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2528) (meaning t m 2573) (meaning t m 2663) (meaning t m 3083) (meaning t m 3574) source

theorem rule16803 (p1997 p2027 p2545 p2657 p2946 p3156 p3880 : Prop) (h : (¬ p3880) ∨ (¬ p1997) ∨ (¬ p3156) ∨ p2545 ∨ (¬ p2657) ∨ (¬ p2946) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial16803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory6075 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 8)
  exact rule16803 (meaning t m 1997) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) (meaning t m 3156) (meaning t m 3880) source

theorem rule16804 (p2001 p2027 p2210 p2373 p2699 p2972 p4948 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p2373) ∨ (¬ p2972) ∨ (¬ p2210) ∨ (¬ p2001) ∨ (¬ p4948)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2373) ∨ (p2699) ∨ (¬ p2972) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2373)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory6076 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule16804 (meaning t m 2001) (meaning t m 2027) (meaning t m 2210) (meaning t m 2373) (meaning t m 2699) (meaning t m 2972) (meaning t m 4948) source

theorem rule16807 (p1985 p2027 p2545 p2657 p2807 p3032 p3527 p3570 : Prop) (h : (¬ p2807) ∨ p2545 ∨ (¬ p1985) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3032) ∨ (¬ p2657) ∨ p2027) : (¬ p1985) ∨ (p2027) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial16807 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory6079 t (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 8)
  exact rule16807 (meaning t m 1985) (meaning t m 2027) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 3032) (meaning t m 3527) (meaning t m 3570) source

theorem rule16808 (p1990 p2027 p2210 p2563 p2699 p2891 p4235 : Prop) (h : (¬ p2210) ∨ (¬ p2891) ∨ p2699 ∨ p2027 ∨ (¬ p4235) ∨ (¬ p1990) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2563) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial16808 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory6080 t (m.theta 0 1) (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16808 (meaning t m 1990) (meaning t m 2027) (meaning t m 2210) (meaning t m 2563) (meaning t m 2699) (meaning t m 2891) (meaning t m 4235) source

theorem rule16809 (p2010 p2027 p2264 p2545 p2657 p2807 p3644 : Prop) (h : (¬ p2657) ∨ (¬ p2807) ∨ p2545 ∨ (¬ p2010) ∨ p2027 ∨ (¬ p3644) ∨ (¬ p2264)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2264) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial16809 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory6081 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule16809 (meaning t m 2010) (meaning t m 2027) (meaning t m 2264) (meaning t m 2545) (meaning t m 2657) (meaning t m 2807) (meaning t m 3644) source

theorem rule16810 (p1977 p2027 p2764 p2957 p3556 p3662 p3690 p4381 : Prop) (h : p2764 ∨ p2027 ∨ (¬ p4381) ∨ (¬ p3690) ∨ (¬ p2957) ∨ (¬ p1977) ∨ (¬ p3556) ∨ (¬ p3662)) : (¬ p1977) ∨ (p2027) ∨ (p2764) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6082 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16810 (meaning t m 1977) (meaning t m 2027) (meaning t m 2764) (meaning t m 2957) (meaning t m 3556) (meaning t m 3662) (meaning t m 3690) (meaning t m 4381) source

theorem rule16811 (p1977 p2027 p2657 p2946 p3008 p3574 p3662 : Prop) (h : p3008 ∨ (¬ p3662) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p1977) ∨ (¬ p3574) ∨ (¬ p2657)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2657) ∨ (¬ p2946) ∨ (p3008) ∨ (¬ p3574) ∨ (¬ p3662) := by
  classical
  tauto

theorem initial16811 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3662)) := by
  have source := ElevenTheory.theory6083 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 6)
  exact rule16811 (meaning t m 1977) (meaning t m 2027) (meaning t m 2657) (meaning t m 2946) (meaning t m 3008) (meaning t m 3574) (meaning t m 3662) source

theorem rule16813 (p1998 p2027 p2608 p2699 p2911 p3201 p3367 : Prop) (h : p2699 ∨ (¬ p3367) ∨ (¬ p2911) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p3201) ∨ (¬ p2608)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial16813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory6085 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule16813 (meaning t m 1998) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2911) (meaning t m 3201) (meaning t m 3367) source

theorem rule16814 (p1997 p2027 p2287 p2406 p2499 p3323 p4137 : Prop) (h : p2287 ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4137) ∨ (¬ p2406) ∨ (¬ p3323) ∨ (¬ p2499)) : (¬ p1997) ∨ (p2027) ∨ (p2287) ∨ (¬ p2406) ∨ (¬ p2499) ∨ (¬ p3323) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial16814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory6086 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule16814 (meaning t m 1997) (meaning t m 2027) (meaning t m 2287) (meaning t m 2406) (meaning t m 2499) (meaning t m 3323) (meaning t m 4137) source

theorem rule16815 (p2008 p2027 p2114 p3399 p3527 p3659 p3954 : Prop) (h : (¬ p3954) ∨ p2114 ∨ (¬ p3527) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p2008)) : (¬ p2008) ∨ (p2027) ∨ (p2114) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial16815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2008)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory6087 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule16815 (meaning t m 2008) (meaning t m 2027) (meaning t m 2114) (meaning t m 3399) (meaning t m 3527) (meaning t m 3659) (meaning t m 3954) source

theorem rule16817 (p1995 p2027 p2274 p2765 p3379 p3549 p3591 : Prop) (h : (¬ p2274) ∨ p2765 ∨ (¬ p3379) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) := by
  classical
  tauto

theorem initial16817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3591)) := by
  have source := ElevenTheory.theory6089 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16817 (meaning t m 1995) (meaning t m 2027) (meaning t m 2274) (meaning t m 2765) (meaning t m 3379) (meaning t m 3549) (meaning t m 3591) source

theorem rule16818 (p1991 p2027 p2764 p2952 p3497 p3692 p4444 : Prop) (h : (¬ p1991) ∨ (¬ p3692) ∨ p2764 ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p4444)) : (¬ p1991) ∨ (p2027) ∨ (p2764) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16818 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6090 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule16818 (meaning t m 1991) (meaning t m 2027) (meaning t m 2764) (meaning t m 2952) (meaning t m 3497) (meaning t m 3692) (meaning t m 4444) source

theorem rule16819 (p1988 p2027 p2417 p2699 p2761 p2922 p3379 : Prop) (h : (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3379) ∨ (¬ p1988) ∨ p2699) : (¬ p1988) ∨ (p2027) ∨ (¬ p2417) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p2922) ∨ (¬ p3379) := by
  classical
  tauto

theorem initial16819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) := by
  have source := ElevenTheory.theory6091 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule16819 (meaning t m 1988) (meaning t m 2027) (meaning t m 2417) (meaning t m 2699) (meaning t m 2761) (meaning t m 2922) (meaning t m 3379) source

theorem rule16820 (p1998 p2027 p2699 p2911 p3399 p3631 p4278 : Prop) (h : (¬ p1998) ∨ p2699 ∨ (¬ p3399) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p4278)) : (¬ p1998) ∨ (p2027) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial16820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory6092 t (m.theta 0 1) (m.theta 1 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16820 (meaning t m 1998) (meaning t m 2027) (meaning t m 2699) (meaning t m 2911) (meaning t m 3399) (meaning t m 3631) (meaning t m 4278) source

theorem rule16821 (p1997 p2027 p2156 p2766 p4110 p4120 p4347 p4506 : Prop) (h : (¬ p4506) ∨ (¬ p2156) ∨ (¬ p4110) ∨ (¬ p4120) ∨ p2766 ∨ (¬ p4347) ∨ p2027 ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2156) ∨ (p2766) ∨ (¬ p4110) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial16821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory6093 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16821 (meaning t m 1997) (meaning t m 2027) (meaning t m 2156) (meaning t m 2766) (meaning t m 4110) (meaning t m 4120) (meaning t m 4347) (meaning t m 4506) source

theorem rule16822 (p1977 p2611 p2696 p2745 : Prop) (h : p2745 ∨ p2611 ∨ (¬ p2696) ∨ (¬ p1977)) : (¬ p1977) ∨ (p2611) ∨ (¬ p2696) ∨ (p2745) := by
  classical
  tauto

theorem initial16822 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2745) := by
  have source := ElevenTheory.theory6094 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3)
  exact rule16822 (meaning t m 1977) (meaning t m 2611) (meaning t m 2696) (meaning t m 2745) source

theorem rule16823 (p4243 p4282 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p4243) ∨ p4282) : (¬ p4243) ∨ (p4282) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial16823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4243)) ∨ (meaning t m 4282) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory6095 (m.theta 1 5) (m.theta 2 5) (m.theta 3 5)
  exact rule16823 (meaning t m 4243) (meaning t m 4282) (meaning t m 5051) source

theorem rule16824 (p1991 p2027 p2177 p2284 p2950 p2997 p3497 p3646 p4132 : Prop) (h : (¬ p2950) ∨ (¬ p1991) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3497) ∨ (¬ p2177) ∨ p2997 ∨ (¬ p4132)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2284) ∨ (¬ p2950) ∨ (p2997) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4132) := by
  classical
  tauto

theorem initial16824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2950)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4132)) := by
  have source := ElevenTheory.theory6096 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule16824 (meaning t m 1991) (meaning t m 2027) (meaning t m 2177) (meaning t m 2284) (meaning t m 2950) (meaning t m 2997) (meaning t m 3497) (meaning t m 3646) (meaning t m 4132) source

theorem rule16825 (p1976 p2027 p2177 p2997 p3365 p3553 p3572 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p2177) ∨ p2997 ∨ (¬ p3365)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) := by
  classical
  tauto

theorem initial16825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3572)) := by
  have source := ElevenTheory.theory6097 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16825 (meaning t m 1976) (meaning t m 2027) (meaning t m 2177) (meaning t m 2997) (meaning t m 3365) (meaning t m 3553) (meaning t m 3572) source

theorem rule16826 (p1987 p2027 p2138 p2388 p2696 p2901 p4244 : Prop) (h : p2388 ∨ p2027 ∨ (¬ p4244) ∨ (¬ p1987) ∨ (¬ p2901) ∨ (¬ p2138) ∨ (¬ p2696)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (p2388) ∨ (¬ p2696) ∨ (¬ p2901) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial16826 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory6098 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule16826 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2388) (meaning t m 2696) (meaning t m 2901) (meaning t m 4244) source

theorem rule16827 (p1976 p2027 p2462 p2797 p2963 p3572 p3947 p4236 : Prop) (h : (¬ p2963) ∨ (¬ p1976) ∨ (¬ p2797) ∨ p2027 ∨ (¬ p4236) ∨ p2462 ∨ (¬ p3947) ∨ (¬ p3572)) : (¬ p1976) ∨ (p2027) ∨ (p2462) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial16827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory6099 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9)
  exact rule16827 (meaning t m 1976) (meaning t m 2027) (meaning t m 2462) (meaning t m 2797) (meaning t m 2963) (meaning t m 3572) (meaning t m 3947) (meaning t m 4236) source

theorem rule16828 (p1982 p2027 p2699 p3222 p3276 p3379 p4444 : Prop) (h : (¬ p1982) ∨ p2027 ∨ (¬ p3379) ∨ p2699 ∨ (¬ p3276) ∨ (¬ p4444) ∨ (¬ p3222)) : (¬ p1982) ∨ (p2027) ∨ (p2699) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial16828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory6100 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule16828 (meaning t m 1982) (meaning t m 2027) (meaning t m 2699) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 4444) source

theorem rule16829 (p1997 p2027 p2220 p2997 p3097 p3646 p3880 : Prop) (h : p2027 ∨ (¬ p3097) ∨ (¬ p3646) ∨ p2997 ∨ (¬ p2220) ∨ (¬ p3880) ∨ (¬ p1997)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2220) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial16829 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory6101 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule16829 (meaning t m 1997) (meaning t m 2027) (meaning t m 2220) (meaning t m 2997) (meaning t m 3097) (meaning t m 3646) (meaning t m 3880) source

theorem rule16831 (p1976 p2027 p2449 p2633 p3425 p3553 p4324 : Prop) (h : p2027 ∨ (¬ p1976) ∨ (¬ p3553) ∨ p2633 ∨ (¬ p2449) ∨ (¬ p4324) ∨ (¬ p3425)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2449) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3553) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial16831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory6103 t (m.theta 0 2) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16831 (meaning t m 1976) (meaning t m 2027) (meaning t m 2449) (meaning t m 2633) (meaning t m 3425) (meaning t m 3553) (meaning t m 4324) source

theorem rule16834 (p2006 p2027 p2774 p2839 p2842 p3055 p3688 : Prop) (h : p2842 ∨ (¬ p2839) ∨ (¬ p3688) ∨ (¬ p3055) ∨ (¬ p2774) ∨ p2027 ∨ (¬ p2006)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2774) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial16834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory6106 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 2 6)
  exact rule16834 (meaning t m 2006) (meaning t m 2027) (meaning t m 2774) (meaning t m 2839) (meaning t m 2842) (meaning t m 3055) (meaning t m 3688) source

theorem rule16835 (p1991 p2027 p2177 p2952 p2997 p3570 p4320 : Prop) (h : p2027 ∨ (¬ p2952) ∨ (¬ p1991) ∨ p2997 ∨ (¬ p4320) ∨ (¬ p2177) ∨ (¬ p3570)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial16835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory6107 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16835 (meaning t m 1991) (meaning t m 2027) (meaning t m 2177) (meaning t m 2952) (meaning t m 2997) (meaning t m 3570) (meaning t m 4320) source

theorem rule16836 (p1997 p2027 p2668 p2997 p3568 p3989 p4110 : Prop) (h : (¬ p3989) ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p2668) ∨ (¬ p3568) ∨ p2027 ∨ p2997) : (¬ p1997) ∨ (p2027) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6108 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16836 (meaning t m 1997) (meaning t m 2027) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 3989) (meaning t m 4110) source

theorem rule16837 (p1987 p2027 p2737 p2881 p2938 p3588 p3659 : Prop) (h : (¬ p3659) ∨ (¬ p2737) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p1987) ∨ p2938 ∨ (¬ p3588)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (¬ p2881) ∨ (p2938) ∨ (¬ p3588) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial16837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2881)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory6109 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule16837 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2881) (meaning t m 2938) (meaning t m 3588) (meaning t m 3659) source

theorem rule16838 (p1987 p2027 p2177 p2696 p2997 p3425 p3659 : Prop) (h : p2027 ∨ (¬ p2696) ∨ (¬ p1987) ∨ p2997 ∨ (¬ p2177) ∨ (¬ p3425) ∨ (¬ p3659)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2696) ∨ (p2997) ∨ (¬ p3425) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial16838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory6110 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule16838 (meaning t m 1987) (meaning t m 2027) (meaning t m 2177) (meaning t m 2696) (meaning t m 2997) (meaning t m 3425) (meaning t m 3659) source

theorem rule16839 (p1983 p2027 p2699 p3222 p3276 p3379 p4381 : Prop) (h : (¬ p1983) ∨ p2027 ∨ (¬ p3379) ∨ p2699 ∨ (¬ p3222) ∨ (¬ p4381) ∨ (¬ p3276)) : (¬ p1983) ∨ (p2027) ∨ (p2699) ∨ (¬ p3222) ∨ (¬ p3276) ∨ (¬ p3379) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial16839 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3222)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory6111 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 9) (m.theta 7 9) (m.theta 9 10)
  exact rule16839 (meaning t m 1983) (meaning t m 2027) (meaning t m 2699) (meaning t m 3222) (meaning t m 3276) (meaning t m 3379) (meaning t m 4381) source

theorem rule16840 (p1991 p2545 p3414 p4652 : Prop) (h : (¬ p1991) ∨ (¬ p3414) ∨ p2545 ∨ p4652) : (¬ p1991) ∨ (p2545) ∨ (¬ p3414) ∨ (p4652) := by
  classical
  tauto

theorem initial16840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 3414)) ∨ (meaning t m 4652) := by
  have source := ElevenTheory.theory6112 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7)
  exact rule16840 (meaning t m 1991) (meaning t m 2545) (meaning t m 3414) (meaning t m 4652) source

theorem rule16841 (p1987 p2027 p2177 p2311 p2737 p2785 p2997 p3551 p3688 : Prop) (h : (¬ p2311) ∨ p2997 ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3551) ∨ (¬ p3688) ∨ (¬ p2737) ∨ (¬ p1987) ∨ (¬ p2785)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2737) ∨ (¬ p2785) ∨ (p2997) ∨ (¬ p3551) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial16841 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2785)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory6113 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16841 (meaning t m 1987) (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 2737) (meaning t m 2785) (meaning t m 2997) (meaning t m 3551) (meaning t m 3688) source

theorem rule16843 (p1980 p2997 p3822 p4846 : Prop) (h : (¬ p1980) ∨ p2997 ∨ p4846 ∨ (¬ p3822)) : (¬ p1980) ∨ (p2997) ∨ (¬ p3822) ∨ (p4846) := by
  classical
  tauto

theorem initial16843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3822)) ∨ (meaning t m 4846) := by
  have source := ElevenTheory.theory6115 t (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule16843 (meaning t m 1980) (meaning t m 2997) (meaning t m 3822) (meaning t m 4846) source

theorem rule16844 (p2011 p2964 p2982 p4949 : Prop) (h : p4949 ∨ (¬ p2011) ∨ p2964 ∨ (¬ p2982)) : (¬ p2011) ∨ (p2964) ∨ (¬ p2982) ∨ (p4949) := by
  classical
  tauto

theorem initial16844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2964) ∨ (¬ (meaning t m 2982)) ∨ (meaning t m 4949) := by
  have source := ElevenTheory.theory6116 t (m.theta 4 5) (m.theta 4 9) (m.theta 5 9)
  exact rule16844 (meaning t m 2011) (meaning t m 2964) (meaning t m 2982) (meaning t m 4949) source

theorem rule16845 (p1991 p2027 p2299 p2396 p2633 p3414 p3947 : Prop) (h : (¬ p1991) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3947) ∨ (¬ p3414) ∨ p2027 ∨ p2633) : (¬ p1991) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial16845 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory6117 t (m.theta 0 3) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule16845 (meaning t m 1991) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3414) (meaning t m 3947) source

theorem rule16846 (p1992 p2027 p2284 p2743 p2938 p2950 p3361 p3646 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p2284) ∨ (¬ p3646) ∨ p2027 ∨ p2938 ∨ (¬ p1992) ∨ (¬ p2743) ∨ (¬ p2950) ∨ (¬ p3361)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2743) ∨ (p2938) ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p3646) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial16846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory6118 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7)
  exact rule16846 (meaning t m 1992) (meaning t m 2027) (meaning t m 2284) (meaning t m 2743) (meaning t m 2938) (meaning t m 2950) (meaning t m 3361) (meaning t m 3646) (meaning t m 4320) source

theorem rule16847 (p1978 p2027 p2284 p2766 p3497 p3646 p4347 p4506 : Prop) (h : p2027 ∨ (¬ p1978) ∨ (¬ p3646) ∨ (¬ p4506) ∨ (¬ p2284) ∨ p2766 ∨ (¬ p4347) ∨ (¬ p3497)) : (¬ p1978) ∨ (p2027) ∨ (¬ p2284) ∨ (p2766) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial16847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory6119 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16847 (meaning t m 1978) (meaning t m 2027) (meaning t m 2284) (meaning t m 2766) (meaning t m 3497) (meaning t m 3646) (meaning t m 4347) (meaning t m 4506) source

theorem rule16848 (p1976 p2027 p2766 p2797 p2963 p3877 p4236 p4347 p4769 : Prop) (h : (¬ p2797) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4347) ∨ (¬ p4236) ∨ (¬ p4769) ∨ (¬ p3877) ∨ p2766) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4769) := by
  classical
  tauto

theorem initial16848 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4769)) := by
  have source := ElevenTheory.theory6120 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule16848 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 2797) (meaning t m 2963) (meaning t m 3877) (meaning t m 4236) (meaning t m 4347) (meaning t m 4769) source

theorem rule16849 (p1976 p2027 p2668 p2780 p2997 p3568 p4358 : Prop) (h : (¬ p2780) ∨ p2027 ∨ p2997 ∨ (¬ p1976) ∨ (¬ p4358) ∨ (¬ p2668) ∨ (¬ p3568)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2668) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial16849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory6121 t (m.theta 0 2) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16849 (meaning t m 1976) (meaning t m 2027) (meaning t m 2668) (meaning t m 2780) (meaning t m 2997) (meaning t m 3568) (meaning t m 4358) source

theorem rule16851 (p1992 p2027 p2187 p2997 p3097 p3583 p4193 p4358 : Prop) (h : (¬ p4193) ∨ (¬ p1992) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3097) ∨ p2997 ∨ (¬ p4358) ∨ (¬ p2187)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2187) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3583) ∨ (¬ p4193) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial16851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory6123 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16851 (meaning t m 1992) (meaning t m 2027) (meaning t m 2187) (meaning t m 2997) (meaning t m 3097) (meaning t m 3583) (meaning t m 4193) (meaning t m 4358) source

theorem rule16852 (p1987 p2027 p2737 p2764 p3583 p4208 p4316 p4322 : Prop) (h : p2027 ∨ (¬ p2737) ∨ p2764 ∨ (¬ p4322) ∨ (¬ p4208) ∨ (¬ p1987) ∨ (¬ p4316) ∨ (¬ p3583)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2737) ∨ (p2764) ∨ (¬ p3583) ∨ (¬ p4208) ∨ (¬ p4316) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial16852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory6124 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule16852 (meaning t m 1987) (meaning t m 2027) (meaning t m 2737) (meaning t m 2764) (meaning t m 3583) (meaning t m 4208) (meaning t m 4316) (meaning t m 4322) source

theorem rule16855 (p1997 p2027 p2313 p2383 p2997 p3989 p4110 : Prop) (h : (¬ p1997) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2383) ∨ p2997 ∨ (¬ p2313)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (p2997) ∨ (¬ p3989) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial16855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory6127 t (m.theta 0 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16855 (meaning t m 1997) (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 2997) (meaning t m 3989) (meaning t m 4110) source

theorem rule16856 (p1991 p2027 p2797 p2963 p3497 p3578 p4315 : Prop) (h : (¬ p1991) ∨ (¬ p2797) ∨ (¬ p2963) ∨ p3578 ∨ (¬ p3497) ∨ p2027 ∨ (¬ p4315)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2797) ∨ (¬ p2963) ∨ (¬ p3497) ∨ (p3578) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial16856 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory6128 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 8)
  exact rule16856 (meaning t m 1991) (meaning t m 2027) (meaning t m 2797) (meaning t m 2963) (meaning t m 3497) (meaning t m 3578) (meaning t m 4315) source

theorem rule16859 (p1991 p2027 p2299 p2633 p2952 p3097 p3952 : Prop) (h : (¬ p2299) ∨ (¬ p1991) ∨ p2633 ∨ p2027 ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial16859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6131 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16859 (meaning t m 1991) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 2952) (meaning t m 3097) (meaning t m 3952) source

theorem rule16860 (p1991 p2027 p2764 p2952 p3744 p3952 p4191 : Prop) (h : (¬ p3744) ∨ p2764 ∨ (¬ p4191) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p1991) ∨ p2027) : (¬ p1991) ∨ (p2027) ∨ (p2764) ∨ (¬ p2952) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial16860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory6132 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule16860 (meaning t m 1991) (meaning t m 2027) (meaning t m 2764) (meaning t m 2952) (meaning t m 3744) (meaning t m 3952) (meaning t m 4191) source

theorem rule16861 (p1978 p2027 p2997 p3097 p3156 p3952 p4120 : Prop) (h : (¬ p1978) ∨ (¬ p4120) ∨ (¬ p3156) ∨ (¬ p3097) ∨ (¬ p3952) ∨ p2027 ∨ p2997) : (¬ p1978) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial16861 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory6133 t (m.theta 0 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule16861 (meaning t m 1978) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3156) (meaning t m 3952) (meaning t m 4120) source

theorem rule16863 (p1992 p2027 p2743 p2952 p2997 p3097 p3361 p3952 : Prop) (h : (¬ p1992) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p3361) ∨ (¬ p3952) ∨ p2027 ∨ (¬ p2743) ∨ (¬ p2952)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3361) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial16863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory6135 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule16863 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2952) (meaning t m 2997) (meaning t m 3097) (meaning t m 3361) (meaning t m 3952) source

theorem rule16864 (p1987 p2027 p2138 p2696 p2997 p3097 p3952 p4316 : Prop) (h : p2997 ∨ (¬ p3097) ∨ (¬ p2696) ∨ (¬ p1987) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p4316) ∨ (¬ p2138)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2696) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4316) := by
  classical
  tauto

theorem initial16864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4316)) := by
  have source := ElevenTheory.theory6136 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule16864 (meaning t m 1987) (meaning t m 2027) (meaning t m 2138) (meaning t m 2696) (meaning t m 2997) (meaning t m 3097) (meaning t m 3952) (meaning t m 4316) source

theorem rule16865 (p1991 p2027 p2462 p2952 p3097 p3952 p4107 : Prop) (h : (¬ p3952) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p1991) ∨ (¬ p2952) ∨ p2462 ∨ (¬ p4107)) : (¬ p1991) ∨ (p2027) ∨ (p2462) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3952) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial16865 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory6137 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule16865 (meaning t m 1991) (meaning t m 2027) (meaning t m 2462) (meaning t m 2952) (meaning t m 3097) (meaning t m 3952) (meaning t m 4107) source

theorem rule16866 (p1998 p2027 p2187 p2997 p3097 p3979 p5558 : Prop) (h : (¬ p5558) ∨ (¬ p1998) ∨ p2027 ∨ p2997 ∨ (¬ p2187) ∨ (¬ p3979) ∨ (¬ p3097)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2187) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3979) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial16866 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory6138 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule16866 (meaning t m 1998) (meaning t m 2027) (meaning t m 2187) (meaning t m 2997) (meaning t m 3097) (meaning t m 3979) (meaning t m 5558) source

theorem rule16867 (p2020 p2027 p2699 p2911 p2922 p3379 p3941 : Prop) (h : (¬ p3941) ∨ p2699 ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2020)) : (¬ p2020) ∨ (p2027) ∨ (p2699) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3941) := by
  classical
  tauto

theorem initial16867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3941)) := by
  have source := ElevenTheory.theory6139 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 10)
  exact rule16867 (meaning t m 2020) (meaning t m 2027) (meaning t m 2699) (meaning t m 2911) (meaning t m 2922) (meaning t m 3379) (meaning t m 3941) source

theorem rule16868 (p1997 p2027 p2997 p3097 p3115 p3952 p4948 : Prop) (h : (¬ p3952) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p1997) ∨ (¬ p4948) ∨ (¬ p3115)) : (¬ p1997) ∨ (p2027) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial16868 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory6140 t (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 7)
  exact rule16868 (meaning t m 1997) (meaning t m 2027) (meaning t m 2997) (meaning t m 3097) (meaning t m 3115) (meaning t m 3952) (meaning t m 4948) source

theorem rule16869 (p1981 p2274 p2765 p4405 : Prop) (h : (¬ p1981) ∨ p2765 ∨ (¬ p2274) ∨ p4405) : (¬ p1981) ∨ (¬ p2274) ∨ (p2765) ∨ (p4405) := by
  classical
  tauto

theorem initial16869 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (meaning t m 4405) := by
  have source := ElevenTheory.theory6141 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16869 (meaning t m 1981) (meaning t m 2274) (meaning t m 2765) (meaning t m 4405) source

theorem rule16870 (p1979 p2027 p2274 p2765 p2946 p2963 p3568 : Prop) (h : (¬ p2274) ∨ (¬ p2946) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p2963) ∨ p2765 ∨ (¬ p1979)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2274) ∨ (p2765) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial16870 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory6142 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule16870 (meaning t m 1979) (meaning t m 2027) (meaning t m 2274) (meaning t m 2765) (meaning t m 2946) (meaning t m 2963) (meaning t m 3568) source

theorem rule16872 (p2004 p2027 p2459 p2633 p3399 p3860 p4261 : Prop) (h : (¬ p2004) ∨ p2633 ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3860) ∨ (¬ p2459) ∨ (¬ p4261)) : (¬ p2004) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3399) ∨ (¬ p3860) ∨ (¬ p4261) := by
  classical
  tauto

theorem initial16872 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2004)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) := by
  have source := ElevenTheory.theory6144 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8) (m.theta 8 9)
  exact rule16872 (meaning t m 2004) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 3399) (meaning t m 3860) (meaning t m 4261) source

theorem rule16873 (p1997 p2027 p2230 p2299 p2579 p2588 p2633 : Prop) (h : (¬ p1997) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p2579) ∨ (¬ p2230) ∨ p2633 ∨ (¬ p2299)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (p2633) := by
  classical
  tauto

theorem initial16873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2633) := by
  have source := ElevenTheory.theory6145 t (m.theta 0 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule16873 (meaning t m 1997) (meaning t m 2027) (meaning t m 2230) (meaning t m 2299) (meaning t m 2579) (meaning t m 2588) (meaning t m 2633) source

theorem rule16874 (p1991 p2027 p2169 p2274 p2963 p3568 p3989 : Prop) (h : (¬ p2274) ∨ p2169 ∨ (¬ p3568) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p1991) ∨ (¬ p3989)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2274) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial16874 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory6146 t (m.theta 0 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule16874 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2274) (meaning t m 2963) (meaning t m 3568) (meaning t m 3989) source

end SunPrize.SMT
