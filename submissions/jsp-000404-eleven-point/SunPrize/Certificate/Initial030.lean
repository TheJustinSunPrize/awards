import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule14486 (p6154 p6155 : Prop) : (¬ ((¬ p6154) ∨ (¬ p6155))) ∨ (¬ p6154) ∨ (¬ p6155) := by
  classical
  tauto

theorem initial14486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6153)) ∨ (¬ (meaning t m 6154)) ∨ (¬ (meaning t m 6155)) := by
  exact rule14486 (meaning t m 6154) (meaning t m 6155)

theorem rule14487 (p5588 p6153 : Prop) (h : (p5588 ↔ p6153)) : (¬ p5588) ∨ (p6153) := by
  classical
  tauto

theorem initial14487 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5588)) ∨ (meaning t m 6153) := by
  have source := ElevenTheory.theory4000 t (m.theta 0 10) (m.theta 0 8) (m.theta 8 10)
  exact rule14487 (meaning t m 5588) (meaning t m 6153) source

theorem rule14492 (p1990 p2027 p2284 p2657 p2688 p2727 p2946 : Prop) (h : (¬ p2946) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2657) ∨ p2688 ∨ (¬ p1990) ∨ (¬ p2284)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2657) ∨ (p2688) ∨ (¬ p2727) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial14492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2657)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory4004 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule14492 (meaning t m 1990) (meaning t m 2027) (meaning t m 2284) (meaning t m 2657) (meaning t m 2688) (meaning t m 2727) (meaning t m 2946) source

theorem rule14493 (p1984 p2027 p2247 p2633 p3644 p3742 p4111 : Prop) (h : p2633 ∨ p2027 ∨ (¬ p1984) ∨ (¬ p4111) ∨ (¬ p3742) ∨ (¬ p2247) ∨ (¬ p3644)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2247) ∨ (p2633) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4005 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule14493 (meaning t m 1984) (meaning t m 2027) (meaning t m 2247) (meaning t m 2633) (meaning t m 3644) (meaning t m 3742) (meaning t m 4111) source

theorem rule14494 (p1992 p2027 p2766 p3363 p3540 p3585 p3644 p4348 : Prop) (h : (¬ p3644) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3585) ∨ p2766 ∨ (¬ p4348) ∨ (¬ p3363) ∨ (¬ p3540)) : (¬ p1992) ∨ (p2027) ∨ (p2766) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p3644) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4006 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14494 (meaning t m 1992) (meaning t m 2027) (meaning t m 2766) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 3644) (meaning t m 4348) source

theorem rule14495 (p1975 p2027 p2274 p2284 p2545 p2657 p2946 : Prop) (h : (¬ p1975) ∨ p2545 ∨ (¬ p2946) ∨ (¬ p2657) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2284)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial14495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory4007 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule14495 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2284) (meaning t m 2545) (meaning t m 2657) (meaning t m 2946) source

theorem rule14496 (p1975 p2027 p2274 p2764 p3989 p4138 p4348 p4444 : Prop) (h : p2027 ∨ (¬ p4348) ∨ (¬ p2274) ∨ p2764 ∨ (¬ p1975) ∨ (¬ p4444) ∨ (¬ p4138) ∨ (¬ p3989)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2764) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4008 t (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14496 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2764) (meaning t m 3989) (meaning t m 4138) (meaning t m 4348) (meaning t m 4444) source

theorem rule14497 (p1998 p2027 p2177 p2274 p2284 p2323 p2946 : Prop) (h : p2027 ∨ (¬ p2284) ∨ (¬ p2946) ∨ p2323 ∨ (¬ p2274) ∨ (¬ p1998) ∨ (¬ p2177)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial14497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory4009 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule14497 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2274) (meaning t m 2284) (meaning t m 2323) (meaning t m 2946) source

theorem rule14499 (p2021 p2027 p2202 p3276 p3333 p3684 p3773 : Prop) (h : (¬ p2021) ∨ (¬ p3684) ∨ (¬ p3333) ∨ (¬ p3773) ∨ p2027 ∨ (¬ p3276) ∨ p2202) : (¬ p2021) ∨ (p2027) ∨ (p2202) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3684) ∨ (¬ p3773) := by
  classical
  tauto

theorem initial14499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2021)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3773)) := by
  have source := ElevenTheory.theory4011 t (m.theta 0 9) (m.theta 2 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule14499 (meaning t m 2021) (meaning t m 2027) (meaning t m 2202) (meaning t m 3276) (meaning t m 3333) (meaning t m 3684) (meaning t m 3773) source

theorem rule14500 (p2027 p2589 p3389 p3742 p3948 p4210 p4814 : Prop) (h : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3948) ∨ (¬ p4814) ∨ p2027 ∨ (¬ p4210) ∨ (¬ p3742)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p3948) ∨ (¬ p4210) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial14500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory4012 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7)
  exact rule14500 (meaning t m 2027) (meaning t m 2589) (meaning t m 3389) (meaning t m 3742) (meaning t m 3948) (meaning t m 4210) (meaning t m 4814) source

theorem rule14501 (p1982 p2027 p2323 p2352 p2363 p2651 p3016 : Prop) (h : p2323 ∨ (¬ p2651) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p1982) ∨ (¬ p2363) ∨ (¬ p2352)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2651) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial14501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory4013 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14501 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2352) (meaning t m 2363) (meaning t m 2651) (meaning t m 3016) source

theorem rule14503 (p1975 p2027 p2611 p2797 p2946 p3125 p3986 p4025 p4117 p4315 : Prop) (h : (¬ p3125) ∨ p2611 ∨ p2027 ∨ (¬ p4025) ∨ (¬ p1975) ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p3986)) : (¬ p1975) ∨ (p2027) ∨ (p2611) ∨ (¬ p2797) ∨ (¬ p2946) ∨ (¬ p3125) ∨ (¬ p3986) ∨ (¬ p4025) ∨ (¬ p4117) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial14503 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory4015 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14503 (meaning t m 1975) (meaning t m 2027) (meaning t m 2611) (meaning t m 2797) (meaning t m 2946) (meaning t m 3125) (meaning t m 3986) (meaning t m 4025) (meaning t m 4117) (meaning t m 4315) source

theorem rule14504 (p1984 p2027 p2766 p3588 p3659 p3954 p4348 : Prop) (h : (¬ p3588) ∨ (¬ p3659) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p1984) ∨ p2766 ∨ (¬ p3954)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4016 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14504 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3588) (meaning t m 3659) (meaning t m 3954) (meaning t m 4348) source

theorem rule14505 (p1975 p2027 p2274 p2323 p2331 p2668 p3989 : Prop) (h : p2323 ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2668) ∨ (¬ p1975) ∨ (¬ p2274) ∨ (¬ p3989)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2323) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial14505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory4017 t (m.theta 0 3) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14505 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2323) (meaning t m 2331) (meaning t m 2668) (meaning t m 3989) source

theorem rule14507 (p1994 p2202 p3684 p4753 : Prop) (h : p2202 ∨ (¬ p3684) ∨ (¬ p1994) ∨ p4753) : (¬ p1994) ∨ (p2202) ∨ (¬ p3684) ∨ (p4753) := by
  classical
  tauto

theorem initial14507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 3684)) ∨ (meaning t m 4753) := by
  have source := ElevenTheory.theory4019 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule14507 (meaning t m 1994) (meaning t m 2202) (meaning t m 3684) (meaning t m 4753) source

theorem rule14509 (p1994 p3008 p3584 p4753 : Prop) (h : p3008 ∨ (¬ p3584) ∨ (¬ p1994) ∨ p4753) : (¬ p1994) ∨ (p3008) ∨ (¬ p3584) ∨ (p4753) := by
  classical
  tauto

theorem initial14509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3584)) ∨ (meaning t m 4753) := by
  have source := ElevenTheory.theory4021 t (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule14509 (meaning t m 1994) (meaning t m 3008) (meaning t m 3584) (meaning t m 4753) source

theorem rule14510 (p1990 p2027 p2352 p2764 p3989 p4137 p4191 : Prop) (h : p2764 ∨ (¬ p4137) ∨ (¬ p3989) ∨ (¬ p4191) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p1990)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2352) ∨ (p2764) ∨ (¬ p3989) ∨ (¬ p4137) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4022 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 9 10)
  exact rule14510 (meaning t m 1990) (meaning t m 2027) (meaning t m 2352) (meaning t m 2764) (meaning t m 3989) (meaning t m 4137) (meaning t m 4191) source

theorem rule14511 (p1975 p2027 p2202 p2295 p2383 p2563 p3324 p3743 : Prop) (h : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p3324) ∨ (¬ p1975) ∨ (¬ p3743) ∨ p2027 ∨ p2202 ∨ (¬ p2563)) : (¬ p1975) ∨ (p2027) ∨ (p2202) ∨ (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3324) ∨ (¬ p3743) := by
  classical
  tauto

theorem initial14511 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3743)) := by
  have source := ElevenTheory.theory4023 t (m.theta 0 6) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14511 (meaning t m 1975) (meaning t m 2027) (meaning t m 2202) (meaning t m 2295) (meaning t m 2383) (meaning t m 2563) (meaning t m 3324) (meaning t m 3743) source

theorem rule14513 (p1986 p2611 p2696 p4752 : Prop) (h : p2611 ∨ (¬ p1986) ∨ (¬ p2696) ∨ p4752) : (¬ p1986) ∨ (p2611) ∨ (¬ p2696) ∨ (p4752) := by
  classical
  tauto

theorem initial14513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 4752) := by
  have source := ElevenTheory.theory4025 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4)
  exact rule14513 (meaning t m 1986) (meaning t m 2611) (meaning t m 2696) (meaning t m 4752) source

theorem rule14514 (p1975 p2027 p2295 p2611 p2696 p2819 p3324 p4426 : Prop) (h : p2027 ∨ (¬ p4426) ∨ (¬ p2696) ∨ (¬ p1975) ∨ (¬ p2295) ∨ p2611 ∨ (¬ p2819) ∨ (¬ p3324)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2819) ∨ (¬ p3324) ∨ (¬ p4426) := by
  classical
  tauto

theorem initial14514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4426)) := by
  have source := ElevenTheory.theory4026 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14514 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2696) (meaning t m 2819) (meaning t m 3324) (meaning t m 4426) source

theorem rule14515 (p1987 p2027 p2633 p3016 p3364 p3584 p3644 p3742 : Prop) (h : (¬ p3644) ∨ (¬ p3742) ∨ (¬ p3016) ∨ (¬ p3584) ∨ (¬ p1987) ∨ p2027 ∨ p2633 ∨ (¬ p3364)) : (¬ p1987) ∨ (p2027) ∨ (p2633) ∨ (¬ p3016) ∨ (¬ p3364) ∨ (¬ p3584) ∨ (¬ p3644) ∨ (¬ p3742) := by
  classical
  tauto

theorem initial14515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3742)) := by
  have source := ElevenTheory.theory4027 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule14515 (meaning t m 1987) (meaning t m 2027) (meaning t m 2633) (meaning t m 3016) (meaning t m 3364) (meaning t m 3584) (meaning t m 3644) (meaning t m 3742) source

theorem rule14516 (p2020 p3128 p3979 p4601 : Prop) (h : p4601 ∨ (¬ p2020) ∨ (¬ p3979) ∨ p3128) : (¬ p2020) ∨ (p3128) ∨ (¬ p3979) ∨ (p4601) := by
  classical
  tauto

theorem initial14516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2020)) ∨ (meaning t m 3128) ∨ (¬ (meaning t m 3979)) ∨ (meaning t m 4601) := by
  have source := ElevenTheory.theory4028 t (m.theta 6 8) (m.theta 6 9) (m.theta 8 10)
  exact rule14516 (meaning t m 2020) (meaning t m 3128) (meaning t m 3979) (meaning t m 4601) source

theorem rule14517 (p1975 p2027 p2295 p3146 p3324 p3578 p4347 : Prop) (h : (¬ p3146) ∨ p2027 ∨ p3578 ∨ (¬ p2295) ∨ (¬ p1975) ∨ (¬ p3324) ∨ (¬ p4347)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (p3578) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3324)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4029 t (m.theta 3 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule14517 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 3146) (meaning t m 3324) (meaning t m 3578) (meaning t m 4347) source

theorem rule14518 (p1975 p2027 p2295 p2611 p2797 p3166 p3877 p4117 : Prop) (h : (¬ p1975) ∨ (¬ p3166) ∨ p2611 ∨ (¬ p4117) ∨ (¬ p2295) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2797)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2797) ∨ (¬ p3166) ∨ (¬ p3877) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial14518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory4030 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7)
  exact rule14518 (meaning t m 1975) (meaning t m 2027) (meaning t m 2295) (meaning t m 2611) (meaning t m 2797) (meaning t m 3166) (meaning t m 3877) (meaning t m 4117) source

theorem rule14519 (p5598 p5599 p5600 p5601 p5602 : Prop) : (p5599) ∨ (((¬ p5599) ∨ (¬ p5600) ∨ (¬ p5598) ∨ (¬ p5601) ∨ (¬ p5602))) := by
  classical
  tauto

theorem initial14519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5599) ∨ (meaning t m 6157) := by
  exact rule14519 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule14520 (p5598 p5599 p5600 p5601 p5602 : Prop) : (p5600) ∨ (((¬ p5599) ∨ (¬ p5600) ∨ (¬ p5598) ∨ (¬ p5601) ∨ (¬ p5602))) := by
  classical
  tauto

theorem initial14520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5600) ∨ (meaning t m 6157) := by
  exact rule14520 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule14521 (p5598 p5599 p5600 p5601 p5602 : Prop) : (p5598) ∨ (((¬ p5599) ∨ (¬ p5600) ∨ (¬ p5598) ∨ (¬ p5601) ∨ (¬ p5602))) := by
  classical
  tauto

theorem initial14521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5598) ∨ (meaning t m 6157) := by
  exact rule14521 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule14522 (p5598 p5599 p5600 p5601 p5602 : Prop) : (p5601) ∨ (((¬ p5599) ∨ (¬ p5600) ∨ (¬ p5598) ∨ (¬ p5601) ∨ (¬ p5602))) := by
  classical
  tauto

theorem initial14522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5601) ∨ (meaning t m 6157) := by
  exact rule14522 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule14523 (p5598 p5599 p5600 p5601 p5602 : Prop) : (p5602) ∨ (((¬ p5599) ∨ (¬ p5600) ∨ (¬ p5598) ∨ (¬ p5601) ∨ (¬ p5602))) := by
  classical
  tauto

theorem initial14523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5602) ∨ (meaning t m 6157) := by
  exact rule14523 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule14524 (p5598 p5599 p5600 p5601 p5602 : Prop) : (¬ p5598) ∨ (¬ p5599) ∨ (¬ p5600) ∨ (¬ p5601) ∨ (¬ p5602) ∨ (¬ ((¬ p5599) ∨ (¬ p5600) ∨ (¬ p5598) ∨ (¬ p5601) ∨ (¬ p5602))) := by
  classical
  tauto

theorem initial14524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5598)) ∨ (¬ (meaning t m 5599)) ∨ (¬ (meaning t m 5600)) ∨ (¬ (meaning t m 5601)) ∨ (¬ (meaning t m 5602)) ∨ (¬ (meaning t m 6157)) := by
  exact rule14524 (meaning t m 5598) (meaning t m 5599) (meaning t m 5600) (meaning t m 5601) (meaning t m 5602)

theorem rule14542 (p4019 p5616 p5617 p5618 p5619 : Prop) : (p5616) ∨ (((¬ p5616) ∨ (¬ p5617) ∨ (¬ p4019) ∨ (¬ p5618) ∨ (¬ p5619))) := by
  classical
  tauto

theorem initial14542 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5616) ∨ (meaning t m 6161) := by
  exact rule14542 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule14543 (p4019 p5616 p5617 p5618 p5619 : Prop) : (p5617) ∨ (((¬ p5616) ∨ (¬ p5617) ∨ (¬ p4019) ∨ (¬ p5618) ∨ (¬ p5619))) := by
  classical
  tauto

theorem initial14543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5617) ∨ (meaning t m 6161) := by
  exact rule14543 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule14544 (p4019 p5616 p5617 p5618 p5619 : Prop) : (p4019) ∨ (((¬ p5616) ∨ (¬ p5617) ∨ (¬ p4019) ∨ (¬ p5618) ∨ (¬ p5619))) := by
  classical
  tauto

theorem initial14544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4019) ∨ (meaning t m 6161) := by
  exact rule14544 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule14545 (p4019 p5616 p5617 p5618 p5619 : Prop) : (p5618) ∨ (((¬ p5616) ∨ (¬ p5617) ∨ (¬ p4019) ∨ (¬ p5618) ∨ (¬ p5619))) := by
  classical
  tauto

theorem initial14545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5618) ∨ (meaning t m 6161) := by
  exact rule14545 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule14546 (p4019 p5616 p5617 p5618 p5619 : Prop) : (p5619) ∨ (((¬ p5616) ∨ (¬ p5617) ∨ (¬ p4019) ∨ (¬ p5618) ∨ (¬ p5619))) := by
  classical
  tauto

theorem initial14546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5619) ∨ (meaning t m 6161) := by
  exact rule14546 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule14547 (p4019 p5616 p5617 p5618 p5619 : Prop) : (¬ p4019) ∨ (¬ p5616) ∨ (¬ p5617) ∨ (¬ p5618) ∨ (¬ p5619) ∨ (¬ ((¬ p5616) ∨ (¬ p5617) ∨ (¬ p4019) ∨ (¬ p5618) ∨ (¬ p5619))) := by
  classical
  tauto

theorem initial14547 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 5616)) ∨ (¬ (meaning t m 5617)) ∨ (¬ (meaning t m 5618)) ∨ (¬ (meaning t m 5619)) ∨ (¬ (meaning t m 6161)) := by
  exact rule14547 (meaning t m 4019) (meaning t m 5616) (meaning t m 5617) (meaning t m 5618) (meaning t m 5619)

theorem rule14556 (p1983 p2027 p2114 p2417 p2437 p2630 p2737 : Prop) (h : p2027 ∨ (¬ p2417) ∨ p2114 ∨ (¬ p2630) ∨ (¬ p2437) ∨ (¬ p2737) ∨ (¬ p1983)) : (¬ p1983) ∨ (p2027) ∨ (p2114) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2737) := by
  classical
  tauto

theorem initial14556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2737)) := by
  have source := ElevenTheory.theory4036 t (m.theta 1 2) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule14556 (meaning t m 1983) (meaning t m 2027) (meaning t m 2114) (meaning t m 2417) (meaning t m 2437) (meaning t m 2630) (meaning t m 2737) source

theorem rule14557 (p2307 p2578 p2588 : Prop) (h : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2578)) : (¬ p2307) ∨ (¬ p2578) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial14557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2578)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory4037 (m.theta 0 6) (m.theta 4 6) (m.theta 6 7)
  exact rule14557 (meaning t m 2307) (meaning t m 2578) (meaning t m 2588) source

theorem rule14559 (p1985 p2027 p2241 p2449 p2699 p3027 p3690 : Prop) (h : (¬ p1985) ∨ (¬ p3690) ∨ p2027 ∨ (¬ p2449) ∨ (¬ p3027) ∨ p2699 ∨ (¬ p2241)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2449) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial14559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2449)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory4039 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14559 (meaning t m 1985) (meaning t m 2027) (meaning t m 2241) (meaning t m 2449) (meaning t m 2699) (meaning t m 3027) (meaning t m 3690) source

theorem rule14560 (p1985 p2027 p2156 p2409 p2427 p3452 p4110 p4172 : Prop) (h : (¬ p2427) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p4172) ∨ p2409 ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p2156)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2156) ∨ (p2409) ∨ (¬ p2427) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4172) := by
  classical
  tauto

theorem initial14560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4172)) := by
  have source := ElevenTheory.theory4040 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule14560 (meaning t m 1985) (meaning t m 2027) (meaning t m 2156) (meaning t m 2409) (meaning t m 2427) (meaning t m 3452) (meaning t m 4110) (meaning t m 4172) source

theorem rule14561 (p1994 p2027 p2169 p2307 p2387 p2588 p3574 : Prop) (h : p2169 ∨ (¬ p1994) ∨ (¬ p2387) ∨ (¬ p3574) ∨ (¬ p2588) ∨ (¬ p2307) ∨ p2027) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial14561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory4041 t (m.theta 0 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14561 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2307) (meaning t m 2387) (meaning t m 2588) (meaning t m 3574) source

theorem rule14563 (p1992 p2027 p2299 p2396 p2633 p3588 p3821 p3959 : Prop) (h : (¬ p2396) ∨ (¬ p1992) ∨ p2633 ∨ p2027 ∨ (¬ p3821) ∨ (¬ p2299) ∨ (¬ p3959) ∨ (¬ p3588)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p3588) ∨ (¬ p3821) ∨ (¬ p3959) := by
  classical
  tauto

theorem initial14563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3959)) := by
  have source := ElevenTheory.theory4043 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14563 (meaning t m 1992) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 3588) (meaning t m 3821) (meaning t m 3959) source

theorem rule14565 (p1975 p2027 p2307 p2352 p2387 p2409 p2493 : Prop) (h : p2409 ∨ p2027 ∨ (¬ p2307) ∨ (¬ p1975) ∨ (¬ p2493) ∨ (¬ p2352) ∨ (¬ p2387)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (p2409) ∨ (¬ p2493) := by
  classical
  tauto

theorem initial14565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2387)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) := by
  have source := ElevenTheory.theory4045 t (m.theta 0 6) (m.theta 1 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14565 (meaning t m 1975) (meaning t m 2027) (meaning t m 2307) (meaning t m 2352) (meaning t m 2387) (meaning t m 2409) (meaning t m 2493) source

theorem rule14575 (p1992 p2027 p2387 p2459 p2633 p2785 p3688 p4347 : Prop) (h : (¬ p2785) ∨ (¬ p1992) ∨ p2633 ∨ p2027 ∨ (¬ p2387) ∨ (¬ p3688) ∨ (¬ p2459) ∨ (¬ p4347)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4055 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14575 (meaning t m 1992) (meaning t m 2027) (meaning t m 2387) (meaning t m 2459) (meaning t m 2633) (meaning t m 2785) (meaning t m 3688) (meaning t m 4347) source

theorem rule14582 (p1988 p2027 p2241 p2699 p2727 p3276 p3343 : Prop) (h : (¬ p1988) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p3343) ∨ p2699 ∨ (¬ p2727) ∨ (¬ p2241)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p2727) ∨ (¬ p3276) ∨ (¬ p3343) := by
  classical
  tauto

theorem initial14582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) := by
  have source := ElevenTheory.theory4062 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 9) (m.theta 9 10)
  exact rule14582 (meaning t m 1988) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 2727) (meaning t m 3276) (meaning t m 3343) source

theorem rule14583 (p2002 p2027 p2307 p3043 p3680 p3773 p3822 p5378 : Prop) (h : (¬ p2002) ∨ (¬ p3822) ∨ (¬ p3680) ∨ (¬ p3773) ∨ p3043 ∨ (¬ p2307) ∨ (¬ p5378) ∨ p2027) : (¬ p2002) ∨ (p2027) ∨ (¬ p2307) ∨ (p3043) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3822) ∨ (¬ p5378) := by
  classical
  tauto

theorem initial14583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2002)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 3043) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3773)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 5378)) := by
  have source := ElevenTheory.theory4063 t (m.theta 0 6) (m.theta 0 9) (m.theta 2 6) (m.theta 5 9) (m.theta 6 7) (m.theta 9 10)
  exact rule14583 (meaning t m 2002) (meaning t m 2027) (meaning t m 2307) (meaning t m 3043) (meaning t m 3680) (meaning t m 3773) (meaning t m 3822) (meaning t m 5378) source

theorem rule14585 (p2010 p2027 p2323 p2499 p2651 p2922 p3016 : Prop) (h : p2323 ∨ (¬ p2010) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p2499) ∨ (¬ p2922)) : (¬ p2010) ∨ (p2027) ∨ (p2323) ∨ (¬ p2499) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p3016) := by
  classical
  tauto

theorem initial14585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3016)) := by
  have source := ElevenTheory.theory4065 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule14585 (meaning t m 2010) (meaning t m 2027) (meaning t m 2323) (meaning t m 2499) (meaning t m 2651) (meaning t m 2922) (meaning t m 3016) source

theorem rule14588 (p1997 p2027 p2295 p2588 p2590 p2611 p2696 p2797 : Prop) (h : (¬ p1997) ∨ (¬ p2590) ∨ (¬ p2295) ∨ (¬ p2588) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p2797) ∨ p2027) : (¬ p1997) ∨ (p2027) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2797) := by
  classical
  tauto

theorem initial14588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) := by
  have source := ElevenTheory.theory4068 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule14588 (meaning t m 1997) (meaning t m 2027) (meaning t m 2295) (meaning t m 2588) (meaning t m 2590) (meaning t m 2611) (meaning t m 2696) (meaning t m 2797) source

theorem rule14590 (p1992 p2027 p2459 p2633 p2743 p3172 p3361 p4118 : Prop) (h : (¬ p3361) ∨ (¬ p2459) ∨ (¬ p2743) ∨ p2633 ∨ (¬ p3172) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p4118)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p2743) ∨ (¬ p3172) ∨ (¬ p3361) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial14590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory4070 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14590 (meaning t m 1992) (meaning t m 2027) (meaning t m 2459) (meaning t m 2633) (meaning t m 2743) (meaning t m 3172) (meaning t m 3361) (meaning t m 4118) source

theorem rule14597 (p1980 p2027 p2202 p2553 p2573 p2589 p3568 : Prop) (h : (¬ p2589) ∨ p2027 ∨ p2202 ∨ (¬ p2553) ∨ (¬ p3568) ∨ (¬ p2573) ∨ (¬ p1980)) : (¬ p1980) ∨ (p2027) ∨ (p2202) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3568) := by
  classical
  tauto

theorem initial14597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3568)) := by
  have source := ElevenTheory.theory4077 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule14597 (meaning t m 1980) (meaning t m 2027) (meaning t m 2202) (meaning t m 2553) (meaning t m 2573) (meaning t m 2589) (meaning t m 3568) source

theorem rule14600 (p1988 p2027 p2406 p2699 p2982 p3379 p3680 : Prop) (h : (¬ p2406) ∨ p2699 ∨ (¬ p3379) ∨ (¬ p3680) ∨ (¬ p1988) ∨ (¬ p2982) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3680) := by
  classical
  tauto

theorem initial14600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3680)) := by
  have source := ElevenTheory.theory4080 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule14600 (meaning t m 1988) (meaning t m 2027) (meaning t m 2406) (meaning t m 2699) (meaning t m 2982) (meaning t m 3379) (meaning t m 3680) source

theorem rule14603 (p2015 p2027 p2307 p2764 p3549 p3946 p4191 : Prop) (h : (¬ p2307) ∨ (¬ p3946) ∨ (¬ p2015) ∨ p2027 ∨ (¬ p3549) ∨ p2764 ∨ (¬ p4191)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2307) ∨ (p2764) ∨ (¬ p3549) ∨ (¬ p3946) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4083 t (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 9) (m.theta 9 10)
  exact rule14603 (meaning t m 2015) (meaning t m 2027) (meaning t m 2307) (meaning t m 2764) (meaning t m 3549) (meaning t m 3946) (meaning t m 4191) source

theorem rule14605 (p1989 p2027 p2191 p2406 p2699 p2982 p3379 p4335 : Prop) (h : (¬ p1989) ∨ (¬ p2191) ∨ (¬ p4335) ∨ p2027 ∨ p2699 ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p2406)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2406) ∨ (p2699) ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p4335) := by
  classical
  tauto

theorem initial14605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4335)) := by
  have source := ElevenTheory.theory4085 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9)
  exact rule14605 (meaning t m 1989) (meaning t m 2027) (meaning t m 2191) (meaning t m 2406) (meaning t m 2699) (meaning t m 2982) (meaning t m 3379) (meaning t m 4335) source

theorem rule14606 (p1987 p2027 p2104 p2169 p2363 p2696 p4340 : Prop) (h : (¬ p2696) ∨ p2169 ∨ (¬ p2104) ∨ (¬ p4340) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2104) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2696) ∨ (¬ p4340) := by
  classical
  tauto

theorem initial14606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4340)) := by
  have source := ElevenTheory.theory4086 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14606 (meaning t m 1987) (meaning t m 2027) (meaning t m 2104) (meaning t m 2169) (meaning t m 2363) (meaning t m 2696) (meaning t m 4340) source

theorem rule14610 (p2005 p2027 p2409 p2588 p3093 p3309 p3452 : Prop) (h : (¬ p3452) ∨ p2409 ∨ (¬ p2005) ∨ (¬ p2588) ∨ (¬ p3309) ∨ p2027 ∨ (¬ p3093)) : (¬ p2005) ∨ (p2027) ∨ (p2409) ∨ (¬ p2588) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial14610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory4090 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7)
  exact rule14610 (meaning t m 2005) (meaning t m 2027) (meaning t m 2409) (meaning t m 2588) (meaning t m 3093) (meaning t m 3309) (meaning t m 3452) source

theorem rule14613 (p2005 p2027 p2166 p2307 p2588 p2873 p2962 p4120 : Prop) (h : p2027 ∨ (¬ p2166) ∨ (¬ p2588) ∨ p2873 ∨ (¬ p4120) ∨ (¬ p2962) ∨ (¬ p2005) ∨ (¬ p2307)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2166) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (p2873) ∨ (¬ p2962) ∨ (¬ p4120) := by
  classical
  tauto

theorem initial14613 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 4120)) := by
  have source := ElevenTheory.theory4093 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7)
  exact rule14613 (meaning t m 2005) (meaning t m 2027) (meaning t m 2166) (meaning t m 2307) (meaning t m 2588) (meaning t m 2873) (meaning t m 2962) (meaning t m 4120) source

theorem rule14614 (p2220 p3370 p3906 p4492 : Prop) (h : (¬ p3370) ∨ (¬ p3906) ∨ (¬ p2220) ∨ (¬ p4492)) : (¬ p2220) ∨ (¬ p3370) ∨ (¬ p3906) ∨ (¬ p4492) := by
  classical
  tauto

theorem initial14614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4492)) := by
  have source := ElevenTheory.theory4094 (m.theta 0 5) (m.theta 1 5) (m.theta 1 8) (m.theta 5 8)
  exact rule14614 (meaning t m 2220) (meaning t m 3370) (meaning t m 3906) (meaning t m 4492) source

theorem rule14615 (p1982 p2027 p2177 p2761 p3309 p3818 p3945 p4444 : Prop) (h : (¬ p3945) ∨ (¬ p4444) ∨ (¬ p1982) ∨ (¬ p2177) ∨ (¬ p2761) ∨ p2027 ∨ p3818 ∨ (¬ p3309)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2761) ∨ (¬ p3309) ∨ (p3818) ∨ (¬ p3945) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14615 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3309)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4095 t (m.theta 1 6) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14615 (meaning t m 1982) (meaning t m 2027) (meaning t m 2177) (meaning t m 2761) (meaning t m 3309) (meaning t m 3818) (meaning t m 3945) (meaning t m 4444) source

theorem rule14617 (p1978 p2027 p2169 p2891 p3556 p3989 p4173 : Prop) (h : (¬ p4173) ∨ (¬ p3556) ∨ p2027 ∨ (¬ p3989) ∨ p2169 ∨ (¬ p2891) ∨ (¬ p1978)) : (¬ p1978) ∨ (p2027) ∨ (p2169) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3989) ∨ (¬ p4173) := by
  classical
  tauto

theorem initial14617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1978)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) := by
  have source := ElevenTheory.theory4097 t (m.theta 0 5) (m.theta 1 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule14617 (meaning t m 1978) (meaning t m 2027) (meaning t m 2169) (meaning t m 2891) (meaning t m 3556) (meaning t m 3989) (meaning t m 4173) source

theorem rule14618 (p1984 p2027 p2766 p3486 p3555 p3570 p4348 : Prop) (h : (¬ p3555) ∨ (¬ p1984) ∨ (¬ p4348) ∨ (¬ p3570) ∨ (¬ p3486) ∨ p2027 ∨ p2766) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14618 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4098 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14618 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3486) (meaning t m 3555) (meaning t m 3570) (meaning t m 4348) source

theorem rule14619 (p2005 p2027 p2274 p2313 p2765 p3654 p4137 : Prop) (h : p2027 ∨ p2765 ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p2005) ∨ (¬ p4137)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p3654) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial14619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory4099 t (m.theta 0 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14619 (meaning t m 2005) (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 3654) (meaning t m 4137) source

theorem rule14620 (p2274 p2307 p3743 : Prop) (h : (¬ p3743) ∨ (¬ p2307) ∨ p2274) : (p2274) ∨ (¬ p2307) ∨ (¬ p3743) := by
  classical
  tauto

theorem initial14620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2274) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3743)) := by
  have source := ElevenTheory.theory4100 (m.theta 0 6) (m.theta 5 6) (m.theta 6 7)
  exact rule14620 (meaning t m 2274) (meaning t m 2307) (meaning t m 3743) source

theorem rule14622 (p1999 p2027 p2114 p2230 p2563 p3125 p3367 p3759 : Prop) (h : p2114 ∨ p2027 ∨ (¬ p2563) ∨ (¬ p3367) ∨ (¬ p1999) ∨ (¬ p2230) ∨ (¬ p3125) ∨ (¬ p3759)) : (¬ p1999) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial14622 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory4102 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule14622 (meaning t m 1999) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2563) (meaning t m 3125) (meaning t m 3367) (meaning t m 3759) source

theorem rule14626 (p2005 p2027 p2307 p2588 p3319 p3818 p3946 : Prop) (h : p2027 ∨ (¬ p2005) ∨ (¬ p2307) ∨ (¬ p3946) ∨ (¬ p2588) ∨ p3818 ∨ (¬ p3319)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p3319) ∨ (p3818) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial14626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3319)) ∨ (meaning t m 3818) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory4106 t (m.theta 0 6) (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14626 (meaning t m 2005) (meaning t m 2027) (meaning t m 2307) (meaning t m 2588) (meaning t m 3319) (meaning t m 3818) (meaning t m 3946) source

theorem rule14636 (p1981 p2765 p3063 p4514 : Prop) (h : (¬ p3063) ∨ p2765 ∨ (¬ p1981) ∨ p4514) : (¬ p1981) ∨ (p2765) ∨ (¬ p3063) ∨ (p4514) := by
  classical
  tauto

theorem initial14636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3063)) ∨ (meaning t m 4514) := by
  have source := ElevenTheory.theory4116 t (m.theta 1 6) (m.theta 5 6) (m.theta 6 8)
  exact rule14636 (meaning t m 1981) (meaning t m 2765) (meaning t m 3063) (meaning t m 4514) source

theorem rule14639 (p1990 p2027 p2169 p2363 p2563 p3692 p3880 : Prop) (h : (¬ p3692) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3880) ∨ (¬ p1990) ∨ (¬ p2563)) : (¬ p1990) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial14639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4119 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14639 (meaning t m 1990) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2563) (meaning t m 3692) (meaning t m 3880) source

theorem rule14640 (p1990 p2027 p2241 p2542 p2563 p2699 p2727 : Prop) (h : (¬ p2563) ∨ (¬ p1990) ∨ p2699 ∨ (¬ p2241) ∨ (¬ p2727) ∨ p2027 ∨ (¬ p2542)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (p2699) ∨ (¬ p2727) := by
  classical
  tauto

theorem initial14640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2727)) := by
  have source := ElevenTheory.theory4120 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule14640 (meaning t m 1990) (meaning t m 2027) (meaning t m 2241) (meaning t m 2542) (meaning t m 2563) (meaning t m 2699) (meaning t m 2727) source

theorem rule14642 (p1990 p2027 p2253 p2563 p2651 p2699 p2992 p4111 p4241 : Prop) (h : (¬ p2563) ∨ (¬ p1990) ∨ p2699 ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p4111) ∨ (¬ p2992) ∨ (¬ p4241)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2253) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (p2699) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial14642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory4122 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule14642 (meaning t m 1990) (meaning t m 2027) (meaning t m 2253) (meaning t m 2563) (meaning t m 2651) (meaning t m 2699) (meaning t m 2992) (meaning t m 4111) (meaning t m 4241) source

theorem rule14643 (p2001 p2027 p2323 p2528 p2651 p3083 p3692 : Prop) (h : p2323 ∨ (¬ p2001) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p3692) ∨ (¬ p2528) ∨ (¬ p3083)) : (¬ p2001) ∨ (p2027) ∨ (p2323) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3083) ∨ (¬ p3692) := by
  classical
  tauto

theorem initial14643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3692)) := by
  have source := ElevenTheory.theory4123 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule14643 (meaning t m 2001) (meaning t m 2027) (meaning t m 2323) (meaning t m 2528) (meaning t m 2651) (meaning t m 3083) (meaning t m 3692) source

theorem rule14644 (p2651 p2946 p3413 : Prop) (h : (¬ p3413) ∨ (¬ p2651) ∨ p2946) : (¬ p2651) ∨ (p2946) ∨ (¬ p3413) := by
  classical
  tauto

theorem initial14644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2651)) ∨ (meaning t m 2946) ∨ (¬ (meaning t m 3413)) := by
  have source := ElevenTheory.theory4124 (m.theta 0 3) (m.theta 3 4) (m.theta 3 5)
  exact rule14644 (meaning t m 2651) (meaning t m 2946) (meaning t m 3413) source

theorem rule14645 (p2010 p2027 p2191 p2253 p2699 p2946 p3027 p3156 p3368 p3579 : Prop) (h : p2699 ∨ (¬ p3027) ∨ (¬ p2010) ∨ p2027 ∨ (¬ p3368) ∨ (¬ p2253) ∨ (¬ p3579) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p2191)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2191) ∨ (¬ p2253) ∨ (p2699) ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3156) ∨ (¬ p3368) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial14645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2253)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory4125 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 4 7) (m.theta 5 8)
  exact rule14645 (meaning t m 2010) (meaning t m 2027) (meaning t m 2191) (meaning t m 2253) (meaning t m 2699) (meaning t m 2946) (meaning t m 3027) (meaning t m 3156) (meaning t m 3368) (meaning t m 3579) source

theorem rule14646 (p2015 p2027 p2169 p3426 p3434 p3549 p4107 p4358 : Prop) (h : p2169 ∨ (¬ p3426) ∨ (¬ p4358) ∨ (¬ p2015) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p3549) ∨ (¬ p3434)) : (¬ p2015) ∨ (p2027) ∨ (p2169) ∨ (¬ p3426) ∨ (¬ p3434) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial14646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory4126 t (m.theta 1 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 9)
  exact rule14646 (meaning t m 2015) (meaning t m 2027) (meaning t m 2169) (meaning t m 3426) (meaning t m 3434) (meaning t m 3549) (meaning t m 4107) (meaning t m 4358) source

theorem rule14648 (p1991 p2027 p2169 p2685 p3324 p3414 p4195 : Prop) (h : p2027 ∨ p2169 ∨ (¬ p3414) ∨ (¬ p1991) ∨ (¬ p2685) ∨ (¬ p3324) ∨ (¬ p4195)) : (¬ p1991) ∨ (p2027) ∨ (p2169) ∨ (¬ p2685) ∨ (¬ p3324) ∨ (¬ p3414) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial14648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4128 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 8)
  exact rule14648 (meaning t m 1991) (meaning t m 2027) (meaning t m 2169) (meaning t m 2685) (meaning t m 3324) (meaning t m 3414) (meaning t m 4195) source

theorem rule14651 (p1992 p2027 p2098 p2633 p3425 p3659 p4242 : Prop) (h : p2633 ∨ (¬ p3425) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p4242) ∨ (¬ p1992) ∨ (¬ p2098)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2098) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial14651 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory4131 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8)
  exact rule14651 (meaning t m 1992) (meaning t m 2027) (meaning t m 2098) (meaning t m 2633) (meaning t m 3425) (meaning t m 3659) (meaning t m 4242) source

theorem rule14655 (p2577 p2962 p3904 : Prop) (h : (¬ p2577) ∨ (¬ p2962) ∨ p3904) : (¬ p2577) ∨ (¬ p2962) ∨ (p3904) := by
  classical
  tauto

theorem initial14655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2962)) ∨ (meaning t m 3904) := by
  have source := ElevenTheory.theory4135 (m.theta 0 4) (m.theta 0 5) (m.theta 0 6)
  exact rule14655 (meaning t m 2577) (meaning t m 2962) (meaning t m 3904) source

theorem rule14661 (p1987 p2027 p2132 p2737 p2842 p3055 p3583 : Prop) (h : (¬ p3583) ∨ (¬ p1987) ∨ p2842 ∨ (¬ p2132) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p2737)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2132) ∨ (¬ p2737) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial14661 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory4141 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule14661 (meaning t m 1987) (meaning t m 2027) (meaning t m 2132) (meaning t m 2737) (meaning t m 2842) (meaning t m 3055) (meaning t m 3583) source

theorem rule14662 (p1992 p2027 p2743 p2764 p2952 p3361 p4208 p4322 : Prop) (h : (¬ p2952) ∨ (¬ p4208) ∨ (¬ p3361) ∨ (¬ p2743) ∨ p2764 ∨ p2027 ∨ (¬ p4322) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p4208) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial14662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory4142 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule14662 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2764) (meaning t m 2952) (meaning t m 3361) (meaning t m 4208) (meaning t m 4322) source

theorem rule14664 (p1977 p2027 p2764 p2946 p3292 p3662 p4040 p4322 : Prop) (h : (¬ p1977) ∨ p2764 ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p3292) ∨ (¬ p4322) ∨ (¬ p4040)) : (¬ p1977) ∨ (p2027) ∨ (p2764) ∨ (¬ p2946) ∨ (¬ p3292) ∨ (¬ p3662) ∨ (¬ p4040) ∨ (¬ p4322) := by
  classical
  tauto

theorem initial14664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4322)) := by
  have source := ElevenTheory.theory4144 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9) (m.theta 9 10)
  exact rule14664 (meaning t m 1977) (meaning t m 2027) (meaning t m 2764) (meaning t m 2946) (meaning t m 3292) (meaning t m 3662) (meaning t m 4040) (meaning t m 4322) source

theorem rule14670 (p1976 p2027 p2138 p2177 p2997 p3570 p4244 : Prop) (h : (¬ p1976) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2138) ∨ (¬ p4244) ∨ p2997 ∨ (¬ p2177)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2177) ∨ (p2997) ∨ (¬ p3570) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial14670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory4150 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule14670 (meaning t m 1976) (meaning t m 2027) (meaning t m 2138) (meaning t m 2177) (meaning t m 2997) (meaning t m 3570) (meaning t m 4244) source

theorem rule14673 (p1985 p2027 p2233 p2427 p2573 p2850 p3584 : Prop) (h : p2233 ∨ (¬ p2573) ∨ (¬ p2427) ∨ (¬ p3584) ∨ (¬ p1985) ∨ p2027 ∨ (¬ p2850)) : (¬ p1985) ∨ (p2027) ∨ (p2233) ∨ (¬ p2427) ∨ (¬ p2573) ∨ (¬ p2850) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial14673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory4153 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule14673 (meaning t m 1985) (meaning t m 2027) (meaning t m 2233) (meaning t m 2427) (meaning t m 2573) (meaning t m 2850) (meaning t m 3584) source

theorem rule14674 (p2001 p2027 p2528 p2545 p2810 p3005 p3692 p4346 : Prop) (h : (¬ p2528) ∨ (¬ p4346) ∨ (¬ p2001) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3005) ∨ (¬ p2810) ∨ p2545) : (¬ p2001) ∨ (p2027) ∨ (¬ p2528) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4346) := by
  classical
  tauto

theorem initial14674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2528)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4346)) := by
  have source := ElevenTheory.theory4154 t (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 8) (m.theta 5 8) (m.theta 8 9)
  exact rule14674 (meaning t m 2001) (meaning t m 2027) (meaning t m 2528) (meaning t m 2545) (meaning t m 2810) (meaning t m 3005) (meaning t m 3692) (meaning t m 4346) source

theorem rule14675 (p1977 p2027 p2331 p2764 p2811 p4035 p4154 p4190 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p4154) ∨ (¬ p1977) ∨ p2764 ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4035) ∨ (¬ p4190) ∨ (¬ p2811)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2764) ∨ (¬ p2811) ∨ (¬ p4035) ∨ (¬ p4154) ∨ (¬ p4190) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4190)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4155 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 9) (m.theta 6 9) (m.theta 9 10)
  exact rule14675 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2764) (meaning t m 2811) (meaning t m 4035) (meaning t m 4154) (meaning t m 4190) (meaning t m 4191) source

theorem rule14677 (p1988 p2027 p2210 p2699 p2761 p2891 p3246 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p2761) ∨ (¬ p2891) ∨ (¬ p2210) ∨ (¬ p3246) ∨ (¬ p1988)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2761) ∨ (¬ p2891) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial14677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory4157 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule14677 (meaning t m 1988) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2761) (meaning t m 2891) (meaning t m 3246) source

theorem rule14678 (p1976 p2027 p2764 p3365 p4037 p4191 p4195 : Prop) (h : (¬ p3365) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p4191) ∨ p2764 ∨ (¬ p4195)) : (¬ p1976) ∨ (p2027) ∨ (p2764) ∨ (¬ p3365) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial14678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4158 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14678 (meaning t m 1976) (meaning t m 2027) (meaning t m 2764) (meaning t m 3365) (meaning t m 4037) (meaning t m 4191) (meaning t m 4195) source

theorem rule14679 (p1977 p2027 p2331 p2462 p3414 p3947 p4154 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p2331) ∨ p2462 ∨ (¬ p4154) ∨ (¬ p3414) ∨ (¬ p3947)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2462) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial14679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4159 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 7 9)
  exact rule14679 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2462) (meaning t m 3414) (meaning t m 3947) (meaning t m 4154) source

theorem rule14681 (p2005 p2027 p2230 p2493 p3238 p3441 p3860 p4079 : Prop) (h : p2027 ∨ p3441 ∨ (¬ p3238) ∨ (¬ p2230) ∨ (¬ p2005) ∨ (¬ p2493) ∨ (¬ p3860) ∨ (¬ p4079)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (p3441) ∨ (¬ p3860) ∨ (¬ p4079) := by
  classical
  tauto

theorem initial14681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (meaning t m 3441) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4079)) := by
  have source := ElevenTheory.theory4161 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 4 6)
  exact rule14681 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2493) (meaning t m 3238) (meaning t m 3441) (meaning t m 3860) (meaning t m 4079) source

theorem rule14682 (p1992 p2027 p2743 p2764 p2963 p3361 p4037 p4191 : Prop) (h : (¬ p2743) ∨ (¬ p3361) ∨ p2764 ∨ (¬ p4037) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4191)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2764) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4037) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4162 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14682 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2764) (meaning t m 2963) (meaning t m 3361) (meaning t m 4037) (meaning t m 4191) source

theorem rule14683 (p2005 p2027 p2230 p2493 p2914 p3238 p3540 : Prop) (h : p2027 ∨ (¬ p2230) ∨ p2914 ∨ (¬ p3540) ∨ (¬ p2005) ∨ (¬ p3238) ∨ (¬ p2493)) : (¬ p2005) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2493) ∨ (p2914) ∨ (¬ p3238) ∨ (¬ p3540) := by
  classical
  tauto

theorem initial14683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2005)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) := by
  have source := ElevenTheory.theory4163 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule14683 (meaning t m 2005) (meaning t m 2027) (meaning t m 2230) (meaning t m 2493) (meaning t m 2914) (meaning t m 3238) (meaning t m 3540) source

theorem rule14684 (p1998 p2027 p2470 p2528 p2656 p2914 p3742 p4348 : Prop) (h : (¬ p2528) ∨ (¬ p1998) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2470) ∨ (¬ p2656) ∨ p2914 ∨ (¬ p3742)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2656) ∨ (p2914) ∨ (¬ p3742) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2656)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4164 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14684 (meaning t m 1998) (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 2656) (meaning t m 2914) (meaning t m 3742) (meaning t m 4348) source

theorem rule14685 (p1988 p2027 p2761 p3399 p3591 p3631 p3818 : Prop) (h : (¬ p3631) ∨ (¬ p1988) ∨ (¬ p3399) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3591) ∨ p3818) : (¬ p1988) ∨ (p2027) ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3591) ∨ (¬ p3631) ∨ (p3818) := by
  classical
  tauto

theorem initial14685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3631)) ∨ (meaning t m 3818) := by
  have source := ElevenTheory.theory4165 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 7 9) (m.theta 9 10)
  exact rule14685 (meaning t m 1988) (meaning t m 2027) (meaning t m 2761) (meaning t m 3399) (meaning t m 3591) (meaning t m 3631) (meaning t m 3818) source

theorem rule14687 (p1981 p2027 p2088 p2274 p2313 p2765 p4114 p4347 : Prop) (h : (¬ p2088) ∨ p2765 ∨ (¬ p2274) ∨ p2027 ∨ (¬ p2313) ∨ (¬ p4347) ∨ (¬ p4114) ∨ (¬ p1981)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2088) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p4114) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4167 t (m.theta 0 6) (m.theta 0 8) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule14687 (meaning t m 1981) (meaning t m 2027) (meaning t m 2088) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 4114) (meaning t m 4347) source

theorem rule14689 (p1998 p2027 p2264 p2274 p2313 p2765 p3204 p3319 p3947 p4623 : Prop) (h : (¬ p4623) ∨ (¬ p1998) ∨ (¬ p3319) ∨ (¬ p3204) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2274) ∨ p2765 ∨ (¬ p2313) ∨ (¬ p3947)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (p2765) ∨ (¬ p3204) ∨ (¬ p3319) ∨ (¬ p3947) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial14689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory4169 t (m.theta 0 6) (m.theta 1 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule14689 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2274) (meaning t m 2313) (meaning t m 2765) (meaning t m 3204) (meaning t m 3319) (meaning t m 3947) (meaning t m 4623) source

theorem rule14690 (p1988 p2027 p2192 p2210 p2699 p3125 p3461 : Prop) (h : (¬ p2192) ∨ (¬ p3125) ∨ (¬ p1988) ∨ (¬ p3461) ∨ p2699 ∨ (¬ p2210) ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial14690 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory4170 t (m.theta 0 1) (m.theta 1 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14690 (meaning t m 1988) (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 2699) (meaning t m 3125) (meaning t m 3461) source

theorem rule14691 (p1975 p2027 p2230 p2233 p2299 p2934 p3238 p3527 : Prop) (h : p2233 ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3238) ∨ (¬ p2299) ∨ (¬ p3527) ∨ (¬ p2934) ∨ (¬ p1975)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2299) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) := by
  classical
  tauto

theorem initial14691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3527)) := by
  have source := ElevenTheory.theory4171 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 6 7) (m.theta 7 8)
  exact rule14691 (meaning t m 1975) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2299) (meaning t m 2934) (meaning t m 3238) (meaning t m 3527) source

theorem rule14693 (p1975 p2027 p2241 p2264 p2299 p2641 p2699 p4156 : Prop) (h : p2699 ∨ (¬ p1975) ∨ (¬ p2299) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4156) ∨ (¬ p2264)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2641) ∨ (p2699) ∨ (¬ p4156) := by
  classical
  tauto

theorem initial14693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2641)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 4156)) := by
  have source := ElevenTheory.theory4173 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule14693 (meaning t m 1975) (meaning t m 2027) (meaning t m 2241) (meaning t m 2264) (meaning t m 2299) (meaning t m 2641) (meaning t m 2699) (meaning t m 4156) source

theorem rule14697 (p1975 p2027 p2274 p2699 p3093 p4053 p4393 : Prop) (h : (¬ p3093) ∨ p2027 ∨ (¬ p1975) ∨ (¬ p4053) ∨ p2699 ∨ (¬ p4393) ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2274) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4393) := by
  classical
  tauto

theorem initial14697 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4393)) := by
  have source := ElevenTheory.theory4177 t (m.theta 0 1) (m.theta 1 6) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7)
  exact rule14697 (meaning t m 1975) (meaning t m 2027) (meaning t m 2274) (meaning t m 2699) (meaning t m 3093) (meaning t m 4053) (meaning t m 4393) source

theorem rule14699 (p4435 p5622 p5623 p5624 p5625 : Prop) : (p4435) ∨ (((¬ p5623) ∨ (¬ p4435) ∨ (¬ p5622) ∨ (¬ p5624) ∨ (¬ p5625))) := by
  classical
  tauto

theorem initial14699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4435) ∨ (meaning t m 6163) := by
  exact rule14699 (meaning t m 4435) (meaning t m 5622) (meaning t m 5623) (meaning t m 5624) (meaning t m 5625)

theorem rule14706 (p4053 p5627 p5628 p5629 p5630 : Prop) : (p4053) ∨ (((¬ p5627) ∨ (¬ p5628) ∨ (¬ p4053) ∨ (¬ p5629) ∨ (¬ p5630))) := by
  classical
  tauto

theorem initial14706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4053) ∨ (meaning t m 6164) := by
  exact rule14706 (meaning t m 4053) (meaning t m 5627) (meaning t m 5628) (meaning t m 5629) (meaning t m 5630)

theorem rule14712 (p6163 p6164 : Prop) : (¬ ((¬ p6163) ∨ (¬ p6164))) ∨ (¬ p6163) ∨ (¬ p6164) := by
  classical
  tauto

theorem initial14712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6162)) ∨ (¬ (meaning t m 6163)) ∨ (¬ (meaning t m 6164)) := by
  exact rule14712 (meaning t m 6163) (meaning t m 6164)

theorem rule14713 (p5620 p6162 : Prop) (h : (p5620 ↔ p6162)) : (¬ p5620) ∨ (p6162) := by
  classical
  tauto

theorem initial14713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5620)) ∨ (meaning t m 6162) := by
  have source := ElevenTheory.theory4178 t (m.theta 1 10) (m.theta 1 6) (m.theta 6 10)
  exact rule14713 (meaning t m 5620) (meaning t m 6162) source

theorem rule14715 (p1988 p2027 p2230 p2233 p2563 p3125 p3461 : Prop) (h : (¬ p2230) ∨ p2233 ∨ (¬ p3125) ∨ (¬ p1988) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p2563)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2230) ∨ (p2233) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3461) := by
  classical
  tauto

theorem initial14715 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2233) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3461)) := by
  have source := ElevenTheory.theory4179 t (m.theta 0 4) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 9 10)
  exact rule14715 (meaning t m 1988) (meaning t m 2027) (meaning t m 2230) (meaning t m 2233) (meaning t m 2563) (meaning t m 3125) (meaning t m 3461) source

theorem rule14718 (p4372 p5633 p5634 p5635 p5636 : Prop) : (p4372) ∨ (((¬ p5633) ∨ (¬ p4372) ∨ (¬ p5636) ∨ (¬ p5635) ∨ (¬ p5634))) := by
  classical
  tauto

theorem initial14718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4372) ∨ (meaning t m 6166) := by
  exact rule14718 (meaning t m 4372) (meaning t m 5633) (meaning t m 5634) (meaning t m 5635) (meaning t m 5636)

theorem rule14727 (p4063 p5638 p5639 p5640 p5641 : Prop) : (p4063) ∨ (((¬ p5638) ∨ (¬ p5640) ∨ (¬ p5641) ∨ (¬ p5639) ∨ (¬ p4063))) := by
  classical
  tauto

theorem initial14727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4063) ∨ (meaning t m 6167) := by
  exact rule14727 (meaning t m 4063) (meaning t m 5638) (meaning t m 5639) (meaning t m 5640) (meaning t m 5641)

theorem rule14731 (p6166 p6167 : Prop) : (¬ ((¬ p6166) ∨ (¬ p6167))) ∨ (¬ p6166) ∨ (¬ p6167) := by
  classical
  tauto

theorem initial14731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6165)) ∨ (¬ (meaning t m 6166)) ∨ (¬ (meaning t m 6167)) := by
  exact rule14731 (meaning t m 6166) (meaning t m 6167)

theorem rule14732 (p5631 p6165 : Prop) (h : (p5631 ↔ p6165)) : (¬ p5631) ∨ (p6165) := by
  classical
  tauto

theorem initial14732 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5631)) ∨ (meaning t m 6165) := by
  have source := ElevenTheory.theory4181 t (m.theta 0 10) (m.theta 0 7) (m.theta 7 10)
  exact rule14732 (meaning t m 5631) (meaning t m 6165) source

theorem rule14737 (p1998 p2027 p2210 p2699 p2881 p3631 p3690 p4431 : Prop) (h : (¬ p2881) ∨ p2699 ∨ (¬ p3690) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p4431) ∨ (¬ p2210) ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2881) ∨ (¬ p3631) ∨ (¬ p3690) ∨ (¬ p4431) := by
  classical
  tauto

theorem initial14737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4431)) := by
  have source := ElevenTheory.theory4185 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14737 (meaning t m 1998) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2881) (meaning t m 3631) (meaning t m 3690) (meaning t m 4431) source

theorem rule14739 (p2017 p2027 p2608 p2685 p2699 p2737 p3931 : Prop) (h : (¬ p2017) ∨ p2027 ∨ (¬ p2685) ∨ (¬ p2608) ∨ (¬ p3931) ∨ (¬ p2737) ∨ p2699) : (¬ p2017) ∨ (p2027) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (p2699) ∨ (¬ p2737) ∨ (¬ p3931) := by
  classical
  tauto

theorem initial14739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2017)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3931)) := by
  have source := ElevenTheory.theory4187 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 3) (m.theta 3 7) (m.theta 7 10)
  exact rule14739 (meaning t m 2017) (meaning t m 2027) (meaning t m 2608) (meaning t m 2685) (meaning t m 2699) (meaning t m 2737) (meaning t m 3931) source

theorem rule14741 (p2006 p2027 p2109 p2169 p2363 p2839 p3857 p4242 : Prop) (h : (¬ p2839) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3857) ∨ (¬ p2109) ∨ (¬ p4242) ∨ (¬ p2006)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2109) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2839) ∨ (¬ p3857) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial14741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2109)) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory4189 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14741 (meaning t m 2006) (meaning t m 2027) (meaning t m 2109) (meaning t m 2169) (meaning t m 2363) (meaning t m 2839) (meaning t m 3857) (meaning t m 4242) source

theorem rule14744 (p1994 p2027 p2630 p2699 p3399 p3631 p4324 p4357 : Prop) (h : (¬ p1994) ∨ (¬ p3631) ∨ (¬ p2630) ∨ (¬ p3399) ∨ p2027 ∨ p2699 ∨ (¬ p4324) ∨ (¬ p4357)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2630) ∨ (p2699) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4324) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial14744 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory4192 t (m.theta 0 1) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 7 9)
  exact rule14744 (meaning t m 1994) (meaning t m 2027) (meaning t m 2630) (meaning t m 2699) (meaning t m 3399) (meaning t m 3631) (meaning t m 4324) (meaning t m 4357) source

theorem rule14745 (p1995 p2027 p2499 p2668 p2997 p3568 p3956 : Prop) (h : (¬ p1995) ∨ p2997 ∨ (¬ p3568) ∨ (¬ p2668) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p2499)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p3956) := by
  classical
  tauto

theorem initial14745 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3956)) := by
  have source := ElevenTheory.theory4193 t (m.theta 1 4) (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14745 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 3956) source

theorem rule14746 (p1987 p2027 p2169 p2737 p3979 p4242 p5612 : Prop) (h : (¬ p1987) ∨ (¬ p2737) ∨ p2169 ∨ (¬ p3979) ∨ p2027 ∨ (¬ p5612) ∨ (¬ p4242)) : (¬ p1987) ∨ (p2027) ∨ (p2169) ∨ (¬ p2737) ∨ (¬ p3979) ∨ (¬ p4242) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial14746 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory4194 t (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 6 8) (m.theta 8 10)
  exact rule14746 (meaning t m 1987) (meaning t m 2027) (meaning t m 2169) (meaning t m 2737) (meaning t m 3979) (meaning t m 4242) (meaning t m 5612) source

theorem rule14748 (p1993 p2027 p2952 p2997 p3097 p3166 p3952 : Prop) (h : (¬ p1993) ∨ (¬ p3097) ∨ (¬ p3166) ∨ (¬ p3952) ∨ (¬ p2952) ∨ p2997 ∨ p2027) : (¬ p1993) ∨ (p2027) ∨ (¬ p2952) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3166) ∨ (¬ p3952) := by
  classical
  tauto

theorem initial14748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1993)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2952)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3952)) := by
  have source := ElevenTheory.theory4196 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6) (m.theta 6 7)
  exact rule14748 (meaning t m 1993) (meaning t m 2027) (meaning t m 2952) (meaning t m 2997) (meaning t m 3097) (meaning t m 3166) (meaning t m 3952) source

theorem rule14750 (p4442 p5644 p5645 p5646 p5647 : Prop) : (p4442) ∨ (((¬ p5645) ∨ (¬ p4442) ∨ (¬ p5644) ∨ (¬ p5646) ∨ (¬ p5647))) := by
  classical
  tauto

theorem initial14750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4442) ∨ (meaning t m 6169) := by
  exact rule14750 (meaning t m 4442) (meaning t m 5644) (meaning t m 5645) (meaning t m 5646) (meaning t m 5647)

theorem rule14755 (p4075 p5649 p5650 p5651 p5652 : Prop) : (p5649) ∨ (((¬ p5649) ∨ (¬ p5650) ∨ (¬ p4075) ∨ (¬ p5651) ∨ (¬ p5652))) := by
  classical
  tauto

theorem initial14755 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5649) ∨ (meaning t m 6170) := by
  exact rule14755 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule14756 (p4075 p5649 p5650 p5651 p5652 : Prop) : (p5650) ∨ (((¬ p5649) ∨ (¬ p5650) ∨ (¬ p4075) ∨ (¬ p5651) ∨ (¬ p5652))) := by
  classical
  tauto

theorem initial14756 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5650) ∨ (meaning t m 6170) := by
  exact rule14756 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule14757 (p4075 p5649 p5650 p5651 p5652 : Prop) : (p4075) ∨ (((¬ p5649) ∨ (¬ p5650) ∨ (¬ p4075) ∨ (¬ p5651) ∨ (¬ p5652))) := by
  classical
  tauto

theorem initial14757 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4075) ∨ (meaning t m 6170) := by
  exact rule14757 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule14758 (p4075 p5649 p5650 p5651 p5652 : Prop) : (p5651) ∨ (((¬ p5649) ∨ (¬ p5650) ∨ (¬ p4075) ∨ (¬ p5651) ∨ (¬ p5652))) := by
  classical
  tauto

theorem initial14758 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5651) ∨ (meaning t m 6170) := by
  exact rule14758 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule14759 (p4075 p5649 p5650 p5651 p5652 : Prop) : (p5652) ∨ (((¬ p5649) ∨ (¬ p5650) ∨ (¬ p4075) ∨ (¬ p5651) ∨ (¬ p5652))) := by
  classical
  tauto

theorem initial14759 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 5652) ∨ (meaning t m 6170) := by
  exact rule14759 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule14760 (p4075 p5649 p5650 p5651 p5652 : Prop) : (¬ p4075) ∨ (¬ p5649) ∨ (¬ p5650) ∨ (¬ p5651) ∨ (¬ p5652) ∨ (¬ ((¬ p5649) ∨ (¬ p5650) ∨ (¬ p4075) ∨ (¬ p5651) ∨ (¬ p5652))) := by
  classical
  tauto

theorem initial14760 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 5649)) ∨ (¬ (meaning t m 5650)) ∨ (¬ (meaning t m 5651)) ∨ (¬ (meaning t m 5652)) ∨ (¬ (meaning t m 6170)) := by
  exact rule14760 (meaning t m 4075) (meaning t m 5649) (meaning t m 5650) (meaning t m 5651) (meaning t m 5652)

theorem rule14763 (p6169 p6170 : Prop) : (¬ ((¬ p6169) ∨ (¬ p6170))) ∨ (¬ p6169) ∨ (¬ p6170) := by
  classical
  tauto

theorem initial14763 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 6168)) ∨ (¬ (meaning t m 6169)) ∨ (¬ (meaning t m 6170)) := by
  exact rule14763 (meaning t m 6169) (meaning t m 6170)

theorem rule14764 (p5642 p6168 : Prop) (h : (p5642 ↔ p6168)) : (¬ p5642) ∨ (p6168) := by
  classical
  tauto

theorem initial14764 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5642)) ∨ (meaning t m 6168) := by
  have source := ElevenTheory.theory4197 t (m.theta 1 10) (m.theta 1 7) (m.theta 7 10)
  exact rule14764 (meaning t m 5642) (meaning t m 6168) source

theorem rule14767 (p1985 p2027 p2608 p2699 p2707 p2717 p3570 : Prop) (h : p2027 ∨ (¬ p3570) ∨ (¬ p2707) ∨ p2699 ∨ (¬ p2608) ∨ (¬ p2717) ∨ (¬ p1985)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial14767 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory4199 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule14767 (meaning t m 1985) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2707) (meaning t m 2717) (meaning t m 3570) source

theorem rule14768 (p1990 p2027 p2696 p2699 p2743 p2839 p2860 p3589 : Prop) (h : p2027 ∨ (¬ p2860) ∨ (¬ p1990) ∨ p2699 ∨ (¬ p2839) ∨ (¬ p3589) ∨ (¬ p2696) ∨ (¬ p2743)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2696) ∨ (p2699) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p2860) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial14768 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory4200 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 5 6)
  exact rule14768 (meaning t m 1990) (meaning t m 2027) (meaning t m 2696) (meaning t m 2699) (meaning t m 2743) (meaning t m 2839) (meaning t m 2860) (meaning t m 3589) source

theorem rule14769 (p1981 p2027 p2352 p2608 p2699 p3367 p3422 : Prop) (h : p2027 ∨ (¬ p3367) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p1981) ∨ (¬ p2352) ∨ (¬ p3422)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2352) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p3367) ∨ (¬ p3422) := by
  classical
  tauto

theorem initial14769 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3422)) := by
  have source := ElevenTheory.theory4201 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8)
  exact rule14769 (meaning t m 1981) (meaning t m 2027) (meaning t m 2352) (meaning t m 2608) (meaning t m 2699) (meaning t m 3367) (meaning t m 3422) source

theorem rule14770 (p1981 p2027 p2187 p2608 p2699 p2839 p2860 : Prop) (h : (¬ p2608) ∨ p2699 ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p1981) ∨ (¬ p2860)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2839) ∨ (¬ p2860) := by
  classical
  tauto

theorem initial14770 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 2860)) := by
  have source := ElevenTheory.theory4202 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 5) (m.theta 5 6) (m.theta 6 8)
  exact rule14770 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2608) (meaning t m 2699) (meaning t m 2839) (meaning t m 2860) source

theorem rule14771 (p1992 p2027 p2696 p2743 p2780 p2997 p3822 : Prop) (h : (¬ p3822) ∨ (¬ p2696) ∨ p2997 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p2743) ∨ (¬ p2780)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2780) ∨ (p2997) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial14771 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2780)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory4203 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule14771 (meaning t m 1992) (meaning t m 2027) (meaning t m 2696) (meaning t m 2743) (meaning t m 2780) (meaning t m 2997) (meaning t m 3822) source

theorem rule14772 (p1995 p2027 p2499 p2573 p2764 p3346 p4022 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p4022) ∨ (¬ p2499) ∨ p2764 ∨ p2027 ∨ (¬ p1995) ∨ (¬ p3346) ∨ (¬ p2573)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (p2764) ∨ (¬ p3346) ∨ (¬ p4022) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial14772 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 4022)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory4204 t (m.theta 0 4) (m.theta 1 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9) (m.theta 9 10)
  exact rule14772 (meaning t m 1995) (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 2764) (meaning t m 3346) (meaning t m 4022) (meaning t m 4191) source

theorem rule14773 (p1981 p2027 p2187 p2241 p2284 p2699 p2992 : Prop) (h : (¬ p2241) ∨ (¬ p1981) ∨ (¬ p2992) ∨ p2699 ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (p2699) ∨ (¬ p2992) := by
  classical
  tauto

theorem initial14773 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2992)) := by
  have source := ElevenTheory.theory4205 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule14773 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2241) (meaning t m 2284) (meaning t m 2699) (meaning t m 2992) source

theorem rule14774 (p1998 p2027 p2241 p2699 p3027 p3256 p4044 p4348 : Prop) (h : p2699 ∨ (¬ p2241) ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3027) ∨ (¬ p4044) ∨ (¬ p3256) ∨ (¬ p4348)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2241) ∨ (p2699) ∨ (¬ p3027) ∨ (¬ p3256) ∨ (¬ p4044) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14774 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4206 t (m.theta 0 1) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14774 (meaning t m 1998) (meaning t m 2027) (meaning t m 2241) (meaning t m 2699) (meaning t m 3027) (meaning t m 3256) (meaning t m 4044) (meaning t m 4348) source

theorem rule14776 (p1976 p2027 p2169 p2363 p3365 p4118 p4195 p4196 : Prop) (h : (¬ p4195) ∨ p2169 ∨ (¬ p3365) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p4196) ∨ (¬ p4118)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial14776 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory4208 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14776 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 3365) (meaning t m 4118) (meaning t m 4195) (meaning t m 4196) source

theorem rule14777 (p1976 p2027 p2766 p3324 p3365 p4195 p4347 : Prop) (h : p2766 ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p1976) ∨ (¬ p3324) ∨ (¬ p4347) ∨ p2027) : (¬ p1976) ∨ (p2027) ∨ (p2766) ∨ (¬ p3324) ∨ (¬ p3365) ∨ (¬ p4195) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial14777 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory4209 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14777 (meaning t m 1976) (meaning t m 2027) (meaning t m 2766) (meaning t m 3324) (meaning t m 3365) (meaning t m 4195) (meaning t m 4347) source

theorem rule14778 (p1998 p2027 p2363 p2668 p2997 p3568 p4348 : Prop) (h : (¬ p2363) ∨ (¬ p3568) ∨ (¬ p2668) ∨ (¬ p4348) ∨ p2027 ∨ p2997 ∨ (¬ p1998)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (p2997) ∨ (¬ p3568) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14778 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2668)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4210 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14778 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2668) (meaning t m 2997) (meaning t m 3568) (meaning t m 4348) source

theorem rule14782 (p2009 p2027 p2545 p2810 p3005 p3256 p3857 : Prop) (h : (¬ p3256) ∨ (¬ p2009) ∨ p2027 ∨ (¬ p3857) ∨ p2545 ∨ (¬ p3005) ∨ (¬ p2810)) : (¬ p2009) ∨ (p2027) ∨ (p2545) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3857) := by
  classical
  tauto

theorem initial14782 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2009)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) := by
  have source := ElevenTheory.theory4214 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule14782 (meaning t m 2009) (meaning t m 2027) (meaning t m 2545) (meaning t m 2810) (meaning t m 3005) (meaning t m 3256) (meaning t m 3857) source

theorem rule14786 (p2001 p2027 p2363 p2819 p2997 p3692 p3822 : Prop) (h : p2027 ∨ p2997 ∨ (¬ p3692) ∨ (¬ p3822) ∨ (¬ p2819) ∨ (¬ p2001) ∨ (¬ p2363)) : (¬ p2001) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2819) ∨ (p2997) ∨ (¬ p3692) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial14786 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory4218 t (m.theta 2 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule14786 (meaning t m 2001) (meaning t m 2027) (meaning t m 2363) (meaning t m 2819) (meaning t m 2997) (meaning t m 3692) (meaning t m 3822) source

theorem rule14787 (p2015 p2027 p2774 p2819 p2842 p3055 p3923 : Prop) (h : (¬ p2015) ∨ (¬ p2774) ∨ (¬ p3923) ∨ p2027 ∨ (¬ p2819) ∨ p2842 ∨ (¬ p3055)) : (¬ p2015) ∨ (p2027) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (p2842) ∨ (¬ p3055) ∨ (¬ p3923) := by
  classical
  tauto

theorem initial14787 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2015)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3923)) := by
  have source := ElevenTheory.theory4219 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8)
  exact rule14787 (meaning t m 2015) (meaning t m 2027) (meaning t m 2774) (meaning t m 2819) (meaning t m 2842) (meaning t m 3055) (meaning t m 3923) source

theorem rule14788 (p1992 p2027 p2138 p2383 p2786 p3474 p3688 p4358 : Prop) (h : (¬ p1992) ∨ p3474 ∨ (¬ p3688) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p2786) ∨ (¬ p2383) ∨ (¬ p4358)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2138) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (p3474) ∨ (¬ p3688) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial14788 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2786)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory4220 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 6 8)
  exact rule14788 (meaning t m 1992) (meaning t m 2027) (meaning t m 2138) (meaning t m 2383) (meaning t m 2786) (meaning t m 3474) (meaning t m 3688) (meaning t m 4358) source

theorem rule14789 (p1992 p2027 p2743 p2997 p3323 p3361 p3568 p3946 p3983 : Prop) (h : p2997 ∨ p2027 ∨ (¬ p1992) ∨ (¬ p3946) ∨ (¬ p3323) ∨ (¬ p3983) ∨ (¬ p3568) ∨ (¬ p2743) ∨ (¬ p3361)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2743) ∨ (p2997) ∨ (¬ p3323) ∨ (¬ p3361) ∨ (¬ p3568) ∨ (¬ p3946) ∨ (¬ p3983) := by
  classical
  tauto

theorem initial14789 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2743)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 3983)) := by
  have source := ElevenTheory.theory4221 t (m.theta 0 3) (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9)
  exact rule14789 (meaning t m 1992) (meaning t m 2027) (meaning t m 2743) (meaning t m 2997) (meaning t m 3323) (meaning t m 3361) (meaning t m 3568) (meaning t m 3946) (meaning t m 3983) source

theorem rule14791 (p1992 p2027 p2169 p2363 p2743 p2963 p3361 p4118 p4196 : Prop) (h : (¬ p3361) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p4196) ∨ p2027 ∨ (¬ p1992) ∨ p2169 ∨ (¬ p4118) ∨ (¬ p2363)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2743) ∨ (¬ p2963) ∨ (¬ p3361) ∨ (¬ p4118) ∨ (¬ p4196) := by
  classical
  tauto

theorem initial14791 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4196)) := by
  have source := ElevenTheory.theory4223 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14791 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2743) (meaning t m 2963) (meaning t m 3361) (meaning t m 4118) (meaning t m 4196) source

theorem rule14793 (p1977 p2027 p2545 p2668 p2797 p2810 p3923 p4245 : Prop) (h : (¬ p2668) ∨ (¬ p4245) ∨ (¬ p1977) ∨ p2545 ∨ (¬ p2810) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p3923)) : (¬ p1977) ∨ (p2027) ∨ (p2545) ∨ (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3923) ∨ (¬ p4245) := by
  classical
  tauto

theorem initial14793 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4245)) := by
  have source := ElevenTheory.theory4225 t (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule14793 (meaning t m 1977) (meaning t m 2027) (meaning t m 2545) (meaning t m 2668) (meaning t m 2797) (meaning t m 2810) (meaning t m 3923) (meaning t m 4245) source

theorem rule14794 (p1994 p2027 p2493 p2509 p2766 p3574 p4347 p4432 : Prop) (h : (¬ p4432) ∨ (¬ p1994) ∨ (¬ p2509) ∨ (¬ p2493) ∨ p2027 ∨ (¬ p3574) ∨ p2766 ∨ (¬ p4347)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (p2766) ∨ (¬ p3574) ∨ (¬ p4347) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial14794 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory4226 t (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule14794 (meaning t m 1994) (meaning t m 2027) (meaning t m 2493) (meaning t m 2509) (meaning t m 2766) (meaning t m 3574) (meaning t m 4347) (meaning t m 4432) source

theorem rule14796 (p1977 p2027 p2331 p2766 p3172 p4118 p4154 : Prop) (h : p2766 ∨ (¬ p4118) ∨ (¬ p2331) ∨ (¬ p1977) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p4154)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2331) ∨ (p2766) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4154) := by
  classical
  tauto

theorem initial14796 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4154)) := by
  have source := ElevenTheory.theory4228 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 8 9)
  exact rule14796 (meaning t m 1977) (meaning t m 2027) (meaning t m 2331) (meaning t m 2766) (meaning t m 3172) (meaning t m 4118) (meaning t m 4154) source

theorem rule14801 (p1994 p2027 p2573 p2727 p2914 p3540 p4154 p4389 : Prop) (h : (¬ p2727) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p1994) ∨ (¬ p4154) ∨ (¬ p4389) ∨ p2914 ∨ (¬ p2573)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2573) ∨ (¬ p2727) ∨ (p2914) ∨ (¬ p3540) ∨ (¬ p4154) ∨ (¬ p4389) := by
  classical
  tauto

theorem initial14801 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2727)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4389)) := by
  have source := ElevenTheory.theory4233 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7)
  exact rule14801 (meaning t m 1994) (meaning t m 2027) (meaning t m 2573) (meaning t m 2727) (meaning t m 2914) (meaning t m 3540) (meaning t m 4154) (meaning t m 4389) source

theorem rule14802 (p1998 p2027 p2264 p2611 p2696 p2707 p2743 p4325 : Prop) (h : (¬ p2696) ∨ (¬ p4325) ∨ (¬ p2264) ∨ (¬ p2707) ∨ (¬ p1998) ∨ p2611 ∨ (¬ p2743) ∨ p2027) : (¬ p1998) ∨ (p2027) ∨ (¬ p2264) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p4325) := by
  classical
  tauto

theorem initial14802 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 4325)) := by
  have source := ElevenTheory.theory4234 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule14802 (meaning t m 1998) (meaning t m 2027) (meaning t m 2264) (meaning t m 2611) (meaning t m 2696) (meaning t m 2707) (meaning t m 2743) (meaning t m 4325) source

theorem rule14803 (p1995 p2027 p2230 p2437 p3008 p3238 p3540 p3574 : Prop) (h : p2027 ∨ (¬ p3238) ∨ (¬ p2230) ∨ (¬ p1995) ∨ p3008 ∨ (¬ p3574) ∨ (¬ p3540) ∨ (¬ p2437)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2437) ∨ (p3008) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial14803 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory4235 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule14803 (meaning t m 1995) (meaning t m 2027) (meaning t m 2230) (meaning t m 2437) (meaning t m 3008) (meaning t m 3238) (meaning t m 3540) (meaning t m 3574) source

theorem rule14804 (p1986 p2027 p2230 p2462 p3540 p3684 p3690 p4001 : Prop) (h : p2462 ∨ p2027 ∨ (¬ p2230) ∨ (¬ p4001) ∨ (¬ p3690) ∨ (¬ p1986) ∨ (¬ p3684) ∨ (¬ p3540)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2230) ∨ (p2462) ∨ (¬ p3540) ∨ (¬ p3684) ∨ (¬ p3690) ∨ (¬ p4001) := by
  classical
  tauto

theorem initial14804 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4001)) := by
  have source := ElevenTheory.theory4236 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14804 (meaning t m 1986) (meaning t m 2027) (meaning t m 2230) (meaning t m 2462) (meaning t m 3540) (meaning t m 3684) (meaning t m 3690) (meaning t m 4001) source

theorem rule14805 (p1987 p2027 p2287 p2307 p2737 p3567 p3688 p3822 : Prop) (h : (¬ p2307) ∨ (¬ p3822) ∨ p2287 ∨ (¬ p3688) ∨ p2027 ∨ (¬ p1987) ∨ (¬ p2737) ∨ (¬ p3567)) : (¬ p1987) ∨ (p2027) ∨ (p2287) ∨ (¬ p2307) ∨ (¬ p2737) ∨ (¬ p3567) ∨ (¬ p3688) ∨ (¬ p3822) := by
  classical
  tauto

theorem initial14805 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3822)) := by
  have source := ElevenTheory.theory4237 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6) (m.theta 6 7)
  exact rule14805 (meaning t m 1987) (meaning t m 2027) (meaning t m 2287) (meaning t m 2307) (meaning t m 2737) (meaning t m 3567) (meaning t m 3688) (meaning t m 3822) source

theorem rule14806 (p1981 p2027 p2122 p2611 p2774 p3063 p3549 : Prop) (h : p2027 ∨ (¬ p1981) ∨ (¬ p3063) ∨ (¬ p3549) ∨ p2611 ∨ (¬ p2774) ∨ (¬ p2122)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2122) ∨ (p2611) ∨ (¬ p2774) ∨ (¬ p3063) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial14806 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory4238 t (m.theta 0 2) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8)
  exact rule14806 (meaning t m 1981) (meaning t m 2027) (meaning t m 2122) (meaning t m 2611) (meaning t m 2774) (meaning t m 3063) (meaning t m 3549) source

theorem rule14810 (p1991 p2027 p2299 p2766 p2963 p3568 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3568) ∨ p2766 ∨ (¬ p1991) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2963)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2299) ∨ (p2766) ∨ (¬ p2963) ∨ (¬ p3568) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14810 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4242 t (m.theta 0 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14810 (meaning t m 1991) (meaning t m 2027) (meaning t m 2299) (meaning t m 2766) (meaning t m 2963) (meaning t m 3568) (meaning t m 4348) source

theorem rule14813 (p1997 p2027 p2611 p2696 p2743 p2850 p3367 : Prop) (h : (¬ p1997) ∨ (¬ p3367) ∨ (¬ p2850) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p2743) ∨ p2611) : (¬ p1997) ∨ (p2027) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2850) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial14813 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory4245 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule14813 (meaning t m 1997) (meaning t m 2027) (meaning t m 2611) (meaning t m 2696) (meaning t m 2743) (meaning t m 2850) (meaning t m 3367) source

theorem rule14814 (p1998 p2027 p2699 p2707 p2717 p2774 p3589 p3688 : Prop) (h : p2027 ∨ (¬ p2717) ∨ (¬ p2707) ∨ (¬ p1998) ∨ (¬ p3589) ∨ (¬ p3688) ∨ (¬ p2774) ∨ p2699) : (¬ p1998) ∨ (p2027) ∨ (p2699) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2774) ∨ (¬ p3589) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial14814 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory4246 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 7 8)
  exact rule14814 (meaning t m 1998) (meaning t m 2027) (meaning t m 2699) (meaning t m 2707) (meaning t m 2717) (meaning t m 2774) (meaning t m 3589) (meaning t m 3688) source

theorem rule14815 (p1998 p2027 p2177 p2295 p2611 p2696 p2797 : Prop) (h : p2611 ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2797) ∨ p2027) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (¬ p2295) ∨ (p2611) ∨ (¬ p2696) ∨ (¬ p2797) := by
  classical
  tauto

theorem initial14815 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2295)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) := by
  have source := ElevenTheory.theory4247 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 6) (m.theta 6 7) (m.theta 7 8)
  exact rule14815 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2295) (meaning t m 2611) (meaning t m 2696) (meaning t m 2797) source

theorem rule14816 (p1986 p2027 p2417 p2914 p3367 p3588 p4324 : Prop) (h : p2914 ∨ (¬ p4324) ∨ (¬ p3588) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p1986) ∨ (¬ p3367)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2417) ∨ (p2914) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p4324) := by
  classical
  tauto

theorem initial14816 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4324)) := by
  have source := ElevenTheory.theory4248 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule14816 (meaning t m 1986) (meaning t m 2027) (meaning t m 2417) (meaning t m 2914) (meaning t m 3367) (meaning t m 3588) (meaning t m 4324) source

theorem rule14817 (p2001 p2027 p2611 p2619 p2774 p2839 p3688 : Prop) (h : p2027 ∨ (¬ p2619) ∨ (¬ p2001) ∨ p2611 ∨ (¬ p2839) ∨ (¬ p2774) ∨ (¬ p3688)) : (¬ p2001) ∨ (p2027) ∨ (p2611) ∨ (¬ p2619) ∨ (¬ p2774) ∨ (¬ p2839) ∨ (¬ p3688) := by
  classical
  tauto

theorem initial14817 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2001)) ∨ (meaning t m 2027) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3688)) := by
  have source := ElevenTheory.theory4249 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 8)
  exact rule14817 (meaning t m 2001) (meaning t m 2027) (meaning t m 2611) (meaning t m 2619) (meaning t m 2774) (meaning t m 2839) (meaning t m 3688) source

theorem rule14819 (p1998 p2027 p2177 p2611 p3434 p3471 p4107 : Prop) (h : p2027 ∨ (¬ p3471) ∨ (¬ p1998) ∨ (¬ p2177) ∨ (¬ p3434) ∨ p2611 ∨ (¬ p4107)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2177) ∨ (p2611) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4107) := by
  classical
  tauto

theorem initial14819 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4107)) := by
  have source := ElevenTheory.theory4251 t (m.theta 0 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14819 (meaning t m 1998) (meaning t m 2027) (meaning t m 2177) (meaning t m 2611) (meaning t m 3434) (meaning t m 3471) (meaning t m 4107) source

theorem rule14820 (p1986 p2027 p2109 p3146 p3367 p3578 p3857 p4242 : Prop) (h : p2027 ∨ (¬ p3146) ∨ p3578 ∨ (¬ p4242) ∨ (¬ p2109) ∨ (¬ p1986) ∨ (¬ p3367) ∨ (¬ p3857)) : (¬ p1986) ∨ (p2027) ∨ (¬ p2109) ∨ (¬ p3146) ∨ (¬ p3367) ∨ (p3578) ∨ (¬ p3857) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial14820 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2109)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3367)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory4252 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 4) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule14820 (meaning t m 1986) (meaning t m 2027) (meaning t m 2109) (meaning t m 3146) (meaning t m 3367) (meaning t m 3578) (meaning t m 3857) (meaning t m 4242) source

theorem rule14821 (p1995 p2027 p2608 p2699 p2850 p3238 p3367 : Prop) (h : p2699 ∨ (¬ p2608) ∨ (¬ p3367) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p1995)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2608) ∨ (p2699) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p3367) := by
  classical
  tauto

theorem initial14821 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3367)) := by
  have source := ElevenTheory.theory4253 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule14821 (meaning t m 1995) (meaning t m 2027) (meaning t m 2608) (meaning t m 2699) (meaning t m 2850) (meaning t m 3238) (meaning t m 3367) source

theorem rule14823 (p1985 p2027 p2873 p3399 p3527 p3555 p3570 : Prop) (h : p2873 ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p1985) ∨ (¬ p3570) ∨ (¬ p3527)) : (¬ p1985) ∨ (p2027) ∨ (p2873) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3555) ∨ (¬ p3570) := by
  classical
  tauto

theorem initial14823 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3570)) := by
  have source := ElevenTheory.theory4255 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 7) (m.theta 7 8)
  exact rule14823 (meaning t m 1985) (meaning t m 2027) (meaning t m 2873) (meaning t m 3399) (meaning t m 3527) (meaning t m 3555) (meaning t m 3570) source

theorem rule14824 (p1994 p2027 p2651 p2938 p3246 p3414 p3947 : Prop) (h : (¬ p1994) ∨ p2938 ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2651) ∨ (¬ p3947) ∨ (¬ p3414)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2651) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3414) ∨ (¬ p3947) := by
  classical
  tauto

theorem initial14824 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) := by
  have source := ElevenTheory.theory4256 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 7) (m.theta 7 9)
  exact rule14824 (meaning t m 1994) (meaning t m 2027) (meaning t m 2651) (meaning t m 2938) (meaning t m 3246) (meaning t m 3414) (meaning t m 3947) source

theorem rule14825 (p1982 p2027 p2699 p3093 p3319 p3461 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3093) ∨ (¬ p3319) ∨ p2027 ∨ p2699 ∨ (¬ p3461) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3461) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14825 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4257 t (m.theta 0 1) (m.theta 1 6) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14825 (meaning t m 1982) (meaning t m 2027) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 3461) (meaning t m 4444) source

theorem rule14827 (p1983 p2027 p2148 p2299 p2396 p2881 p3051 : Prop) (h : (¬ p2396) ∨ p2148 ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p2299)) : (¬ p1983) ∨ (p2027) ∨ (p2148) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3051) := by
  classical
  tauto

theorem initial14827 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) := by
  have source := ElevenTheory.theory4259 t (m.theta 0 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14827 (meaning t m 1983) (meaning t m 2027) (meaning t m 2148) (meaning t m 2299) (meaning t m 2396) (meaning t m 2881) (meaning t m 3051) source

theorem rule14828 (p1992 p2027 p2462 p2608 p2928 p3452 p4278 : Prop) (h : (¬ p2928) ∨ (¬ p1992) ∨ (¬ p2608) ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3452) ∨ p2462) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2608) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14828 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4260 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 4 7) (m.theta 7 9)
  exact rule14828 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2608) (meaning t m 2928) (meaning t m 3452) (meaning t m 4278) source

theorem rule14830 (p1995 p2027 p2299 p2396 p2633 p2928 p4278 : Prop) (h : p2633 ∨ (¬ p1995) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p2396) ∨ (¬ p2299) ∨ (¬ p2928)) : (¬ p1995) ∨ (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (p2633) ∨ (¬ p2928) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14830 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1995)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4262 t (m.theta 1 4) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule14830 (meaning t m 1995) (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 2633) (meaning t m 2928) (meaning t m 4278) source

theorem rule14831 (p1975 p2027 p2284 p2299 p2323 p2881 p2946 p3872 : Prop) (h : p2323 ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3872) ∨ (¬ p2299) ∨ (¬ p2881)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2299) ∨ (p2323) ∨ (¬ p2881) ∨ (¬ p2946) ∨ (¬ p3872) := by
  classical
  tauto

theorem initial14831 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3872)) := by
  have source := ElevenTheory.theory4263 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule14831 (meaning t m 1975) (meaning t m 2027) (meaning t m 2284) (meaning t m 2299) (meaning t m 2323) (meaning t m 2881) (meaning t m 2946) (meaning t m 3872) source

theorem rule14833 (p1982 p2027 p2187 p2284 p2323 p2363 p2946 : Prop) (h : p2027 ∨ p2323 ∨ (¬ p2284) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p2946) ∨ (¬ p1982)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (p2323) ∨ (¬ p2363) ∨ (¬ p2946) := by
  classical
  tauto

theorem initial14833 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2946)) := by
  have source := ElevenTheory.theory4265 t (m.theta 0 3) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14833 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2323) (meaning t m 2363) (meaning t m 2946) source

theorem rule14834 (p1984 p2027 p2534 p2766 p3585 p3874 p3954 : Prop) (h : p2766 ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p1984) ∨ (¬ p3874) ∨ (¬ p2534)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2534) ∨ (p2766) ∨ (¬ p3585) ∨ (¬ p3874) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial14834 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory4266 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 8) (m.theta 8 9)
  exact rule14834 (meaning t m 1984) (meaning t m 2027) (meaning t m 2534) (meaning t m 2766) (meaning t m 3585) (meaning t m 3874) (meaning t m 3954) source

theorem rule14835 (p1984 p2027 p2509 p2914 p3452 p3641 p3876 : Prop) (h : (¬ p3452) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p3641) ∨ p2914 ∨ (¬ p3876)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2509) ∨ (p2914) ∨ (¬ p3452) ∨ (¬ p3641) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial14835 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (meaning t m 2914) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory4267 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8)
  exact rule14835 (meaning t m 1984) (meaning t m 2027) (meaning t m 2509) (meaning t m 2914) (meaning t m 3452) (meaning t m 3641) (meaning t m 3876) source

theorem rule14836 (p1984 p2027 p2462 p3585 p3876 p3954 p4278 : Prop) (h : (¬ p4278) ∨ (¬ p3954) ∨ p2462 ∨ (¬ p3585) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p1984)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p3585) ∨ (¬ p3876) ∨ (¬ p3954) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14836 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4268 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9)
  exact rule14836 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 3585) (meaning t m 3876) (meaning t m 3954) (meaning t m 4278) source

theorem rule14837 (p1982 p2027 p2187 p2331 p2363 p2388 p2952 p3986 : Prop) (h : p2388 ∨ (¬ p1982) ∨ (¬ p2187) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3986) ∨ (¬ p2952) ∨ (¬ p2331)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (p2388) ∨ (¬ p2952) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial14837 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory4269 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule14837 (meaning t m 1982) (meaning t m 2027) (meaning t m 2187) (meaning t m 2331) (meaning t m 2363) (meaning t m 2388) (meaning t m 2952) (meaning t m 3986) source

theorem rule14838 (p1982 p2027 p2323 p2437 p2459 p2651 p2911 : Prop) (h : p2323 ∨ (¬ p1982) ∨ (¬ p2437) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2911)) : (¬ p1982) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2911) := by
  classical
  tauto

theorem initial14838 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2911)) := by
  have source := ElevenTheory.theory4270 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule14838 (meaning t m 1982) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2459) (meaning t m 2651) (meaning t m 2911) source

theorem rule14840 (p1998 p2027 p2437 p2622 p2911 p3422 p3475 p3574 : Prop) (h : (¬ p1998) ∨ p2622 ∨ (¬ p2911) ∨ (¬ p3574) ∨ (¬ p3422) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p3475)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2437) ∨ (p2622) ∨ (¬ p2911) ∨ (¬ p3422) ∨ (¬ p3475) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial14840 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3475)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory4272 t (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule14840 (meaning t m 1998) (meaning t m 2027) (meaning t m 2437) (meaning t m 2622) (meaning t m 2911) (meaning t m 3422) (meaning t m 3475) (meaning t m 3574) source

theorem rule14843 (p1975 p2027 p2148 p2299 p2962 p3527 p3654 p4026 p4452 : Prop) (h : (¬ p1975) ∨ (¬ p3654) ∨ p2148 ∨ (¬ p2299) ∨ (¬ p2962) ∨ p2027 ∨ (¬ p3527) ∨ (¬ p4452) ∨ (¬ p4026)) : (¬ p1975) ∨ (p2027) ∨ (p2148) ∨ (¬ p2299) ∨ (¬ p2962) ∨ (¬ p3527) ∨ (¬ p3654) ∨ (¬ p4026) ∨ (¬ p4452) := by
  classical
  tauto

theorem initial14843 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2962)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4452)) := by
  have source := ElevenTheory.theory4275 t (m.theta 0 5) (m.theta 0 6) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule14843 (meaning t m 1975) (meaning t m 2027) (meaning t m 2148) (meaning t m 2299) (meaning t m 2962) (meaning t m 3527) (meaning t m 3654) (meaning t m 4026) (meaning t m 4452) source

theorem rule14844 (p1987 p2027 p2766 p2946 p3172 p4118 p4315 : Prop) (h : (¬ p2946) ∨ (¬ p3172) ∨ p2027 ∨ p2766 ∨ (¬ p4118) ∨ (¬ p4315) ∨ (¬ p1987)) : (¬ p1987) ∨ (p2027) ∨ (p2766) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial14844 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory4276 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 8) (m.theta 8 9)
  exact rule14844 (meaning t m 1987) (meaning t m 2027) (meaning t m 2766) (meaning t m 2946) (meaning t m 3172) (meaning t m 4118) (meaning t m 4315) source

theorem rule14846 (p1987 p2027 p2589 p2737 p2765 p3363 p3585 p4110 : Prop) (h : (¬ p1987) ∨ (¬ p4110) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p2737) ∨ p2765 ∨ (¬ p3363) ∨ (¬ p2589)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2589) ∨ (¬ p2737) ∨ (p2765) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14846 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2737)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4278 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule14846 (meaning t m 1987) (meaning t m 2027) (meaning t m 2589) (meaning t m 2737) (meaning t m 2765) (meaning t m 3363) (meaning t m 3585) (meaning t m 4110) source

theorem rule14847 (p1992 p2027 p2287 p2598 p3365 p3585 p4195 : Prop) (h : (¬ p4195) ∨ p2287 ∨ (¬ p3365) ∨ (¬ p1992) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p2598)) : (¬ p1992) ∨ (p2027) ∨ (p2287) ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3585) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial14847 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4279 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule14847 (meaning t m 1992) (meaning t m 2027) (meaning t m 2287) (meaning t m 2598) (meaning t m 3365) (meaning t m 3585) (meaning t m 4195) source

theorem rule14849 (p1991 p2027 p2685 p2765 p3414 p3952 p4315 : Prop) (h : (¬ p3952) ∨ p2765 ∨ p2027 ∨ (¬ p1991) ∨ (¬ p4315) ∨ (¬ p2685) ∨ (¬ p3414)) : (¬ p1991) ∨ (p2027) ∨ (¬ p2685) ∨ (p2765) ∨ (¬ p3414) ∨ (¬ p3952) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial14849 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory4281 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule14849 (meaning t m 1991) (meaning t m 2027) (meaning t m 2685) (meaning t m 2765) (meaning t m 3414) (meaning t m 3952) (meaning t m 4315) source

theorem rule14850 (p1996 p2027 p2287 p2651 p2685 p2810 p2963 : Prop) (h : p2027 ∨ (¬ p1996) ∨ (¬ p2685) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p2963) ∨ p2287) : (¬ p1996) ∨ (p2027) ∨ (p2287) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p2963) := by
  classical
  tauto

theorem initial14850 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2287) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2963)) := by
  have source := ElevenTheory.theory4282 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7)
  exact rule14850 (meaning t m 1996) (meaning t m 2027) (meaning t m 2287) (meaning t m 2651) (meaning t m 2685) (meaning t m 2810) (meaning t m 2963) source

theorem rule14851 (p1979 p2027 p2114 p2319 p2641 p2749 p3136 p3516 p3567 p4324 p4357 : Prop) (h : (¬ p3516) ∨ (¬ p3567) ∨ (¬ p2641) ∨ p2114 ∨ (¬ p4357) ∨ p2027 ∨ (¬ p2749) ∨ (¬ p3136) ∨ (¬ p1979) ∨ (¬ p4324) ∨ (¬ p2319)) : (¬ p1979) ∨ (p2027) ∨ (p2114) ∨ (¬ p2319) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3136) ∨ (¬ p3516) ∨ (¬ p3567) ∨ (¬ p4324) ∨ (¬ p4357) := by
  classical
  tauto

theorem initial14851 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4357)) := by
  have source := ElevenTheory.theory4283 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 5) (m.theta 3 6) (m.theta 7 9)
  exact rule14851 (meaning t m 1979) (meaning t m 2027) (meaning t m 2114) (meaning t m 2319) (meaning t m 2641) (meaning t m 2749) (meaning t m 3136) (meaning t m 3516) (meaning t m 3567) (meaning t m 4324) (meaning t m 4357) source

theorem rule14852 (p2641 p2742 p4195 : Prop) (h : (¬ p2641) ∨ (¬ p4195) ∨ (¬ p2742)) : (¬ p2641) ∨ (¬ p2742) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial14852 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory4284 (m.theta 1 3) (m.theta 2 3) (m.theta 3 6)
  exact rule14852 (meaning t m 2641) (meaning t m 2742) (meaning t m 4195) source

theorem rule14853 (p1984 p2027 p2766 p3238 p3452 p3692 p3880 : Prop) (h : (¬ p3238) ∨ p2766 ∨ (¬ p1984) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3692)) : (¬ p1984) ∨ (p2027) ∨ (p2766) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial14853 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory4285 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule14853 (meaning t m 1984) (meaning t m 2027) (meaning t m 2766) (meaning t m 3238) (meaning t m 3452) (meaning t m 3692) (meaning t m 3880) source

theorem rule14854 (p2027 p2373 p2946 p3172 p3906 p4288 p4702 : Prop) (h : (¬ p3172) ∨ (¬ p3906) ∨ (¬ p4288) ∨ p2027 ∨ (¬ p4702) ∨ (¬ p2373) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3906) ∨ (¬ p4288) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial14854 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4288)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory4286 t (m.theta 0 3) (m.theta 1 8) (m.theta 3 5) (m.theta 3 8) (m.theta 4 5) (m.theta 5 8)
  exact rule14854 (meaning t m 2027) (meaning t m 2373) (meaning t m 2946) (meaning t m 3172) (meaning t m 3906) (meaning t m 4288) (meaning t m 4702) source

theorem rule14855 (p1988 p2027 p2264 p2459 p2622 p2685 p3266 : Prop) (h : (¬ p2264) ∨ p2622 ∨ (¬ p1988) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p2685)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (p2622) ∨ (¬ p2685) ∨ (¬ p3266) := by
  classical
  tauto

theorem initial14855 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3266)) := by
  have source := ElevenTheory.theory4287 t (m.theta 2 3) (m.theta 3 7) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule14855 (meaning t m 1988) (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2622) (meaning t m 2685) (meaning t m 3266) source

theorem rule14858 (p1984 p2027 p2462 p3238 p3452 p3690 p4235 : Prop) (h : p2027 ∨ (¬ p1984) ∨ (¬ p3238) ∨ (¬ p4235) ∨ p2462 ∨ (¬ p3452) ∨ (¬ p3690)) : (¬ p1984) ∨ (p2027) ∨ (p2462) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3690) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial14858 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory4290 t (m.theta 0 1) (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule14858 (meaning t m 1984) (meaning t m 2027) (meaning t m 2462) (meaning t m 3238) (meaning t m 3452) (meaning t m 3690) (meaning t m 4235) source

theorem rule14859 (p1994 p2622 p2651 p4787 : Prop) (h : p2622 ∨ (¬ p1994) ∨ (¬ p2651) ∨ p4787) : (¬ p1994) ∨ (p2622) ∨ (¬ p2651) ∨ (p4787) := by
  classical
  tauto

theorem initial14859 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 4787) := by
  have source := ElevenTheory.theory4291 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4)
  exact rule14859 (meaning t m 1994) (meaning t m 2622) (meaning t m 2651) (meaning t m 4787) source

theorem rule14860 (p1984 p2027 p2765 p3585 p3684 p3954 p4110 : Prop) (h : (¬ p1984) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p3585) ∨ (¬ p3684) ∨ p2765) : (¬ p1984) ∨ (p2027) ∨ (p2765) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial14860 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory4292 t (m.theta 0 1) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule14860 (meaning t m 1984) (meaning t m 2027) (meaning t m 2765) (meaning t m 3585) (meaning t m 3684) (meaning t m 3954) (meaning t m 4110) source

theorem rule14862 (p1984 p2027 p2202 p2440 p2509 p3083 p3452 : Prop) (h : (¬ p2440) ∨ p2202 ∨ (¬ p1984) ∨ (¬ p2509) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3083)) : (¬ p1984) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p2509) ∨ (¬ p3083) ∨ (¬ p3452) := by
  classical
  tauto

theorem initial14862 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3452)) := by
  have source := ElevenTheory.theory4294 t (m.theta 0 1) (m.theta 1 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule14862 (meaning t m 1984) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 2509) (meaning t m 3083) (meaning t m 3452) source

theorem rule14863 (p1984 p2027 p2406 p2589 p2764 p3193 p4108 p4425 : Prop) (h : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p1984) ∨ (¬ p4108) ∨ p2027 ∨ (¬ p3193) ∨ (¬ p4425) ∨ p2764) : (¬ p1984) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (p2764) ∨ (¬ p3193) ∨ (¬ p4108) ∨ (¬ p4425) := by
  classical
  tauto

theorem initial14863 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4425)) := by
  have source := ElevenTheory.theory4295 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule14863 (meaning t m 1984) (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2764) (meaning t m 3193) (meaning t m 4108) (meaning t m 4425) source

theorem rule14864 (p1976 p2027 p2406 p2509 p3055 p3498 p3684 : Prop) (h : p3498 ∨ p2027 ∨ (¬ p2509) ∨ (¬ p3684) ∨ (¬ p2406) ∨ (¬ p3055) ∨ (¬ p1976)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p3055) ∨ (p3498) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial14864 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3055)) ∨ (meaning t m 3498) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory4296 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 8)
  exact rule14864 (meaning t m 1976) (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 3055) (meaning t m 3498) (meaning t m 3684) source

theorem rule14867 (p1984 p2027 p2406 p2462 p2589 p2928 p4108 p4278 : Prop) (h : (¬ p4278) ∨ p2462 ∨ (¬ p2928) ∨ (¬ p4108) ∨ p2027 ∨ (¬ p1984) ∨ (¬ p2406) ∨ (¬ p2589)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2406) ∨ (p2462) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p4108) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14867 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4299 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 9)
  exact rule14867 (meaning t m 1984) (meaning t m 2027) (meaning t m 2406) (meaning t m 2462) (meaning t m 2589) (meaning t m 2928) (meaning t m 4108) (meaning t m 4278) source

theorem rule14873 (p3546 p3551 p4189 p5307 : Prop) (h : (¬ p5307) ∨ (¬ p3546) ∨ (¬ p4189) ∨ (¬ p3551)) : (¬ p3546) ∨ (¬ p3551) ∨ (¬ p4189) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial14873 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory4305 (m.theta 0 7) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8)
  exact rule14873 (meaning t m 3546) (meaning t m 3551) (meaning t m 4189) (meaning t m 5307) source

theorem rule14878 (p1982 p2027 p2169 p3096 p3461 p3564 p3989 p4444 : Prop) (h : (¬ p4444) ∨ (¬ p3096) ∨ (¬ p1982) ∨ (¬ p3564) ∨ (¬ p3461) ∨ p2027 ∨ p2169 ∨ (¬ p3989)) : (¬ p1982) ∨ (p2027) ∨ (p2169) ∨ (¬ p3096) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3989) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial14878 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory4310 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule14878 (meaning t m 1982) (meaning t m 2027) (meaning t m 2169) (meaning t m 3096) (meaning t m 3461) (meaning t m 3564) (meaning t m 3989) (meaning t m 4444) source

theorem rule14879 (p1976 p3055 p3586 p5221 : Prop) (h : p3586 ∨ (¬ p1976) ∨ p5221 ∨ (¬ p3055)) : (¬ p1976) ∨ (¬ p3055) ∨ (p3586) ∨ (p5221) := by
  classical
  tauto

theorem initial14879 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (¬ (meaning t m 3055)) ∨ (meaning t m 3586) ∨ (meaning t m 5221) := by
  have source := ElevenTheory.theory4311 t (m.theta 0 2) (m.theta 2 4) (m.theta 2 6)
  exact rule14879 (meaning t m 1976) (meaning t m 3055) (meaning t m 3586) (meaning t m 5221) source

theorem rule14881 (p1998 p2027 p2323 p2437 p2528 p2651 p3875 p4348 : Prop) (h : p2323 ∨ (¬ p2651) ∨ (¬ p3875) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p2528) ∨ (¬ p1998) ∨ (¬ p2437)) : (¬ p1998) ∨ (p2027) ∨ (p2323) ∨ (¬ p2437) ∨ (¬ p2528) ∨ (¬ p2651) ∨ (¬ p3875) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial14881 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2323) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory4313 t (m.theta 0 3) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule14881 (meaning t m 1998) (meaning t m 2027) (meaning t m 2323) (meaning t m 2437) (meaning t m 2528) (meaning t m 2651) (meaning t m 3875) (meaning t m 4348) source

theorem rule14884 (p1977 p2355 p4111 p4650 : Prop) (h : (¬ p4111) ∨ (¬ p1977) ∨ p2355 ∨ p4650) : (¬ p1977) ∨ (p2355) ∨ (¬ p4111) ∨ (p4650) := by
  classical
  tauto

theorem initial14884 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2355) ∨ (¬ (meaning t m 4111)) ∨ (meaning t m 4650) := by
  have source := ElevenTheory.theory4316 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7)
  exact rule14884 (meaning t m 1977) (meaning t m 2355) (meaning t m 4111) (meaning t m 4650) source

theorem rule14886 (p1988 p2027 p2132 p2611 p2761 p2870 p3246 : Prop) (h : (¬ p3246) ∨ p2611 ∨ p2027 ∨ (¬ p2870) ∨ (¬ p1988) ∨ (¬ p2761) ∨ (¬ p2132)) : (¬ p1988) ∨ (p2027) ∨ (¬ p2132) ∨ (p2611) ∨ (¬ p2761) ∨ (¬ p2870) ∨ (¬ p3246) := by
  classical
  tauto

theorem initial14886 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3246)) := by
  have source := ElevenTheory.theory4318 t (m.theta 0 2) (m.theta 2 5) (m.theta 5 7) (m.theta 7 9) (m.theta 9 10)
  exact rule14886 (meaning t m 1988) (meaning t m 2027) (meaning t m 2132) (meaning t m 2611) (meaning t m 2761) (meaning t m 2870) (meaning t m 3246) source

theorem rule14890 (p1991 p2027 p2202 p2440 p3027 p3414 p4111 : Prop) (h : p2202 ∨ p2027 ∨ (¬ p3027) ∨ (¬ p2440) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p1991)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial14890 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory4322 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule14890 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3027) (meaning t m 3414) (meaning t m 4111) source

theorem rule14892 (p1999 p2027 p2699 p3063 p3093 p3483 p4358 : Prop) (h : (¬ p3063) ∨ (¬ p1999) ∨ p2027 ∨ (¬ p4358) ∨ (¬ p3093) ∨ p2699 ∨ (¬ p3483)) : (¬ p1999) ∨ (p2027) ∨ (p2699) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3483) ∨ (¬ p4358) := by
  classical
  tauto

theorem initial14892 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1999)) ∨ (meaning t m 2027) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4358)) := by
  have source := ElevenTheory.theory4324 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 8) (m.theta 6 9)
  exact rule14892 (meaning t m 1999) (meaning t m 2027) (meaning t m 2699) (meaning t m 3063) (meaning t m 3093) (meaning t m 3483) (meaning t m 4358) source

theorem rule14894 (p2010 p2027 p2396 p2699 p3093 p3309 p4278 : Prop) (h : p2027 ∨ p2699 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p2396) ∨ (¬ p4278) ∨ (¬ p2010)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2396) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial14894 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory4326 t (m.theta 0 1) (m.theta 1 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule14894 (meaning t m 2010) (meaning t m 2027) (meaning t m 2396) (meaning t m 2699) (meaning t m 3093) (meaning t m 3309) (meaning t m 4278) source

theorem rule14895 (p3546 p4372 p5649 p5650 : Prop) (h : (¬ p5650) ∨ (¬ p5649) ∨ (¬ p3546) ∨ (¬ p4372)) : (¬ p3546) ∨ (¬ p4372) ∨ (¬ p5649) ∨ (¬ p5650) := by
  classical
  tauto

theorem initial14895 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 4372)) ∨ (¬ (meaning t m 5649)) ∨ (¬ (meaning t m 5650)) := by
  have source := ElevenTheory.theory4327 (m.theta 0 7) (m.theta 1 10) (m.theta 1 7) (m.theta 7 10)
  exact rule14895 (meaning t m 3546) (meaning t m 4372) (meaning t m 5649) (meaning t m 5650) source

theorem rule14896 (p1994 p2027 p2169 p2427 p3989 p4110 p4320 p4700 : Prop) (h : (¬ p4110) ∨ (¬ p1994) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p4700) ∨ p2169 ∨ (¬ p2427)) : (¬ p1994) ∨ (p2027) ∨ (p2169) ∨ (¬ p2427) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4700) := by
  classical
  tauto

theorem initial14896 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) := by
  have source := ElevenTheory.theory4328 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule14896 (meaning t m 1994) (meaning t m 2027) (meaning t m 2169) (meaning t m 2427) (meaning t m 3989) (meaning t m 4110) (meaning t m 4320) (meaning t m 4700) source

theorem rule14897 (p1979 p2210 p2699 p4960 : Prop) (h : p2699 ∨ (¬ p1979) ∨ p4960 ∨ (¬ p2210)) : (¬ p1979) ∨ (¬ p2210) ∨ (p2699) ∨ (p4960) := by
  classical
  tauto

theorem initial14897 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (meaning t m 4960) := by
  have source := ElevenTheory.theory4329 t (m.theta 0 1) (m.theta 1 5) (m.theta 3 5)
  exact rule14897 (meaning t m 1979) (meaning t m 2210) (meaning t m 2699) (meaning t m 4960) source

end SunPrize.SMT
