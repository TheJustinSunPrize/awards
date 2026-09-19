import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory008
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule10421 (p2027 p2274 p2313 p3063 p3204 p3744 p4601 : Prop) (h : (¬ p2313) ∨ (¬ p3063) ∨ (¬ p3204) ∨ (¬ p2274) ∨ p2027 ∨ (¬ p4601) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3063) ∨ (¬ p3204) ∨ (¬ p3744) ∨ (¬ p4601) := by
  classical
  tauto

theorem initial10421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4601)) := by
  have source := ElevenTheory.theory2013 t (m.theta 0 6) (m.theta 1 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule10421 (meaning t m 2027) (meaning t m 2274) (meaning t m 2313) (meaning t m 3063) (meaning t m 3204) (meaning t m 3744) (meaning t m 4601) source

theorem rule10425 (p2027 p2727 p2850 p2957 p3662 p4109 p4753 : Prop) (h : (¬ p4109) ∨ (¬ p2957) ∨ (¬ p2727) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p4109) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial10425 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2017 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule10425 (meaning t m 2027) (meaning t m 2727) (meaning t m 2850) (meaning t m 2957) (meaning t m 3662) (meaning t m 4109) (meaning t m 4753) source

theorem rule10427 (p2027 p2589 p3097 p3399 p3527 p3553 p4110 p4570 p5193 : Prop) (h : (¬ p3399) ∨ (¬ p4110) ∨ (¬ p2589) ∨ (¬ p3097) ∨ (¬ p4570) ∨ (¬ p5193) ∨ (¬ p3527) ∨ (¬ p3553) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p3097) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4110) ∨ (¬ p4570) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial10427 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory2019 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule10427 (meaning t m 2027) (meaning t m 2589) (meaning t m 3097) (meaning t m 3399) (meaning t m 3527) (meaning t m 3553) (meaning t m 4110) (meaning t m 4570) (meaning t m 5193) source

theorem rule10431 (p5715 p5716 p5717 p5718 p5719 : Prop) : (¬ (p5715 ∧ p5716 ∧ p5717 ∧ p5718 ∧ p5719)) ∨ (p5717) := by
  classical
  tauto

theorem initial10431 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5714)) ∨ (meaning t m 5717) := by
  exact rule10431 (meaning t m 5715) (meaning t m 5716) (meaning t m 5717) (meaning t m 5718) (meaning t m 5719)

theorem rule10437 (p4228 p5721 p5722 p5723 p5724 : Prop) : (p4228) ∨ (¬ (p5721 ∧ p5722 ∧ p4228 ∧ p5723 ∧ p5724)) := by
  classical
  tauto

theorem initial10437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4228) ∨ (¬ (meaning t m 5720)) := by
  exact rule10437 (meaning t m 4228) (meaning t m 5721) (meaning t m 5722) (meaning t m 5723) (meaning t m 5724)

theorem rule10443 (p5714 p5720 : Prop) : (¬ (p5714 ∨ p5720)) ∨ (p5714) ∨ (p5720) := by
  classical
  tauto

theorem initial10443 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5713)) ∨ (meaning t m 5714) ∨ (meaning t m 5720) := by
  exact rule10443 (meaning t m 5714) (meaning t m 5720)

theorem rule10444 (p4222 p5713 : Prop) (h : (p4222 ↔ p5713)) : (¬ p4222) ∨ (p5713) := by
  classical
  tauto

theorem initial10444 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4222)) ∨ (meaning t m 5713) := by
  have source := ElevenTheory.theory2021 t (m.theta 3 10) (m.theta 3 6) (m.theta 6 10)
  exact rule10444 (meaning t m 4222) (meaning t m 5713) source

theorem rule10446 (p2027 p3246 p3947 p4067 p4228 p4275 p5477 : Prop) (h : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4275) ∨ (¬ p4067) ∨ (¬ p5477) ∨ p2027 ∨ (¬ p4228)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4228) ∨ (¬ p4275) ∨ (¬ p5477) := by
  classical
  tauto

theorem initial10446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 5477)) := by
  have source := ElevenTheory.theory2022 t (m.theta 3 6) (m.theta 3 7) (m.theta 5 7) (m.theta 6 10) (m.theta 6 7) (m.theta 7 9)
  exact rule10446 (meaning t m 2027) (meaning t m 3246) (meaning t m 3947) (meaning t m 4067) (meaning t m 4228) (meaning t m 4275) (meaning t m 5477) source

theorem rule10450 (p2027 p2241 p2589 p3027 p3744 p3872 p3931 p4235 p4396 p4830 p5193 : Prop) (h : (¬ p3931) ∨ (¬ p5193) ∨ (¬ p3027) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p2589) ∨ (¬ p4235) ∨ (¬ p3744) ∨ (¬ p3872)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3744) ∨ (¬ p3872) ∨ (¬ p3931) ∨ (¬ p4235) ∨ (¬ p4396) ∨ (¬ p4830) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial10450 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3872)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4396)) ∨ (¬ (meaning t m 4830)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory2026 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 10) (m.theta 7 9)
  exact rule10450 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 3027) (meaning t m 3744) (meaning t m 3872) (meaning t m 3931) (meaning t m 4235) (meaning t m 4396) (meaning t m 4830) (meaning t m 5193) source

theorem rule10452 (p2839 p3587 p3588 : Prop) (h : (¬ p2839) ∨ (¬ p3588) ∨ (¬ p3587)) : (¬ p2839) ∨ (¬ p3587) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial10452 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory2028 (m.theta 1 2) (m.theta 2 5) (m.theta 2 7)
  exact rule10452 (meaning t m 2839) (meaning t m 3587) (meaning t m 3588) source

theorem rule10455 (p2027 p2761 p2952 p3361 p3425 p3619 p3952 p4393 p4778 p5233 p5254 : Prop) (h : (¬ p3952) ∨ (¬ p3425) ∨ (¬ p3361) ∨ (¬ p4778) ∨ (¬ p4393) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3619) ∨ (¬ p5233) ∨ (¬ p5254)) : (p2027) ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3425) ∨ (¬ p3619) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4778) ∨ (¬ p5233) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial10455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 4778)) ∨ (¬ (meaning t m 5233)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory2031 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 2 9) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule10455 (meaning t m 2027) (meaning t m 2761) (meaning t m 2952) (meaning t m 3361) (meaning t m 3425) (meaning t m 3619) (meaning t m 3952) (meaning t m 4393) (meaning t m 4778) (meaning t m 5233) (meaning t m 5254) source

theorem rule10460 (p2027 p2542 p2589 p3399 p3527 p3659 p3742 p5083 p5193 : Prop) (h : (¬ p5083) ∨ (¬ p2542) ∨ (¬ p5193) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3742) ∨ (¬ p3527) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3742) ∨ (¬ p5083) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial10460 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 5083)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory2036 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 2 7) (m.theta 3 4) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule10460 (meaning t m 2027) (meaning t m 2542) (meaning t m 2589) (meaning t m 3399) (meaning t m 3527) (meaning t m 3659) (meaning t m 3742) (meaning t m 5083) (meaning t m 5193) source

theorem rule10464 (p2027 p2717 p3367 p3548 p4400 p4752 p4781 : Prop) (h : (¬ p3548) ∨ (¬ p4781) ∨ p2027 ∨ (¬ p4752) ∨ (¬ p3367) ∨ (¬ p4400) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3367) ∨ (¬ p3548) ∨ (¬ p4400) ∨ (¬ p4752) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial10464 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4752)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory2040 t (m.theta 1 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule10464 (meaning t m 2027) (meaning t m 2717) (meaning t m 3367) (meaning t m 3548) (meaning t m 4400) (meaning t m 4752) (meaning t m 4781) source

theorem rule10465 (p2027 p2741 p2811 p3166 p3367 p4360 p4752 : Prop) (h : (¬ p2741) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p3367) ∨ (¬ p4752) ∨ p2027) : (p2027) ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3367) ∨ (¬ p4360) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial10465 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory2041 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 8)
  exact rule10465 (meaning t m 2027) (meaning t m 2741) (meaning t m 2811) (meaning t m 3166) (meaning t m 3367) (meaning t m 4360) (meaning t m 4752) source

theorem rule10470 (p2027 p2166 p2946 p3172 p4312 p4960 : Prop) (h : (¬ p2946) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p4960) ∨ (¬ p4312)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p4312) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10470 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4312)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory2046 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule10470 (meaning t m 2027) (meaning t m 2166) (meaning t m 2946) (meaning t m 3172) (meaning t m 4312) (meaning t m 4960) source

theorem rule10476 (p2027 p2499 p2761 p3051 p3246 p3452 p4521 p5254 p5514 : Prop) (h : (¬ p5254) ∨ p2027 ∨ (¬ p5514) ∨ (¬ p2761) ∨ (¬ p3452) ∨ (¬ p4521) ∨ (¬ p3246) ∨ (¬ p3051) ∨ (¬ p2499)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4521) ∨ (¬ p5254) ∨ (¬ p5514) := by
  classical
  tauto

theorem initial10476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5514)) := by
  have source := ElevenTheory.theory2052 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule10476 (meaning t m 2027) (meaning t m 2499) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 3452) (meaning t m 4521) (meaning t m 5254) (meaning t m 5514) source

theorem rule10477 (p2027 p2954 p3189 p3662 p4120 p4311 : Prop) (h : p2027 ∨ (¬ p2954) ∨ (¬ p4120) ∨ (¬ p4311) ∨ (¬ p3662) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2954) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p4120) ∨ (¬ p4311) := by
  classical
  tauto

theorem initial10477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4311)) := by
  have source := ElevenTheory.theory2053 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8)
  exact rule10477 (meaning t m 2027) (meaning t m 2954) (meaning t m 3189) (meaning t m 3662) (meaning t m 4120) (meaning t m 4311) source

theorem rule10478 (p2761 p4381 : Prop) (h : (¬ p4381) ∨ (¬ p2761)) : (¬ p2761) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial10478 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory2054 (m.theta 7 9) (m.theta 9 10)
  exact rule10478 (meaning t m 2761) (meaning t m 4381) source

theorem rule10481 (p2027 p2641 p2954 p3646 p3662 p3986 : Prop) (h : (¬ p3986) ∨ (¬ p3646) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p2641) ∨ (¬ p2954)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2954) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p3986) := by
  classical
  tauto

theorem initial10481 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) := by
  have source := ElevenTheory.theory2057 t (m.theta 0 5) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6)
  exact rule10481 (meaning t m 2027) (meaning t m 2641) (meaning t m 2954) (meaning t m 3646) (meaning t m 3662) (meaning t m 3986) source

theorem rule10482 (p2027 p2542 p2563 p2659 p3646 p3904 : Prop) (h : p2027 ∨ (¬ p3904) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p2542) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2659) ∨ (¬ p3646) ∨ (¬ p3904) := by
  classical
  tauto

theorem initial10482 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) := by
  have source := ElevenTheory.theory2058 t (m.theta 0 4) (m.theta 0 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 6)
  exact rule10482 (meaning t m 2027) (meaning t m 2542) (meaning t m 2563) (meaning t m 2659) (meaning t m 3646) (meaning t m 3904) source

theorem rule10484 (p2027 p2659 p2685 p2810 p3540 p3579 : Prop) (h : (¬ p2659) ∨ (¬ p3540) ∨ (¬ p2810) ∨ (¬ p3579) ∨ p2027 ∨ (¬ p2685)) : (p2027) ∨ (¬ p2659) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3540) ∨ (¬ p3579) := by
  classical
  tauto

theorem initial10484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3579)) := by
  have source := ElevenTheory.theory2060 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule10484 (meaning t m 2027) (meaning t m 2659) (meaning t m 2685) (meaning t m 2810) (meaning t m 3540) (meaning t m 3579) source

theorem rule10486 (p2027 p2499 p2588 p2662 p3083 p3519 p4157 p4405 : Prop) (h : (¬ p3083) ∨ (¬ p3519) ∨ (¬ p2662) ∨ (¬ p4405) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p2588) ∨ (¬ p4157)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2662) ∨ (¬ p3083) ∨ (¬ p3519) ∨ (¬ p4157) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2062 t (m.theta 0 4) (m.theta 1 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule10486 (meaning t m 2027) (meaning t m 2499) (meaning t m 2588) (meaning t m 2662) (meaning t m 3083) (meaning t m 3519) (meaning t m 4157) (meaning t m 4405) source

theorem rule10488 (p2027 p2166 p2589 p3880 p3948 p5191 : Prop) (h : p2027 ∨ (¬ p5191) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p2166) ∨ (¬ p3948)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p3948) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial10488 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory2064 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 5 8)
  exact rule10488 (meaning t m 2027) (meaning t m 2166) (meaning t m 2589) (meaning t m 3880) (meaning t m 3948) (meaning t m 5191) source

theorem rule10489 (p2027 p2252 p2440 p2657 p2750 p3399 p3527 p3880 p3954 p4905 : Prop) (h : (¬ p2440) ∨ (¬ p3880) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p2657) ∨ (¬ p3527) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10489 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory2065 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule10489 (meaning t m 2027) (meaning t m 2252) (meaning t m 2440) (meaning t m 2657) (meaning t m 2750) (meaning t m 3399) (meaning t m 3527) (meaning t m 3880) (meaning t m 3954) (meaning t m 4905) source

theorem rule10490 (p2027 p2241 p2748 p3588 p3954 p4778 : Prop) (h : (¬ p2748) ∨ (¬ p4778) ∨ (¬ p3588) ∨ (¬ p2241) ∨ (¬ p3954) ∨ p2027) : (p2027) ∨ (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3588) ∨ (¬ p3954) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial10490 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory2066 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 7)
  exact rule10490 (meaning t m 2027) (meaning t m 2241) (meaning t m 2748) (meaning t m 3588) (meaning t m 3954) (meaning t m 4778) source

theorem rule10491 (p2027 p2252 p2750 p2963 p3324 p3399 p3631 p3950 p3954 p4347 : Prop) (h : p2027 ∨ (¬ p3950) ∨ (¬ p3631) ∨ (¬ p4347) ∨ (¬ p3324) ∨ (¬ p2963) ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p3399) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial10491 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory2067 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10491 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2963) (meaning t m 3324) (meaning t m 3399) (meaning t m 3631) (meaning t m 3950) (meaning t m 3954) (meaning t m 4347) source

theorem rule10492 (p2027 p2247 p2751 p3449 p3877 p4288 : Prop) (h : (¬ p3877) ∨ (¬ p4288) ∨ (¬ p3449) ∨ (¬ p2751) ∨ p2027 ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p3449) ∨ (¬ p3877) ∨ (¬ p4288) := by
  classical
  tauto

theorem initial10492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4288)) := by
  have source := ElevenTheory.theory2068 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 8)
  exact rule10492 (meaning t m 2027) (meaning t m 2247) (meaning t m 2751) (meaning t m 3449) (meaning t m 3877) (meaning t m 4288) source

theorem rule10493 (p3631 p3817 : Prop) (h : (¬ p3817) ∨ (¬ p3631)) : (¬ p3631) ∨ (¬ p3817) := by
  classical
  tauto

theorem initial10493 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3817)) := by
  have source := ElevenTheory.theory2069 (m.theta 1 7) (m.theta 7 9)
  exact rule10493 (meaning t m 3631) (meaning t m 3817) source

theorem rule10494 (p2027 p3954 p3998 p5242 p5317 p5693 : Prop) (h : p2027 ∨ (¬ p5317) ∨ (¬ p3954) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5693)) : (p2027) ∨ (¬ p3954) ∨ (¬ p3998) ∨ (¬ p5242) ∨ (¬ p5317) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial10494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 5242)) ∨ (¬ (meaning t m 5317)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory2070 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 8) (m.theta 8 10)
  exact rule10494 (meaning t m 2027) (meaning t m 3954) (meaning t m 3998) (meaning t m 5242) (meaning t m 5317) (meaning t m 5693) source

theorem rule10495 (p2027 p2192 p3554 p4129 p4442 p4555 : Prop) (h : (¬ p3554) ∨ p2027 ∨ (¬ p2192) ∨ (¬ p4442) ∨ (¬ p4555) ∨ (¬ p4129)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3554) ∨ (¬ p4129) ∨ (¬ p4442) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial10495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2071 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 10)
  exact rule10495 (meaning t m 2027) (meaning t m 2192) (meaning t m 3554) (meaning t m 4129) (meaning t m 4442) (meaning t m 4555) source

theorem rule10496 (p2027 p2352 p2497 p3016 p3923 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p2497) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p3923) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2497) ∨ (¬ p3016) ∨ (¬ p3923) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10496 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2072 t (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 8)
  exact rule10496 (meaning t m 2027) (meaning t m 2352) (meaning t m 2497) (meaning t m 3016) (meaning t m 3923) (meaning t m 4811) source

theorem rule10497 (p2027 p2088 p3954 p4261 p5242 p5317 : Prop) (h : p2027 ∨ (¬ p3954) ∨ (¬ p5317) ∨ (¬ p5242) ∨ (¬ p2088) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3954) ∨ (¬ p4261) ∨ (¬ p5242) ∨ (¬ p5317) := by
  classical
  tauto

theorem initial10497 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5242)) ∨ (¬ (meaning t m 5317)) := by
  have source := ElevenTheory.theory2073 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 8) (m.theta 8 9)
  exact rule10497 (meaning t m 2027) (meaning t m 2088) (meaning t m 3954) (meaning t m 4261) (meaning t m 5242) (meaning t m 5317) source

theorem rule10498 (p2027 p2252 p2579 p2655 p2750 p3016 p3399 p3527 p3954 p4256 p4438 : Prop) (h : (¬ p3399) ∨ (¬ p2750) ∨ (¬ p2252) ∨ (¬ p3954) ∨ (¬ p3527) ∨ (¬ p4438) ∨ (¬ p2655) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p4256) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2579) ∨ (¬ p2655) ∨ (¬ p2750) ∨ (¬ p3016) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3954) ∨ (¬ p4256) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial10498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory2074 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 7 8)
  exact rule10498 (meaning t m 2027) (meaning t m 2252) (meaning t m 2579) (meaning t m 2655) (meaning t m 2750) (meaning t m 3016) (meaning t m 3399) (meaning t m 3527) (meaning t m 3954) (meaning t m 4256) (meaning t m 4438) source

theorem rule10499 (p2027 p2156 p2437 p3575 p4173 p4202 p4811 p4984 : Prop) (h : (¬ p4202) ∨ (¬ p3575) ∨ (¬ p4984) ∨ (¬ p2156) ∨ (¬ p2437) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p4811)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2437) ∨ (¬ p3575) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4811) ∨ (¬ p4984) := by
  classical
  tauto

theorem initial10499 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4811)) ∨ (¬ (meaning t m 4984)) := by
  have source := ElevenTheory.theory2075 t (m.theta 0 5) (m.theta 0 7) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 6)
  exact rule10499 (meaning t m 2027) (meaning t m 2156) (meaning t m 2437) (meaning t m 3575) (meaning t m 4173) (meaning t m 4202) (meaning t m 4811) (meaning t m 4984) source

theorem rule10501 (p2027 p2437 p2927 p3379 p4366 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p2437) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p2927) ∨ p2027) : (p2027) ∨ (¬ p2437) ∨ (¬ p2927) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2077 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7)
  exact rule10501 (meaning t m 2027) (meaning t m 2437) (meaning t m 2927) (meaning t m 3379) (meaning t m 4366) (meaning t m 4811) source

theorem rule10502 (p2027 p2352 p3146 p4134 p4137 p4171 : Prop) (h : (¬ p4171) ∨ p2027 ∨ (¬ p4134) ∨ (¬ p2352) ∨ (¬ p4137) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4137) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial10502 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4134)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory2078 t (m.theta 4 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule10502 (meaning t m 2027) (meaning t m 2352) (meaning t m 3146) (meaning t m 4134) (meaning t m 4137) (meaning t m 4171) source

theorem rule10504 (p2027 p2252 p2750 p2952 p3399 p3631 p3744 p3952 p3954 p4625 : Prop) (h : (¬ p3399) ∨ (¬ p2750) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3744) ∨ (¬ p4625) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial10504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory2080 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 9)
  exact rule10504 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3399) (meaning t m 3631) (meaning t m 3744) (meaning t m 3952) (meaning t m 3954) (meaning t m 4625) source

theorem rule10505 (p2027 p2274 p2588 p3564 p4037 p4564 : Prop) (h : p2027 ∨ (¬ p4564) ∨ (¬ p2274) ∨ (¬ p4037) ∨ (¬ p3564) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial10505 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory2081 t (m.theta 3 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule10505 (meaning t m 2027) (meaning t m 2274) (meaning t m 2588) (meaning t m 3564) (meaning t m 4037) (meaning t m 4564) source

theorem rule10506 (p3449 p3860 : Prop) (h : (¬ p3860) ∨ (¬ p3449)) : (¬ p3449) ∨ (¬ p3860) := by
  classical
  tauto

theorem initial10506 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3860)) := by
  have source := ElevenTheory.theory2082 (m.theta 0 1) (m.theta 1 8)
  exact rule10506 (meaning t m 3449) (meaning t m 3860) source

theorem rule10507 (p2027 p2470 p2579 p3324 p4157 p4973 : Prop) (h : (¬ p4157) ∨ (¬ p4973) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p3324)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2579) ∨ (¬ p3324) ∨ (¬ p4157) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10507 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory2083 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule10507 (meaning t m 2027) (meaning t m 2470) (meaning t m 2579) (meaning t m 3324) (meaning t m 4157) (meaning t m 4973) source

theorem rule10508 (p2027 p3461 p3564 p3922 p4321 p4430 p4973 : Prop) (h : p2027 ∨ (¬ p3922) ∨ (¬ p3461) ∨ (¬ p4430) ∨ (¬ p4321) ∨ (¬ p3564) ∨ (¬ p4973)) : (p2027) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3922) ∨ (¬ p4321) ∨ (¬ p4430) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4430)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory2084 t (m.theta 1 6) (m.theta 1 9) (m.theta 3 6) (m.theta 4 6) (m.theta 6 9) (m.theta 9 10)
  exact rule10508 (meaning t m 2027) (meaning t m 3461) (meaning t m 3564) (meaning t m 3922) (meaning t m 4321) (meaning t m 4430) (meaning t m 4973) source

theorem rule10509 (p2027 p2717 p2933 p3540 p3548 p4727 p5085 : Prop) (h : (¬ p4727) ∨ p2027 ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p5085) ∨ (¬ p3548) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p2933) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4727) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial10509 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4727)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory2085 t (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 8)
  exact rule10509 (meaning t m 2027) (meaning t m 2717) (meaning t m 2933) (meaning t m 3540) (meaning t m 3548) (meaning t m 4727) (meaning t m 5085) source

theorem rule10510 (p2027 p2922 p3238 p3575 p4283 p4320 p4702 : Prop) (h : (¬ p2922) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p4283) ∨ (¬ p4702) ∨ (¬ p3238) ∨ (¬ p3575)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3575) ∨ (¬ p4283) ∨ (¬ p4320) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10510 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3575)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory2086 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule10510 (meaning t m 2027) (meaning t m 2922) (meaning t m 3238) (meaning t m 3575) (meaning t m 4283) (meaning t m 4320) (meaning t m 4702) source

theorem rule10512 (p2027 p2934 p3238 p3527 p3551 p4279 p4646 : Prop) (h : p2027 ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4279) ∨ (¬ p3238) ∨ (¬ p2934) ∨ (¬ p4646)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4279) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial10512 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2088 t (m.theta 0 7) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule10512 (meaning t m 2027) (meaning t m 2934) (meaning t m 3238) (meaning t m 3527) (meaning t m 3551) (meaning t m 4279) (meaning t m 4646) source

theorem rule10514 (p2027 p3246 p3346 p3389 p4277 p4636 : Prop) (h : p2027 ∨ (¬ p4277) ∨ (¬ p3389) ∨ (¬ p4636) ∨ (¬ p3246) ∨ (¬ p3346)) : (p2027) ∨ (¬ p3246) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p4277) ∨ (¬ p4636) := by
  classical
  tauto

theorem initial10514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3346)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4636)) := by
  have source := ElevenTheory.theory2090 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 9) (m.theta 5 7) (m.theta 7 9)
  exact rule10514 (meaning t m 2027) (meaning t m 3246) (meaning t m 3346) (meaning t m 3389) (meaning t m 4277) (meaning t m 4636) source

theorem rule10516 (p2027 p2427 p3568 p4110 p4140 p4564 : Prop) (h : (¬ p2427) ∨ (¬ p3568) ∨ (¬ p4140) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4564)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3568) ∨ (¬ p4110) ∨ (¬ p4140) ∨ (¬ p4564) := by
  classical
  tauto

theorem initial10516 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4140)) ∨ (¬ (meaning t m 4564)) := by
  have source := ElevenTheory.theory2092 t (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule10516 (meaning t m 2027) (meaning t m 2427) (meaning t m 3568) (meaning t m 4110) (meaning t m 4140) (meaning t m 4564) source

theorem rule10517 (p2027 p2470 p2577 p3564 p3946 p4598 : Prop) (h : (¬ p2577) ∨ p2027 ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p2470) ∨ (¬ p4598)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2577) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4598) := by
  classical
  tauto

theorem initial10517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4598)) := by
  have source := ElevenTheory.theory2093 t (m.theta 0 4) (m.theta 0 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 9)
  exact rule10517 (meaning t m 2027) (meaning t m 2470) (meaning t m 2577) (meaning t m 3564) (meaning t m 3946) (meaning t m 4598) source

theorem rule10518 (p2027 p2187 p2246 p2284 p2946 p3039 p3955 p4427 : Prop) (h : (¬ p4427) ∨ (¬ p2246) ∨ (¬ p3039) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2284) ∨ (¬ p3955)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2246) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3039) ∨ (¬ p3955) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial10518 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3039)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory2094 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule10518 (meaning t m 2027) (meaning t m 2187) (meaning t m 2246) (meaning t m 2284) (meaning t m 2946) (meaning t m 3039) (meaning t m 3955) (meaning t m 4427) source

theorem rule10519 (p2027 p2553 p3641 p3660 p3822 p4610 p5220 : Prop) (h : (¬ p3822) ∨ (¬ p3660) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p4610) ∨ (¬ p3641) ∨ (¬ p5220)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3641) ∨ (¬ p3660) ∨ (¬ p3822) ∨ (¬ p4610) ∨ (¬ p5220) := by
  classical
  tauto

theorem initial10519 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 5220)) := by
  have source := ElevenTheory.theory2095 t (m.theta 2 4) (m.theta 2 6) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule10519 (meaning t m 2027) (meaning t m 2553) (meaning t m 3641) (meaning t m 3660) (meaning t m 3822) (meaning t m 4610) (meaning t m 5220) source

theorem rule10520 (p2027 p3414 p3654 p3987 p4037 p4194 p4650 : Prop) (h : (¬ p4194) ∨ (¬ p4650) ∨ (¬ p3414) ∨ (¬ p3654) ∨ p2027 ∨ (¬ p3987) ∨ (¬ p4037)) : (p2027) ∨ (¬ p3414) ∨ (¬ p3654) ∨ (¬ p3987) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial10520 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4194)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory2096 t (m.theta 0 3) (m.theta 0 6) (m.theta 3 4) (m.theta 3 6) (m.theta 3 7) (m.theta 6 9)
  exact rule10520 (meaning t m 2027) (meaning t m 3414) (meaning t m 3654) (meaning t m 3987) (meaning t m 4037) (meaning t m 4194) (meaning t m 4650) source

theorem rule10521 (p2027 p2284 p2589 p2659 p3413 p4110 : Prop) (h : (¬ p2659) ∨ (¬ p2589) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2284) ∨ (¬ p3413)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p3413) ∨ (¬ p4110) := by
  classical
  tauto

theorem initial10521 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 4110)) := by
  have source := ElevenTheory.theory2097 t (m.theta 0 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule10521 (meaning t m 2027) (meaning t m 2284) (meaning t m 2589) (meaning t m 2659) (meaning t m 3413) (meaning t m 4110) source

theorem rule10522 (p2027 p2252 p2657 p2750 p3399 p3574 p3631 p3954 p4137 p4625 : Prop) (h : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3574) ∨ (¬ p3631) ∨ (¬ p3954) ∨ (¬ p4137) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial10522 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory2098 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 6 9) (m.theta 7 9)
  exact rule10522 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 3399) (meaning t m 3574) (meaning t m 3631) (meaning t m 3954) (meaning t m 4137) (meaning t m 4625) source

theorem rule10523 (p2027 p3193 p3246 p3399 p3461 p3571 p3954 p4425 p4625 p5216 : Prop) (h : (¬ p4425) ∨ (¬ p3571) ∨ (¬ p3193) ∨ (¬ p4625) ∨ (¬ p3399) ∨ (¬ p3246) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p5216) ∨ (¬ p3461)) : (p2027) ∨ (¬ p3193) ∨ (¬ p3246) ∨ (¬ p3399) ∨ (¬ p3461) ∨ (¬ p3571) ∨ (¬ p3954) ∨ (¬ p4425) ∨ (¬ p4625) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial10523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3571)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory2099 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 4 9) (m.theta 5 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule10523 (meaning t m 2027) (meaning t m 3193) (meaning t m 3246) (meaning t m 3399) (meaning t m 3461) (meaning t m 3571) (meaning t m 3954) (meaning t m 4425) (meaning t m 4625) (meaning t m 5216) source

theorem rule10524 (p2027 p2579 p2659 p2797 p2810 p3984 : Prop) (h : (¬ p2810) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p2797) ∨ (¬ p3984) ∨ (¬ p2579)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2659) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3984) := by
  classical
  tauto

theorem initial10524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3984)) := by
  have source := ElevenTheory.theory2100 t (m.theta 0 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule10524 (meaning t m 2027) (meaning t m 2579) (meaning t m 2659) (meaning t m 2797) (meaning t m 2810) (meaning t m 3984) source

theorem rule10527 (p4423 p5727 p5728 p5729 p5730 : Prop) : (p4423) ∨ (¬ (p5727 ∧ p5728 ∧ p4423 ∧ p5729 ∧ p5730)) := by
  classical
  tauto

theorem initial10527 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4423) ∨ (¬ (meaning t m 5726)) := by
  exact rule10527 (meaning t m 4423) (meaning t m 5727) (meaning t m 5728) (meaning t m 5729) (meaning t m 5730)

theorem rule10533 (p4253 p5732 p5733 p5734 p5735 : Prop) : (p4253) ∨ (¬ (p5732 ∧ p5733 ∧ p4253 ∧ p5734 ∧ p5735)) := by
  classical
  tauto

theorem initial10533 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4253) ∨ (¬ (meaning t m 5731)) := by
  exact rule10533 (meaning t m 4253) (meaning t m 5732) (meaning t m 5733) (meaning t m 5734) (meaning t m 5735)

theorem rule10539 (p5726 p5731 : Prop) : (¬ (p5726 ∨ p5731)) ∨ (p5726) ∨ (p5731) := by
  classical
  tauto

theorem initial10539 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5725)) ∨ (meaning t m 5726) ∨ (meaning t m 5731) := by
  exact rule10539 (meaning t m 5726) (meaning t m 5731)

theorem rule10540 (p4247 p5725 : Prop) (h : (p4247 ↔ p5725)) : (¬ p4247) ∨ (p5725) := by
  classical
  tauto

theorem initial10540 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4247)) ∨ (meaning t m 5725) := by
  have source := ElevenTheory.theory2101 t (m.theta 2 10) (m.theta 2 7) (m.theta 7 10)
  exact rule10540 (meaning t m 4247) (meaning t m 5725) source

theorem rule10543 (p2027 p3276 p4032 p4322 p4449 p4533 : Prop) (h : (¬ p4449) ∨ (¬ p4533) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4032) ∨ (¬ p4322)) : (p2027) ∨ (¬ p3276) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4449) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10543 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4449)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory2103 t (m.theta 0 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 9) (m.theta 9 10)
  exact rule10543 (meaning t m 2027) (meaning t m 3276) (meaning t m 4032) (meaning t m 4322) (meaning t m 4449) (meaning t m 4533) source

theorem rule10544 (p2027 p3399 p3576 p3585 p3954 p5086 : Prop) (h : (¬ p3576) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3399) ∨ (¬ p3954) ∨ (¬ p5086)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3585) ∨ (¬ p3954) ∨ (¬ p5086) := by
  classical
  tauto

theorem initial10544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 5086)) := by
  have source := ElevenTheory.theory2104 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7)
  exact rule10544 (meaning t m 2027) (meaning t m 3399) (meaning t m 3576) (meaning t m 3585) (meaning t m 3954) (meaning t m 5086) source

theorem rule10546 (p2027 p3941 p4321 p4348 p5002 p5121 : Prop) (h : (¬ p5002) ∨ p2027 ∨ (¬ p5121) ∨ (¬ p4321) ∨ (¬ p4348) ∨ (¬ p3941)) : (p2027) ∨ (¬ p3941) ∨ (¬ p4321) ∨ (¬ p4348) ∨ (¬ p5002) ∨ (¬ p5121) := by
  classical
  tauto

theorem initial10546 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5002)) ∨ (¬ (meaning t m 5121)) := by
  have source := ElevenTheory.theory2106 t (m.theta 1 9) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9) (m.theta 9 10)
  exact rule10546 (meaning t m 2027) (meaning t m 3941) (meaning t m 4321) (meaning t m 4348) (meaning t m 5002) (meaning t m 5121) source

theorem rule10548 (p2027 p3115 p3680 p4321 p4938 p4957 : Prop) (h : p2027 ∨ (¬ p4957) ∨ (¬ p4321) ∨ (¬ p4938) ∨ (¬ p3115) ∨ (¬ p3680)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4938) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial10548 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4938)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory2108 t (m.theta 1 5) (m.theta 1 9) (m.theta 3 5) (m.theta 5 9) (m.theta 9 10)
  exact rule10548 (meaning t m 2027) (meaning t m 3115) (meaning t m 3680) (meaning t m 4321) (meaning t m 4938) (meaning t m 4957) source

theorem rule10549 (p2027 p2750 p3449 p3954 p4037 p4154 p4181 p4191 p5119 : Prop) (h : (¬ p4154) ∨ (¬ p4191) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4181) ∨ (¬ p5119) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p2750)) : (p2027) ∨ (¬ p2750) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4181) ∨ (¬ p4191) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial10549 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2109 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 1 8) (m.theta 3 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule10549 (meaning t m 2027) (meaning t m 2750) (meaning t m 3449) (meaning t m 3954) (meaning t m 4037) (meaning t m 4154) (meaning t m 4181) (meaning t m 4191) (meaning t m 5119) source

theorem rule10551 (p2027 p2187 p3399 p3631 p3744 p3923 p3954 p4625 p4870 : Prop) (h : (¬ p2187) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p4625) ∨ p2027 ∨ (¬ p3923) ∨ (¬ p4870) ∨ (¬ p3954) ∨ (¬ p3744)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3744) ∨ (¬ p3923) ∨ (¬ p3954) ∨ (¬ p4625) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial10551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory2111 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule10551 (meaning t m 2027) (meaning t m 2187) (meaning t m 3399) (meaning t m 3631) (meaning t m 3744) (meaning t m 3923) (meaning t m 3954) (meaning t m 4625) (meaning t m 4870) source

theorem rule10552 (p2027 p2810 p3365 p3471 p4325 p4652 : Prop) (h : (¬ p4652) ∨ (¬ p3365) ∨ (¬ p3471) ∨ p2027 ∨ (¬ p4325) ∨ (¬ p2810)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p4325) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial10552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4325)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2112 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7)
  exact rule10552 (meaning t m 2027) (meaning t m 2810) (meaning t m 3365) (meaning t m 3471) (meaning t m 4325) (meaning t m 4652) source

theorem rule10553 (p2027 p2954 p3146 p3156 p3857 p4197 p4198 : Prop) (h : (¬ p4198) ∨ (¬ p4197) ∨ (¬ p3857) ∨ (¬ p2954) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p3156)) : (p2027) ∨ (¬ p2954) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4198) := by
  classical
  tauto

theorem initial10553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4198)) := by
  have source := ElevenTheory.theory2113 t (m.theta 0 5) (m.theta 0 6) (m.theta 0 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule10553 (meaning t m 2027) (meaning t m 2954) (meaning t m 3146) (meaning t m 3156) (meaning t m 3857) (meaning t m 4197) (meaning t m 4198) source

theorem rule10554 (p2027 p2190 p3146 p3923 p4347 p4514 : Prop) (h : (¬ p2190) ∨ (¬ p3923) ∨ (¬ p4514) ∨ p2027 ∨ (¬ p4347) ∨ (¬ p3146)) : (p2027) ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p4514) := by
  classical
  tauto

theorem initial10554 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2190)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4514)) := by
  have source := ElevenTheory.theory2114 t (m.theta 1 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule10554 (meaning t m 2027) (meaning t m 2190) (meaning t m 3146) (meaning t m 3923) (meaning t m 4347) (meaning t m 4514) source

theorem rule10556 (p2027 p2373 p3146 p3697 p3857 p4533 : Prop) (h : (¬ p3697) ∨ (¬ p3146) ∨ p2027 ∨ (¬ p4533) ∨ (¬ p2373) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4533) := by
  classical
  tauto

theorem initial10556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3697)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4533)) := by
  have source := ElevenTheory.theory2116 t (m.theta 0 5) (m.theta 0 8) (m.theta 4 5) (m.theta 5 8) (m.theta 8 9)
  exact rule10556 (meaning t m 2027) (meaning t m 2373) (meaning t m 3146) (meaning t m 3697) (meaning t m 3857) (meaning t m 4533) source

theorem rule10557 (p2027 p2553 p3097 p3660 p4173 p4629 : Prop) (h : (¬ p3097) ∨ (¬ p2553) ∨ (¬ p4629) ∨ (¬ p3660) ∨ (¬ p4173) ∨ p2027) : (p2027) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p4173) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial10557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory2117 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule10557 (meaning t m 2027) (meaning t m 2553) (meaning t m 3097) (meaning t m 3660) (meaning t m 4173) (meaning t m 4629) source

theorem rule10558 (p2027 p2331 p2352 p3172 p4769 p4973 : Prop) (h : (¬ p4769) ∨ (¬ p4973) ∨ p2027 ∨ (¬ p3172) ∨ (¬ p2331) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2352) ∨ (¬ p3172) ∨ (¬ p4769) ∨ (¬ p4973) := by
  classical
  tauto

theorem initial10558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4769)) ∨ (¬ (meaning t m 4973)) := by
  have source := ElevenTheory.theory2118 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 6) (m.theta 6 8)
  exact rule10558 (meaning t m 2027) (meaning t m 2331) (meaning t m 2352) (meaning t m 3172) (meaning t m 4769) (meaning t m 4973) source

theorem rule10559 (p2027 p2298 p2331 p3309 p3414 p4761 : Prop) (h : p2027 ∨ (¬ p3414) ∨ (¬ p4761) ∨ (¬ p3309) ∨ (¬ p2331) ∨ (¬ p2298)) : (p2027) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3309) ∨ (¬ p3414) ∨ (¬ p4761) := by
  classical
  tauto

theorem initial10559 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4761)) := by
  have source := ElevenTheory.theory2119 t (m.theta 0 3) (m.theta 1 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule10559 (meaning t m 2027) (meaning t m 2298) (meaning t m 2331) (meaning t m 3309) (meaning t m 3414) (meaning t m 4761) source

theorem rule10560 (p2027 p2751 p2951 p2992 p3051 p4244 p4392 : Prop) (h : (¬ p3051) ∨ (¬ p2751) ∨ (¬ p4244) ∨ (¬ p4392) ∨ p2027 ∨ (¬ p2951) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2751) ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3051) ∨ (¬ p4244) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial10560 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2951)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory2120 t (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule10560 (meaning t m 2027) (meaning t m 2751) (meaning t m 2951) (meaning t m 2992) (meaning t m 3051) (meaning t m 4244) (meaning t m 4392) source

theorem rule10561 (p2027 p2137 p2156 p2553 p4244 p4275 p4718 : Prop) (h : (¬ p2553) ∨ (¬ p4275) ∨ (¬ p2156) ∨ (¬ p2137) ∨ p2027 ∨ (¬ p4244) ∨ (¬ p4718)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2553) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10561 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory2121 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule10561 (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2553) (meaning t m 4244) (meaning t m 4275) (meaning t m 4718) source

theorem rule10562 (p2027 p2246 p2807 p3662 p4244 p4333 p4906 : Prop) (h : (¬ p4906) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p3662) ∨ (¬ p4333) ∨ (¬ p2807) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2807) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial10562 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2122 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule10562 (meaning t m 2027) (meaning t m 2246) (meaning t m 2807) (meaning t m 3662) (meaning t m 4244) (meaning t m 4333) (meaning t m 4906) source

theorem rule10564 (p2027 p2352 p2860 p3694 p4115 p4170 p4718 : Prop) (h : (¬ p4718) ∨ (¬ p3694) ∨ (¬ p4115) ∨ (¬ p4170) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p2860)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2860) ∨ (¬ p3694) ∨ (¬ p4115) ∨ (¬ p4170) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10564 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4115)) ∨ (¬ (meaning t m 4170)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory2124 t (m.theta 0 8) (m.theta 2 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule10564 (meaning t m 2027) (meaning t m 2352) (meaning t m 2860) (meaning t m 3694) (meaning t m 4115) (meaning t m 4170) (meaning t m 4718) source

theorem rule10566 (p2027 p2727 p3343 p3662 p3879 p4953 : Prop) (h : (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3662) ∨ (¬ p4953) ∨ p2027 ∨ (¬ p3879)) : (p2027) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial10566 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory2126 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 9)
  exact rule10566 (meaning t m 2027) (meaning t m 2727) (meaning t m 3343) (meaning t m 3662) (meaning t m 3879) (meaning t m 4953) source

theorem rule10567 (p2027 p2387 p2577 p2662 p2819 p4315 p4426 p4701 : Prop) (h : (¬ p2577) ∨ (¬ p2387) ∨ p2027 ∨ (¬ p4426) ∨ (¬ p4701) ∨ (¬ p2662) ∨ (¬ p4315) ∨ (¬ p2819)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p2662) ∨ (¬ p2819) ∨ (¬ p4315) ∨ (¬ p4426) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial10567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4426)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory2127 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 5) (m.theta 6 8)
  exact rule10567 (meaning t m 2027) (meaning t m 2387) (meaning t m 2577) (meaning t m 2662) (meaning t m 2819) (meaning t m 4315) (meaning t m 4426) (meaning t m 4701) source

theorem rule10569 (p2027 p2295 p2860 p4244 p4275 p4560 : Prop) (h : (¬ p2295) ∨ (¬ p4244) ∨ (¬ p2860) ∨ (¬ p4275) ∨ p2027 ∨ (¬ p4560)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2860) ∨ (¬ p4244) ∨ (¬ p4275) ∨ (¬ p4560) := by
  classical
  tauto

theorem initial10569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4560)) := by
  have source := ElevenTheory.theory2129 t (m.theta 2 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule10569 (meaning t m 2027) (meaning t m 2295) (meaning t m 2860) (meaning t m 4244) (meaning t m 4275) (meaning t m 4560) source

theorem rule10570 (p2027 p2295 p2313 p3758 p4336 p4356 p4906 : Prop) (h : (¬ p4356) ∨ (¬ p4336) ∨ (¬ p2295) ∨ (¬ p4906) ∨ (¬ p2313) ∨ (¬ p3758) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3758) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial10570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2130 t (m.theta 0 6) (m.theta 2 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule10570 (meaning t m 2027) (meaning t m 2295) (meaning t m 2313) (meaning t m 3758) (meaning t m 4336) (meaning t m 4356) (meaning t m 4906) source

theorem rule10572 (p2027 p2518 p3364 p3541 p3583 p3874 p5049 : Prop) (h : (¬ p3541) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p2518) ∨ p2027 ∨ (¬ p5049) ∨ (¬ p3583)) : (p2027) ∨ (¬ p2518) ∨ (¬ p3364) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3874) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial10572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory2132 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 5) (m.theta 4 8)
  exact rule10572 (meaning t m 2027) (meaning t m 2518) (meaning t m 3364) (meaning t m 3541) (meaning t m 3583) (meaning t m 3874) (meaning t m 5049) source

theorem rule10573 (p2027 p3027 p3662 p4244 p4333 p4906 : Prop) (h : (¬ p4906) ∨ p2027 ∨ (¬ p3662) ∨ (¬ p3027) ∨ (¬ p4244) ∨ (¬ p4333)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3662) ∨ (¬ p4244) ∨ (¬ p4333) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial10573 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4333)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2133 t (m.theta 1 3) (m.theta 2 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule10573 (meaning t m 2027) (meaning t m 3027) (meaning t m 3662) (meaning t m 4244) (meaning t m 4333) (meaning t m 4906) source

theorem rule10574 (p2027 p3333 p3367 p3583 p3698 p4953 : Prop) (h : (¬ p4953) ∨ p2027 ∨ (¬ p3333) ∨ (¬ p3698) ∨ (¬ p3367) ∨ (¬ p3583)) : (p2027) ∨ (¬ p3333) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial10574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3333)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory2134 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 9)
  exact rule10574 (meaning t m 2027) (meaning t m 3333) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 4953) source

theorem rule10575 (p2027 p3367 p3641 p3688 p4342 p4598 : Prop) (h : (¬ p3367) ∨ (¬ p4598) ∨ (¬ p3641) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p4342)) : (p2027) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4598) := by
  classical
  tauto

theorem initial10575 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4598)) := by
  have source := ElevenTheory.theory2135 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 8)
  exact rule10575 (meaning t m 2027) (meaning t m 3367) (meaning t m 3641) (meaning t m 3688) (meaning t m 4342) (meaning t m 4598) source

theorem rule10576 (p2027 p2156 p3309 p3556 p4275 p4518 : Prop) (h : (¬ p4518) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p2156) ∨ (¬ p4275)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3309) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4518) := by
  classical
  tauto

theorem initial10576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4275)) ∨ (¬ (meaning t m 4518)) := by
  have source := ElevenTheory.theory2136 t (m.theta 0 5) (m.theta 1 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7)
  exact rule10576 (meaning t m 2027) (meaning t m 2156) (meaning t m 3309) (meaning t m 3556) (meaning t m 4275) (meaning t m 4518) source

theorem rule10577 (p2027 p2996 p3189 p3551 p4378 p4851 : Prop) (h : p2027 ∨ (¬ p4851) ∨ (¬ p3551) ∨ (¬ p3189) ∨ (¬ p2996) ∨ (¬ p4378)) : (p2027) ∨ (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3551) ∨ (¬ p4378) ∨ (¬ p4851) := by
  classical
  tauto

theorem initial10577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4378)) ∨ (¬ (meaning t m 4851)) := by
  have source := ElevenTheory.theory2137 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule10577 (meaning t m 2027) (meaning t m 2996) (meaning t m 3189) (meaning t m 3551) (meaning t m 4378) (meaning t m 4851) source

theorem rule10578 (p2027 p2246 p2751 p2901 p2946 p4244 p4392 : Prop) (h : (¬ p4392) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p2751) ∨ (¬ p2246) ∨ (¬ p2901) ∨ (¬ p4244)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2751) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p4244) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial10578 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory2138 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 7)
  exact rule10578 (meaning t m 2027) (meaning t m 2246) (meaning t m 2751) (meaning t m 2901) (meaning t m 2946) (meaning t m 4244) (meaning t m 4392) source

theorem rule10581 (p2027 p2440 p3842 p4111 p4953 p5175 : Prop) (h : (¬ p2440) ∨ (¬ p3842) ∨ (¬ p5175) ∨ (¬ p4953) ∨ (¬ p4111) ∨ p2027) : (p2027) ∨ (¬ p2440) ∨ (¬ p3842) ∨ (¬ p4111) ∨ (¬ p4953) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial10581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4953)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory2141 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9)
  exact rule10581 (meaning t m 2027) (meaning t m 2440) (meaning t m 3842) (meaning t m 4111) (meaning t m 4953) (meaning t m 5175) source

theorem rule10582 (p2027 p2440 p3506 p4425 p4953 p5176 : Prop) (h : (¬ p4425) ∨ p2027 ∨ (¬ p4953) ∨ (¬ p5176) ∨ (¬ p3506) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3506) ∨ (¬ p4425) ∨ (¬ p4953) ∨ (¬ p5176) := by
  classical
  tauto

theorem initial10582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4953)) ∨ (¬ (meaning t m 5176)) := by
  have source := ElevenTheory.theory2142 t (m.theta 3 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule10582 (meaning t m 2027) (meaning t m 2440) (meaning t m 3506) (meaning t m 4425) (meaning t m 4953) (meaning t m 5176) source

theorem rule10583 (p2027 p2177 p2247 p2307 p3848 p3941 p5017 p5119 p5284 : Prop) (h : (¬ p5284) ∨ (¬ p2307) ∨ (¬ p3848) ∨ (¬ p5017) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p5119) ∨ (¬ p3941) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3848) ∨ (¬ p3941) ∨ (¬ p5017) ∨ (¬ p5119) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial10583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2143 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10) (m.theta 9 10)
  exact rule10583 (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2307) (meaning t m 3848) (meaning t m 3941) (meaning t m 5017) (meaning t m 5119) (meaning t m 5284) source

theorem rule10584 (p2027 p2579 p3355 p3744 p4331 p4718 : Prop) (h : (¬ p2579) ∨ p2027 ∨ (¬ p3744) ∨ (¬ p4718) ∨ (¬ p4331) ∨ (¬ p3355)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3744) ∨ (¬ p4331) ∨ (¬ p4718) := by
  classical
  tauto

theorem initial10584 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4331)) ∨ (¬ (meaning t m 4718)) := by
  have source := ElevenTheory.theory2144 t (m.theta 0 4) (m.theta 4 6) (m.theta 4 9) (m.theta 5 6) (m.theta 6 9)
  exact rule10584 (meaning t m 2027) (meaning t m 2579) (meaning t m 3355) (meaning t m 3744) (meaning t m 4331) (meaning t m 4718) source

theorem rule10585 (p2027 p2501 p3343 p3574 p4026 p4331 : Prop) (h : (¬ p3574) ∨ (¬ p4331) ∨ p2027 ∨ (¬ p2501) ∨ (¬ p4026) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2501) ∨ (¬ p3343) ∨ (¬ p3574) ∨ (¬ p4026) ∨ (¬ p4331) := by
  classical
  tauto

theorem initial10585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4331)) := by
  have source := ElevenTheory.theory2145 t (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule10585 (meaning t m 2027) (meaning t m 2501) (meaning t m 3343) (meaning t m 3574) (meaning t m 4026) (meaning t m 4331) source

theorem rule10587 (p2027 p2440 p3019 p3319 p4137 p4319 p4717 : Prop) (h : (¬ p3019) ∨ (¬ p4319) ∨ (¬ p3319) ∨ (¬ p4137) ∨ (¬ p4717) ∨ (¬ p2440) ∨ p2027) : (p2027) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3319) ∨ (¬ p4137) ∨ (¬ p4319) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10587 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3019)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4319)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2147 t (m.theta 1 6) (m.theta 3 4) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule10587 (meaning t m 2027) (meaning t m 2440) (meaning t m 3019) (meaning t m 3319) (meaning t m 4137) (meaning t m 4319) (meaning t m 4717) source

theorem rule10589 (p3246 p3690 : Prop) (h : (¬ p3690) ∨ (¬ p3246)) : (¬ p3246) ∨ (¬ p3690) := by
  classical
  tauto

theorem initial10589 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3690)) := by
  have source := ElevenTheory.theory2149 (m.theta 5 7) (m.theta 7 9)
  exact rule10589 (meaning t m 3246) (meaning t m 3690) source

theorem rule10590 (p2027 p2386 p2505 p3238 p3319 p3946 p4717 : Prop) (h : (¬ p2386) ∨ (¬ p4717) ∨ (¬ p3946) ∨ (¬ p3319) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p2505)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3319) ∨ (¬ p3946) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2150 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 9)
  exact rule10590 (meaning t m 2027) (meaning t m 2386) (meaning t m 2505) (meaning t m 3238) (meaning t m 3319) (meaning t m 3946) (meaning t m 4717) source

theorem rule10591 (p2027 p3233 p3238 p3707 p4953 p5175 p5284 : Prop) (h : (¬ p4953) ∨ (¬ p3233) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p5175) ∨ (¬ p5284) ∨ (¬ p3707)) : (p2027) ∨ (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4953) ∨ (¬ p5175) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial10591 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3707)) ∨ (¬ (meaning t m 4953)) ∨ (¬ (meaning t m 5175)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2151 t (m.theta 1 4) (m.theta 1 9) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9) (m.theta 9 10)
  exact rule10591 (meaning t m 2027) (meaning t m 3233) (meaning t m 3238) (meaning t m 3707) (meaning t m 4953) (meaning t m 5175) (meaning t m 5284) source

theorem rule10592 (p2027 p2440 p2505 p3063 p3956 p4116 p4717 : Prop) (h : (¬ p2505) ∨ p2027 ∨ (¬ p4717) ∨ (¬ p3063) ∨ (¬ p3956) ∨ (¬ p4116) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3956) ∨ (¬ p4116) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2152 t (m.theta 1 4) (m.theta 1 6) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule10592 (meaning t m 2027) (meaning t m 2440) (meaning t m 2505) (meaning t m 3063) (meaning t m 3956) (meaning t m 4116) (meaning t m 4717) source

theorem rule10595 (p3193 p3222 : Prop) (h : (¬ p3193) ∨ (¬ p3222)) : (¬ p3193) ∨ (¬ p3222) := by
  classical
  tauto

theorem initial10595 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3222)) := by
  have source := ElevenTheory.theory2155 (m.theta 1 4) (m.theta 4 9)
  exact rule10595 (meaning t m 3193) (meaning t m 3222) source

theorem rule10598 (p3537 p4242 : Prop) (h : (¬ p4242) ∨ (¬ p3537)) : (¬ p3537) ∨ (¬ p4242) := by
  classical
  tauto

theorem initial10598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 4242)) := by
  have source := ElevenTheory.theory2158 (m.theta 1 2) (m.theta 2 8)
  exact rule10598 (meaning t m 3537) (meaning t m 4242) source

theorem rule10599 (p2138 p2143 p2144 : Prop) (h : (¬ p2143) ∨ (¬ p2138) ∨ (¬ p2144)) : (¬ p2138) ∨ (¬ p2143) ∨ (¬ p2144) := by
  classical
  tauto

theorem initial10599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2143)) ∨ (¬ (meaning t m 2144)) := by
  have source := ElevenTheory.theory2159 (m.theta 0 2) (m.theta 0 5) (m.theta 2 5)
  exact rule10599 (meaning t m 2138) (meaning t m 2143) (meaning t m 2144) source

theorem rule10600 (p2027 p2295 p3324 p3791 p4138 p5564 : Prop) (h : (¬ p3324) ∨ (¬ p4138) ∨ (¬ p2295) ∨ (¬ p3791) ∨ p2027 ∨ (¬ p5564)) : (p2027) ∨ (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3791) ∨ (¬ p4138) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial10600 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2160 t (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8)
  exact rule10600 (meaning t m 2027) (meaning t m 2295) (meaning t m 3324) (meaning t m 3791) (meaning t m 4138) (meaning t m 5564) source

theorem rule10601 (p2027 p2088 p3156 p3696 p4261 p4492 p4957 : Prop) (h : (¬ p4957) ∨ (¬ p3696) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p4492) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4261) ∨ (¬ p4492) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial10601 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory2161 t (m.theta 0 8) (m.theta 1 5) (m.theta 1 8) (m.theta 3 5) (m.theta 5 8) (m.theta 8 9)
  exact rule10601 (meaning t m 2027) (meaning t m 2088) (meaning t m 3156) (meaning t m 3696) (meaning t m 4261) (meaning t m 4492) (meaning t m 4957) source

theorem rule10602 (p2027 p2138 p2241 p2750 p2839 p3873 : Prop) (h : (¬ p2750) ∨ (¬ p2839) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p3873) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2839) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial10602 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory2162 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 5)
  exact rule10602 (meaning t m 2027) (meaning t m 2138) (meaning t m 2241) (meaning t m 2750) (meaning t m 2839) (meaning t m 3873) source

theorem rule10603 (p2027 p2132 p2657 p2870 p2881 p3742 p4278 p4666 p4789 : Prop) (h : (¬ p4789) ∨ (¬ p2870) ∨ (¬ p2657) ∨ (¬ p2132) ∨ (¬ p3742) ∨ (¬ p2881) ∨ p2027 ∨ (¬ p4278) ∨ (¬ p4666)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial10603 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory2163 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule10603 (meaning t m 2027) (meaning t m 2132) (meaning t m 2657) (meaning t m 2870) (meaning t m 2881) (meaning t m 3742) (meaning t m 4278) (meaning t m 4666) (meaning t m 4789) source

theorem rule10606 (p2027 p3323 p3324 p3692 p4345 p4433 : Prop) (h : (¬ p3692) ∨ (¬ p3324) ∨ (¬ p4345) ∨ p2027 ∨ (¬ p4433) ∨ (¬ p3323)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial10606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory2166 t (m.theta 3 6) (m.theta 5 8) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule10606 (meaning t m 2027) (meaning t m 3323) (meaning t m 3324) (meaning t m 3692) (meaning t m 4345) (meaning t m 4433) source

theorem rule10607 (p2027 p3276 p3358 p3692 p4434 p4444 : Prop) (h : (¬ p3358) ∨ (¬ p4444) ∨ p2027 ∨ (¬ p3276) ∨ (¬ p4434) ∨ (¬ p3692)) : (p2027) ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial10607 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3358)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory2167 t (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9) (m.theta 9 10)
  exact rule10607 (meaning t m 2027) (meaning t m 3276) (meaning t m 3358) (meaning t m 3692) (meaning t m 4434) (meaning t m 4444) source

theorem rule10608 (p2027 p2210 p2619 p3860 p3906 p4875 : Prop) (h : (¬ p4875) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p2619) ∨ (¬ p2210) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2619) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial10608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory2168 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8)
  exact rule10608 (meaning t m 2027) (meaning t m 2210) (meaning t m 2619) (meaning t m 3860) (meaning t m 3906) (meaning t m 4875) source

theorem rule10609 (p2027 p2144 p2220 p2252 p2657 p2750 p2753 p3146 p3266 p3742 p4831 p5503 : Prop) (h : (¬ p2750) ∨ (¬ p4831) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p5503) ∨ (¬ p2657) ∨ (¬ p2252) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p2144) ∨ (¬ p2220)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2220) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3742) ∨ (¬ p4831) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial10609 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4831)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory2169 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule10609 (meaning t m 2027) (meaning t m 2144) (meaning t m 2220) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2753) (meaning t m 3146) (meaning t m 3266) (meaning t m 3742) (meaning t m 4831) (meaning t m 5503) source

theorem rule10610 (p2860 p3758 : Prop) (h : (¬ p3758) ∨ (¬ p2860)) : (¬ p2860) ∨ (¬ p3758) := by
  classical
  tauto

theorem initial10610 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3758)) := by
  have source := ElevenTheory.theory2170 (m.theta 2 5) (m.theta 5 6)
  exact rule10610 (meaning t m 2860) (meaning t m 3758) source

theorem rule10611 (p2027 p2727 p2751 p3343 p3364 p5160 : Prop) (h : (¬ p3364) ∨ p2027 ∨ (¬ p2751) ∨ (¬ p2727) ∨ (¬ p3343) ∨ (¬ p5160)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3343) ∨ (¬ p3364) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial10611 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory2171 t (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 9)
  exact rule10611 (meaning t m 2027) (meaning t m 2727) (meaning t m 2751) (meaning t m 3343) (meaning t m 3364) (meaning t m 5160) source

theorem rule10612 (p2027 p2363 p3325 p4053 p4261 p4371 p5477 : Prop) (h : (¬ p3325) ∨ (¬ p4053) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p5477) ∨ (¬ p4261) ∨ (¬ p4371)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p4053) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p5477) := by
  classical
  tauto

theorem initial10612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4371)) ∨ (¬ (meaning t m 5477)) := by
  have source := ElevenTheory.theory2172 t (m.theta 1 6) (m.theta 1 8) (m.theta 6 10) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule10612 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 4053) (meaning t m 4261) (meaning t m 4371) (meaning t m 5477) source

theorem rule10614 (p2027 p2187 p2493 p2928 p3921 p4203 p4405 : Prop) (h : (¬ p4203) ∨ (¬ p2493) ∨ (¬ p2187) ∨ (¬ p2928) ∨ (¬ p3921) ∨ p2027 ∨ (¬ p4405)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p3921) ∨ (¬ p4203) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2174 t (m.theta 1 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule10614 (meaning t m 2027) (meaning t m 2187) (meaning t m 2493) (meaning t m 2928) (meaning t m 3921) (meaning t m 4203) (meaning t m 4405) source

theorem rule10616 (p2144 p2958 p4236 : Prop) (h : (¬ p2144) ∨ p2958 ∨ (¬ p4236)) : (¬ p2144) ∨ (p2958) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial10616 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2144)) ∨ (meaning t m 2958) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory2176 (m.theta 0 2) (m.theta 0 3) (m.theta 0 5)
  exact rule10616 (meaning t m 2144) (meaning t m 2958) (meaning t m 4236) source

theorem rule10617 (p2027 p2241 p2745 p2797 p3591 p4319 : Prop) (h : (¬ p2745) ∨ p2027 ∨ (¬ p4319) ∨ (¬ p2797) ∨ (¬ p2241) ∨ (¬ p3591)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3591) ∨ (¬ p4319) := by
  classical
  tauto

theorem initial10617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4319)) := by
  have source := ElevenTheory.theory2177 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6)
  exact rule10617 (meaning t m 2027) (meaning t m 2241) (meaning t m 2745) (meaning t m 2797) (meaning t m 3591) (meaning t m 4319) source

theorem rule10619 (p3461 p4191 : Prop) (h : (¬ p4191) ∨ (¬ p3461)) : (¬ p3461) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial10619 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory2179 (m.theta 6 9) (m.theta 9 10)
  exact rule10619 (meaning t m 3461) (meaning t m 4191) source

theorem rule10621 (p2027 p2505 p3063 p3238 p3956 p4717 : Prop) (h : (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p4717)) : (p2027) ∨ (¬ p2505) ∨ (¬ p3063) ∨ (¬ p3238) ∨ (¬ p3956) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10621 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2181 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 8)
  exact rule10621 (meaning t m 2027) (meaning t m 2505) (meaning t m 3063) (meaning t m 3238) (meaning t m 3956) (meaning t m 4717) source

theorem rule10623 (p2027 p2341 p2589 p3644 p4646 p5201 : Prop) (h : p2027 ∨ (¬ p4646) ∨ (¬ p2589) ∨ (¬ p5201) ∨ (¬ p2341) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p4646) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial10623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4646)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory2183 t (m.theta 0 4) (m.theta 0 7) (m.theta 4 5) (m.theta 4 7) (m.theta 7 8)
  exact rule10623 (meaning t m 2027) (meaning t m 2341) (meaning t m 2589) (meaning t m 3644) (meaning t m 4646) (meaning t m 5201) source

theorem rule10624 (p2027 p2177 p2476 p3389 p4276 p4383 : Prop) (h : p2027 ∨ (¬ p2177) ∨ (¬ p4276) ∨ (¬ p4383) ∨ (¬ p2476) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4276) ∨ (¬ p4383) := by
  classical
  tauto

theorem initial10624 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4383)) := by
  have source := ElevenTheory.theory2184 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 6 7) (m.theta 7 8)
  exact rule10624 (meaning t m 2027) (meaning t m 2177) (meaning t m 2476) (meaning t m 3389) (meaning t m 4276) (meaning t m 4383) source

theorem rule10625 (p2027 p2963 p3166 p3568 p4405 p4417 : Prop) (h : (¬ p4417) ∨ (¬ p3568) ∨ (¬ p3166) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p2963)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3568) ∨ (¬ p4405) ∨ (¬ p4417) := by
  classical
  tauto

theorem initial10625 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4417)) := by
  have source := ElevenTheory.theory2185 t (m.theta 0 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 7) (m.theta 6 8)
  exact rule10625 (meaning t m 2027) (meaning t m 2963) (meaning t m 3166) (meaning t m 3568) (meaning t m 4405) (meaning t m 4417) source

theorem rule10626 (p2027 p2166 p2573 p3904 p4034 p4120 p4717 : Prop) (h : (¬ p2573) ∨ (¬ p4717) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p4034) ∨ (¬ p2166) ∨ (¬ p3904)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2573) ∨ (¬ p3904) ∨ (¬ p4034) ∨ (¬ p4120) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10626 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2186 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule10626 (meaning t m 2027) (meaning t m 2166) (meaning t m 2573) (meaning t m 3904) (meaning t m 4034) (meaning t m 4120) (meaning t m 4717) source

theorem rule10628 (p2027 p2295 p2573 p3540 p3921 p4976 : Prop) (h : (¬ p4976) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ p2027 ∨ (¬ p2295)) : (p2027) ∨ (¬ p2295) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial10628 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory2188 t (m.theta 0 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule10628 (meaning t m 2027) (meaning t m 2295) (meaning t m 2573) (meaning t m 3540) (meaning t m 3921) (meaning t m 4976) source

theorem rule10629 (p2027 p2417 p2437 p2926 p3817 p4811 : Prop) (h : (¬ p4811) ∨ (¬ p2926) ∨ (¬ p2417) ∨ (¬ p3817) ∨ p2027 ∨ (¬ p2437)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (¬ p2926) ∨ (¬ p3817) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial10629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2189 t (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule10629 (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 2926) (meaning t m 3817) (meaning t m 4811) source

theorem rule10630 (p2027 p2504 p3093 p3238 p3452 p4717 : Prop) (h : (¬ p3093) ∨ (¬ p4717) ∨ (¬ p3238) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p2504)) : (p2027) ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10630 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2190 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6)
  exact rule10630 (meaning t m 2027) (meaning t m 2504) (meaning t m 3093) (meaning t m 3238) (meaning t m 3452) (meaning t m 4717) source

theorem rule10631 (p2027 p2563 p3355 p3646 p3904 p4953 : Prop) (h : (¬ p4953) ∨ (¬ p2563) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3355) ∨ (¬ p3904)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3355) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4953) := by
  classical
  tauto

theorem initial10631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4953)) := by
  have source := ElevenTheory.theory2191 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 9) (m.theta 5 6)
  exact rule10631 (meaning t m 2027) (meaning t m 2563) (meaning t m 3355) (meaning t m 3646) (meaning t m 3904) (meaning t m 4953) source

theorem rule10632 (p2027 p2440 p3449 p3452 p4116 p4610 p4687 : Prop) (h : (¬ p4687) ∨ (¬ p3449) ∨ p2027 ∨ (¬ p2440) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4610)) : (p2027) ∨ (¬ p2440) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4610) ∨ (¬ p4687) := by
  classical
  tauto

theorem initial10632 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4610)) ∨ (¬ (meaning t m 4687)) := by
  have source := ElevenTheory.theory2192 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule10632 (meaning t m 2027) (meaning t m 2440) (meaning t m 3449) (meaning t m 3452) (meaning t m 4116) (meaning t m 4610) (meaning t m 4687) source

theorem rule10634 (p2027 p2608 p2891 p3369 p3556 p4377 : Prop) (h : (¬ p2608) ∨ p2027 ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4377)) : (p2027) ∨ (¬ p2608) ∨ (¬ p2891) ∨ (¬ p3369) ∨ (¬ p3556) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial10634 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory2194 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 7)
  exact rule10634 (meaning t m 2027) (meaning t m 2608) (meaning t m 2891) (meaning t m 3369) (meaning t m 3556) (meaning t m 4377) source

theorem rule10635 (p2027 p2476 p3355 p3692 p4434 p4695 : Prop) (h : (¬ p3355) ∨ (¬ p4695) ∨ (¬ p2476) ∨ (¬ p3692) ∨ (¬ p4434) ∨ p2027) : (p2027) ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial10635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4434)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory2195 t (m.theta 0 4) (m.theta 4 8) (m.theta 4 9) (m.theta 5 8) (m.theta 8 9)
  exact rule10635 (meaning t m 2027) (meaning t m 2476) (meaning t m 3355) (meaning t m 3692) (meaning t m 4434) (meaning t m 4695) source

theorem rule10636 (p2027 p2177 p3146 p4107 p4445 p4905 : Prop) (h : (¬ p4905) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p4445) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory2196 t (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10636 (meaning t m 2027) (meaning t m 2177) (meaning t m 3146) (meaning t m 4107) (meaning t m 4445) (meaning t m 4905) source

theorem rule10637 (p2027 p3256 p3644 p4044 p4348 p4653 : Prop) (h : (¬ p3644) ∨ (¬ p4653) ∨ (¬ p4044) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p4348)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3644) ∨ (¬ p4044) ∨ (¬ p4348) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial10637 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory2197 t (m.theta 3 7) (m.theta 3 8) (m.theta 4 7) (m.theta 7 8) (m.theta 8 9)
  exact rule10637 (meaning t m 2027) (meaning t m 3256) (meaning t m 3644) (meaning t m 4044) (meaning t m 4348) (meaning t m 4653) source

theorem rule10638 (p2027 p2363 p3325 p3644 p4118 p4276 p4378 : Prop) (h : p2027 ∨ (¬ p4378) ∨ (¬ p4118) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p4276) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p4118) ∨ (¬ p4276) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial10638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory2198 t (m.theta 3 8) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule10638 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3644) (meaning t m 4118) (meaning t m 4276) (meaning t m 4378) source

theorem rule10639 (p2027 p2810 p3434 p3947 p4652 p4781 : Prop) (h : (¬ p2810) ∨ (¬ p4652) ∨ p2027 ∨ (¬ p3947) ∨ (¬ p4781) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3434) ∨ (¬ p3947) ∨ (¬ p4652) ∨ (¬ p4781) := by
  classical
  tauto

theorem initial10639 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4652)) ∨ (¬ (meaning t m 4781)) := by
  have source := ElevenTheory.theory2199 t (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 7 9)
  exact rule10639 (meaning t m 2027) (meaning t m 2810) (meaning t m 3434) (meaning t m 3947) (meaning t m 4652) (meaning t m 4781) source

theorem rule10640 (p2027 p2177 p3027 p4360 p4548 p4570 : Prop) (h : (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570) ∨ (¬ p3027) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial10640 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4548)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory2200 t (m.theta 1 3) (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8)
  exact rule10640 (meaning t m 2027) (meaning t m 2177) (meaning t m 3027) (meaning t m 4360) (meaning t m 4548) (meaning t m 4570) source

theorem rule10641 (p2027 p2341 p2441 p2870 p3644 p3691 p4885 : Prop) (h : (¬ p3691) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p3644) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p4885)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2441) ∨ (¬ p2870) ∨ (¬ p3644) ∨ (¬ p3691) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial10641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3691)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory2201 t (m.theta 0 7) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule10641 (meaning t m 2027) (meaning t m 2341) (meaning t m 2441) (meaning t m 2870) (meaning t m 3644) (meaning t m 3691) (meaning t m 4885) source

theorem rule10642 (p2027 p3097 p3125 p4276 p4278 p4623 : Prop) (h : (¬ p3125) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p4623)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial10642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory2202 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule10642 (meaning t m 2027) (meaning t m 3097) (meaning t m 3125) (meaning t m 4276) (meaning t m 4278) (meaning t m 4623) source

theorem rule10643 (p2027 p2088 p2313 p4114 p4347 p4405 : Prop) (h : p2027 ∨ (¬ p4114) ∨ (¬ p4405) ∨ (¬ p2313) ∨ (¬ p4347) ∨ (¬ p2088)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2313) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10643 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2203 t (m.theta 0 6) (m.theta 0 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule10643 (meaning t m 2027) (meaning t m 2088) (meaning t m 2313) (meaning t m 4114) (meaning t m 4347) (meaning t m 4405) source

theorem rule10644 (p2027 p2510 p2528 p2588 p3857 p4113 p4405 : Prop) (h : p2027 ∨ (¬ p4113) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (¬ p4405) ∨ (¬ p2510) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2588) ∨ (¬ p3857) ∨ (¬ p4113) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial10644 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2510)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4113)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory2204 t (m.theta 0 8) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule10644 (meaning t m 2027) (meaning t m 2510) (meaning t m 2528) (meaning t m 2588) (meaning t m 3857) (meaning t m 4113) (meaning t m 4405) source

theorem rule10645 (p2027 p2927 p3201 p3379 p4366 p5214 : Prop) (h : (¬ p3379) ∨ (¬ p5214) ∨ (¬ p4366) ∨ (¬ p3201) ∨ p2027 ∨ (¬ p2927)) : (p2027) ∨ (¬ p2927) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p4366) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial10645 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2927)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2205 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 7)
  exact rule10645 (meaning t m 2027) (meaning t m 2927) (meaning t m 3201) (meaning t m 3379) (meaning t m 4366) (meaning t m 5214) source

theorem rule10646 (p2027 p2437 p2928 p2992 p3402 p4704 : Prop) (h : (¬ p2928) ∨ (¬ p2992) ∨ (¬ p3402) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2928) ∨ (¬ p2992) ∨ (¬ p3402) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10646 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2206 t (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule10646 (meaning t m 2027) (meaning t m 2437) (meaning t m 2928) (meaning t m 2992) (meaning t m 3402) (meaning t m 4704) source

theorem rule10647 (p2027 p2573 p2589 p3952 p4203 p4702 : Prop) (h : (¬ p4702) ∨ (¬ p2589) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p2573) ∨ p2027) : (p2027) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702) := by
  classical
  tauto

theorem initial10647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4702)) := by
  have source := ElevenTheory.theory2207 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule10647 (meaning t m 2027) (meaning t m 2573) (meaning t m 2589) (meaning t m 3952) (meaning t m 4203) (meaning t m 4702) source

theorem rule10648 (p2027 p2247 p2608 p2742 p2829 p4845 : Prop) (h : (¬ p2247) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p4845) ∨ (¬ p2829) ∨ (¬ p2742)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p2829) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial10648 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory2208 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6)
  exact rule10648 (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2742) (meaning t m 2829) (meaning t m 4845) source

theorem rule10649 (p2027 p2313 p2383 p3550 p3644 p4276 : Prop) (h : (¬ p3644) ∨ (¬ p2383) ∨ p2027 ∨ (¬ p3550) ∨ (¬ p2313) ∨ (¬ p4276)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial10649 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory2209 t (m.theta 0 6) (m.theta 4 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule10649 (meaning t m 2027) (meaning t m 2313) (meaning t m 2383) (meaning t m 3550) (meaning t m 3644) (meaning t m 4276) source

theorem rule10652 (p5738 p5739 p5740 p5741 p5742 : Prop) : (¬ (p5738 ∧ p5739 ∧ p5740 ∧ p5741 ∧ p5742)) ∨ (p5740) := by
  classical
  tauto

theorem initial10652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5737)) ∨ (meaning t m 5740) := by
  exact rule10652 (meaning t m 5738) (meaning t m 5739) (meaning t m 5740) (meaning t m 5741) (meaning t m 5742)

theorem rule10658 (p4272 p5744 p5745 p5746 p5747 : Prop) : (p4272) ∨ (¬ (p5744 ∧ p5745 ∧ p4272 ∧ p5746 ∧ p5747)) := by
  classical
  tauto

theorem initial10658 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4272) ∨ (¬ (meaning t m 5743)) := by
  exact rule10658 (meaning t m 4272) (meaning t m 5744) (meaning t m 5745) (meaning t m 5746) (meaning t m 5747)

theorem rule10664 (p5737 p5743 : Prop) : (¬ (p5737 ∨ p5743)) ∨ (p5737) ∨ (p5743) := by
  classical
  tauto

theorem initial10664 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5736)) ∨ (meaning t m 5737) ∨ (meaning t m 5743) := by
  exact rule10664 (meaning t m 5737) (meaning t m 5743)

theorem rule10665 (p4266 p5736 : Prop) (h : (p4266 ↔ p5736)) : (¬ p4266) ∨ (p5736) := by
  classical
  tauto

theorem initial10665 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4266)) ∨ (meaning t m 5736) := by
  have source := ElevenTheory.theory2210 t (m.theta 3 10) (m.theta 3 5) (m.theta 5 10)
  exact rule10665 (meaning t m 4266) (meaning t m 5736) source

theorem rule10667 (p2027 p2373 p3016 p3497 p4700 p4717 : Prop) (h : (¬ p4700) ∨ p2027 ∨ (¬ p3016) ∨ (¬ p4717) ∨ (¬ p3497) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3016) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial10667 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2211 t (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 8)
  exact rule10667 (meaning t m 2027) (meaning t m 2373) (meaning t m 3016) (meaning t m 3497) (meaning t m 4700) (meaning t m 4717) source

theorem rule10668 (p2027 p2341 p2437 p4256 p4383 p5203 : Prop) (h : p2027 ∨ (¬ p2437) ∨ (¬ p4256) ∨ (¬ p2341) ∨ (¬ p4383) ∨ (¬ p5203)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5203) := by
  classical
  tauto

theorem initial10668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5203)) := by
  have source := ElevenTheory.theory2212 t (m.theta 0 7) (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule10668 (meaning t m 2027) (meaning t m 2341) (meaning t m 2437) (meaning t m 4256) (meaning t m 4383) (meaning t m 5203) source

theorem rule10669 (p2027 p3093 p3452 p3590 p3874 p3922 p3984 p4595 : Prop) (h : (¬ p3984) ∨ (¬ p3922) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p4595) ∨ (¬ p3874) ∨ (¬ p3590) ∨ (¬ p3452)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p3874) ∨ (¬ p3922) ∨ (¬ p3984) ∨ (¬ p4595) := by
  classical
  tauto

theorem initial10669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 3922)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4595)) := by
  have source := ElevenTheory.theory2213 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 6) (m.theta 4 8)
  exact rule10669 (meaning t m 2027) (meaning t m 3093) (meaning t m 3452) (meaning t m 3590) (meaning t m 3874) (meaning t m 3922) (meaning t m 3984) (meaning t m 4595) source

theorem rule10670 (p2027 p3483 p3822 p3947 p4570 p5299 p5379 : Prop) (h : (¬ p4570) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3947) ∨ (¬ p5299) ∨ p2027 ∨ (¬ p5379)) : (p2027) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p3947) ∨ (¬ p4570) ∨ (¬ p5299) ∨ (¬ p5379) := by
  classical
  tauto

theorem initial10670 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5299)) ∨ (¬ (meaning t m 5379)) := by
  have source := ElevenTheory.theory2214 t (m.theta 0 9) (m.theta 2 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule10670 (meaning t m 2027) (meaning t m 3483) (meaning t m 3822) (meaning t m 3947) (meaning t m 4570) (meaning t m 5299) (meaning t m 5379) source

theorem rule10671 (p2027 p2122 p2312 p3516 p3947 p4067 p4846 : Prop) (h : p2027 ∨ (¬ p4067) ∨ (¬ p4846) ∨ (¬ p2122) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p2312)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial10671 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2312)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory2215 t (m.theta 0 7) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule10671 (meaning t m 2027) (meaning t m 2122) (meaning t m 2312) (meaning t m 3516) (meaning t m 3947) (meaning t m 4067) (meaning t m 4846) source

theorem rule10672 (p2027 p2299 p2396 p3692 p4443 p4902 : Prop) (h : (¬ p2396) ∨ (¬ p4443) ∨ (¬ p2299) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p4902)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) := by
  classical
  tauto

theorem initial10672 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4443)) ∨ (¬ (meaning t m 4902)) := by
  have source := ElevenTheory.theory2216 t (m.theta 5 8) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule10672 (meaning t m 2027) (meaning t m 2299) (meaning t m 2396) (meaning t m 3692) (meaning t m 4443) (meaning t m 4902) source

theorem rule10673 (p2027 p2187 p3097 p3550 p3644 p4276 : Prop) (h : (¬ p3644) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p3644) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial10673 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory2217 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule10673 (meaning t m 2027) (meaning t m 2187) (meaning t m 3097) (meaning t m 3550) (meaning t m 3644) (meaning t m 4276) source

theorem rule10674 (p2027 p2589 p3516 p3947 p3984 p4067 p4717 p5201 : Prop) (h : (¬ p2589) ∨ (¬ p5201) ∨ (¬ p3516) ∨ p2027 ∨ (¬ p3984) ∨ (¬ p4717) ∨ (¬ p3947) ∨ (¬ p4067)) : (p2027) ∨ (¬ p2589) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4717) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial10674 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4717)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory2218 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 6) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 7 9)
  exact rule10674 (meaning t m 2027) (meaning t m 2589) (meaning t m 3516) (meaning t m 3947) (meaning t m 3984) (meaning t m 4067) (meaning t m 4717) (meaning t m 5201) source

theorem rule10675 (p2027 p3641 p3969 p4158 p5670 p5681 : Prop) (h : (¬ p4158) ∨ (¬ p5670) ∨ (¬ p3641) ∨ (¬ p5681) ∨ p2027 ∨ (¬ p3969)) : (p2027) ∨ (¬ p3641) ∨ (¬ p3969) ∨ (¬ p4158) ∨ (¬ p5670) ∨ (¬ p5681) := by
  classical
  tauto

theorem initial10675 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4158)) ∨ (¬ (meaning t m 5670)) ∨ (¬ (meaning t m 5681)) := by
  have source := ElevenTheory.theory2219 t (m.theta 2 4) (m.theta 4 10) (m.theta 4 8) (m.theta 5 8) (m.theta 8 10)
  exact rule10675 (meaning t m 2027) (meaning t m 3641) (meaning t m 3969) (meaning t m 4158) (meaning t m 5670) (meaning t m 5681) source

theorem rule10677 (p2027 p2177 p3919 p3941 p4570 p5600 : Prop) (h : (¬ p2177) ∨ (¬ p5600) ∨ (¬ p3941) ∨ (¬ p4570) ∨ p2027 ∨ (¬ p3919)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3919) ∨ (¬ p3941) ∨ (¬ p4570) ∨ (¬ p5600) := by
  classical
  tauto

theorem initial10677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5600)) := by
  have source := ElevenTheory.theory2221 t (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 10)
  exact rule10677 (meaning t m 2027) (meaning t m 2177) (meaning t m 3919) (meaning t m 3941) (meaning t m 4570) (meaning t m 5600) source

theorem rule10678 (p2027 p2177 p2761 p3945 p4429 p4570 p5284 : Prop) (h : (¬ p4570) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p4429) ∨ (¬ p3945) ∨ (¬ p5284) ∨ (¬ p2761)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4429) ∨ (¬ p4570) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial10678 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3945)) ∨ (¬ (meaning t m 4429)) ∨ (¬ (meaning t m 4570)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2222 t (m.theta 3 7) (m.theta 3 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9) (m.theta 9 10)
  exact rule10678 (meaning t m 2027) (meaning t m 2177) (meaning t m 2761) (meaning t m 3945) (meaning t m 4429) (meaning t m 4570) (meaning t m 5284) source

theorem rule10679 (p2027 p2177 p2459 p3919 p4118 p4570 : Prop) (h : (¬ p2177) ∨ (¬ p4570) ∨ (¬ p4118) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p3919)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2459) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial10679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory2223 t (m.theta 3 7) (m.theta 3 8) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule10679 (meaning t m 2027) (meaning t m 2177) (meaning t m 2459) (meaning t m 3919) (meaning t m 4118) (meaning t m 4570) source

theorem rule10680 (p2027 p2177 p2311 p3309 p3551 p5018 : Prop) (h : (¬ p2311) ∨ (¬ p3551) ∨ (¬ p3309) ∨ (¬ p5018) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p3309) ∨ (¬ p3551) ∨ (¬ p5018) := by
  classical
  tauto

theorem initial10680 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 5018)) := by
  have source := ElevenTheory.theory2224 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule10680 (meaning t m 2027) (meaning t m 2177) (meaning t m 2311) (meaning t m 3309) (meaning t m 3551) (meaning t m 5018) source

theorem rule10681 (p2027 p2396 p2807 p3292 p3579 p4276 p4656 : Prop) (h : (¬ p3292) ∨ (¬ p4656) ∨ (¬ p2807) ∨ (¬ p4276) ∨ p2027 ∨ (¬ p3579) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2807) ∨ (¬ p3292) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4656) := by
  classical
  tauto

theorem initial10681 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4656)) := by
  have source := ElevenTheory.theory2225 t (m.theta 0 3) (m.theta 3 7) (m.theta 3 9) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule10681 (meaning t m 2027) (meaning t m 2396) (meaning t m 2807) (meaning t m 3292) (meaning t m 3579) (meaning t m 4276) (meaning t m 4656) source

theorem rule10682 (p2027 p2311 p3631 p3821 p4110 p4356 p4431 p4632 : Prop) (h : (¬ p3821) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4632) ∨ (¬ p4431) ∨ (¬ p4356) ∨ (¬ p2311) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2311) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4431) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial10682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2226 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 5 6) (m.theta 7 9)
  exact rule10682 (meaning t m 2027) (meaning t m 2311) (meaning t m 3631) (meaning t m 3821) (meaning t m 4110) (meaning t m 4356) (meaning t m 4431) (meaning t m 4632) source

theorem rule10683 (p2027 p3434 p3587 p3821 p4235 p4283 p4885 : Prop) (h : (¬ p4235) ∨ (¬ p3434) ∨ (¬ p4283) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p3587) ∨ (¬ p4885)) : (p2027) ∨ (¬ p3434) ∨ (¬ p3587) ∨ (¬ p3821) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial10683 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory2227 t (m.theta 0 7) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule10683 (meaning t m 2027) (meaning t m 3434) (meaning t m 3587) (meaning t m 3821) (meaning t m 4235) (meaning t m 4283) (meaning t m 4885) source

theorem rule10684 (p2027 p2187 p2192 p2590 p3324 p3984 p4632 : Prop) (h : (¬ p4632) ∨ (¬ p2187) ∨ (¬ p3984) ∨ (¬ p2590) ∨ (¬ p3324) ∨ (¬ p2192) ∨ p2027) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p3324) ∨ (¬ p3984) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial10684 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2228 t (m.theta 1 5) (m.theta 3 6) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8)
  exact rule10684 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2590) (meaning t m 3324) (meaning t m 3984) (meaning t m 4632) source

theorem rule10685 (p2027 p2891 p2946 p3414 p3699 p4960 : Prop) (h : (¬ p4960) ∨ p2027 ∨ (¬ p3699) ∨ (¬ p2891) ∨ (¬ p3414) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2891) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial10685 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3699)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory2229 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 7) (m.theta 5 7)
  exact rule10685 (meaning t m 2027) (meaning t m 2891) (meaning t m 2946) (meaning t m 3414) (meaning t m 3699) (meaning t m 4960) source

theorem rule10686 (p2027 p2220 p2657 p2958 p3497 p4704 : Prop) (h : (¬ p3497) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p4704) ∨ (¬ p2220) ∨ (¬ p2958)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3497) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10686 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2230 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule10686 (meaning t m 2027) (meaning t m 2220) (meaning t m 2657) (meaning t m 2958) (meaning t m 3497) (meaning t m 4704) source

theorem rule10687 (p2027 p2441 p2881 p2891 p3644 p4632 : Prop) (h : (¬ p2891) ∨ (¬ p4632) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p2441)) : (p2027) ∨ (¬ p2441) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3644) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial10687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2231 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule10687 (meaning t m 2027) (meaning t m 2441) (meaning t m 2881) (meaning t m 2891) (meaning t m 3644) (meaning t m 4632) source

theorem rule10688 (p3516 p3821 : Prop) (h : (¬ p3821) ∨ (¬ p3516)) : (¬ p3516) ∨ (¬ p3821) := by
  classical
  tauto

theorem initial10688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3821)) := by
  have source := ElevenTheory.theory2232 (m.theta 0 7) (m.theta 7 9)
  exact rule10688 (meaning t m 3516) (meaning t m 3821) source

theorem rule10691 (p2027 p2656 p2727 p2751 p3364 p3389 p3876 : Prop) (h : p2027 ∨ (¬ p2751) ∨ (¬ p2727) ∨ (¬ p3876) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p2656)) : (p2027) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial10691 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory2235 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7)
  exact rule10691 (meaning t m 2027) (meaning t m 2656) (meaning t m 2727) (meaning t m 2751) (meaning t m 3364) (meaning t m 3389) (meaning t m 3876) source

theorem rule10692 (p2027 p2192 p2274 p2588 p2590 p4632 : Prop) (h : (¬ p2590) ∨ (¬ p2588) ∨ (¬ p2192) ∨ (¬ p4632) ∨ p2027 ∨ (¬ p2274)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial10692 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2236 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule10692 (meaning t m 2027) (meaning t m 2192) (meaning t m 2274) (meaning t m 2588) (meaning t m 2590) (meaning t m 4632) source

theorem rule10693 (p2027 p2470 p3097 p3201 p3555 p3874 p4173 p4276 p5190 : Prop) (h : p2027 ∨ (¬ p5190) ∨ (¬ p2470) ∨ (¬ p4173) ∨ (¬ p3097) ∨ (¬ p3555) ∨ (¬ p3874) ∨ (¬ p4276) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2470) ∨ (¬ p3097) ∨ (¬ p3201) ∨ (¬ p3555) ∨ (¬ p3874) ∨ (¬ p4173) ∨ (¬ p4276) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial10693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2237 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7)
  exact rule10693 (meaning t m 2027) (meaning t m 2470) (meaning t m 3097) (meaning t m 3201) (meaning t m 3555) (meaning t m 3874) (meaning t m 4173) (meaning t m 4276) (meaning t m 5190) source

theorem rule10694 (p2027 p2246 p2264 p2946 p3031 p3548 p3580 p4704 : Prop) (h : (¬ p2246) ∨ (¬ p3580) ∨ (¬ p4704) ∨ (¬ p2264) ∨ (¬ p3031) ∨ (¬ p3548) ∨ p2027 ∨ (¬ p2946)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2264) ∨ (¬ p2946) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3580) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2238 t (m.theta 0 3) (m.theta 1 3) (m.theta 1 7) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule10694 (meaning t m 2027) (meaning t m 2246) (meaning t m 2264) (meaning t m 2946) (meaning t m 3031) (meaning t m 3548) (meaning t m 3580) (meaning t m 4704) source

theorem rule10696 (p2027 p2533 p3680 p4348 p4444 p4905 : Prop) (h : p2027 ∨ (¬ p4444) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p2533) ∨ (¬ p3680)) : (p2027) ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial10696 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2533)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory2240 t (m.theta 5 8) (m.theta 5 9) (m.theta 7 8) (m.theta 8 9) (m.theta 9 10)
  exact rule10696 (meaning t m 2027) (meaning t m 2533) (meaning t m 3680) (meaning t m 4348) (meaning t m 4444) (meaning t m 4905) source

theorem rule10698 (p2027 p2192 p3952 p4111 p4365 p4704 : Prop) (h : (¬ p4365) ∨ (¬ p2192) ∨ (¬ p4704) ∨ (¬ p4111) ∨ p2027 ∨ (¬ p3952)) : (p2027) ∨ (¬ p2192) ∨ (¬ p3952) ∨ (¬ p4111) ∨ (¬ p4365) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10698 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2242 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule10698 (meaning t m 2027) (meaning t m 2192) (meaning t m 3952) (meaning t m 4111) (meaning t m 4365) (meaning t m 4704) source

theorem rule10699 (p2027 p2166 p2957 p4111 p4120 p4365 p4704 : Prop) (h : (¬ p4120) ∨ (¬ p2166) ∨ p2027 ∨ (¬ p4365) ∨ (¬ p4111) ∨ (¬ p2957) ∨ (¬ p4704)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2957) ∨ (¬ p4111) ∨ (¬ p4120) ∨ (¬ p4365) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4365)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2243 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 8)
  exact rule10699 (meaning t m 2027) (meaning t m 2166) (meaning t m 2957) (meaning t m 4111) (meaning t m 4120) (meaning t m 4365) (meaning t m 4704) source

theorem rule10700 (p2027 p2656 p3136 p3364 p3389 p3876 p4704 : Prop) (h : p2027 ∨ (¬ p3389) ∨ (¬ p2656) ∨ (¬ p3876) ∨ (¬ p4704) ∨ (¬ p3364) ∨ (¬ p3136)) : (p2027) ∨ (¬ p2656) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2244 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 7)
  exact rule10700 (meaning t m 2027) (meaning t m 2656) (meaning t m 3136) (meaning t m 3364) (meaning t m 3389) (meaning t m 3876) (meaning t m 4704) source

theorem rule10701 (p2027 p2534 p3125 p3989 p4345 p4596 : Prop) (h : (¬ p4345) ∨ (¬ p4596) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p2534) ∨ (¬ p3989)) : (p2027) ∨ (¬ p2534) ∨ (¬ p3125) ∨ (¬ p3989) ∨ (¬ p4345) ∨ (¬ p4596) := by
  classical
  tauto

theorem initial10701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4596)) := by
  have source := ElevenTheory.theory2245 t (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule10701 (meaning t m 2027) (meaning t m 2534) (meaning t m 3125) (meaning t m 3989) (meaning t m 4345) (meaning t m 4596) source

theorem rule10702 (p2027 p2751 p4053 p4195 p4759 p5717 : Prop) (h : (¬ p2751) ∨ (¬ p4053) ∨ p2027 ∨ (¬ p4759) ∨ (¬ p4195) ∨ (¬ p5717)) : (p2027) ∨ (¬ p2751) ∨ (¬ p4053) ∨ (¬ p4195) ∨ (¬ p4759) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial10702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4759)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory2246 t (m.theta 1 3) (m.theta 1 6) (m.theta 2 3) (m.theta 3 6) (m.theta 6 10)
  exact rule10702 (meaning t m 2027) (meaning t m 2751) (meaning t m 4053) (meaning t m 4195) (meaning t m 4759) (meaning t m 5717) source

theorem rule10703 (p2027 p3389 p3555 p3641 p3876 p3989 p4173 p4596 p5190 : Prop) (h : (¬ p4596) ∨ (¬ p3641) ∨ (¬ p3555) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p3876) ∨ (¬ p3389)) : (p2027) ∨ (¬ p3389) ∨ (¬ p3555) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p3989) ∨ (¬ p4173) ∨ (¬ p4596) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial10703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4596)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2247 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule10703 (meaning t m 2027) (meaning t m 3389) (meaning t m 3555) (meaning t m 3641) (meaning t m 3876) (meaning t m 3989) (meaning t m 4173) (meaning t m 4596) (meaning t m 5190) source

theorem rule10704 (p2027 p2246 p3286 p4041 p4348 p4350 p4360 : Prop) (h : (¬ p4041) ∨ p2027 ∨ (¬ p2246) ∨ (¬ p4348) ∨ (¬ p3286) ∨ (¬ p4360) ∨ (¬ p4350)) : (p2027) ∨ (¬ p2246) ∨ (¬ p3286) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4350) ∨ (¬ p4360) := by
  classical
  tauto

theorem initial10704 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4350)) ∨ (¬ (meaning t m 4360)) := by
  have source := ElevenTheory.theory2248 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 8) (m.theta 3 9) (m.theta 7 8) (m.theta 8 9)
  exact rule10704 (meaning t m 2027) (meaning t m 2246) (meaning t m 3286) (meaning t m 4041) (meaning t m 4348) (meaning t m 4350) (meaning t m 4360) source

theorem rule10705 (p2027 p2810 p3105 p4208 p4313 p4704 : Prop) (h : (¬ p4313) ∨ (¬ p2810) ∨ (¬ p3105) ∨ (¬ p4208) ∨ p2027 ∨ (¬ p4704)) : (p2027) ∨ (¬ p2810) ∨ (¬ p3105) ∨ (¬ p4208) ∨ (¬ p4313) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial10705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4313)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory2249 t (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 9)
  exact rule10705 (meaning t m 2027) (meaning t m 2810) (meaning t m 3105) (meaning t m 4208) (meaning t m 4313) (meaning t m 4704) source

theorem rule10706 (p2027 p2230 p2656 p2727 p2751 p3364 p3684 : Prop) (h : (¬ p2656) ∨ (¬ p3364) ∨ (¬ p3684) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2727) ∨ (¬ p2751)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3364) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial10706 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory2250 t (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule10706 (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 2727) (meaning t m 2751) (meaning t m 3364) (meaning t m 3684) source

theorem rule10707 (p2027 p2307 p2584 p2588 p3584 p4730 : Prop) (h : (¬ p2584) ∨ (¬ p4730) ∨ (¬ p2588) ∨ p2027 ∨ (¬ p3584) ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3584) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial10707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory2251 t (m.theta 0 4) (m.theta 0 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7)
  exact rule10707 (meaning t m 2027) (meaning t m 2307) (meaning t m 2584) (meaning t m 2588) (meaning t m 3584) (meaning t m 4730) source

theorem rule10712 (p2027 p3105 p4244 p4277 p4278 p4323 p5299 : Prop) (h : (¬ p4244) ∨ (¬ p4323) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p5299) ∨ p2027 ∨ (¬ p3105)) : (p2027) ∨ (¬ p3105) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p4323) ∨ (¬ p5299) := by
  classical
  tauto

theorem initial10712 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4323)) ∨ (¬ (meaning t m 5299)) := by
  have source := ElevenTheory.theory2256 t (m.theta 0 9) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule10712 (meaning t m 2027) (meaning t m 3105) (meaning t m 4244) (meaning t m 4277) (meaning t m 4278) (meaning t m 4323) (meaning t m 5299) source

theorem rule10713 (p2027 p2563 p2850 p3646 p3904 p4727 : Prop) (h : (¬ p2850) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p2563) ∨ (¬ p4727)) : (p2027) ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial10713 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory2257 t (m.theta 0 4) (m.theta 0 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 6)
  exact rule10713 (meaning t m 2027) (meaning t m 2563) (meaning t m 2850) (meaning t m 3646) (meaning t m 3904) (meaning t m 4727) source

theorem rule10714 (p2027 p2396 p3399 p3834 p5142 p5358 : Prop) (h : (¬ p2396) ∨ (¬ p5142) ∨ (¬ p5358) ∨ p2027 ∨ (¬ p3399) ∨ (¬ p3834)) : (p2027) ∨ (¬ p2396) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5142) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial10714 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5142)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory2258 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 6 7) (m.theta 7 9)
  exact rule10714 (meaning t m 2027) (meaning t m 2396) (meaning t m 3399) (meaning t m 3834) (meaning t m 5142) (meaning t m 5358) source

theorem rule10716 (p3286 p3292 : Prop) (h : (¬ p3292) ∨ (¬ p3286)) : (¬ p3286) ∨ (¬ p3292) := by
  classical
  tauto

theorem initial10716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3292)) := by
  have source := ElevenTheory.theory2260 (m.theta 0 3) (m.theta 3 9)
  exact rule10716 (meaning t m 3286) (meaning t m 3292) source

theorem rule10717 (p2027 p2210 p3583 p3954 p4875 : Prop) (h : (¬ p2210) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p4875)) : (p2027) ∨ (¬ p2210) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4875) := by
  classical
  tauto

theorem initial10717 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4875)) := by
  have source := ElevenTheory.theory2261 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 5) (m.theta 2 5)
  exact rule10717 (meaning t m 2027) (meaning t m 2210) (meaning t m 3583) (meaning t m 3954) (meaning t m 4875) source

theorem rule10718 (p2027 p3631 p3767 p4322 p4402 p4914 p5295 : Prop) (h : (¬ p5295) ∨ (¬ p4402) ∨ (¬ p3631) ∨ (¬ p3767) ∨ p2027 ∨ (¬ p4322) ∨ (¬ p4914)) : (p2027) ∨ (¬ p3631) ∨ (¬ p3767) ∨ (¬ p4322) ∨ (¬ p4402) ∨ (¬ p4914) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial10718 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4402)) ∨ (¬ (meaning t m 4914)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory2262 t (m.theta 0 9) (m.theta 1 7) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9) (m.theta 9 10)
  exact rule10718 (meaning t m 2027) (meaning t m 3631) (meaning t m 3767) (meaning t m 4322) (meaning t m 4402) (meaning t m 4914) (meaning t m 5295) source

theorem rule10719 (p2027 p2685 p3246 p3297 p4035 p4280 p5295 : Prop) (h : (¬ p4280) ∨ (¬ p5295) ∨ (¬ p4035) ∨ (¬ p3246) ∨ (¬ p3297) ∨ p2027 ∨ (¬ p2685)) : (p2027) ∨ (¬ p2685) ∨ (¬ p3246) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4280) ∨ (¬ p5295) := by
  classical
  tauto

theorem initial10719 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3297)) ∨ (¬ (meaning t m 4035)) ∨ (¬ (meaning t m 4280)) ∨ (¬ (meaning t m 5295)) := by
  have source := ElevenTheory.theory2263 t (m.theta 0 9) (m.theta 2 3) (m.theta 3 7) (m.theta 3 9) (m.theta 5 7) (m.theta 7 9)
  exact rule10719 (meaning t m 2027) (meaning t m 2685) (meaning t m 3246) (meaning t m 3297) (meaning t m 4035) (meaning t m 4280) (meaning t m 5295) source

theorem rule10720 (p2027 p2311 p2891 p3246 p3821 p4198 p4522 : Prop) (h : p2027 ∨ (¬ p4198) ∨ (¬ p4522) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p2311) ∨ (¬ p3821)) : (p2027) ∨ (¬ p2311) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4198) ∨ (¬ p4522) := by
  classical
  tauto

theorem initial10720 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4198)) ∨ (¬ (meaning t m 4522)) := by
  have source := ElevenTheory.theory2264 t (m.theta 0 5) (m.theta 0 6) (m.theta 0 7) (m.theta 1 5) (m.theta 5 7) (m.theta 7 9)
  exact rule10720 (meaning t m 2027) (meaning t m 2311) (meaning t m 2891) (meaning t m 3246) (meaning t m 3821) (meaning t m 4198) (meaning t m 4522) source

theorem rule10722 (p2027 p2619 p3544 p3554 p3969 p4875 p5693 : Prop) (h : (¬ p3544) ∨ (¬ p3554) ∨ (¬ p4875) ∨ (¬ p2619) ∨ (¬ p3969) ∨ (¬ p5693) ∨ p2027) : (p2027) ∨ (¬ p2619) ∨ (¬ p3544) ∨ (¬ p3554) ∨ (¬ p3969) ∨ (¬ p4875) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial10722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4875)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory2266 t (m.theta 1 5) (m.theta 1 7) (m.theta 1 8) (m.theta 2 5) (m.theta 5 8) (m.theta 8 10)
  exact rule10722 (meaning t m 2027) (meaning t m 2619) (meaning t m 3544) (meaning t m 3554) (meaning t m 3969) (meaning t m 4875) (meaning t m 5693) source

theorem rule10723 (p2027 p2619 p3146 p3661 p4118 p5053 : Prop) (h : p2027 ∨ (¬ p5053) ∨ (¬ p4118) ∨ (¬ p3146) ∨ (¬ p2619) ∨ (¬ p3661)) : (p2027) ∨ (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p5053) := by
  classical
  tauto

theorem initial10723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3661)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 5053)) := by
  have source := ElevenTheory.theory2267 t (m.theta 2 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule10723 (meaning t m 2027) (meaning t m 2619) (meaning t m 3146) (meaning t m 3661) (meaning t m 4118) (meaning t m 5053) source

theorem rule10724 (p2027 p2751 p2891 p2957 p3556 p4315 p4365 : Prop) (h : (¬ p2751) ∨ p2027 ∨ (¬ p4315) ∨ (¬ p3556) ∨ (¬ p2891) ∨ (¬ p4365) ∨ (¬ p2957)) : (p2027) ∨ (¬ p2751) ∨ (¬ p2891) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4315) ∨ (¬ p4365) := by
  classical
  tauto

theorem initial10724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4365)) := by
  have source := ElevenTheory.theory2268 t (m.theta 0 5) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7)
  exact rule10724 (meaning t m 2027) (meaning t m 2751) (meaning t m 2891) (meaning t m 2957) (meaning t m 3556) (meaning t m 4315) (meaning t m 4365) source

theorem rule10726 (p2027 p2145 p2177 p2651 p2685 p2810 p3570 p3646 p4117 p4204 p4570 : Prop) (h : (¬ p2685) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p2177) ∨ (¬ p4570) ∨ (¬ p2145) ∨ (¬ p4204) ∨ (¬ p3646) ∨ (¬ p2810) ∨ (¬ p2651) ∨ (¬ p4117)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3570) ∨ (¬ p3646) ∨ (¬ p4117) ∨ (¬ p4204) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial10726 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory2270 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 7) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10726 (meaning t m 2027) (meaning t m 2145) (meaning t m 2177) (meaning t m 2651) (meaning t m 2685) (meaning t m 2810) (meaning t m 3570) (meaning t m 3646) (meaning t m 4117) (meaning t m 4204) (meaning t m 4570) source

theorem rule10727 (p2027 p2881 p2933 p3544 p3941 p4277 p5693 : Prop) (h : (¬ p5693) ∨ (¬ p3544) ∨ (¬ p2933) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p4277) ∨ (¬ p3941)) : (p2027) ∨ (¬ p2881) ∨ (¬ p2933) ∨ (¬ p3544) ∨ (¬ p3941) ∨ (¬ p4277) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial10727 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3544)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory2271 t (m.theta 1 7) (m.theta 1 8) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10)
  exact rule10727 (meaning t m 2027) (meaning t m 2881) (meaning t m 2933) (meaning t m 3544) (meaning t m 3941) (meaning t m 4277) (meaning t m 5693) source

theorem rule10728 (p2027 p3097 p3737 p4276 p5475 p5503 : Prop) (h : (¬ p4276) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3737) ∨ (¬ p5475) ∨ (¬ p5503)) : (p2027) ∨ (¬ p3097) ∨ (¬ p3737) ∨ (¬ p4276) ∨ (¬ p5475) ∨ (¬ p5503) := by
  classical
  tauto

theorem initial10728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 5475)) ∨ (¬ (meaning t m 5503)) := by
  have source := ElevenTheory.theory2272 t (m.theta 4 7) (m.theta 5 6) (m.theta 6 10) (m.theta 6 7) (m.theta 7 10)
  exact rule10728 (meaning t m 2027) (meaning t m 3097) (meaning t m 3737) (meaning t m 4276) (meaning t m 5475) (meaning t m 5503) source

theorem rule10731 (p2027 p2387 p2619 p3758 p4441 p4486 : Prop) (h : (¬ p2387) ∨ p2027 ∨ (¬ p4486) ∨ (¬ p4441) ∨ (¬ p3758) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2619) ∨ (¬ p3758) ∨ (¬ p4441) ∨ (¬ p4486) := by
  classical
  tauto

theorem initial10731 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4486)) := by
  have source := ElevenTheory.theory2275 t (m.theta 0 6) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule10731 (meaning t m 2027) (meaning t m 2387) (meaning t m 2619) (meaning t m 3758) (meaning t m 4441) (meaning t m 4486) source

theorem rule10735 (p4149 p4286 : Prop) (h : (¬ p4286) ∨ (¬ p4149)) : (¬ p4149) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial10735 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory2279 (m.theta 4 8) (m.theta 8 10)
  exact rule10735 (meaning t m 4149) (meaning t m 4286) source

theorem rule10737 (p2027 p2210 p2247 p4282 p4360 p5062 : Prop) (h : (¬ p4282) ∨ (¬ p2247) ∨ (¬ p4360) ∨ p2027 ∨ (¬ p5062) ∨ (¬ p2210)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4282) ∨ (¬ p4360) ∨ (¬ p5062) := by
  classical
  tauto

theorem initial10737 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5062)) := by
  have source := ElevenTheory.theory2281 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8)
  exact rule10737 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 4282) (meaning t m 4360) (meaning t m 5062) source

theorem rule10739 (p2027 p3347 p3434 p3540 p4278 p5085 p5214 : Prop) (h : (¬ p3540) ∨ (¬ p5085) ∨ (¬ p5214) ∨ p2027 ∨ (¬ p3347) ∨ (¬ p4278) ∨ (¬ p3434)) : (p2027) ∨ (¬ p3347) ∨ (¬ p3434) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p5085) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial10739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 5085)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory2283 t (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7) (m.theta 7 9)
  exact rule10739 (meaning t m 2027) (meaning t m 3347) (meaning t m 3434) (meaning t m 3540) (meaning t m 4278) (meaning t m 5085) (meaning t m 5214) source

theorem rule10740 (p4172 p4984 p5206 : Prop) (h : (¬ p4172) ∨ p4984 ∨ (¬ p5206)) : (¬ p4172) ∨ (p4984) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial10740 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4172)) ∨ (meaning t m 4984) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory2284 (m.theta 0 1) (m.theta 0 5) (m.theta 0 7)
  exact rule10740 (meaning t m 4172) (meaning t m 4984) (meaning t m 5206) source

theorem rule10741 (p2027 p2145 p2177 p2437 p2630 p2696 p3556 p3570 p4276 : Prop) (h : p2027 ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2145) ∨ (¬ p2696) ∨ (¬ p3570) ∨ (¬ p3556) ∨ (¬ p4276) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2177) ∨ (¬ p2437) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4276) := by
  classical
  tauto

theorem initial10741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4276)) := by
  have source := ElevenTheory.theory2285 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule10741 (meaning t m 2027) (meaning t m 2145) (meaning t m 2177) (meaning t m 2437) (meaning t m 2630) (meaning t m 2696) (meaning t m 3556) (meaning t m 3570) (meaning t m 4276) source

end SunPrize.SMT
