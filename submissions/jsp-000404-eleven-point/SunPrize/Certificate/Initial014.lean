import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory005
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule9054 (p2608 p3954 : Prop) (h : (¬ p3954) ∨ (¬ p2608)) : (¬ p2608) ∨ (¬ p3954) := by
  classical
  tauto

theorem initial9054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3954)) := by
  have source := ElevenTheory.theory1304 (m.theta 0 1) (m.theta 1 2)
  exact rule9054 (meaning t m 2608) (meaning t m 3954) source

theorem rule9055 (p2027 p2299 p2319 p2341 p2586 p2588 : Prop) (h : p2027 ∨ (¬ p2586) ∨ (¬ p2341) ∨ (¬ p2299) ∨ (¬ p2588) ∨ (¬ p2319)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2586) ∨ (¬ p2588) := by
  classical
  tauto

theorem initial9055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 2588)) := by
  have source := ElevenTheory.theory1305 t (m.theta 0 6) (m.theta 0 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule9055 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 2586) (meaning t m 2588) source

theorem rule9056 (p2027 p3367 p3389 p3588 p4106 p4730 : Prop) (h : (¬ p4106) ∨ (¬ p3367) ∨ (¬ p3588) ∨ p2027 ∨ (¬ p3389) ∨ (¬ p4730)) : (p2027) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4106)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1306 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 4 7)
  exact rule9056 (meaning t m 2027) (meaning t m 3367) (meaning t m 3389) (meaning t m 3588) (meaning t m 4106) (meaning t m 4730) source

theorem rule9057 (p2027 p2493 p2630 p4195 p4389 p4814 : Prop) (h : (¬ p4389) ∨ (¬ p4814) ∨ (¬ p4195) ∨ (¬ p2630) ∨ p2027 ∨ (¬ p2493)) : (p2027) ∨ (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial9057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory1307 t (m.theta 1 4) (m.theta 2 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule9057 (meaning t m 2027) (meaning t m 2493) (meaning t m 2630) (meaning t m 4195) (meaning t m 4389) (meaning t m 4814) source

theorem rule9058 (p2027 p2470 p2509 p3954 p4079 p5216 : Prop) (h : (¬ p4079) ∨ (¬ p5216) ∨ (¬ p2470) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2509)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial9058 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory1308 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 8)
  exact rule9058 (meaning t m 2027) (meaning t m 2470) (meaning t m 2509) (meaning t m 3954) (meaning t m 4079) (meaning t m 5216) source

theorem rule9059 (p4242 p4353 p4436 p5312 p5313 : Prop) : (p4436) ∨ (¬ (p4436 ∧ p4353 ∧ p4242 ∧ p5312 ∧ p5313)) := by
  classical
  tauto

theorem initial9059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4436) ∨ (¬ (meaning t m 5311)) := by
  exact rule9059 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule9061 (p4242 p4353 p4436 p5312 p5313 : Prop) : (p4242) ∨ (¬ (p4436 ∧ p4353 ∧ p4242 ∧ p5312 ∧ p5313)) := by
  classical
  tauto

theorem initial9061 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4242) ∨ (¬ (meaning t m 5311)) := by
  exact rule9061 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule9063 (p4242 p4353 p4436 p5312 p5313 : Prop) : (¬ (p4436 ∧ p4353 ∧ p4242 ∧ p5312 ∧ p5313)) ∨ (p5313) := by
  classical
  tauto

theorem initial9063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5311)) ∨ (meaning t m 5313) := by
  exact rule9063 (meaning t m 4242) (meaning t m 4353) (meaning t m 4436) (meaning t m 5312) (meaning t m 5313)

theorem rule9065 (p3537 p5315 p5316 p5317 p5318 : Prop) : (¬ (p5315 ∧ p5316 ∧ p3537 ∧ p5317 ∧ p5318)) ∨ (p5315) := by
  classical
  tauto

theorem initial9065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5314)) ∨ (meaning t m 5315) := by
  exact rule9065 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule9066 (p3537 p5315 p5316 p5317 p5318 : Prop) : (¬ (p5315 ∧ p5316 ∧ p3537 ∧ p5317 ∧ p5318)) ∨ (p5316) := by
  classical
  tauto

theorem initial9066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5314)) ∨ (meaning t m 5316) := by
  exact rule9066 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule9067 (p3537 p5315 p5316 p5317 p5318 : Prop) : (p3537) ∨ (¬ (p5315 ∧ p5316 ∧ p3537 ∧ p5317 ∧ p5318)) := by
  classical
  tauto

theorem initial9067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3537) ∨ (¬ (meaning t m 5314)) := by
  exact rule9067 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule9068 (p3537 p5315 p5316 p5317 p5318 : Prop) : (¬ (p5315 ∧ p5316 ∧ p3537 ∧ p5317 ∧ p5318)) ∨ (p5317) := by
  classical
  tauto

theorem initial9068 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5314)) ∨ (meaning t m 5317) := by
  exact rule9068 (meaning t m 3537) (meaning t m 5315) (meaning t m 5316) (meaning t m 5317) (meaning t m 5318)

theorem rule9073 (p5311 p5314 : Prop) : (¬ (p5311 ∨ p5314)) ∨ (p5311) ∨ (p5314) := by
  classical
  tauto

theorem initial9073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5310)) ∨ (meaning t m 5311) ∨ (meaning t m 5314) := by
  exact rule9073 (meaning t m 5311) (meaning t m 5314)

theorem rule9074 (p3531 p5310 : Prop) (h : (p3531 ↔ p5310)) : (¬ p3531) ∨ (p5310) := by
  classical
  tauto

theorem initial9074 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3531)) ∨ (meaning t m 5310) := by
  have source := ElevenTheory.theory1309 t (m.theta 1 2) (m.theta 1 8) (m.theta 2 8)
  exact rule9074 (meaning t m 3531) (meaning t m 5310) source

theorem rule9076 (p2027 p2247 p3379 p3487 p4154 p4972 : Prop) (h : (¬ p3487) ∨ (¬ p3379) ∨ (¬ p4154) ∨ p2027 ∨ (¬ p4972) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4154) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial9076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory1310 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6)
  exact rule9076 (meaning t m 2027) (meaning t m 2247) (meaning t m 3379) (meaning t m 3487) (meaning t m 4154) (meaning t m 4972) source

theorem rule9077 (p2027 p2245 p2749 p3172 p3189 p3379 p5216 : Prop) (h : (¬ p3379) ∨ p2027 ∨ (¬ p5216) ∨ (¬ p3172) ∨ (¬ p2245) ∨ (¬ p3189) ∨ (¬ p2749)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2749) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3379) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial9077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory1311 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8)
  exact rule9077 (meaning t m 2027) (meaning t m 2245) (meaning t m 2749) (meaning t m 3172) (meaning t m 3189) (meaning t m 3379) (meaning t m 5216) source

theorem rule9078 (p2027 p2146 p2881 p3051 p3659 p4136 : Prop) (h : (¬ p4136) ∨ p2027 ∨ (¬ p2881) ∨ (¬ p3659) ∨ (¬ p3051) ∨ (¬ p2146)) : (p2027) ∨ (¬ p2146) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3659) ∨ (¬ p4136) := by
  classical
  tauto

theorem initial9078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4136)) := by
  have source := ElevenTheory.theory1312 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 7) (m.theta 7 8)
  exact rule9078 (meaning t m 2027) (meaning t m 2146) (meaning t m 2881) (meaning t m 3051) (meaning t m 3659) (meaning t m 4136) source

theorem rule9079 (p2027 p2651 p2850 p2952 p3879 p4753 : Prop) (h : p2027 ∨ (¬ p4753) ∨ (¬ p2952) ∨ (¬ p2651) ∨ (¬ p3879) ∨ (¬ p2850)) : (p2027) ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial9079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory1313 t (m.theta 0 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule9079 (meaning t m 2027) (meaning t m 2651) (meaning t m 2850) (meaning t m 2952) (meaning t m 3879) (meaning t m 4753) source

theorem rule9080 (p2696 p3365 : Prop) (h : (¬ p3365) ∨ (¬ p2696)) : (¬ p2696) ∨ (¬ p3365) := by
  classical
  tauto

theorem initial9080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3365)) := by
  have source := ElevenTheory.theory1314 (m.theta 0 2) (m.theta 2 3)
  exact rule9080 (meaning t m 2696) (meaning t m 3365) source

theorem rule9081 (p2027 p2341 p2685 p2745 p3031 p3548 p4066 : Prop) (h : p2027 ∨ (¬ p4066) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p2341)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial9081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3031)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory1315 t (m.theta 0 7) (m.theta 1 3) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 7 8)
  exact rule9081 (meaning t m 2027) (meaning t m 2341) (meaning t m 2685) (meaning t m 2745) (meaning t m 3031) (meaning t m 3548) (meaning t m 4066) source

theorem rule9082 (p2027 p2299 p2319 p2341 p3549 p5022 : Prop) (h : (¬ p2319) ∨ (¬ p2299) ∨ (¬ p5022) ∨ (¬ p2341) ∨ (¬ p3549) ∨ p2027) : (p2027) ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3549) ∨ (¬ p5022) := by
  classical
  tauto

theorem initial9082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5022)) := by
  have source := ElevenTheory.theory1316 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 6) (m.theta 6 7) (m.theta 7 8)
  exact rule9082 (meaning t m 2027) (meaning t m 2299) (meaning t m 2319) (meaning t m 2341) (meaning t m 3549) (meaning t m 5022) source

theorem rule9085 (p2027 p2668 p3548 p3550 p3568 p5142 : Prop) (h : p2027 ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p3548) ∨ (¬ p2668) ∨ (¬ p5142)) : (p2027) ∨ (¬ p2668) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p5142) := by
  classical
  tauto

theorem initial9085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 5142)) := by
  have source := ElevenTheory.theory1319 t (m.theta 1 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule9085 (meaning t m 2027) (meaning t m 2668) (meaning t m 3548) (meaning t m 3550) (meaning t m 3568) (meaning t m 5142) source

theorem rule9086 (p2027 p2427 p2881 p3548 p3554 p4629 : Prop) (h : (¬ p2427) ∨ p2027 ∨ (¬ p3554) ∨ (¬ p3548) ∨ (¬ p2881) ∨ (¬ p4629)) : (p2027) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial9086 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory1320 t (m.theta 1 5) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule9086 (meaning t m 2027) (meaning t m 2427) (meaning t m 2881) (meaning t m 3548) (meaning t m 3554) (meaning t m 4629) source

theorem rule9087 (p2027 p2192 p2881 p3548 p3554 p4555 : Prop) (h : p2027 ∨ (¬ p4555) ∨ (¬ p2192) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p2881)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial9087 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3554)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1321 t (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule9087 (meaning t m 2027) (meaning t m 2192) (meaning t m 2881) (meaning t m 3548) (meaning t m 3554) (meaning t m 4555) source

theorem rule9088 (p2027 p2187 p3097 p3548 p3550 p5142 : Prop) (h : (¬ p2187) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p5142) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p5142) := by
  classical
  tauto

theorem initial9088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 5142)) := by
  have source := ElevenTheory.theory1322 t (m.theta 1 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule9088 (meaning t m 2027) (meaning t m 2187) (meaning t m 3097) (meaning t m 3548) (meaning t m 3550) (meaning t m 5142) source

theorem rule9089 (p2027 p2933 p3238 p3399 p3452 p4646 : Prop) (h : (¬ p2933) ∨ (¬ p3399) ∨ p2027 ∨ (¬ p3452) ∨ (¬ p3238) ∨ (¬ p4646)) : (p2027) ∨ (¬ p2933) ∨ (¬ p3238) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial9089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2933)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory1323 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 7) (m.theta 4 5) (m.theta 4 7)
  exact rule9089 (meaning t m 2027) (meaning t m 2933) (meaning t m 3238) (meaning t m 3399) (meaning t m 3452) (meaning t m 4646) source

theorem rule9091 (p2027 p2341 p2459 p3692 p4119 p4990 : Prop) (h : (¬ p4990) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2341) ∨ (¬ p4119) ∨ (¬ p3692)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4990) := by
  classical
  tauto

theorem initial9091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4119)) ∨ (¬ (meaning t m 4990)) := by
  have source := ElevenTheory.theory1325 t (m.theta 0 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9091 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 3692) (meaning t m 4119) (meaning t m 4990) source

theorem rule9093 (p2027 p2352 p2459 p4133 p4137 p4171 : Prop) (h : (¬ p4171) ∨ (¬ p2459) ∨ (¬ p4133) ∨ p2027 ∨ (¬ p4137) ∨ (¬ p2352)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4137) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial9093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory1327 t (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule9093 (meaning t m 2027) (meaning t m 2352) (meaning t m 2459) (meaning t m 4133) (meaning t m 4137) (meaning t m 4171) source

theorem rule9094 (p2027 p3105 p3238 p3582 p4948 p5214 : Prop) (h : (¬ p5214) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3105) ∨ (¬ p3582) ∨ (¬ p4948)) : (p2027) ∨ (¬ p3105) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4948) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial9094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory1328 t (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 9)
  exact rule9094 (meaning t m 2027) (meaning t m 3105) (meaning t m 3238) (meaning t m 3582) (meaning t m 4948) (meaning t m 5214) source

theorem rule9095 (p2598 p3055 : Prop) (h : (¬ p3055) ∨ (¬ p2598)) : (¬ p2598) ∨ (¬ p3055) := by
  classical
  tauto

theorem initial9095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3055)) := by
  have source := ElevenTheory.theory1329 (m.theta 0 2) (m.theta 2 4)
  exact rule9095 (meaning t m 2598) (meaning t m 3055) source

theorem rule9096 (p2807 p3414 : Prop) (h : (¬ p3414) ∨ (¬ p2807)) : (¬ p2807) ∨ (¬ p3414) := by
  classical
  tauto

theorem initial9096 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3414)) := by
  have source := ElevenTheory.theory1330 (m.theta 0 3) (m.theta 3 7)
  exact rule9096 (meaning t m 2807) (meaning t m 3414) source

theorem rule9098 (p2230 p2589 : Prop) (h : (¬ p2589) ∨ (¬ p2230)) : (¬ p2230) ∨ (¬ p2589) := by
  classical
  tauto

theorem initial9098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2589)) := by
  have source := ElevenTheory.theory1332 (m.theta 0 4) (m.theta 4 5)
  exact rule9098 (meaning t m 2230) (meaning t m 2589) source

theorem rule9099 (p2027 p2437 p2911 p2926 p3548 p4811 : Prop) (h : (¬ p2911) ∨ p2027 ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4811) ∨ (¬ p2437)) : (p2027) ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2926)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1333 t (m.theta 1 4) (m.theta 1 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule9099 (meaning t m 2027) (meaning t m 2437) (meaning t m 2911) (meaning t m 2926) (meaning t m 3548) (meaning t m 4811) source

theorem rule9100 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p3746) ∨ (¬ (p3746 ∧ p4022 ∧ p4137 ∧ p5321 ∧ p5322)) := by
  classical
  tauto

theorem initial9100 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3746) ∨ (¬ (meaning t m 5320)) := by
  exact rule9100 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule9101 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p4022) ∨ (¬ (p3746 ∧ p4022 ∧ p4137 ∧ p5321 ∧ p5322)) := by
  classical
  tauto

theorem initial9101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4022) ∨ (¬ (meaning t m 5320)) := by
  exact rule9101 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule9102 (p3746 p4022 p4137 p5321 p5322 : Prop) : (p4137) ∨ (¬ (p3746 ∧ p4022 ∧ p4137 ∧ p5321 ∧ p5322)) := by
  classical
  tauto

theorem initial9102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4137) ∨ (¬ (meaning t m 5320)) := by
  exact rule9102 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule9103 (p3746 p4022 p4137 p5321 p5322 : Prop) : (¬ (p3746 ∧ p4022 ∧ p4137 ∧ p5321 ∧ p5322)) ∨ (p5321) := by
  classical
  tauto

theorem initial9103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5320)) ∨ (meaning t m 5321) := by
  exact rule9103 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule9104 (p3746 p4022 p4137 p5321 p5322 : Prop) : (¬ (p3746 ∧ p4022 ∧ p4137 ∧ p5321 ∧ p5322)) ∨ (p5322) := by
  classical
  tauto

theorem initial9104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5320)) ∨ (meaning t m 5322) := by
  exact rule9104 (meaning t m 3746) (meaning t m 4022) (meaning t m 4137) (meaning t m 5321) (meaning t m 5322)

theorem rule9106 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p4331) ∨ (¬ (p4331 ∧ p4422 ∧ p3564 ∧ p5324 ∧ p5325)) := by
  classical
  tauto

theorem initial9106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4331) ∨ (¬ (meaning t m 5323)) := by
  exact rule9106 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule9107 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p4422) ∨ (¬ (p4331 ∧ p4422 ∧ p3564 ∧ p5324 ∧ p5325)) := by
  classical
  tauto

theorem initial9107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4422) ∨ (¬ (meaning t m 5323)) := by
  exact rule9107 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule9108 (p3564 p4331 p4422 p5324 p5325 : Prop) : (p3564) ∨ (¬ (p4331 ∧ p4422 ∧ p3564 ∧ p5324 ∧ p5325)) := by
  classical
  tauto

theorem initial9108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3564) ∨ (¬ (meaning t m 5323)) := by
  exact rule9108 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule9109 (p3564 p4331 p4422 p5324 p5325 : Prop) : (¬ (p4331 ∧ p4422 ∧ p3564 ∧ p5324 ∧ p5325)) ∨ (p5324) := by
  classical
  tauto

theorem initial9109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5323)) ∨ (meaning t m 5324) := by
  exact rule9109 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule9110 (p3564 p4331 p4422 p5324 p5325 : Prop) : (¬ (p4331 ∧ p4422 ∧ p3564 ∧ p5324 ∧ p5325)) ∨ (p5325) := by
  classical
  tauto

theorem initial9110 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5323)) ∨ (meaning t m 5325) := by
  exact rule9110 (meaning t m 3564) (meaning t m 4331) (meaning t m 4422) (meaning t m 5324) (meaning t m 5325)

theorem rule9114 (p5320 p5323 : Prop) : (¬ (p5320 ∨ p5323)) ∨ (p5320) ∨ (p5323) := by
  classical
  tauto

theorem initial9114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5319)) ∨ (meaning t m 5320) ∨ (meaning t m 5323) := by
  exact rule9114 (meaning t m 5320) (meaning t m 5323)

theorem rule9115 (p3558 p5319 : Prop) (h : (p3558 ↔ p5319)) : (¬ p3558) ∨ (p5319) := by
  classical
  tauto

theorem initial9115 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3558)) ∨ (meaning t m 5319) := by
  have source := ElevenTheory.theory1334 t (m.theta 4 6) (m.theta 4 9) (m.theta 6 9)
  exact rule9115 (meaning t m 3558) (meaning t m 5319) source

theorem rule9117 (p2027 p2264 p3574 p3580 p3644 p4711 : Prop) (h : (¬ p2264) ∨ (¬ p4711) ∨ (¬ p3580) ∨ (¬ p3574) ∨ (¬ p3644) ∨ p2027) : (p2027) ∨ (¬ p2264) ∨ (¬ p3574) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p4711) := by
  classical
  tauto

theorem initial9117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4711)) := by
  have source := ElevenTheory.theory1335 t (m.theta 3 4) (m.theta 3 7) (m.theta 4 6) (m.theta 4 7) (m.theta 7 8)
  exact rule9117 (meaning t m 2027) (meaning t m 2264) (meaning t m 3574) (meaning t m 3580) (meaning t m 3644) (meaning t m 4711) source

theorem rule9119 (p2027 p3005 p3034 p3171 p3548 p3572 p4403 : Prop) (h : p2027 ∨ (¬ p3034) ∨ (¬ p4403) ∨ (¬ p3548) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3171)) : (p2027) ∨ (¬ p3005) ∨ (¬ p3034) ∨ (¬ p3171) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4403) := by
  classical
  tauto

theorem initial9119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3034)) ∨ (¬ (meaning t m 3171)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4403)) := by
  have source := ElevenTheory.theory1337 t (m.theta 0 8) (m.theta 1 7) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule9119 (meaning t m 2027) (meaning t m 3005) (meaning t m 3034) (meaning t m 3171) (meaning t m 3548) (meaning t m 3572) (meaning t m 4403) source

theorem rule9120 (p2027 p3034 p3166 p3414 p3548 p4378 : Prop) (h : (¬ p4378) ∨ (¬ p3166) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p3034) ∨ (¬ p3548)) : (p2027) ∨ (¬ p3034) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p4378) := by
  classical
  tauto

theorem initial9120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3034)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4378)) := by
  have source := ElevenTheory.theory1338 t (m.theta 0 3) (m.theta 1 7) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8)
  exact rule9120 (meaning t m 2027) (meaning t m 3034) (meaning t m 3166) (meaning t m 3414) (meaning t m 3548) (meaning t m 4378) source

theorem rule9121 (p2341 p3551 : Prop) (h : (¬ p3551) ∨ (¬ p2341)) : (¬ p2341) ∨ (¬ p3551) := by
  classical
  tauto

theorem initial9121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3551)) := by
  have source := ElevenTheory.theory1339 (m.theta 0 7) (m.theta 7 8)
  exact rule9121 (meaning t m 2341) (meaning t m 3551) source

theorem rule9122 (p2027 p2331 p2499 p2657 p3984 p4811 : Prop) (h : (¬ p2499) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p3984) ∨ (¬ p2657) ∨ (¬ p4811)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3984) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial9122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory1340 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule9122 (meaning t m 2027) (meaning t m 2331) (meaning t m 2499) (meaning t m 2657) (meaning t m 3984) (meaning t m 4811) source

theorem rule9123 (p2027 p2470 p2588 p2656 p3574 p4157 p4405 : Prop) (h : (¬ p4157) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p3574) ∨ (¬ p2588) ∨ (¬ p4405)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (¬ p3574) ∨ (¬ p4157) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial9123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4157)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory1341 t (m.theta 0 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7) (m.theta 6 8)
  exact rule9123 (meaning t m 2027) (meaning t m 2470) (meaning t m 2588) (meaning t m 2656) (meaning t m 3574) (meaning t m 4157) (meaning t m 4405) source

theorem rule9124 (p2027 p2177 p2307 p2586 p3581 p3644 : Prop) (h : (¬ p2586) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial9124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory1342 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule9124 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2586) (meaning t m 3581) (meaning t m 3644) source

theorem rule9125 (p2911 p3644 : Prop) (h : (¬ p3644) ∨ (¬ p2911)) : (¬ p2911) ∨ (¬ p3644) := by
  classical
  tauto

theorem initial9125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3644)) := by
  have source := ElevenTheory.theory1343 (m.theta 4 7) (m.theta 7 8)
  exact rule9125 (meaning t m 2911) (meaning t m 3644) source

theorem rule9126 (p2027 p2922 p3238 p3569 p3880 p4901 : Prop) (h : (¬ p3569) ∨ (¬ p4901) ∨ p2027 ∨ (¬ p3880) ∨ (¬ p3238) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p3880) ∨ (¬ p4901) := by
  classical
  tauto

theorem initial9126 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3569)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4901)) := by
  have source := ElevenTheory.theory1344 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8)
  exact rule9126 (meaning t m 2027) (meaning t m 2922) (meaning t m 3238) (meaning t m 3569) (meaning t m 3880) (meaning t m 4901) source

theorem rule9127 (p2027 p2341 p2427 p3880 p4132 p4990 : Prop) (h : (¬ p2341) ∨ (¬ p4132) ∨ (¬ p4990) ∨ (¬ p2427) ∨ (¬ p3880) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4990) := by
  classical
  tauto

theorem initial9127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4990)) := by
  have source := ElevenTheory.theory1345 t (m.theta 0 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule9127 (meaning t m 2027) (meaning t m 2341) (meaning t m 2427) (meaning t m 3880) (meaning t m 4132) (meaning t m 4990) source

theorem rule9128 (p2027 p2331 p2901 p2950 p3556 p4566 : Prop) (h : (¬ p2950) ∨ (¬ p3556) ∨ (¬ p2901) ∨ (¬ p4566) ∨ p2027 ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4566) := by
  classical
  tauto

theorem initial9128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4566)) := by
  have source := ElevenTheory.theory1346 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 7)
  exact rule9128 (meaning t m 2027) (meaning t m 2331) (meaning t m 2901) (meaning t m 2950) (meaning t m 3556) (meaning t m 4566) source

theorem rule9130 (p2027 p2641 p3497 p3662 p3986 p4507 : Prop) (h : (¬ p3986) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p4507) ∨ (¬ p3662) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2641) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial9130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory1348 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8)
  exact rule9130 (meaning t m 2027) (meaning t m 2641) (meaning t m 3497) (meaning t m 3662) (meaning t m 3986) (meaning t m 4507) source

theorem rule9131 (p2027 p2264 p2459 p2534 p4186 p4653 : Prop) (h : (¬ p4653) ∨ (¬ p2459) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2534) ∨ (¬ p4186)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p4653) := by
  classical
  tauto

theorem initial9131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 4653)) := by
  have source := ElevenTheory.theory1349 t (m.theta 3 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9131 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2534) (meaning t m 4186) (meaning t m 4653) source

theorem rule9132 (p2027 p2363 p3325 p3548 p4348 p5142 : Prop) (h : p2027 ∨ (¬ p4348) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p5142) ∨ (¬ p3548)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p5142) := by
  classical
  tauto

theorem initial9132 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3325)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5142)) := by
  have source := ElevenTheory.theory1350 t (m.theta 1 7) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9132 (meaning t m 2027) (meaning t m 2363) (meaning t m 3325) (meaning t m 3548) (meaning t m 4348) (meaning t m 5142) source

theorem rule9133 (p2027 p2717 p3471 p3548 p4400 p4737 : Prop) (h : (¬ p4400) ∨ (¬ p3471) ∨ (¬ p3548) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p4737)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3548) ∨ (¬ p4400) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial9133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4400)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory1351 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8)
  exact rule9133 (meaning t m 2027) (meaning t m 2717) (meaning t m 3471) (meaning t m 3548) (meaning t m 4400) (meaning t m 4737) source

theorem rule9135 (p2027 p2230 p3362 p3585 p3684 p4737 : Prop) (h : (¬ p3362) ∨ (¬ p3684) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p4737) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial9135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory1353 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5)
  exact rule9135 (meaning t m 2027) (meaning t m 2230) (meaning t m 3362) (meaning t m 3585) (meaning t m 3684) (meaning t m 4737) source

theorem rule9136 (p2027 p2230 p3367 p3583 p3698 p4730 : Prop) (h : p2027 ∨ (¬ p4730) ∨ (¬ p2230) ∨ (¬ p3583) ∨ (¬ p3367) ∨ (¬ p3698)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9136 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1354 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule9136 (meaning t m 2027) (meaning t m 2230) (meaning t m 3367) (meaning t m 3583) (meaning t m 3698) (meaning t m 4730) source

theorem rule9137 (p2027 p2749 p2952 p2992 p3361 p3585 p4749 : Prop) (h : (¬ p2952) ∨ (¬ p4749) ∨ (¬ p3361) ∨ p2027 ∨ (¬ p2749) ∨ (¬ p3585) ∨ (¬ p2992)) : (p2027) ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial9137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory1355 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5)
  exact rule9137 (meaning t m 2027) (meaning t m 2749) (meaning t m 2952) (meaning t m 2992) (meaning t m 3361) (meaning t m 3585) (meaning t m 4749) source

theorem rule9138 (p2341 p3553 p4066 : Prop) (h : (¬ p2341) ∨ (¬ p3553) ∨ (¬ p4066)) : (¬ p2341) ∨ (¬ p3553) ∨ (¬ p4066) := by
  classical
  tauto

theorem initial9138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4066)) := by
  have source := ElevenTheory.theory1356 (m.theta 0 7) (m.theta 3 7) (m.theta 7 8)
  exact rule9138 (meaning t m 2341) (meaning t m 3553) (meaning t m 4066) source

theorem rule9139 (p2027 p2341 p3644 p3876 p4730 p5201 : Prop) (h : (¬ p2341) ∨ (¬ p5201) ∨ (¬ p4730) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p3644)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4730) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial9139 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4730)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory1357 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 4) (m.theta 4 7) (m.theta 7 8)
  exact rule9139 (meaning t m 2027) (meaning t m 2341) (meaning t m 3644) (meaning t m 3876) (meaning t m 4730) (meaning t m 5201) source

theorem rule9140 (p2027 p2210 p2247 p2751 p4282 p4315 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p4282) ∨ (¬ p4315) ∨ (¬ p2210) ∨ (¬ p2751)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p4282) ∨ (¬ p4315) := by
  classical
  tauto

theorem initial9140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4315)) := by
  have source := ElevenTheory.theory1358 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 5)
  exact rule9140 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2751) (meaning t m 4282) (meaning t m 4315) source

theorem rule9141 (p2027 p2247 p2598 p2744 p3585 p3589 : Prop) (h : (¬ p2247) ∨ p2027 ∨ (¬ p2744) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2598) ∨ (¬ p2744) ∨ (¬ p3585) ∨ (¬ p3589) := by
  classical
  tauto

theorem initial9141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) := by
  have source := ElevenTheory.theory1359 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4)
  exact rule9141 (meaning t m 2027) (meaning t m 2247) (meaning t m 2598) (meaning t m 2744) (meaning t m 3585) (meaning t m 3589) source

theorem rule9142 (p2027 p2247 p2608 p2742 p3367 p4752 : Prop) (h : (¬ p4752) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3367)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p3367) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial9142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory1360 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4)
  exact rule9142 (meaning t m 2027) (meaning t m 2247) (meaning t m 2608) (meaning t m 2742) (meaning t m 3367) (meaning t m 4752) source

theorem rule9143 (p2027 p2132 p2630 p2657 p4236 p5052 : Prop) (h : (¬ p5052) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p5052) := by
  classical
  tauto

theorem initial9143 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 5052)) := by
  have source := ElevenTheory.theory1361 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4)
  exact rule9143 (meaning t m 2027) (meaning t m 2132) (meaning t m 2630) (meaning t m 2657) (meaning t m 4236) (meaning t m 5052) source

theorem rule9144 (p2839 p3583 : Prop) (h : (¬ p3583) ∨ (¬ p2839)) : (¬ p2839) ∨ (¬ p3583) := by
  classical
  tauto

theorem initial9144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3583)) := by
  have source := ElevenTheory.theory1362 (m.theta 1 2) (m.theta 2 5)
  exact rule9144 (meaning t m 2839) (meaning t m 3583) source

theorem rule9145 (p2132 p3365 p4392 : Prop) (h : (¬ p2132) ∨ (¬ p3365) ∨ (¬ p4392)) : (¬ p2132) ∨ (¬ p3365) ∨ (¬ p4392) := by
  classical
  tauto

theorem initial9145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4392)) := by
  have source := ElevenTheory.theory1363 (m.theta 0 2) (m.theta 2 3) (m.theta 2 5)
  exact rule9145 (meaning t m 2132) (meaning t m 3365) (meaning t m 4392) source

theorem rule9147 (p2027 p2598 p2850 p3238 p4257 p4737 : Prop) (h : (¬ p2850) ∨ (¬ p4257) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial9147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory1365 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule9147 (meaning t m 2027) (meaning t m 2598) (meaning t m 2850) (meaning t m 3238) (meaning t m 4257) (meaning t m 4737) source

theorem rule9148 (p2027 p2891 p3684 p3948 p4235 p5217 : Prop) (h : (¬ p5217) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3948) ∨ (¬ p3684) ∨ (¬ p2891)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3684) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5217) := by
  classical
  tauto

theorem initial9148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 5217)) := by
  have source := ElevenTheory.theory1366 t (m.theta 1 4) (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 5 7)
  exact rule9148 (meaning t m 2027) (meaning t m 2891) (meaning t m 3684) (meaning t m 3948) (meaning t m 4235) (meaning t m 5217) source

theorem rule9149 (p2027 p2829 p3583 p4185 p4385 p5043 : Prop) (h : p2027 ∨ (¬ p5043) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p2829) ∨ (¬ p4385)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p4385) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial9149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory1367 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 9)
  exact rule9149 (meaning t m 2027) (meaning t m 2829) (meaning t m 3583) (meaning t m 4185) (meaning t m 4385) (meaning t m 5043) source

theorem rule9150 (p2363 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p2363)) : (¬ p2363) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial9150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory1368 (m.theta 6 8) (m.theta 8 9)
  exact rule9150 (meaning t m 2363) (meaning t m 4347) source

theorem rule9152 (p3051 p3556 : Prop) (h : (¬ p3556) ∨ (¬ p3051)) : (¬ p3051) ∨ (¬ p3556) := by
  classical
  tauto

theorem initial9152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3556)) := by
  have source := ElevenTheory.theory1370 (m.theta 0 5) (m.theta 5 7)
  exact rule9152 (meaning t m 3051) (meaning t m 3556) source

theorem rule9153 (p2870 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p2870)) : (¬ p2870) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial9153 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory1371 (m.theta 2 5) (m.theta 5 7)
  exact rule9153 (meaning t m 2870) (meaning t m 4244) source

theorem rule9154 (p2707 p3588 : Prop) (h : (¬ p3588) ∨ (¬ p2707)) : (¬ p2707) ∨ (¬ p3588) := by
  classical
  tauto

theorem initial9154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3588)) := by
  have source := ElevenTheory.theory1372 (m.theta 1 2) (m.theta 2 7)
  exact rule9154 (meaning t m 2707) (meaning t m 3588) source

theorem rule9157 (p4029 p4379 p5328 p5329 p5330 : Prop) : (p4029) ∨ (¬ (p5328 ∧ p4029 ∧ p4379 ∧ p5329 ∧ p5330)) := by
  classical
  tauto

theorem initial9157 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4029) ∨ (¬ (meaning t m 5327)) := by
  exact rule9157 (meaning t m 4029) (meaning t m 4379) (meaning t m 5328) (meaning t m 5329) (meaning t m 5330)

theorem rule9158 (p4029 p4379 p5328 p5329 p5330 : Prop) : (p4379) ∨ (¬ (p5328 ∧ p4029 ∧ p4379 ∧ p5329 ∧ p5330)) := by
  classical
  tauto

theorem initial9158 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4379) ∨ (¬ (meaning t m 5327)) := by
  exact rule9158 (meaning t m 4029) (meaning t m 4379) (meaning t m 5328) (meaning t m 5329) (meaning t m 5330)

theorem rule9159 (p4029 p4379 p5328 p5329 p5330 : Prop) : (¬ (p5328 ∧ p4029 ∧ p4379 ∧ p5329 ∧ p5330)) ∨ (p5329) := by
  classical
  tauto

theorem initial9159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5327)) ∨ (meaning t m 5329) := by
  exact rule9159 (meaning t m 4029) (meaning t m 4379) (meaning t m 5328) (meaning t m 5329) (meaning t m 5330)

theorem rule9162 (p3599 p5332 p5333 p5334 p5335 : Prop) : (¬ (p5332 ∧ p5333 ∧ p3599 ∧ p5334 ∧ p5335)) ∨ (p5332) := by
  classical
  tauto

theorem initial9162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5331)) ∨ (meaning t m 5332) := by
  exact rule9162 (meaning t m 3599) (meaning t m 5332) (meaning t m 5333) (meaning t m 5334) (meaning t m 5335)

theorem rule9164 (p3599 p5332 p5333 p5334 p5335 : Prop) : (p3599) ∨ (¬ (p5332 ∧ p5333 ∧ p3599 ∧ p5334 ∧ p5335)) := by
  classical
  tauto

theorem initial9164 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3599) ∨ (¬ (meaning t m 5331)) := by
  exact rule9164 (meaning t m 3599) (meaning t m 5332) (meaning t m 5333) (meaning t m 5334) (meaning t m 5335)

theorem rule9170 (p5327 p5331 : Prop) : (¬ (p5327 ∨ p5331)) ∨ (p5327) ∨ (p5331) := by
  classical
  tauto

theorem initial9170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5326)) ∨ (meaning t m 5327) ∨ (meaning t m 5331) := by
  exact rule9170 (meaning t m 5327) (meaning t m 5331)

theorem rule9171 (p3593 p5326 : Prop) (h : (p3593 ↔ p5326)) : (¬ p3593) ∨ (p5326) := by
  classical
  tauto

theorem initial9171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3593)) ∨ (meaning t m 5326) := by
  have source := ElevenTheory.theory1374 t (m.theta 1 2) (m.theta 1 9) (m.theta 2 9)
  exact rule9171 (meaning t m 3593) (meaning t m 5326) source

theorem rule9173 (p4340 p5338 p5339 p5340 p5341 : Prop) : (¬ (p5338 ∧ p5339 ∧ p4340 ∧ p5340 ∧ p5341)) ∨ (p5338) := by
  classical
  tauto

theorem initial9173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5337)) ∨ (meaning t m 5338) := by
  exact rule9173 (meaning t m 4340) (meaning t m 5338) (meaning t m 5339) (meaning t m 5340) (meaning t m 5341)

theorem rule9174 (p4340 p5338 p5339 p5340 p5341 : Prop) : (¬ (p5338 ∧ p5339 ∧ p4340 ∧ p5340 ∧ p5341)) ∨ (p5339) := by
  classical
  tauto

theorem initial9174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5337)) ∨ (meaning t m 5339) := by
  exact rule9174 (meaning t m 4340) (meaning t m 5338) (meaning t m 5339) (meaning t m 5340) (meaning t m 5341)

theorem rule9175 (p4340 p5338 p5339 p5340 p5341 : Prop) : (p4340) ∨ (¬ (p5338 ∧ p5339 ∧ p4340 ∧ p5340 ∧ p5341)) := by
  classical
  tauto

theorem initial9175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4340) ∨ (¬ (meaning t m 5337)) := by
  exact rule9175 (meaning t m 4340) (meaning t m 5338) (meaning t m 5339) (meaning t m 5340) (meaning t m 5341)

theorem rule9179 (p3609 p5343 p5344 p5345 p5346 : Prop) : (¬ (p5343 ∧ p5344 ∧ p3609 ∧ p5345 ∧ p5346)) ∨ (p5343) := by
  classical
  tauto

theorem initial9179 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5342)) ∨ (meaning t m 5343) := by
  exact rule9179 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule9180 (p3609 p5343 p5344 p5345 p5346 : Prop) : (¬ (p5343 ∧ p5344 ∧ p3609 ∧ p5345 ∧ p5346)) ∨ (p5344) := by
  classical
  tauto

theorem initial9180 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5342)) ∨ (meaning t m 5344) := by
  exact rule9180 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule9181 (p3609 p5343 p5344 p5345 p5346 : Prop) : (p3609) ∨ (¬ (p5343 ∧ p5344 ∧ p3609 ∧ p5345 ∧ p5346)) := by
  classical
  tauto

theorem initial9181 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3609) ∨ (¬ (meaning t m 5342)) := by
  exact rule9181 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule9183 (p3609 p5343 p5344 p5345 p5346 : Prop) : (¬ (p5343 ∧ p5344 ∧ p3609 ∧ p5345 ∧ p5346)) ∨ (p5346) := by
  classical
  tauto

theorem initial9183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5342)) ∨ (meaning t m 5346) := by
  exact rule9183 (meaning t m 3609) (meaning t m 5343) (meaning t m 5344) (meaning t m 5345) (meaning t m 5346)

theorem rule9187 (p5337 p5342 : Prop) : (¬ (p5337 ∨ p5342)) ∨ (p5337) ∨ (p5342) := by
  classical
  tauto

theorem initial9187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5336)) ∨ (meaning t m 5337) ∨ (meaning t m 5342) := by
  exact rule9187 (meaning t m 5337) (meaning t m 5342)

theorem rule9188 (p3603 p5336 : Prop) (h : (p3603 ↔ p5336)) : (¬ p3603) ∨ (p5336) := by
  classical
  tauto

theorem initial9188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3603)) ∨ (meaning t m 5336) := by
  have source := ElevenTheory.theory1375 t (m.theta 2 8) (m.theta 2 9) (m.theta 8 9)
  exact rule9188 (meaning t m 3603) (meaning t m 5336) source

theorem rule9190 (p4232 p4234 p4398 p5349 p5350 : Prop) : (p4398) ∨ (¬ (p4398 ∧ p4234 ∧ p4232 ∧ p5349 ∧ p5350)) := by
  classical
  tauto

theorem initial9190 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4398) ∨ (¬ (meaning t m 5348)) := by
  exact rule9190 (meaning t m 4232) (meaning t m 4234) (meaning t m 4398) (meaning t m 5349) (meaning t m 5350)

theorem rule9191 (p4232 p4234 p4398 p5349 p5350 : Prop) : (p4234) ∨ (¬ (p4398 ∧ p4234 ∧ p4232 ∧ p5349 ∧ p5350)) := by
  classical
  tauto

theorem initial9191 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4234) ∨ (¬ (meaning t m 5348)) := by
  exact rule9191 (meaning t m 4232) (meaning t m 4234) (meaning t m 4398) (meaning t m 5349) (meaning t m 5350)

theorem rule9192 (p4232 p4234 p4398 p5349 p5350 : Prop) : (p4232) ∨ (¬ (p4398 ∧ p4234 ∧ p4232 ∧ p5349 ∧ p5350)) := by
  classical
  tauto

theorem initial9192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4232) ∨ (¬ (meaning t m 5348)) := by
  exact rule9192 (meaning t m 4232) (meaning t m 4234) (meaning t m 4398) (meaning t m 5349) (meaning t m 5350)

theorem rule9196 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p4233) ∨ (¬ (p4233 ∧ p5352 ∧ p3619 ∧ p5353 ∧ p5354)) := by
  classical
  tauto

theorem initial9196 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4233) ∨ (¬ (meaning t m 5351)) := by
  exact rule9196 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule9197 (p3619 p4233 p5352 p5353 p5354 : Prop) : (¬ (p4233 ∧ p5352 ∧ p3619 ∧ p5353 ∧ p5354)) ∨ (p5352) := by
  classical
  tauto

theorem initial9197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5351)) ∨ (meaning t m 5352) := by
  exact rule9197 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule9198 (p3619 p4233 p5352 p5353 p5354 : Prop) : (p3619) ∨ (¬ (p4233 ∧ p5352 ∧ p3619 ∧ p5353 ∧ p5354)) := by
  classical
  tauto

theorem initial9198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3619) ∨ (¬ (meaning t m 5351)) := by
  exact rule9198 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule9199 (p3619 p4233 p5352 p5353 p5354 : Prop) : (¬ (p4233 ∧ p5352 ∧ p3619 ∧ p5353 ∧ p5354)) ∨ (p5353) := by
  classical
  tauto

theorem initial9199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5351)) ∨ (meaning t m 5353) := by
  exact rule9199 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule9200 (p3619 p4233 p5352 p5353 p5354 : Prop) : (¬ (p4233 ∧ p5352 ∧ p3619 ∧ p5353 ∧ p5354)) ∨ (p5354) := by
  classical
  tauto

theorem initial9200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5351)) ∨ (meaning t m 5354) := by
  exact rule9200 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule9201 (p3619 p4233 p5352 p5353 p5354 : Prop) : (¬ p3619) ∨ (¬ p4233) ∨ ((p4233 ∧ p5352 ∧ p3619 ∧ p5353 ∧ p5354)) ∨ (¬ p5352) ∨ (¬ p5353) ∨ (¬ p5354) := by
  classical
  tauto

theorem initial9201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 4233)) ∨ (meaning t m 5351) ∨ (¬ (meaning t m 5352)) ∨ (¬ (meaning t m 5353)) ∨ (¬ (meaning t m 5354)) := by
  exact rule9201 (meaning t m 3619) (meaning t m 4233) (meaning t m 5352) (meaning t m 5353) (meaning t m 5354)

theorem rule9204 (p5348 p5351 : Prop) : (¬ (p5348 ∨ p5351)) ∨ (p5348) ∨ (p5351) := by
  classical
  tauto

theorem initial9204 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5347)) ∨ (meaning t m 5348) ∨ (meaning t m 5351) := by
  exact rule9204 (meaning t m 5348) (meaning t m 5351)

theorem rule9205 (p3613 p5347 : Prop) (h : (p3613 ↔ p5347)) : (¬ p3613) ∨ (p5347) := by
  classical
  tauto

theorem initial9205 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3613)) ∨ (meaning t m 5347) := by
  have source := ElevenTheory.theory1376 t (m.theta 0 2) (m.theta 0 9) (m.theta 2 9)
  exact rule9205 (meaning t m 3613) (meaning t m 5347) source

theorem rule9208 (p2027 p2254 p2608 p2707 p2963 p3324 p3434 p3950 p4347 : Prop) (h : (¬ p3324) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p4347) ∨ (¬ p2963) ∨ (¬ p2254) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial9208 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory1378 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule9208 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2963) (meaning t m 3324) (meaning t m 3434) (meaning t m 3950) (meaning t m 4347) source

theorem rule9209 (p3817 p5357 p5358 p5359 p5360 : Prop) : (¬ (p5357 ∧ p5358 ∧ p3817 ∧ p5359 ∧ p5360)) ∨ (p5357) := by
  classical
  tauto

theorem initial9209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5356)) ∨ (meaning t m 5357) := by
  exact rule9209 (meaning t m 3817) (meaning t m 5357) (meaning t m 5358) (meaning t m 5359) (meaning t m 5360)

theorem rule9210 (p3817 p5357 p5358 p5359 p5360 : Prop) : (¬ (p5357 ∧ p5358 ∧ p3817 ∧ p5359 ∧ p5360)) ∨ (p5358) := by
  classical
  tauto

theorem initial9210 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5356)) ∨ (meaning t m 5358) := by
  exact rule9210 (meaning t m 3817) (meaning t m 5357) (meaning t m 5358) (meaning t m 5359) (meaning t m 5360)

theorem rule9211 (p3817 p5357 p5358 p5359 p5360 : Prop) : (p3817) ∨ (¬ (p5357 ∧ p5358 ∧ p3817 ∧ p5359 ∧ p5360)) := by
  classical
  tauto

theorem initial9211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3817) ∨ (¬ (meaning t m 5356)) := by
  exact rule9211 (meaning t m 3817) (meaning t m 5357) (meaning t m 5358) (meaning t m 5359) (meaning t m 5360)

theorem rule9215 (p3631 p5362 p5363 p5364 p5365 : Prop) : (¬ (p5362 ∧ p5363 ∧ p3631 ∧ p5364 ∧ p5365)) ∨ (p5362) := by
  classical
  tauto

theorem initial9215 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5361)) ∨ (meaning t m 5362) := by
  exact rule9215 (meaning t m 3631) (meaning t m 5362) (meaning t m 5363) (meaning t m 5364) (meaning t m 5365)

theorem rule9216 (p3631 p5362 p5363 p5364 p5365 : Prop) : (¬ (p5362 ∧ p5363 ∧ p3631 ∧ p5364 ∧ p5365)) ∨ (p5363) := by
  classical
  tauto

theorem initial9216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5361)) ∨ (meaning t m 5363) := by
  exact rule9216 (meaning t m 3631) (meaning t m 5362) (meaning t m 5363) (meaning t m 5364) (meaning t m 5365)

theorem rule9217 (p3631 p5362 p5363 p5364 p5365 : Prop) : (p3631) ∨ (¬ (p5362 ∧ p5363 ∧ p3631 ∧ p5364 ∧ p5365)) := by
  classical
  tauto

theorem initial9217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3631) ∨ (¬ (meaning t m 5361)) := by
  exact rule9217 (meaning t m 3631) (meaning t m 5362) (meaning t m 5363) (meaning t m 5364) (meaning t m 5365)

theorem rule9223 (p5356 p5361 : Prop) : (¬ (p5356 ∨ p5361)) ∨ (p5356) ∨ (p5361) := by
  classical
  tauto

theorem initial9223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5355)) ∨ (meaning t m 5356) ∨ (meaning t m 5361) := by
  exact rule9223 (meaning t m 5356) (meaning t m 5361)

theorem rule9224 (p3625 p5355 : Prop) (h : (p3625 ↔ p5355)) : (¬ p3625) ∨ (p5355) := by
  classical
  tauto

theorem initial9224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3625)) ∨ (meaning t m 5355) := by
  have source := ElevenTheory.theory1379 t (m.theta 1 7) (m.theta 1 9) (m.theta 7 9)
  exact rule9224 (meaning t m 3625) (meaning t m 5355) source

theorem rule9226 (p2027 p2839 p3585 p3695 p3876 p4644 : Prop) (h : (¬ p2839) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p3695) ∨ (¬ p4644) ∨ (¬ p3585)) : (p2027) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p3876) ∨ (¬ p4644) := by
  classical
  tauto

theorem initial9226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4644)) := by
  have source := ElevenTheory.theory1380 t (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7)
  exact rule9226 (meaning t m 2027) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) (meaning t m 3876) (meaning t m 4644) source

theorem rule9227 (p2027 p2829 p2901 p3588 p4169 p4193 p4906 : Prop) (h : (¬ p4169) ∨ p2027 ∨ (¬ p2901) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4193) ∨ (¬ p4906)) : (p2027) ∨ (¬ p2829) ∨ (¬ p2901) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4193) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial9227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 4169)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory1381 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7)
  exact rule9227 (meaning t m 2027) (meaning t m 2829) (meaning t m 2901) (meaning t m 3588) (meaning t m 4169) (meaning t m 4193) (meaning t m 4906) source

theorem rule9228 (p2027 p2156 p2254 p2952 p3952 p4172 : Prop) (h : (¬ p3952) ∨ (¬ p4172) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p2254) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4172) := by
  classical
  tauto

theorem initial9228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4172)) := by
  have source := ElevenTheory.theory1382 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 3 5) (m.theta 5 6)
  exact rule9228 (meaning t m 2027) (meaning t m 2156) (meaning t m 2254) (meaning t m 2952) (meaning t m 3952) (meaning t m 4172) source

theorem rule9229 (p2027 p3093 p3555 p4110 p4516 p4632 : Prop) (h : p2027 ∨ (¬ p4632) ∨ (¬ p3555) ∨ (¬ p3093) ∨ (¬ p4516) ∨ (¬ p4110)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p4110) ∨ (¬ p4516) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial9229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory1383 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6)
  exact rule9229 (meaning t m 2027) (meaning t m 3093) (meaning t m 3555) (meaning t m 4110) (meaning t m 4516) (meaning t m 4632) source

theorem rule9230 (p2027 p3156 p3644 p4042 p4277 p4320 : Prop) (h : (¬ p4042) ∨ (¬ p4277) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3156) ∨ (¬ p3644)) : (p2027) ∨ (¬ p3156) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial9230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory1384 t (m.theta 3 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule9230 (meaning t m 2027) (meaning t m 3156) (meaning t m 3644) (meaning t m 4042) (meaning t m 4277) (meaning t m 4320) source

theorem rule9231 (p2027 p2341 p2459 p2534 p4186 p5203 : Prop) (h : (¬ p5203) ∨ (¬ p2534) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p4186)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p5203) := by
  classical
  tauto

theorem initial9231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 4186)) ∨ (¬ (meaning t m 5203)) := by
  have source := ElevenTheory.theory1385 t (m.theta 0 7) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9231 (meaning t m 2027) (meaning t m 2341) (meaning t m 2459) (meaning t m 2534) (meaning t m 4186) (meaning t m 5203) source

theorem rule9232 (p2027 p2341 p2707 p4242 p4800 p5261 : Prop) (h : (¬ p4800) ∨ (¬ p4242) ∨ (¬ p2341) ∨ (¬ p5261) ∨ (¬ p2707) ∨ p2027) : (p2027) ∨ (¬ p2341) ∨ (¬ p2707) ∨ (¬ p4242) ∨ (¬ p4800) ∨ (¬ p5261) := by
  classical
  tauto

theorem initial9232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4800)) ∨ (¬ (meaning t m 5261)) := by
  have source := ElevenTheory.theory1386 t (m.theta 0 7) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 7 8)
  exact rule9232 (meaning t m 2027) (meaning t m 2341) (meaning t m 2707) (meaning t m 4242) (meaning t m 4800) (meaning t m 5261) source

theorem rule9233 (p3874 p5368 p5369 p5370 p5371 : Prop) : (¬ (p5368 ∧ p5369 ∧ p3874 ∧ p5370 ∧ p5371)) ∨ (p5368) := by
  classical
  tauto

theorem initial9233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5367)) ∨ (meaning t m 5368) := by
  exact rule9233 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule9234 (p3874 p5368 p5369 p5370 p5371 : Prop) : (¬ (p5368 ∧ p5369 ∧ p3874 ∧ p5370 ∧ p5371)) ∨ (p5369) := by
  classical
  tauto

theorem initial9234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5367)) ∨ (meaning t m 5369) := by
  exact rule9234 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule9235 (p3874 p5368 p5369 p5370 p5371 : Prop) : (p3874) ∨ (¬ (p5368 ∧ p5369 ∧ p3874 ∧ p5370 ∧ p5371)) := by
  classical
  tauto

theorem initial9235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3874) ∨ (¬ (meaning t m 5367)) := by
  exact rule9235 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule9236 (p3874 p5368 p5369 p5370 p5371 : Prop) : (¬ (p5368 ∧ p5369 ∧ p3874 ∧ p5370 ∧ p5371)) ∨ (p5370) := by
  classical
  tauto

theorem initial9236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5367)) ∨ (meaning t m 5370) := by
  exact rule9236 (meaning t m 3874) (meaning t m 5368) (meaning t m 5369) (meaning t m 5370) (meaning t m 5371)

theorem rule9239 (p3641 p4354 p5373 p5374 p5375 : Prop) : (¬ (p5373 ∧ p4354 ∧ p3641 ∧ p5374 ∧ p5375)) ∨ (p5373) := by
  classical
  tauto

theorem initial9239 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5372)) ∨ (meaning t m 5373) := by
  exact rule9239 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule9240 (p3641 p4354 p5373 p5374 p5375 : Prop) : (p4354) ∨ (¬ (p5373 ∧ p4354 ∧ p3641 ∧ p5374 ∧ p5375)) := by
  classical
  tauto

theorem initial9240 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4354) ∨ (¬ (meaning t m 5372)) := by
  exact rule9240 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule9241 (p3641 p4354 p5373 p5374 p5375 : Prop) : (p3641) ∨ (¬ (p5373 ∧ p4354 ∧ p3641 ∧ p5374 ∧ p5375)) := by
  classical
  tauto

theorem initial9241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3641) ∨ (¬ (meaning t m 5372)) := by
  exact rule9241 (meaning t m 3641) (meaning t m 4354) (meaning t m 5373) (meaning t m 5374) (meaning t m 5375)

theorem rule9247 (p5367 p5372 : Prop) : (¬ (p5367 ∨ p5372)) ∨ (p5367) ∨ (p5372) := by
  classical
  tauto

theorem initial9247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5366)) ∨ (meaning t m 5367) ∨ (meaning t m 5372) := by
  exact rule9247 (meaning t m 5367) (meaning t m 5372)

theorem rule9248 (p3635 p5366 : Prop) (h : (p3635 ↔ p5366)) : (¬ p3635) ∨ (p5366) := by
  classical
  tauto

theorem initial9248 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3635)) ∨ (meaning t m 5366) := by
  have source := ElevenTheory.theory1387 t (m.theta 2 4) (m.theta 2 8) (m.theta 4 8)
  exact rule9248 (meaning t m 3635) (meaning t m 5366) source

theorem rule9250 (p2027 p2341 p3201 p3874 p4383 p5203 : Prop) (h : (¬ p2341) ∨ (¬ p5203) ∨ p2027 ∨ (¬ p3874) ∨ (¬ p4383) ∨ (¬ p3201)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p4383) ∨ (¬ p5203) := by
  classical
  tauto

theorem initial9250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5203)) := by
  have source := ElevenTheory.theory1388 t (m.theta 0 7) (m.theta 2 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8)
  exact rule9250 (meaning t m 2027) (meaning t m 2341) (meaning t m 3201) (meaning t m 3874) (meaning t m 4383) (meaning t m 5203) source

theorem rule9251 (p2027 p2341 p2952 p3037 p3548 p4104 p4919 : Prop) (h : (¬ p3548) ∨ (¬ p2341) ∨ p2027 ∨ (¬ p2952) ∨ (¬ p4104) ∨ (¬ p4919) ∨ (¬ p3037)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2952) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4919) := by
  classical
  tauto

theorem initial9251 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4104)) ∨ (¬ (meaning t m 4919)) := by
  have source := ElevenTheory.theory1389 t (m.theta 0 3) (m.theta 0 7) (m.theta 1 7) (m.theta 3 5) (m.theta 3 7) (m.theta 7 8)
  exact rule9251 (meaning t m 2027) (meaning t m 2341) (meaning t m 2952) (meaning t m 3037) (meaning t m 3548) (meaning t m 4104) (meaning t m 4919) source

theorem rule9252 (p2027 p2230 p2563 p3054 p4173 p4243 p4730 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p4730) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p4243) ∨ (¬ p4173)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9252 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4243)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1390 t (m.theta 0 4) (m.theta 1 5) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 6)
  exact rule9252 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 3054) (meaning t m 4173) (meaning t m 4243) (meaning t m 4730) source

theorem rule9253 (p3946 p5378 p5379 p5380 p5381 : Prop) : (¬ (p5378 ∧ p5379 ∧ p3946 ∧ p5380 ∧ p5381)) ∨ (p5378) := by
  classical
  tauto

theorem initial9253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5377)) ∨ (meaning t m 5378) := by
  exact rule9253 (meaning t m 3946) (meaning t m 5378) (meaning t m 5379) (meaning t m 5380) (meaning t m 5381)

theorem rule9254 (p3946 p5378 p5379 p5380 p5381 : Prop) : (¬ (p5378 ∧ p5379 ∧ p3946 ∧ p5380 ∧ p5381)) ∨ (p5379) := by
  classical
  tauto

theorem initial9254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5377)) ∨ (meaning t m 5379) := by
  exact rule9254 (meaning t m 3946) (meaning t m 5378) (meaning t m 5379) (meaning t m 5380) (meaning t m 5381)

theorem rule9255 (p3946 p5378 p5379 p5380 p5381 : Prop) : (p3946) ∨ (¬ (p5378 ∧ p5379 ∧ p3946 ∧ p5380 ∧ p5381)) := by
  classical
  tauto

theorem initial9255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3946) ∨ (¬ (meaning t m 5377)) := by
  exact rule9255 (meaning t m 3946) (meaning t m 5378) (meaning t m 5379) (meaning t m 5380) (meaning t m 5381)

theorem rule9259 (p3654 p4036 p4038 p5383 p5384 : Prop) : (p4038) ∨ (¬ (p4038 ∧ p4036 ∧ p3654 ∧ p5383 ∧ p5384)) := by
  classical
  tauto

theorem initial9259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4038) ∨ (¬ (meaning t m 5382)) := by
  exact rule9259 (meaning t m 3654) (meaning t m 4036) (meaning t m 4038) (meaning t m 5383) (meaning t m 5384)

theorem rule9260 (p3654 p4036 p4038 p5383 p5384 : Prop) : (p4036) ∨ (¬ (p4038 ∧ p4036 ∧ p3654 ∧ p5383 ∧ p5384)) := by
  classical
  tauto

theorem initial9260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4036) ∨ (¬ (meaning t m 5382)) := by
  exact rule9260 (meaning t m 3654) (meaning t m 4036) (meaning t m 4038) (meaning t m 5383) (meaning t m 5384)

theorem rule9261 (p3654 p4036 p4038 p5383 p5384 : Prop) : (p3654) ∨ (¬ (p4038 ∧ p4036 ∧ p3654 ∧ p5383 ∧ p5384)) := by
  classical
  tauto

theorem initial9261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3654) ∨ (¬ (meaning t m 5382)) := by
  exact rule9261 (meaning t m 3654) (meaning t m 4036) (meaning t m 4038) (meaning t m 5383) (meaning t m 5384)

theorem rule9267 (p5377 p5382 : Prop) : (¬ (p5377 ∨ p5382)) ∨ (p5377) ∨ (p5382) := by
  classical
  tauto

theorem initial9267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5376)) ∨ (meaning t m 5377) ∨ (meaning t m 5382) := by
  exact rule9267 (meaning t m 5377) (meaning t m 5382)

theorem rule9268 (p3648 p5376 : Prop) (h : (p3648 ↔ p5376)) : (¬ p3648) ∨ (p5376) := by
  classical
  tauto

theorem initial9268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3648)) ∨ (meaning t m 5376) := by
  have source := ElevenTheory.theory1391 t (m.theta 0 6) (m.theta 0 9) (m.theta 6 9)
  exact rule9268 (meaning t m 3648) (meaning t m 5376) source

theorem rule9270 (p2027 p2319 p2341 p3547 p3548 p3946 p4620 : Prop) (h : (¬ p2319) ∨ (¬ p4620) ∨ p2027 ∨ (¬ p3946) ∨ (¬ p3548) ∨ (¬ p2341) ∨ (¬ p3547)) : (p2027) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3547) ∨ (¬ p3548) ∨ (¬ p3946) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial9270 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2319)) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory1392 t (m.theta 0 6) (m.theta 0 7) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule9270 (meaning t m 2027) (meaning t m 2319) (meaning t m 2341) (meaning t m 3547) (meaning t m 3548) (meaning t m 3946) (meaning t m 4620) source

theorem rule9271 (p2027 p2573 p3367 p3688 p4342 p4730 : Prop) (h : (¬ p3688) ∨ (¬ p2573) ∨ p2027 ∨ (¬ p4730) ∨ (¬ p4342) ∨ (¬ p3367)) : (p2027) ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4342)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1393 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6)
  exact rule9271 (meaning t m 2027) (meaning t m 2573) (meaning t m 3367) (meaning t m 3688) (meaning t m 4342) (meaning t m 4730) source

theorem rule9272 (p2027 p2307 p2396 p2586 p3581 p4278 : Prop) (h : (¬ p3581) ∨ (¬ p4278) ∨ (¬ p2396) ∨ (¬ p2586) ∨ p2027 ∨ (¬ p2307)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p4278) := by
  classical
  tauto

theorem initial9272 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2586)) ∨ (¬ (meaning t m 3581)) ∨ (¬ (meaning t m 4278)) := by
  have source := ElevenTheory.theory1394 t (m.theta 0 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7) (m.theta 7 9)
  exact rule9272 (meaning t m 2027) (meaning t m 2307) (meaning t m 2396) (meaning t m 2586) (meaning t m 3581) (meaning t m 4278) source

theorem rule9274 (p2027 p3256 p3659 p3857 p4044 p4403 p4779 : Prop) (h : (¬ p3256) ∨ (¬ p4779) ∨ (¬ p4403) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p3857) ∨ (¬ p4044)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3659) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4403) ∨ (¬ p4779) := by
  classical
  tauto

theorem initial9274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4044)) ∨ (¬ (meaning t m 4403)) ∨ (¬ (meaning t m 4779)) := by
  have source := ElevenTheory.theory1396 t (m.theta 0 8) (m.theta 2 7) (m.theta 3 7) (m.theta 3 8) (m.theta 7 8) (m.theta 8 9)
  exact rule9274 (meaning t m 2027) (meaning t m 3256) (meaning t m 3659) (meaning t m 3857) (meaning t m 4044) (meaning t m 4403) (meaning t m 4779) source

theorem rule9275 (p2027 p2088 p3659 p4348 p4590 p5261 : Prop) (h : (¬ p4590) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p2088) ∨ p2027 ∨ (¬ p5261)) : (p2027) ∨ (¬ p2088) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p5261) := by
  classical
  tauto

theorem initial9275 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4590)) ∨ (¬ (meaning t m 5261)) := by
  have source := ElevenTheory.theory1397 t (m.theta 0 7) (m.theta 0 8) (m.theta 2 7) (m.theta 7 8) (m.theta 8 9)
  exact rule9275 (meaning t m 2027) (meaning t m 2088) (meaning t m 3659) (meaning t m 4348) (meaning t m 4590) (meaning t m 5261) source

theorem rule9276 (p2027 p2230 p2255 p2440 p2663 p4111 : Prop) (h : (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2440) ∨ (¬ p2255) ∨ p2027 ∨ (¬ p4111)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2255) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial9276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2255)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory1398 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 4 5)
  exact rule9276 (meaning t m 2027) (meaning t m 2230) (meaning t m 2255) (meaning t m 2440) (meaning t m 2663) (meaning t m 4111) source

theorem rule9277 (p2027 p2230 p2665 p2727 p3662 p3879 : Prop) (h : (¬ p2230) ∨ p2027 ∨ (¬ p2665) ∨ (¬ p3879) ∨ (¬ p3662) ∨ (¬ p2727)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) := by
  classical
  tauto

theorem initial9277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) := by
  have source := ElevenTheory.theory1399 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule9277 (meaning t m 2027) (meaning t m 2230) (meaning t m 2665) (meaning t m 2727) (meaning t m 3662) (meaning t m 3879) source

theorem rule9279 (p2027 p2284 p3189 p3368 p4173 p5065 : Prop) (h : (¬ p3189) ∨ (¬ p5065) ∨ p2027 ∨ (¬ p4173) ∨ (¬ p3368) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3189) ∨ (¬ p3368) ∨ (¬ p4173) ∨ (¬ p5065) := by
  classical
  tauto

theorem initial9279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 5065)) := by
  have source := ElevenTheory.theory1401 t (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 6)
  exact rule9279 (meaning t m 2027) (meaning t m 2284) (meaning t m 3189) (meaning t m 3368) (meaning t m 4173) (meaning t m 5065) source

theorem rule9280 (p2027 p2542 p2651 p3364 p3684 p4790 : Prop) (h : p2027 ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p4790)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial9280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory1402 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5)
  exact rule9280 (meaning t m 2027) (meaning t m 2542) (meaning t m 2651) (meaning t m 3364) (meaning t m 3684) (meaning t m 4790) source

theorem rule9281 (p2027 p2641 p3662 p3986 p4208 p5043 : Prop) (h : (¬ p4208) ∨ (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p5043) ∨ p2027) : (p2027) ∨ (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p5043) := by
  classical
  tauto

theorem initial9281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 5043)) := by
  have source := ElevenTheory.theory1403 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 5 9)
  exact rule9281 (meaning t m 2027) (meaning t m 2641) (meaning t m 3662) (meaning t m 3986) (meaning t m 4208) (meaning t m 5043) source

theorem rule9282 (p2027 p2177 p2553 p3548 p3576 p3689 p5222 : Prop) (h : (¬ p3689) ∨ p2027 ∨ (¬ p3576) ∨ (¬ p5222) ∨ (¬ p3548) ∨ (¬ p2553) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3689) ∨ (¬ p5222) := by
  classical
  tauto

theorem initial9282 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 5222)) := by
  have source := ElevenTheory.theory1404 t (m.theta 1 7) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule9282 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 3548) (meaning t m 3576) (meaning t m 3689) (meaning t m 5222) source

theorem rule9283 (p2027 p2284 p2946 p3758 p4392 p4790 : Prop) (h : (¬ p2946) ∨ (¬ p3758) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p4790) ∨ (¬ p4392)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4790) := by
  classical
  tauto

theorem initial9283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4790)) := by
  have source := ElevenTheory.theory1405 t (m.theta 0 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule9283 (meaning t m 2027) (meaning t m 2284) (meaning t m 2946) (meaning t m 3758) (meaning t m 4392) (meaning t m 4790) source

theorem rule9285 (p2027 p2352 p2588 p3037 p3548 p3550 p4570 : Prop) (h : (¬ p3037) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p2588) ∨ (¬ p4570)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial9285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3037)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory1407 t (m.theta 1 7) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule9285 (meaning t m 2027) (meaning t m 2352) (meaning t m 2588) (meaning t m 3037) (meaning t m 3548) (meaning t m 3550) (meaning t m 4570) source

theorem rule9286 (p2459 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p2459)) : (¬ p2459) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial9286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory1408 (m.theta 7 8) (m.theta 8 9)
  exact rule9286 (meaning t m 2459) (meaning t m 4348) source

theorem rule9287 (p2027 p3461 p4187 p4324 p4381 p4473 : Prop) (h : (¬ p4473) ∨ (¬ p4324) ∨ p2027 ∨ (¬ p4381) ∨ (¬ p4187) ∨ (¬ p3461)) : (p2027) ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial9287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory1409 t (m.theta 2 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9287 (meaning t m 2027) (meaning t m 3461) (meaning t m 4187) (meaning t m 4324) (meaning t m 4381) (meaning t m 4473) source

theorem rule9288 (p2027 p2911 p3434 p3659 p3947 p4327 : Prop) (h : (¬ p3434) ∨ (¬ p4327) ∨ (¬ p3659) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p2911)) : (p2027) ∨ (¬ p2911) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3947) ∨ (¬ p4327) := by
  classical
  tauto

theorem initial9288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4327)) := by
  have source := ElevenTheory.theory1410 t (m.theta 2 7) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8) (m.theta 7 9)
  exact rule9288 (meaning t m 2027) (meaning t m 2911) (meaning t m 3434) (meaning t m 3659) (meaning t m 3947) (meaning t m 4327) source

theorem rule9291 (p4027 p4028 p5387 p5388 p5389 : Prop) : (¬ (p4028 ∧ p4027 ∧ p5387 ∧ p5388 ∧ p5389)) ∨ (p5387) := by
  classical
  tauto

theorem initial9291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5386)) ∨ (meaning t m 5387) := by
  exact rule9291 (meaning t m 4027) (meaning t m 4028) (meaning t m 5387) (meaning t m 5388) (meaning t m 5389)

theorem rule9297 (p3670 p5391 p5392 p5393 p5394 : Prop) : (p3670) ∨ (¬ (p5391 ∧ p5392 ∧ p3670 ∧ p5393 ∧ p5394)) := by
  classical
  tauto

theorem initial9297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3670) ∨ (¬ (meaning t m 5390)) := by
  exact rule9297 (meaning t m 3670) (meaning t m 5391) (meaning t m 5392) (meaning t m 5393) (meaning t m 5394)

theorem rule9303 (p5386 p5390 : Prop) : (¬ (p5386 ∨ p5390)) ∨ (p5386) ∨ (p5390) := by
  classical
  tauto

theorem initial9303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5385)) ∨ (meaning t m 5386) ∨ (meaning t m 5390) := by
  exact rule9303 (meaning t m 5386) (meaning t m 5390)

theorem rule9304 (p3664 p5385 : Prop) (h : (p3664 ↔ p5385)) : (¬ p3664) ∨ (p5385) := by
  classical
  tauto

theorem initial9304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3664)) ∨ (meaning t m 5385) := by
  have source := ElevenTheory.theory1411 t (m.theta 2 10) (m.theta 2 9) (m.theta 9 10)
  exact rule9304 (meaning t m 3664) (meaning t m 5385) source

theorem rule9308 (p4322 p5397 p5398 p5399 p5400 : Prop) : (p4322) ∨ (¬ (p5397 ∧ p5398 ∧ p4322 ∧ p5399 ∧ p5400)) := by
  classical
  tauto

theorem initial9308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4322) ∨ (¬ (meaning t m 5396)) := by
  exact rule9308 (meaning t m 4322) (meaning t m 5397) (meaning t m 5398) (meaning t m 5399) (meaning t m 5400)

theorem rule9310 (p4322 p5397 p5398 p5399 p5400 : Prop) : (¬ (p5397 ∧ p5398 ∧ p4322 ∧ p5399 ∧ p5400)) ∨ (p5400) := by
  classical
  tauto

theorem initial9310 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5396)) ∨ (meaning t m 5400) := by
  exact rule9310 (meaning t m 4322) (meaning t m 5397) (meaning t m 5398) (meaning t m 5399) (meaning t m 5400)

theorem rule9312 (p3680 p5402 p5403 p5404 p5405 : Prop) : (¬ (p5402 ∧ p5403 ∧ p3680 ∧ p5404 ∧ p5405)) ∨ (p5402) := by
  classical
  tauto

theorem initial9312 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5401)) ∨ (meaning t m 5402) := by
  exact rule9312 (meaning t m 3680) (meaning t m 5402) (meaning t m 5403) (meaning t m 5404) (meaning t m 5405)

theorem rule9313 (p3680 p5402 p5403 p5404 p5405 : Prop) : (¬ (p5402 ∧ p5403 ∧ p3680 ∧ p5404 ∧ p5405)) ∨ (p5403) := by
  classical
  tauto

theorem initial9313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5401)) ∨ (meaning t m 5403) := by
  exact rule9313 (meaning t m 3680) (meaning t m 5402) (meaning t m 5403) (meaning t m 5404) (meaning t m 5405)

theorem rule9314 (p3680 p5402 p5403 p5404 p5405 : Prop) : (p3680) ∨ (¬ (p5402 ∧ p5403 ∧ p3680 ∧ p5404 ∧ p5405)) := by
  classical
  tauto

theorem initial9314 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3680) ∨ (¬ (meaning t m 5401)) := by
  exact rule9314 (meaning t m 3680) (meaning t m 5402) (meaning t m 5403) (meaning t m 5404) (meaning t m 5405)

theorem rule9316 (p3680 p5402 p5403 p5404 p5405 : Prop) : (¬ (p5402 ∧ p5403 ∧ p3680 ∧ p5404 ∧ p5405)) ∨ (p5405) := by
  classical
  tauto

theorem initial9316 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5401)) ∨ (meaning t m 5405) := by
  exact rule9316 (meaning t m 3680) (meaning t m 5402) (meaning t m 5403) (meaning t m 5404) (meaning t m 5405)

theorem rule9320 (p5396 p5401 : Prop) : (¬ (p5396 ∨ p5401)) ∨ (p5396) ∨ (p5401) := by
  classical
  tauto

theorem initial9320 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5395)) ∨ (meaning t m 5396) ∨ (meaning t m 5401) := by
  exact rule9320 (meaning t m 5396) (meaning t m 5401)

theorem rule9321 (p3674 p5395 : Prop) (h : (p3674 ↔ p5395)) : (¬ p3674) ∨ (p5395) := by
  classical
  tauto

theorem initial9321 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3674)) ∨ (meaning t m 5395) := by
  have source := ElevenTheory.theory1412 t (m.theta 5 10) (m.theta 5 9) (m.theta 9 10)
  exact rule9321 (meaning t m 3674) (meaning t m 5395) source

theorem rule9323 (p2027 p3564 p3956 p4345 p4348 p4503 : Prop) (h : (¬ p3564) ∨ (¬ p3956) ∨ p2027 ∨ (¬ p4348) ∨ (¬ p4345) ∨ (¬ p4503)) : (p2027) ∨ (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial9323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory1413 t (m.theta 4 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule9323 (meaning t m 2027) (meaning t m 3564) (meaning t m 3956) (meaning t m 4345) (meaning t m 4348) (meaning t m 4503) source

theorem rule9324 (p2027 p2518 p2928 p3570 p4404 p4647 : Prop) (h : (¬ p2518) ∨ (¬ p4404) ∨ (¬ p3570) ∨ (¬ p4647) ∨ (¬ p2928) ∨ p2027) : (p2027) ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3570) ∨ (¬ p4404) ∨ (¬ p4647) := by
  classical
  tauto

theorem initial9324 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4647)) := by
  have source := ElevenTheory.theory1414 t (m.theta 1 4) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8)
  exact rule9324 (meaning t m 2027) (meaning t m 2518) (meaning t m 2928) (meaning t m 3570) (meaning t m 4404) (meaning t m 4647) source

theorem rule9326 (p2027 p2230 p2427 p3054 p4244 p4730 : Prop) (h : (¬ p2230) ∨ (¬ p4244) ∨ (¬ p4730) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3054)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3054) ∨ (¬ p4244) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial9326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory1416 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 7)
  exact rule9326 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 3054) (meaning t m 4244) (meaning t m 4730) source

theorem rule9327 (p2027 p2220 p3556 p3659 p4042 p4895 : Prop) (h : (¬ p4042) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p2220) ∨ (¬ p3556) ∨ (¬ p4895)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3659) ∨ (¬ p4042) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial9327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4042)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory1417 t (m.theta 0 5) (m.theta 2 7) (m.theta 5 7) (m.theta 5 8) (m.theta 7 8)
  exact rule9327 (meaning t m 2027) (meaning t m 2220) (meaning t m 3556) (meaning t m 3659) (meaning t m 4042) (meaning t m 4895) source

theorem rule9329 (p2493 p2499 : Prop) (h : (¬ p2499) ∨ (¬ p2493)) : (¬ p2493) ∨ (¬ p2499) := by
  classical
  tauto

theorem initial9329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2499)) := by
  have source := ElevenTheory.theory1419 (m.theta 1 4) (m.theta 4 6)
  exact rule9329 (meaning t m 2493) (meaning t m 2499) source

theorem rule9330 (p2027 p2341 p2656 p2797 p3659 p4357 p4975 p5201 : Prop) (h : (¬ p2656) ∨ (¬ p4975) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p3659) ∨ (¬ p2797) ∨ (¬ p4357)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2656) ∨ (¬ p2797) ∨ (¬ p3659) ∨ (¬ p4357) ∨ (¬ p4975) ∨ (¬ p5201) := by
  classical
  tauto

theorem initial9330 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4357)) ∨ (¬ (meaning t m 4975)) ∨ (¬ (meaning t m 5201)) := by
  have source := ElevenTheory.theory1420 t (m.theta 0 4) (m.theta 0 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4) (m.theta 3 6) (m.theta 7 8)
  exact rule9330 (meaning t m 2027) (meaning t m 2341) (meaning t m 2656) (meaning t m 2797) (meaning t m 3659) (meaning t m 4357) (meaning t m 4975) (meaning t m 5201) source

theorem rule9331 (p2901 p4320 : Prop) (h : (¬ p4320) ∨ (¬ p2901)) : (¬ p2901) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial9331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory1421 (m.theta 3 5) (m.theta 5 7)
  exact rule9331 (meaning t m 2901) (meaning t m 4320) source

theorem rule9332 (p2027 p2493 p3238 p4203 p4235 p4555 : Prop) (h : (¬ p4555) ∨ (¬ p4235) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ p2027) : (p2027) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial9332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory1422 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 5 7)
  exact rule9332 (meaning t m 2027) (meaning t m 2493) (meaning t m 3238) (meaning t m 4203) (meaning t m 4235) (meaning t m 4555) source

theorem rule9334 (p2027 p2138 p2608 p2707 p3582 p3873 p5086 : Prop) (h : (¬ p3582) ∨ p2027 ∨ (¬ p2138) ∨ (¬ p5086) ∨ (¬ p2707) ∨ (¬ p2608) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3582) ∨ (¬ p3873) ∨ (¬ p5086) := by
  classical
  tauto

theorem initial9334 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 5086)) := by
  have source := ElevenTheory.theory1424 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 2 7)
  exact rule9334 (meaning t m 2027) (meaning t m 2138) (meaning t m 2608) (meaning t m 2707) (meaning t m 3582) (meaning t m 3873) (meaning t m 5086) source

theorem rule9335 (p2027 p3323 p3568 p4324 p4473 p4623 : Prop) (h : (¬ p4623) ∨ (¬ p3568) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p4324) ∨ (¬ p4473)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4324) ∨ (¬ p4473) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial9335 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4473)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory1425 t (m.theta 2 7) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9)
  exact rule9335 (meaning t m 2027) (meaning t m 3323) (meaning t m 3568) (meaning t m 4324) (meaning t m 4473) (meaning t m 4623) source

theorem rule9336 (p2027 p3461 p4187 p4276 p4278 p4381 : Prop) (h : (¬ p4276) ∨ (¬ p4187) ∨ p2027 ∨ (¬ p3461) ∨ (¬ p4278) ∨ (¬ p4381)) : (p2027) ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial9336 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 4187)) ∨ (¬ (meaning t m 4276)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory1426 t (m.theta 4 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule9336 (meaning t m 2027) (meaning t m 3461) (meaning t m 4187) (meaning t m 4276) (meaning t m 4278) (meaning t m 4381) source

theorem rule9339 (p4321 p5408 p5409 p5410 p5411 : Prop) : (p4321) ∨ (¬ (p5408 ∧ p5409 ∧ p4321 ∧ p5410 ∧ p5411)) := by
  classical
  tauto

theorem initial9339 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4321) ∨ (¬ (meaning t m 5407)) := by
  exact rule9339 (meaning t m 4321) (meaning t m 5408) (meaning t m 5409) (meaning t m 5410) (meaning t m 5411)

theorem rule9345 (p3707 p5413 p5414 p5415 p5416 : Prop) : (p3707) ∨ (¬ (p5413 ∧ p5414 ∧ p3707 ∧ p5415 ∧ p5416)) := by
  classical
  tauto

theorem initial9345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3707) ∨ (¬ (meaning t m 5412)) := by
  exact rule9345 (meaning t m 3707) (meaning t m 5413) (meaning t m 5414) (meaning t m 5415) (meaning t m 5416)

theorem rule9351 (p5407 p5412 : Prop) : (¬ (p5407 ∨ p5412)) ∨ (p5407) ∨ (p5412) := by
  classical
  tauto

theorem initial9351 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5406)) ∨ (meaning t m 5407) ∨ (meaning t m 5412) := by
  exact rule9351 (meaning t m 5407) (meaning t m 5412)

theorem rule9352 (p3701 p5406 : Prop) (h : (p3701 ↔ p5406)) : (¬ p3701) ∨ (p5406) := by
  classical
  tauto

theorem initial9352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3701)) ∨ (meaning t m 5406) := by
  have source := ElevenTheory.theory1427 t (m.theta 1 10) (m.theta 1 9) (m.theta 9 10)
  exact rule9352 (meaning t m 3701) (meaning t m 5406) source

theorem rule9356 (p5419 p5420 p5421 p5422 p5423 : Prop) : (¬ (p5419 ∧ p5420 ∧ p5421 ∧ p5422 ∧ p5423)) ∨ (p5421) := by
  classical
  tauto

theorem initial9356 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5418)) ∨ (meaning t m 5421) := by
  exact rule9356 (meaning t m 5419) (meaning t m 5420) (meaning t m 5421) (meaning t m 5422) (meaning t m 5423)

theorem rule9362 (p3717 p5425 p5426 p5427 p5428 : Prop) : (p3717) ∨ (¬ (p5425 ∧ p5426 ∧ p3717 ∧ p5427 ∧ p5428)) := by
  classical
  tauto

theorem initial9362 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3717) ∨ (¬ (meaning t m 5424)) := by
  exact rule9362 (meaning t m 3717) (meaning t m 5425) (meaning t m 5426) (meaning t m 5427) (meaning t m 5428)

theorem rule9368 (p5418 p5424 : Prop) : (¬ (p5418 ∨ p5424)) ∨ (p5418) ∨ (p5424) := by
  classical
  tauto

theorem initial9368 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5417)) ∨ (meaning t m 5418) ∨ (meaning t m 5424) := by
  exact rule9368 (meaning t m 5418) (meaning t m 5424)

theorem rule9369 (p3711 p5417 : Prop) (h : (p3711 ↔ p5417)) : (¬ p3711) ∨ (p5417) := by
  classical
  tauto

theorem initial9369 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3711)) ∨ (meaning t m 5417) := by
  have source := ElevenTheory.theory1428 t (m.theta 2 10) (m.theta 2 5) (m.theta 5 10)
  exact rule9369 (meaning t m 3711) (meaning t m 5417) source

theorem rule9371 (p2027 p2230 p3054 p3727 p4730 p5421 : Prop) (h : (¬ p3727) ∨ (¬ p4730) ∨ (¬ p2230) ∨ p2027 ∨ (¬ p3054) ∨ (¬ p5421)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3054) ∨ (¬ p3727) ∨ (¬ p4730) ∨ (¬ p5421) := by
  classical
  tauto

theorem initial9371 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4730)) ∨ (¬ (meaning t m 5421)) := by
  have source := ElevenTheory.theory1429 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 5 10)
  exact rule9371 (meaning t m 2027) (meaning t m 2230) (meaning t m 3054) (meaning t m 3727) (meaning t m 4730) (meaning t m 5421) source

theorem rule9374 (p5431 p5432 p5433 p5434 p5435 : Prop) : (¬ (p5431 ∧ p5432 ∧ p5433 ∧ p5434 ∧ p5435)) ∨ (p5433) := by
  classical
  tauto

theorem initial9374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5430)) ∨ (meaning t m 5433) := by
  exact rule9374 (meaning t m 5431) (meaning t m 5432) (meaning t m 5433) (meaning t m 5434) (meaning t m 5435)

theorem rule9378 (p3727 p4258 p5437 p5438 p5439 : Prop) : (¬ (p5437 ∧ p4258 ∧ p3727 ∧ p5438 ∧ p5439)) ∨ (p5437) := by
  classical
  tauto

theorem initial9378 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5436)) ∨ (meaning t m 5437) := by
  exact rule9378 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule9379 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p4258) ∨ (¬ (p5437 ∧ p4258 ∧ p3727 ∧ p5438 ∧ p5439)) := by
  classical
  tauto

theorem initial9379 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4258) ∨ (¬ (meaning t m 5436)) := by
  exact rule9379 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule9380 (p3727 p4258 p5437 p5438 p5439 : Prop) : (p3727) ∨ (¬ (p5437 ∧ p4258 ∧ p3727 ∧ p5438 ∧ p5439)) := by
  classical
  tauto

theorem initial9380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3727) ∨ (¬ (meaning t m 5436)) := by
  exact rule9380 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule9381 (p3727 p4258 p5437 p5438 p5439 : Prop) : (¬ (p5437 ∧ p4258 ∧ p3727 ∧ p5438 ∧ p5439)) ∨ (p5438) := by
  classical
  tauto

theorem initial9381 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5436)) ∨ (meaning t m 5438) := by
  exact rule9381 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule9382 (p3727 p4258 p5437 p5438 p5439 : Prop) : (¬ (p5437 ∧ p4258 ∧ p3727 ∧ p5438 ∧ p5439)) ∨ (p5439) := by
  classical
  tauto

theorem initial9382 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5436)) ∨ (meaning t m 5439) := by
  exact rule9382 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule9383 (p3727 p4258 p5437 p5438 p5439 : Prop) : (¬ p3727) ∨ (¬ p4258) ∨ ((p5437 ∧ p4258 ∧ p3727 ∧ p5438 ∧ p5439)) ∨ (¬ p5437) ∨ (¬ p5438) ∨ (¬ p5439) := by
  classical
  tauto

theorem initial9383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4258)) ∨ (meaning t m 5436) ∨ (¬ (meaning t m 5437)) ∨ (¬ (meaning t m 5438)) ∨ (¬ (meaning t m 5439)) := by
  exact rule9383 (meaning t m 3727) (meaning t m 4258) (meaning t m 5437) (meaning t m 5438) (meaning t m 5439)

theorem rule9386 (p5430 p5436 : Prop) : (¬ (p5430 ∨ p5436)) ∨ (p5430) ∨ (p5436) := by
  classical
  tauto

theorem initial9386 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5429)) ∨ (meaning t m 5430) ∨ (meaning t m 5436) := by
  exact rule9386 (meaning t m 5430) (meaning t m 5436)

theorem rule9387 (p3721 p5429 : Prop) (h : (p3721 ↔ p5429)) : (¬ p3721) ∨ (p5429) := by
  classical
  tauto

theorem initial9387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3721)) ∨ (meaning t m 5429) := by
  have source := ElevenTheory.theory1430 t (m.theta 4 10) (m.theta 4 5) (m.theta 5 10)
  exact rule9387 (meaning t m 3721) (meaning t m 5429) source

theorem rule9389 (p2027 p2493 p3238 p4203 p5433 p5440 : Prop) (h : (¬ p2493) ∨ (¬ p5433) ∨ (¬ p5440) ∨ (¬ p4203) ∨ (¬ p3238) ∨ p2027) : (p2027) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p5433) ∨ (¬ p5440) := by
  classical
  tauto

theorem initial9389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 5433)) ∨ (¬ (meaning t m 5440)) := by
  have source := ElevenTheory.theory1431 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 10) (m.theta 5 6)
  exact rule9389 (meaning t m 2027) (meaning t m 2493) (meaning t m 3238) (meaning t m 4203) (meaning t m 5433) (meaning t m 5440) source

theorem rule9390 (p4393 p5440 p5443 p5444 p5445 : Prop) : (¬ (p5443 ∧ p5444 ∧ p4393 ∧ p5440 ∧ p5445)) ∨ (p5443) := by
  classical
  tauto

theorem initial9390 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 5442)) ∨ (meaning t m 5443) := by
  exact rule9390 (meaning t m 4393) (meaning t m 5440) (meaning t m 5443) (meaning t m 5444) (meaning t m 5445)

end SunPrize.SMT
