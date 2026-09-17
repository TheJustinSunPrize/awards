import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory047
import SunPrize.Certificate.Theory048
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule27267 (p2563 p3952 p4241 : Prop) (h : (¬ p3952) ∨ (¬ p4241) ∨ (¬ p2563)) : (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial27267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory16523 (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule27267 (meaning t m 2563) (meaning t m 3952) (meaning t m 4241) source

theorem rule27268 (p2027 p2138 p2417 p3367 p3389 p3692 p3694 p3759 p3950 p4734 : Prop) (h : (¬ p3694) ∨ (¬ p3692) ∨ (¬ p2138) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3759) ∨ (¬ p3389) ∨ (¬ p4734) ∨ (¬ p3950)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2417) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3692) ∨ (¬ p3694) ∨ (¬ p3759) ∨ (¬ p3950) ∨ (¬ p4734) := by
  classical
  tauto

theorem initial27268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3759)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4734)) := by
  have source := ElevenTheory.theory16524 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27268 (meaning t m 2027) (meaning t m 2138) (meaning t m 2417) (meaning t m 3367) (meaning t m 3389) (meaning t m 3692) (meaning t m 3694) (meaning t m 3759) (meaning t m 3950) (meaning t m 4734) source

theorem rule27271 (p1998 p2027 p2114 p2717 p3055 p3367 p3471 : Prop) (h : (¬ p3055) ∨ (¬ p3367) ∨ (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2717) ∨ (¬ p3471)) : (¬ p1998) ∨ (p2027) ∨ (p2114) ∨ (¬ p2717) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3471) := by
  classical
  tauto

theorem initial27271 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3471)) := by
  have source := ElevenTheory.theory16527 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 7 8)
  exact rule27271 (meaning t m 1998) (meaning t m 2027) (meaning t m 2114) (meaning t m 2717) (meaning t m 3055) (meaning t m 3367) (meaning t m 3471) source

theorem rule27276 (p2027 p2946 p2972 p3292 p4040 p4960 : Prop) (h : (¬ p2946) ∨ p2027 ∨ (¬ p4040) ∨ (¬ p2972) ∨ (¬ p4960) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2946) ∨ (¬ p2972) ∨ (¬ p3292) ∨ (¬ p4040) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial27276 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 4040)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory16532 t (m.theta 0 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 9) (m.theta 5 9)
  exact rule27276 (meaning t m 2027) (meaning t m 2946) (meaning t m 2972) (meaning t m 3292) (meaning t m 4040) (meaning t m 4960) source

theorem rule27279 (p4636 p4656 p5171 : Prop) (h : (¬ p4636) ∨ (¬ p5171) ∨ p4656) : (¬ p4636) ∨ (p4656) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial27279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4636)) ∨ (meaning t m 4656) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory16535 (m.theta 3 9) (m.theta 4 9) (m.theta 7 9)
  exact rule27279 (meaning t m 4636) (meaning t m 4656) (meaning t m 5171) source

theorem rule27281 (p2027 p2177 p3051 p4120 p4132 p4556 : Prop) (h : (¬ p4132) ∨ (¬ p2177) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p4556) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3051) ∨ (¬ p4120) ∨ (¬ p4132) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial27281 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4132)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory16537 t (m.theta 0 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule27281 (meaning t m 2027) (meaning t m 2177) (meaning t m 3051) (meaning t m 4120) (meaning t m 4132) (meaning t m 4556) source

theorem rule27283 (p2027 p2934 p3093 p3631 p3821 p4281 p4760 p5206 : Prop) (h : (¬ p3631) ∨ (¬ p5206) ∨ (¬ p3821) ∨ (¬ p2934) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p4281) ∨ (¬ p4760)) : (p2027) ∨ (¬ p2934) ∨ (¬ p3093) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4281) ∨ (¬ p4760) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial27283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2934)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4281)) ∨ (¬ (meaning t m 4760)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory16539 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 3) (m.theta 1 4) (m.theta 1 6) (m.theta 1 7) (m.theta 7 9)
  exact rule27283 (meaning t m 2027) (meaning t m 2934) (meaning t m 3093) (meaning t m 3631) (meaning t m 3821) (meaning t m 4281) (meaning t m 4760) (meaning t m 5206) source

theorem rule27285 (p1979 p2027 p2210 p2247 p2688 p2891 p4320 : Prop) (h : p2688 ∨ (¬ p2247) ∨ (¬ p1979) ∨ (¬ p2891) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p2210)) : (¬ p1979) ∨ (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (p2688) ∨ (¬ p2891) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial27285 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1979)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (meaning t m 2688) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory16541 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 5 7)
  exact rule27285 (meaning t m 1979) (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 2688) (meaning t m 2891) (meaning t m 4320) source

theorem rule27290 (p1980 p2027 p2633 p2797 p3177 p3877 p3941 p5590 : Prop) (h : (¬ p1980) ∨ p2633 ∨ (¬ p3177) ∨ (¬ p2797) ∨ (¬ p5590) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p3941)) : (¬ p1980) ∨ (p2027) ∨ (p2633) ∨ (¬ p2797) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p3941) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial27290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1980)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3177)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory16546 t (m.theta 0 8) (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 7 8) (m.theta 8 10)
  exact rule27290 (meaning t m 1980) (meaning t m 2027) (meaning t m 2633) (meaning t m 2797) (meaning t m 3177) (meaning t m 3877) (meaning t m 3941) (meaning t m 5590) source

theorem rule27292 (p2027 p2982 p3054 p3422 p4385 p4717 : Prop) (h : (¬ p3054) ∨ (¬ p3422) ∨ (¬ p2982) ∨ (¬ p4385) ∨ p2027 ∨ (¬ p4717)) : (p2027) ∨ (¬ p2982) ∨ (¬ p3054) ∨ (¬ p3422) ∨ (¬ p4385) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial27292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3054)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory16548 t (m.theta 2 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule27292 (meaning t m 2027) (meaning t m 2982) (meaning t m 3054) (meaning t m 3422) (meaning t m 4385) (meaning t m 4717) source

theorem rule27293 (p2027 p2230 p2440 p2663 p3414 p4650 : Prop) (h : (¬ p4650) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p2230) ∨ (¬ p2663) ∨ (¬ p2440)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p3414) ∨ (¬ p4650) := by
  classical
  tauto

theorem initial27293 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2663)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4650)) := by
  have source := ElevenTheory.theory16549 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule27293 (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2663) (meaning t m 3414) (meaning t m 4650) source

theorem rule27297 (p2027 p2579 p2588 p2696 p2742 p2901 p2992 p3363 p3585 p4556 p4737 : Prop) (h : (¬ p2696) ∨ (¬ p2742) ∨ (¬ p4556) ∨ (¬ p4737) ∨ (¬ p3585) ∨ (¬ p2901) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2992) ∨ (¬ p3363) ∨ (¬ p2588)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p2901) ∨ (¬ p2992) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4556) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial27297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2742)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory16553 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7)
  exact rule27297 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 2696) (meaning t m 2742) (meaning t m 2901) (meaning t m 2992) (meaning t m 3363) (meaning t m 3585) (meaning t m 4556) (meaning t m 4737) source

theorem rule27299 (p1996 p2027 p2622 p3365 p3471 p3527 p3553 p4424 : Prop) (h : (¬ p4424) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p1996) ∨ p2027 ∨ (¬ p3553) ∨ (¬ p3527) ∨ p2622) : (¬ p1996) ∨ (p2027) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial27299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1996)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory16555 t (m.theta 0 2) (m.theta 1 7) (m.theta 2 3) (m.theta 2 7) (m.theta 3 7) (m.theta 7 8)
  exact rule27299 (meaning t m 1996) (meaning t m 2027) (meaning t m 2622) (meaning t m 3365) (meaning t m 3471) (meaning t m 3527) (meaning t m 3553) (meaning t m 4424) source

theorem rule27301 (p2000 p2388 p2589 p4705 : Prop) (h : (¬ p2000) ∨ p2388 ∨ p4705 ∨ (¬ p2589)) : (¬ p2000) ∨ (p2388) ∨ (¬ p2589) ∨ (p4705) := by
  classical
  tauto

theorem initial27301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2000)) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2589)) ∨ (meaning t m 4705) := by
  have source := ElevenTheory.theory16557 t (m.theta 0 4) (m.theta 3 5) (m.theta 4 5)
  exact rule27301 (meaning t m 2000) (meaning t m 2388) (meaning t m 2589) (meaning t m 4705) source

theorem rule27302 (p2003 p2027 p2299 p2633 p3323 p3568 p3946 : Prop) (h : (¬ p2003) ∨ p2633 ∨ (¬ p3946) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p2299) ∨ p2027) : (¬ p2003) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3946) := by
  classical
  tauto

theorem initial27302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2003)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3946)) := by
  have source := ElevenTheory.theory16558 t (m.theta 0 6) (m.theta 3 6) (m.theta 6 7) (m.theta 6 9) (m.theta 7 8)
  exact rule27302 (meaning t m 2003) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3323) (meaning t m 3568) (meaning t m 3946) source

theorem rule27303 (p1976 p2027 p2633 p3365 p3570 p4315 p4320 : Prop) (h : p2633 ∨ (¬ p3365) ∨ (¬ p4320) ∨ (¬ p1976) ∨ p2027 ∨ (¬ p3570) ∨ (¬ p4315)) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4315) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial27303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4315)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory16559 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 7) (m.theta 7 8)
  exact rule27303 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 3365) (meaning t m 3570) (meaning t m 4315) (meaning t m 4320) source

theorem rule27306 (p3698 p4702 p5053 : Prop) (h : (¬ p3698) ∨ (¬ p4702) ∨ p5053) : (¬ p3698) ∨ (¬ p4702) ∨ (p5053) := by
  classical
  tauto

theorem initial27306 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3698)) ∨ (¬ (meaning t m 4702)) ∨ (meaning t m 5053) := by
  have source := ElevenTheory.theory16562 t (m.theta 2 5) (m.theta 3 5) (m.theta 4 5)
  exact rule27306 (meaning t m 3698) (meaning t m 4702) (meaning t m 5053) source

theorem rule27308 (p2132 p3471 p3587 : Prop) (h : (¬ p2132) ∨ (¬ p3587) ∨ p3471) : (¬ p2132) ∨ (p3471) ∨ (¬ p3587) := by
  classical
  tauto

theorem initial27308 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2132)) ∨ (meaning t m 3471) ∨ (¬ (meaning t m 3587)) := by
  have source := ElevenTheory.theory16564 (m.theta 0 2) (m.theta 2 5) (m.theta 2 7)
  exact rule27308 (meaning t m 2132) (meaning t m 3471) (meaning t m 3587) source

theorem rule27309 (p2027 p2241 p2589 p2641 p2668 p3097 p4110 p4405 p5193 : Prop) (h : (¬ p4110) ∨ (¬ p5193) ∨ (¬ p4405) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3097) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4405) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial27309 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory16565 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule27309 (meaning t m 2027) (meaning t m 2241) (meaning t m 2589) (meaning t m 2641) (meaning t m 2668) (meaning t m 3097) (meaning t m 4110) (meaning t m 4405) (meaning t m 5193) source

theorem rule27313 (p1994 p2027 p2230 p2440 p2938 p3246 p3821 p5197 : Prop) (h : (¬ p3246) ∨ (¬ p3821) ∨ p2938 ∨ (¬ p2230) ∨ (¬ p1994) ∨ (¬ p5197) ∨ p2027 ∨ (¬ p2440)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2230) ∨ (¬ p2440) ∨ (p2938) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial27313 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2440)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory16569 t (m.theta 0 4) (m.theta 0 7) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule27313 (meaning t m 1994) (meaning t m 2027) (meaning t m 2230) (meaning t m 2440) (meaning t m 2938) (meaning t m 3246) (meaning t m 3821) (meaning t m 5197) source

theorem rule27315 (p2027 p2136 p2247 p2619 p2744 p2922 p3366 p3379 p4120 p4244 p4277 : Prop) (h : (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4120) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3366) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2136) ∨ p2027 ∨ (¬ p2619)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2619) ∨ (¬ p2744) ∨ (¬ p2922) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p4120) ∨ (¬ p4244) ∨ (¬ p4277) := by
  classical
  tauto

theorem initial27315 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4244)) ∨ (¬ (meaning t m 4277)) := by
  have source := ElevenTheory.theory16571 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 5) (m.theta 4 7) (m.theta 5 7) (m.theta 5 8)
  exact rule27315 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2619) (meaning t m 2744) (meaning t m 2922) (meaning t m 3366) (meaning t m 3379) (meaning t m 4120) (meaning t m 4244) (meaning t m 4277) source

theorem rule27323 (p2007 p2027 p2145 p2264 p2651 p2766 p3580 p3646 p3941 p3989 p4117 p4286 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p2264) ∨ (¬ p4117) ∨ (¬ p3580) ∨ (¬ p4286) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2145) ∨ (¬ p3989) ∨ (¬ p3646) ∨ p2766 ∨ (¬ p3941) ∨ (¬ p2007)) : (¬ p2007) ∨ (p2027) ∨ (¬ p2145) ∨ (¬ p2264) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p3580) ∨ (¬ p3646) ∨ (¬ p3941) ∨ (¬ p3989) ∨ (¬ p4117) ∨ (¬ p4286) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial27323 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2007)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3941)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory16579 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 7) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27323 (meaning t m 2007) (meaning t m 2027) (meaning t m 2145) (meaning t m 2264) (meaning t m 2651) (meaning t m 2766) (meaning t m 3580) (meaning t m 3646) (meaning t m 3941) (meaning t m 3989) (meaning t m 4117) (meaning t m 4286) (meaning t m 4347) source

theorem rule27326 (p2027 p2727 p2952 p3166 p4360 p4701 : Prop) (h : (¬ p2952) ∨ p2027 ∨ (¬ p4701) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p4360)) : (p2027) ∨ (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p4701) := by
  classical
  tauto

theorem initial27326 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4701)) := by
  have source := ElevenTheory.theory16582 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 3 8)
  exact rule27326 (meaning t m 2027) (meaning t m 2727) (meaning t m 2952) (meaning t m 3166) (meaning t m 4360) (meaning t m 4701) source

theorem rule27327 (p2027 p3055 p3366 p3399 p3527 p3591 p3684 p3880 p4866 p4905 : Prop) (h : (¬ p3880) ∨ (¬ p3366) ∨ p2027 ∨ (¬ p3684) ∨ (¬ p3055) ∨ (¬ p4905) ∨ (¬ p4866) ∨ (¬ p3527) ∨ (¬ p3591) ∨ (¬ p3399)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3591) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4866) ∨ (¬ p4905) := by
  classical
  tauto

theorem initial27327 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4866)) ∨ (¬ (meaning t m 4905)) := by
  have source := ElevenTheory.theory16583 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 8) (m.theta 7 8)
  exact rule27327 (meaning t m 2027) (meaning t m 3055) (meaning t m 3366) (meaning t m 3399) (meaning t m 3527) (meaning t m 3591) (meaning t m 3684) (meaning t m 3880) (meaning t m 4866) (meaning t m 4905) source

theorem rule27328 (p1976 p2027 p2169 p2363 p3365 p3877 p4118 : Prop) (h : p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p1976) ∨ (¬ p3877) ∨ (¬ p4118)) : (¬ p1976) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial27328 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory16584 t (m.theta 0 2) (m.theta 2 3) (m.theta 3 8) (m.theta 6 8) (m.theta 8 9)
  exact rule27328 (meaning t m 1976) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 3365) (meaning t m 3877) (meaning t m 4118) source

theorem rule27329 (p1982 p2027 p2192 p2363 p2873 p3156 p3952 p4441 : Prop) (h : (¬ p2363) ∨ p2873 ∨ (¬ p3952) ∨ (¬ p2192) ∨ (¬ p4441) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3156)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (p2873) ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial27329 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2873) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory16585 t (m.theta 1 5) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule27329 (meaning t m 1982) (meaning t m 2027) (meaning t m 2192) (meaning t m 2363) (meaning t m 2873) (meaning t m 3156) (meaning t m 3952) (meaning t m 4441) source

theorem rule27331 (p2027 p2248 p2264 p2299 p2331 p3055 p3367 p3588 p3873 p4156 p4477 : Prop) (h : p2027 ∨ (¬ p2299) ∨ (¬ p4156) ∨ (¬ p3055) ∨ (¬ p2331) ∨ (¬ p2264) ∨ (¬ p3367) ∨ (¬ p4477) ∨ (¬ p2248) ∨ (¬ p3588) ∨ (¬ p3873)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3367) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4156) ∨ (¬ p4477) := by
  classical
  tauto

theorem initial27331 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4156)) ∨ (¬ (meaning t m 4477)) := by
  have source := ElevenTheory.theory16587 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27331 (meaning t m 2027) (meaning t m 2248) (meaning t m 2264) (meaning t m 2299) (meaning t m 2331) (meaning t m 3055) (meaning t m 3367) (meaning t m 3588) (meaning t m 3873) (meaning t m 4156) (meaning t m 4477) source

theorem rule27332 (p1994 p2027 p2598 p2622 p3365 p3422 p3574 : Prop) (h : (¬ p2598) ∨ p2027 ∨ (¬ p3365) ∨ p2622 ∨ (¬ p3422) ∨ (¬ p3574) ∨ (¬ p1994)) : (¬ p1994) ∨ (p2027) ∨ (¬ p2598) ∨ (p2622) ∨ (¬ p3365) ∨ (¬ p3422) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial27332 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1994)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory16588 t (m.theta 0 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6)
  exact rule27332 (meaning t m 1994) (meaning t m 2027) (meaning t m 2598) (meaning t m 2622) (meaning t m 3365) (meaning t m 3422) (meaning t m 3574) source

theorem rule27337 (p2027 p2579 p3399 p3422 p3527 p3570 p3876 p4647 p5193 : Prop) (h : (¬ p3399) ∨ (¬ p3570) ∨ (¬ p5193) ∨ (¬ p3527) ∨ (¬ p2579) ∨ (¬ p4647) ∨ p2027 ∨ (¬ p3876) ∨ (¬ p3422)) : (p2027) ∨ (¬ p2579) ∨ (¬ p3399) ∨ (¬ p3422) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3876) ∨ (¬ p4647) ∨ (¬ p5193) := by
  classical
  tauto

theorem initial27337 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4647)) ∨ (¬ (meaning t m 5193)) := by
  have source := ElevenTheory.theory16593 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule27337 (meaning t m 2027) (meaning t m 2579) (meaning t m 3399) (meaning t m 3422) (meaning t m 3527) (meaning t m 3570) (meaning t m 3876) (meaning t m 4647) (meaning t m 5193) source

theorem rule27343 (p1990 p2027 p2553 p2766 p3097 p3956 p4347 : Prop) (h : (¬ p1990) ∨ p2766 ∨ (¬ p4347) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p3956)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2553) ∨ (p2766) ∨ (¬ p3097) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial27343 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory16599 t (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule27343 (meaning t m 1990) (meaning t m 2027) (meaning t m 2553) (meaning t m 2766) (meaning t m 3097) (meaning t m 3956) (meaning t m 4347) source

theorem rule27344 (p3364 p4881 p5049 : Prop) (h : (¬ p3364) ∨ (¬ p5049) ∨ p4881) : (¬ p3364) ∨ (p4881) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial27344 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3364)) ∨ (meaning t m 4881) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory16600 t (m.theta 2 3) (m.theta 2 4) (m.theta 2 5)
  exact rule27344 (meaning t m 3364) (meaning t m 4881) (meaning t m 5049) source

theorem rule27345 (p1991 p2027 p2202 p2440 p3172 p3189 p4111 : Prop) (h : (¬ p3189) ∨ (¬ p3172) ∨ p2202 ∨ p2027 ∨ (¬ p2440) ∨ (¬ p1991) ∨ (¬ p4111)) : (¬ p1991) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial27345 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1991)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory16601 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5)
  exact rule27345 (meaning t m 1991) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3172) (meaning t m 3189) (meaning t m 4111) source

theorem rule27347 (p2027 p2254 p2588 p2657 p3399 p3527 p3570 p3574 p4556 : Prop) (h : (¬ p4556) ∨ (¬ p2588) ∨ (¬ p3399) ∨ (¬ p2254) ∨ p2027 ∨ (¬ p3574) ∨ (¬ p2657) ∨ (¬ p3570) ∨ (¬ p3527)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2588) ∨ (¬ p2657) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p3574) ∨ (¬ p4556) := by
  classical
  tauto

theorem initial27347 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 4556)) := by
  have source := ElevenTheory.theory16603 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 7) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27347 (meaning t m 2027) (meaning t m 2254) (meaning t m 2588) (meaning t m 2657) (meaning t m 3399) (meaning t m 3527) (meaning t m 3570) (meaning t m 3574) (meaning t m 4556) source

theorem rule27348 (p3985 p4842 p5049 : Prop) (h : (¬ p3985) ∨ (¬ p5049) ∨ p4842) : (¬ p3985) ∨ (p4842) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial27348 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3985)) ∨ (meaning t m 4842) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory16604 t (m.theta 2 3) (m.theta 2 5) (m.theta 2 6)
  exact rule27348 (meaning t m 3985) (meaning t m 4842) (meaning t m 5049) source

theorem rule27350 (p2006 p2027 p2132 p2409 p2493 p3055 p3584 : Prop) (h : (¬ p2132) ∨ (¬ p2493) ∨ (¬ p3584) ∨ (¬ p2006) ∨ p2409 ∨ p2027 ∨ (¬ p3055)) : (¬ p2006) ∨ (p2027) ∨ (¬ p2132) ∨ (p2409) ∨ (¬ p2493) ∨ (¬ p3055) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial27350 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2006)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory16606 t (m.theta 0 2) (m.theta 1 4) (m.theta 2 4) (m.theta 2 5) (m.theta 4 6)
  exact rule27350 (meaning t m 2006) (meaning t m 2027) (meaning t m 2132) (meaning t m 2409) (meaning t m 2493) (meaning t m 3055) (meaning t m 3584) source

theorem rule27352 (p2027 p2252 p2284 p2750 p2922 p2950 p3379 p3646 p3954 p4277 p4320 : Prop) (h : (¬ p3379) ∨ (¬ p2950) ∨ (¬ p4320) ∨ (¬ p2252) ∨ p2027 ∨ (¬ p2750) ∨ (¬ p3954) ∨ (¬ p3646) ∨ (¬ p4277) ∨ (¬ p2284) ∨ (¬ p2922)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2284) ∨ (¬ p2750) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3646) ∨ (¬ p3954) ∨ (¬ p4277) ∨ (¬ p4320) := by
  classical
  tauto

theorem initial27352 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4277)) ∨ (¬ (meaning t m 4320)) := by
  have source := ElevenTheory.theory16608 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7)
  exact rule27352 (meaning t m 2027) (meaning t m 2252) (meaning t m 2284) (meaning t m 2750) (meaning t m 2922) (meaning t m 2950) (meaning t m 3379) (meaning t m 3646) (meaning t m 3954) (meaning t m 4277) (meaning t m 4320) source

theorem rule27357 (p1987 p2027 p2388 p2727 p2810 p2901 p3368 p3486 : Prop) (h : (¬ p1987) ∨ p2027 ∨ p2388 ∨ (¬ p3486) ∨ (¬ p3368) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p2727)) : (¬ p1987) ∨ (p2027) ∨ (p2388) ∨ (¬ p2727) ∨ (¬ p2810) ∨ (¬ p2901) ∨ (¬ p3368) ∨ (¬ p3486) := by
  classical
  tauto

theorem initial27357 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (meaning t m 2388) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 2901)) ∨ (¬ (meaning t m 3368)) ∨ (¬ (meaning t m 3486)) := by
  have source := ElevenTheory.theory16613 t (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 7)
  exact rule27357 (meaning t m 1987) (meaning t m 2027) (meaning t m 2388) (meaning t m 2727) (meaning t m 2810) (meaning t m 2901) (meaning t m 3368) (meaning t m 3486) source

theorem rule27359 (p2088 p3146 p4115 : Prop) (h : (¬ p3146) ∨ (¬ p4115) ∨ p2088) : (p2088) ∨ (¬ p3146) ∨ (¬ p4115) := by
  classical
  tauto

theorem initial27359 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2088) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4115)) := by
  have source := ElevenTheory.theory16615 (m.theta 0 8) (m.theta 5 8) (m.theta 8 9)
  exact rule27359 (meaning t m 2088) (meaning t m 3146) (meaning t m 4115) source

theorem rule27360 (p4042 p4434 p4438 : Prop) (h : (¬ p4042) ∨ (¬ p4438) ∨ p4434) : (¬ p4042) ∨ (p4434) ∨ (¬ p4438) := by
  classical
  tauto

theorem initial27360 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4042)) ∨ (meaning t m 4434) ∨ (¬ (meaning t m 4438)) := by
  have source := ElevenTheory.theory16616 t (m.theta 4 8) (m.theta 5 8) (m.theta 7 8)
  exact rule27360 (meaning t m 4042) (meaning t m 4434) (meaning t m 4438) source

theorem rule27361 (p2027 p3093 p3319 p3347 p3556 p3570 p3904 p3954 p4330 p4348 p5216 : Prop) (h : (¬ p4348) ∨ (¬ p4330) ∨ (¬ p3347) ∨ (¬ p3093) ∨ (¬ p5216) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3904) ∨ (¬ p3556) ∨ (¬ p3319) ∨ (¬ p3570)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3347) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3904) ∨ (¬ p3954) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial27361 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory16617 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule27361 (meaning t m 2027) (meaning t m 3093) (meaning t m 3319) (meaning t m 3347) (meaning t m 3556) (meaning t m 3570) (meaning t m 3904) (meaning t m 3954) (meaning t m 4330) (meaning t m 4348) (meaning t m 5216) source

theorem rule27367 (p2027 p2144 p2156 p3365 p4030 p4173 p4202 p4752 : Prop) (h : p2027 ∨ (¬ p2144) ∨ (¬ p4173) ∨ (¬ p3365) ∨ (¬ p2156) ∨ (¬ p4202) ∨ (¬ p4030) ∨ (¬ p4752)) : (p2027) ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p3365) ∨ (¬ p4030) ∨ (¬ p4173) ∨ (¬ p4202) ∨ (¬ p4752) := by
  classical
  tauto

theorem initial27367 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2144)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4202)) ∨ (¬ (meaning t m 4752)) := by
  have source := ElevenTheory.theory16623 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 2 3) (m.theta 2 4) (m.theta 5 6)
  exact rule27367 (meaning t m 2027) (meaning t m 2144) (meaning t m 2156) (meaning t m 3365) (meaning t m 4030) (meaning t m 4173) (meaning t m 4202) (meaning t m 4752) source

theorem rule27374 (p2027 p2589 p2696 p2797 p3323 p3692 p3880 p4330 p4729 : Prop) (h : (¬ p3323) ∨ (¬ p2589) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p4729) ∨ (¬ p2797) ∨ (¬ p3692) ∨ (¬ p2696) ∨ p2027) : (p2027) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial27374 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory16630 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 9)
  exact rule27374 (meaning t m 2027) (meaning t m 2589) (meaning t m 2696) (meaning t m 2797) (meaning t m 3323) (meaning t m 3692) (meaning t m 3880) (meaning t m 4330) (meaning t m 4729) source

theorem rule27375 (p2027 p2493 p3238 p3758 p4203 p4882 : Prop) (h : (¬ p4882) ∨ (¬ p3238) ∨ (¬ p4203) ∨ p2027 ∨ (¬ p2493) ∨ (¬ p3758)) : (p2027) ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p3758) ∨ (¬ p4203) ∨ (¬ p4882) := by
  classical
  tauto

theorem initial27375 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4203)) ∨ (¬ (meaning t m 4882)) := by
  have source := ElevenTheory.theory16631 t (m.theta 1 4) (m.theta 2 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule27375 (meaning t m 2027) (meaning t m 2493) (meaning t m 3238) (meaning t m 3758) (meaning t m 4203) (meaning t m 4882) source

theorem rule27376 (p2027 p2247 p2819 p3654 p3917 p4111 p4256 p4384 p5017 : Prop) (h : (¬ p4384) ∨ (¬ p4111) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p5017) ∨ (¬ p4256) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2819) ∨ (¬ p3654) ∨ (¬ p3917) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017) := by
  classical
  tauto

theorem initial27376 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4384)) ∨ (¬ (meaning t m 5017)) := by
  have source := ElevenTheory.theory16632 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9)
  exact rule27376 (meaning t m 2027) (meaning t m 2247) (meaning t m 2819) (meaning t m 3654) (meaning t m 3917) (meaning t m 4111) (meaning t m 4256) (meaning t m 4384) (meaning t m 5017) source

theorem rule27380 (p2027 p2363 p2386 p2553 p3857 p4197 p4501 : Prop) (h : p2027 ∨ (¬ p4197) ∨ (¬ p2553) ∨ (¬ p4501) ∨ (¬ p3857) ∨ (¬ p2386) ∨ (¬ p2363)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2386) ∨ (¬ p2553) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4501) := by
  classical
  tauto

theorem initial27380 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4501)) := by
  have source := ElevenTheory.theory16636 t (m.theta 0 6) (m.theta 0 8) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule27380 (meaning t m 2027) (meaning t m 2363) (meaning t m 2386) (meaning t m 2553) (meaning t m 3857) (meaning t m 4197) (meaning t m 4501) source

theorem rule27383 (p1984 p2027 p2313 p2766 p3309 p3923 p4347 p5015 : Prop) (h : (¬ p3923) ∨ (¬ p4347) ∨ (¬ p1984) ∨ (¬ p2313) ∨ p2027 ∨ p2766 ∨ (¬ p5015) ∨ (¬ p3309)) : (¬ p1984) ∨ (p2027) ∨ (¬ p2313) ∨ (p2766) ∨ (¬ p3309) ∨ (¬ p3923) ∨ (¬ p4347) ∨ (¬ p5015) := by
  classical
  tauto

theorem initial27383 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 5015)) := by
  have source := ElevenTheory.theory16639 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule27383 (meaning t m 1984) (meaning t m 2027) (meaning t m 2313) (meaning t m 2766) (meaning t m 3309) (meaning t m 3923) (meaning t m 4347) (meaning t m 5015) source

theorem rule27384 (p1988 p2027 p2114 p2230 p2982 p3367 p3680 p3759 : Prop) (h : (¬ p1988) ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3680) ∨ (¬ p3759) ∨ (¬ p2982) ∨ p2114 ∨ p2027) : (¬ p1988) ∨ (p2027) ∨ (p2114) ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3367) ∨ (¬ p3680) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial27384 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1988)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory16640 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 9 10)
  exact rule27384 (meaning t m 1988) (meaning t m 2027) (meaning t m 2114) (meaning t m 2230) (meaning t m 2982) (meaning t m 3367) (meaning t m 3680) (meaning t m 3759) source

theorem rule27387 (p1982 p2027 p2202 p2440 p3276 p3343 p4444 : Prop) (h : p2202 ∨ (¬ p4444) ∨ (¬ p3343) ∨ (¬ p2440) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3276)) : (¬ p1982) ∨ (p2027) ∨ (p2202) ∨ (¬ p2440) ∨ (¬ p3276) ∨ (¬ p3343) ∨ (¬ p4444) := by
  classical
  tauto

theorem initial27387 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 4444)) := by
  have source := ElevenTheory.theory16643 t (m.theta 3 4) (m.theta 4 5) (m.theta 4 9) (m.theta 8 9) (m.theta 9 10)
  exact rule27387 (meaning t m 1982) (meaning t m 2027) (meaning t m 2202) (meaning t m 2440) (meaning t m 3276) (meaning t m 3343) (meaning t m 4444) source

theorem rule27388 (p2311 p5015 p5206 : Prop) (h : (¬ p2311) ∨ (¬ p5015) ∨ p5206) : (¬ p2311) ∨ (¬ p5015) ∨ (p5206) := by
  classical
  tauto

theorem initial27388 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 5015)) ∨ (meaning t m 5206) := by
  have source := ElevenTheory.theory16644 (m.theta 0 1) (m.theta 0 6) (m.theta 0 7)
  exact rule27388 (meaning t m 2311) (meaning t m 5015) (meaning t m 5206) source

theorem rule27389 (p1981 p2027 p2187 p2284 p2545 p2992 p4111 : Prop) (h : (¬ p2284) ∨ p2545 ∨ (¬ p4111) ∨ p2027 ∨ (¬ p1981) ∨ (¬ p2992) ∨ (¬ p2187)) : (¬ p1981) ∨ (p2027) ∨ (¬ p2187) ∨ (¬ p2284) ∨ (p2545) ∨ (¬ p2992) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial27389 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1981)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2284)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2992)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory16645 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule27389 (meaning t m 1981) (meaning t m 2027) (meaning t m 2187) (meaning t m 2284) (meaning t m 2545) (meaning t m 2992) (meaning t m 4111) source

theorem rule27392 (p2027 p2707 p3097 p3688 p4401 p4475 : Prop) (h : (¬ p2707) ∨ (¬ p4401) ∨ p2027 ∨ (¬ p3688) ∨ (¬ p3097) ∨ (¬ p4475)) : (p2027) ∨ (¬ p2707) ∨ (¬ p3097) ∨ (¬ p3688) ∨ (¬ p4401) ∨ (¬ p4475) := by
  classical
  tauto

theorem initial27392 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 4475)) := by
  have source := ElevenTheory.theory16648 t (m.theta 1 2) (m.theta 2 6) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7)
  exact rule27392 (meaning t m 2027) (meaning t m 2707) (meaning t m 3097) (meaning t m 3688) (meaning t m 4401) (meaning t m 4475) source

theorem rule27393 (p1975 p2027 p2137 p2156 p2274 p2839 p2842 p3585 : Prop) (h : (¬ p2274) ∨ (¬ p1975) ∨ p2027 ∨ p2842 ∨ (¬ p2156) ∨ (¬ p2839) ∨ (¬ p2137) ∨ (¬ p3585)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2839) ∨ (p2842) ∨ (¬ p3585) := by
  classical
  tauto

theorem initial27393 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2839)) ∨ (meaning t m 2842) ∨ (¬ (meaning t m 3585)) := by
  have source := ElevenTheory.theory16649 t (m.theta 0 5) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7)
  exact rule27393 (meaning t m 1975) (meaning t m 2027) (meaning t m 2137) (meaning t m 2156) (meaning t m 2274) (meaning t m 2839) (meaning t m 2842) (meaning t m 3585) source

theorem rule27395 (p2383 p3063 p5016 : Prop) (h : (¬ p5016) ∨ (¬ p2383) ∨ p3063) : (¬ p2383) ∨ (p3063) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial27395 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2383)) ∨ (meaning t m 3063) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory16651 (m.theta 0 6) (m.theta 1 6) (m.theta 6 8)
  exact rule27395 (meaning t m 2383) (meaning t m 3063) (meaning t m 5016) source

theorem rule27399 (p3591 p3860 p4371 : Prop) (h : (¬ p4371) ∨ (¬ p3591) ∨ p3860) : (¬ p3591) ∨ (p3860) ∨ (¬ p4371) := by
  classical
  tauto

theorem initial27399 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3591)) ∨ (meaning t m 3860) ∨ (¬ (meaning t m 4371)) := by
  have source := ElevenTheory.theory16655 (m.theta 0 1) (m.theta 1 6) (m.theta 1 8)
  exact rule27399 (meaning t m 3591) (meaning t m 3860) (meaning t m 4371) source

theorem rule27400 (p2027 p2373 p2850 p3876 p3988 p4001 p4555 : Prop) (h : p2027 ∨ (¬ p3988) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p4555) ∨ (¬ p4001) ∨ (¬ p2373)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p3988) ∨ (¬ p4001) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial27400 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory16656 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule27400 (meaning t m 2027) (meaning t m 2373) (meaning t m 2850) (meaning t m 3876) (meaning t m 3988) (meaning t m 4001) (meaning t m 4555) source

theorem rule27401 (p2027 p2220 p2247 p3146 p4111 p4256 p4348 p4438 p4521 : Prop) (h : (¬ p4521) ∨ (¬ p4256) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p4111) ∨ (¬ p2220) ∨ (¬ p4438) ∨ (¬ p3146) ∨ (¬ p4348)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2247) ∨ (¬ p3146) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial27401 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory16657 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 3) (m.theta 3 4) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27401 (meaning t m 2027) (meaning t m 2220) (meaning t m 2247) (meaning t m 3146) (meaning t m 4111) (meaning t m 4256) (meaning t m 4348) (meaning t m 4438) (meaning t m 4521) source

theorem rule27402 (p2027 p2470 p2542 p2589 p3874 p4750 : Prop) (h : (¬ p4750) ∨ (¬ p3874) ∨ (¬ p2542) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p2589)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3874) ∨ (¬ p4750) := by
  classical
  tauto

theorem initial27402 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4750)) := by
  have source := ElevenTheory.theory16658 t (m.theta 0 4) (m.theta 2 4) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8)
  exact rule27402 (meaning t m 2027) (meaning t m 2470) (meaning t m 2542) (meaning t m 2589) (meaning t m 3874) (meaning t m 4750) source

theorem rule27406 (p2027 p2132 p2619 p2780 p3745 p4337 p4509 : Prop) (h : (¬ p2780) ∨ (¬ p2132) ∨ (¬ p4337) ∨ (¬ p3745) ∨ (¬ p2619) ∨ (¬ p4509) ∨ p2027) : (p2027) ∨ (¬ p2132) ∨ (¬ p2619) ∨ (¬ p2780) ∨ (¬ p3745) ∨ (¬ p4337) ∨ (¬ p4509) := by
  classical
  tauto

theorem initial27406 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 3745)) ∨ (¬ (meaning t m 4337)) ∨ (¬ (meaning t m 4509)) := by
  have source := ElevenTheory.theory16662 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 6) (m.theta 5 6) (m.theta 5 8)
  exact rule27406 (meaning t m 2027) (meaning t m 2132) (meaning t m 2619) (meaning t m 2780) (meaning t m 3745) (meaning t m 4337) (meaning t m 4509) source

theorem rule27407 (p2027 p2177 p2598 p2850 p2982 p3551 p4107 p4395 p5260 : Prop) (h : (¬ p2982) ∨ (¬ p4395) ∨ (¬ p2177) ∨ (¬ p4107) ∨ (¬ p2850) ∨ (¬ p5260) ∨ (¬ p2598) ∨ (¬ p3551) ∨ p2027) : (p2027) ∨ (¬ p2177) ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3551) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p5260) := by
  classical
  tauto

theorem initial27407 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 5260)) := by
  have source := ElevenTheory.theory16663 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27407 (meaning t m 2027) (meaning t m 2177) (meaning t m 2598) (meaning t m 2850) (meaning t m 2982) (meaning t m 3551) (meaning t m 4107) (meaning t m 4395) (meaning t m 5260) source

theorem rule27408 (p1990 p2027 p2563 p2611 p2651 p2810 p3136 p4117 p4241 : Prop) (h : (¬ p2563) ∨ (¬ p1990) ∨ p2027 ∨ (¬ p3136) ∨ p2611 ∨ (¬ p2810) ∨ (¬ p2651) ∨ (¬ p4241) ∨ (¬ p4117)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2563) ∨ (p2611) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4117) ∨ (¬ p4241) := by
  classical
  tauto

theorem initial27408 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4241)) := by
  have source := ElevenTheory.theory16664 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule27408 (meaning t m 1990) (meaning t m 2027) (meaning t m 2563) (meaning t m 2611) (meaning t m 2651) (meaning t m 2810) (meaning t m 3136) (meaning t m 4117) (meaning t m 4241) source

theorem rule27410 (p2027 p2696 p2753 p2797 p3266 p3323 p3645 p4032 p4322 p4330 p4877 : Prop) (h : (¬ p4330) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p3266) ∨ p2027 ∨ (¬ p3323) ∨ (¬ p4877) ∨ (¬ p4032) ∨ (¬ p2753) ∨ (¬ p3645) ∨ (¬ p4322)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2797) ∨ (¬ p3266) ∨ (¬ p3323) ∨ (¬ p3645) ∨ (¬ p4032) ∨ (¬ p4322) ∨ (¬ p4330) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial27410 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory16666 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 3 6) (m.theta 5 9) (m.theta 6 9) (m.theta 8 9) (m.theta 9 10)
  exact rule27410 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 2797) (meaning t m 3266) (meaning t m 3323) (meaning t m 3645) (meaning t m 4032) (meaning t m 4322) (meaning t m 4330) (meaning t m 4877) source

theorem rule27413 (p2027 p2579 p2588 p3073 p3347 p3449 p3954 p4107 p4669 p5216 : Prop) (h : (¬ p3954) ∨ (¬ p5216) ∨ p2027 ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p2588) ∨ (¬ p3449) ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3073)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3073) ∨ (¬ p3347) ∨ (¬ p3449) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4669) ∨ (¬ p5216) := by
  classical
  tauto

theorem initial27413 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3347)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) ∨ (¬ (meaning t m 5216)) := by
  have source := ElevenTheory.theory16669 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule27413 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3073) (meaning t m 3347) (meaning t m 3449) (meaning t m 3954) (meaning t m 4107) (meaning t m 4669) (meaning t m 5216) source

theorem rule27415 (p4382 p4669 p5059 : Prop) (h : (¬ p4669) ∨ (¬ p4382) ∨ p5059) : (¬ p4382) ∨ (¬ p4669) ∨ (p5059) := by
  classical
  tauto

theorem initial27415 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4669)) ∨ (meaning t m 5059) := by
  have source := ElevenTheory.theory16671 t (m.theta 5 9) (m.theta 7 9) (m.theta 8 9)
  exact rule27415 (meaning t m 4382) (meaning t m 4669) (meaning t m 5059) source

theorem rule27416 (p2027 p2630 p2696 p2753 p2761 p3204 p3343 p3946 p4191 p4512 p4638 p4877 : Prop) (h : (¬ p4191) ∨ (¬ p4638) ∨ (¬ p2696) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p2753) ∨ (¬ p4877) ∨ (¬ p2630) ∨ (¬ p3946) ∨ (¬ p3204) ∨ (¬ p4512)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p3204) ∨ (¬ p3343) ∨ (¬ p3946) ∨ (¬ p4191) ∨ (¬ p4512) ∨ (¬ p4638) ∨ (¬ p4877) := by
  classical
  tauto

theorem initial27416 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4877)) := by
  have source := ElevenTheory.theory16672 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule27416 (meaning t m 2027) (meaning t m 2630) (meaning t m 2696) (meaning t m 2753) (meaning t m 2761) (meaning t m 3204) (meaning t m 3343) (meaning t m 3946) (meaning t m 4191) (meaning t m 4512) (meaning t m 4638) (meaning t m 4877) source

theorem rule27418 (p2027 p2187 p3016 p3958 p4256 p4432 : Prop) (h : p2027 ∨ (¬ p4432) ∨ (¬ p3958) ∨ (¬ p2187) ∨ (¬ p3016) ∨ (¬ p4256)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3016) ∨ (¬ p3958) ∨ (¬ p4256) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial27418 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3958)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory16674 t (m.theta 3 4) (m.theta 4 6) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8)
  exact rule27418 (meaning t m 2027) (meaning t m 2187) (meaning t m 3016) (meaning t m 3958) (meaning t m 4256) (meaning t m 4432) source

theorem rule27419 (p2027 p2589 p2685 p3166 p3690 p3877 p3931 p4117 p4235 p4729 p4830 : Prop) (h : (¬ p3690) ∨ (¬ p3166) ∨ (¬ p4830) ∨ (¬ p4117) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2589) ∨ (¬ p3931)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2685) ∨ (¬ p3166) ∨ (¬ p3690) ∨ (¬ p3877) ∨ (¬ p3931) ∨ (¬ p4117) ∨ (¬ p4235) ∨ (¬ p4729) ∨ (¬ p4830) := by
  classical
  tauto

theorem initial27419 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4729)) ∨ (¬ (meaning t m 4830)) := by
  have source := ElevenTheory.theory16675 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 7 9)
  exact rule27419 (meaning t m 2027) (meaning t m 2589) (meaning t m 2685) (meaning t m 3166) (meaning t m 3690) (meaning t m 3877) (meaning t m 3931) (meaning t m 4117) (meaning t m 4235) (meaning t m 4729) (meaning t m 4830) source

theorem rule27420 (p2027 p2246 p2651 p2749 p2810 p3097 p3645 p3646 p3755 p4107 p4638 p4877 p5175 : Prop) (h : (¬ p3646) ∨ (¬ p3645) ∨ p2027 ∨ (¬ p4877) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2246) ∨ (¬ p2810) ∨ (¬ p4107) ∨ (¬ p3097) ∨ (¬ p3755) ∨ (¬ p4638) ∨ (¬ p5175)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2749) ∨ (¬ p2810) ∨ (¬ p3097) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4877) ∨ (¬ p5175) := by
  classical
  tauto

theorem initial27420 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4638)) ∨ (¬ (meaning t m 4877)) ∨ (¬ (meaning t m 5175)) := by
  have source := ElevenTheory.theory16676 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 9) (m.theta 4 9) (m.theta 5 6) (m.theta 6 7) (m.theta 7 9)
  exact rule27420 (meaning t m 2027) (meaning t m 2246) (meaning t m 2651) (meaning t m 2749) (meaning t m 2810) (meaning t m 3097) (meaning t m 3645) (meaning t m 3646) (meaning t m 3755) (meaning t m 4107) (meaning t m 4638) (meaning t m 4877) (meaning t m 5175) source

theorem rule27421 (p2027 p2145 p2459 p2651 p2810 p3005 p3692 p4117 p4120 p4550 : Prop) (h : (¬ p2651) ∨ (¬ p3692) ∨ (¬ p2810) ∨ (¬ p2459) ∨ (¬ p4120) ∨ (¬ p4550) ∨ (¬ p4117) ∨ (¬ p2145) ∨ p2027 ∨ (¬ p3005)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2459) ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3692) ∨ (¬ p4117) ∨ (¬ p4120) ∨ (¬ p4550) := by
  classical
  tauto

theorem initial27421 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4550)) := by
  have source := ElevenTheory.theory16677 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27421 (meaning t m 2027) (meaning t m 2145) (meaning t m 2459) (meaning t m 2651) (meaning t m 2810) (meaning t m 3005) (meaning t m 3692) (meaning t m 4117) (meaning t m 4120) (meaning t m 4550) source

theorem rule27434 (p2553 p3322 p3564 p3955 : Prop) (h : (¬ p3564) ∨ (¬ p3322) ∨ (¬ p3955) ∨ p2553) : (p2553) ∨ (¬ p3322) ∨ (¬ p3564) ∨ (¬ p3955) := by
  classical
  tauto

theorem initial27434 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2553) ∨ (¬ (meaning t m 3322)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3955)) := by
  have source := ElevenTheory.theory16690 (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule27434 (meaning t m 2553) (meaning t m 3322) (meaning t m 3564) (meaning t m 3955) source

theorem rule27437 (p2010 p2027 p2493 p2699 p3201 p3379 p3584 : Prop) (h : p2699 ∨ (¬ p3201) ∨ (¬ p2493) ∨ (¬ p3379) ∨ (¬ p2010) ∨ p2027 ∨ (¬ p3584)) : (¬ p2010) ∨ (p2027) ∨ (¬ p2493) ∨ (p2699) ∨ (¬ p3201) ∨ (¬ p3379) ∨ (¬ p3584) := by
  classical
  tauto

theorem initial27437 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2010)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2493)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3584)) := by
  have source := ElevenTheory.theory16693 t (m.theta 0 1) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 7)
  exact rule27437 (meaning t m 2010) (meaning t m 2027) (meaning t m 2493) (meaning t m 2699) (meaning t m 3201) (meaning t m 3379) (meaning t m 3584) source

theorem rule27439 (p2027 p2156 p2657 p2958 p4173 p4282 p4704 : Prop) (h : (¬ p2657) ∨ p2027 ∨ (¬ p4704) ∨ (¬ p2156) ∨ (¬ p4173) ∨ (¬ p2958) ∨ (¬ p4282)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p4173) ∨ (¬ p4282) ∨ (¬ p4704) := by
  classical
  tauto

theorem initial27439 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2958)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4704)) := by
  have source := ElevenTheory.theory16695 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 5) (m.theta 3 4) (m.theta 3 5) (m.theta 5 6)
  exact rule27439 (meaning t m 2027) (meaning t m 2156) (meaning t m 2657) (meaning t m 2958) (meaning t m 4173) (meaning t m 4282) (meaning t m 4704) source

theorem rule27440 (p2027 p2630 p3170 p3256 p3857 p4121 p4787 : Prop) (h : (¬ p4787) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4121) ∨ (¬ p3170)) : (p2027) ∨ (¬ p2630) ∨ (¬ p3170) ∨ (¬ p3256) ∨ (¬ p3857) ∨ (¬ p4121) ∨ (¬ p4787) := by
  classical
  tauto

theorem initial27440 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 3170)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4787)) := by
  have source := ElevenTheory.theory16696 t (m.theta 0 3) (m.theta 0 8) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule27440 (meaning t m 2027) (meaning t m 2630) (meaning t m 3170) (meaning t m 3256) (meaning t m 3857) (meaning t m 4121) (meaning t m 4787) source

theorem rule27442 (p2027 p2505 p2509 p2588 p3309 p4595 : Prop) (h : (¬ p2505) ∨ p2027 ∨ (¬ p3309) ∨ (¬ p4595) ∨ (¬ p2588) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2505) ∨ (¬ p2509) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p4595) := by
  classical
  tauto

theorem initial27442 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4595)) := by
  have source := ElevenTheory.theory16698 t (m.theta 1 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 7)
  exact rule27442 (meaning t m 2027) (meaning t m 2505) (meaning t m 2509) (meaning t m 2588) (meaning t m 3309) (meaning t m 4595) source

theorem rule27445 (p1982 p2027 p2098 p2138 p2363 p2765 p3758 p4326 : Prop) (h : (¬ p4326) ∨ (¬ p2363) ∨ p2765 ∨ p2027 ∨ (¬ p1982) ∨ (¬ p2138) ∨ (¬ p2098) ∨ (¬ p3758)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2363) ∨ (p2765) ∨ (¬ p3758) ∨ (¬ p4326) := by
  classical
  tauto

theorem initial27445 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2363)) ∨ (meaning t m 2765) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4326)) := by
  have source := ElevenTheory.theory16701 t (m.theta 0 2) (m.theta 2 5) (m.theta 2 8) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule27445 (meaning t m 1982) (meaning t m 2027) (meaning t m 2098) (meaning t m 2138) (meaning t m 2363) (meaning t m 2765) (meaning t m 3758) (meaning t m 4326) source

theorem rule27446 (p2027 p2247 p3767 p3854 p4321 p4439 : Prop) (h : p2027 ∨ (¬ p3854) ∨ (¬ p2247) ∨ (¬ p3767) ∨ (¬ p4321) ∨ (¬ p4439)) : (p2027) ∨ (¬ p2247) ∨ (¬ p3767) ∨ (¬ p3854) ∨ (¬ p4321) ∨ (¬ p4439) := by
  classical
  tauto

theorem initial27446 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 3854)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 4439)) := by
  have source := ElevenTheory.theory16702 t (m.theta 0 1) (m.theta 0 9) (m.theta 1 3) (m.theta 1 9) (m.theta 9 10)
  exact rule27446 (meaning t m 2027) (meaning t m 2247) (meaning t m 3767) (meaning t m 3854) (meaning t m 4321) (meaning t m 4439) source

theorem rule27448 (p2027 p2657 p2807 p2928 p3658 p4777 p4811 : Prop) (h : (¬ p3658) ∨ (¬ p4811) ∨ (¬ p4777) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2807) ∨ (¬ p2928) ∨ (¬ p3658) ∨ (¬ p4777) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial27448 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3658)) ∨ (¬ (meaning t m 4777)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory16704 t (m.theta 0 3) (m.theta 1 4) (m.theta 2 7) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7)
  exact rule27448 (meaning t m 2027) (meaning t m 2657) (meaning t m 2807) (meaning t m 2928) (meaning t m 3658) (meaning t m 4777) (meaning t m 4811) source

theorem rule27451 (p1982 p2027 p2148 p2459 p3051 p3875 p4001 p4149 p5558 : Prop) (h : p2148 ∨ (¬ p4001) ∨ (¬ p3051) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p5558) ∨ (¬ p4149) ∨ (¬ p3875)) : (¬ p1982) ∨ (p2027) ∨ (p2148) ∨ (¬ p2459) ∨ (¬ p3051) ∨ (¬ p3875) ∨ (¬ p4001) ∨ (¬ p4149) ∨ (¬ p5558) := by
  classical
  tauto

theorem initial27451 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3875)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 5558)) := by
  have source := ElevenTheory.theory16707 t (m.theta 0 5) (m.theta 4 7) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27451 (meaning t m 1982) (meaning t m 2027) (meaning t m 2148) (meaning t m 2459) (meaning t m 3051) (meaning t m 3875) (meaning t m 4001) (meaning t m 4149) (meaning t m 5558) source

theorem rule27454 (p2027 p2963 p3324 p3366 p3449 p3452 p4181 p4236 p4347 p4376 p5122 : Prop) (h : (¬ p3324) ∨ (¬ p2963) ∨ (¬ p4347) ∨ (¬ p5122) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p4376) ∨ (¬ p3452) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p4181)) : (p2027) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial27454 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory16710 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27454 (meaning t m 2027) (meaning t m 2963) (meaning t m 3324) (meaning t m 3366) (meaning t m 3449) (meaning t m 3452) (meaning t m 4181) (meaning t m 4236) (meaning t m 4347) (meaning t m 4376) (meaning t m 5122) source

theorem rule27455 (p2027 p2761 p2963 p3051 p3246 p3324 p3366 p3519 p4236 p4376 p4399 p5123 p5580 : Prop) (h : (¬ p3324) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p5123) ∨ (¬ p2963) ∨ (¬ p3519) ∨ (¬ p4399) ∨ (¬ p3051) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p4376) ∨ (¬ p3246) ∨ (¬ p5580)) : (p2027) ∨ (¬ p2761) ∨ (¬ p2963) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4399) ∨ (¬ p5123) ∨ (¬ p5580) := by
  classical
  tauto

theorem initial27455 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5580)) := by
  have source := ElevenTheory.theory16711 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 3 6) (m.theta 5 7) (m.theta 6 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule27455 (meaning t m 2027) (meaning t m 2761) (meaning t m 2963) (meaning t m 3051) (meaning t m 3246) (meaning t m 3324) (meaning t m 3366) (meaning t m 3519) (meaning t m 4236) (meaning t m 4376) (meaning t m 4399) (meaning t m 5123) (meaning t m 5580) source

theorem rule27457 (p1976 p2027 p2299 p2633 p3425 p3791 p4423 : Prop) (h : (¬ p1976) ∨ p2027 ∨ p2633 ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p3791) ∨ (¬ p4423)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3425) ∨ (¬ p3791) ∨ (¬ p4423) := by
  classical
  tauto

theorem initial27457 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4423)) := by
  have source := ElevenTheory.theory16713 t (m.theta 0 2) (m.theta 2 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule27457 (meaning t m 1976) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3425) (meaning t m 3791) (meaning t m 4423) source

theorem rule27463 (p2027 p2122 p2252 p2396 p2534 p2657 p2750 p2829 p3950 p4256 : Prop) (h : (¬ p3950) ∨ (¬ p4256) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p2252) ∨ (¬ p2657) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2122) ∨ (¬ p2396)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3950) ∨ (¬ p4256) := by
  classical
  tauto

theorem initial27463 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4256)) := by
  have source := ElevenTheory.theory16719 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule27463 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2396) (meaning t m 2534) (meaning t m 2657) (meaning t m 2750) (meaning t m 2829) (meaning t m 3950) (meaning t m 4256) source

theorem rule27467 (p4318 p4326 p5315 : Prop) (h : p4318 ∨ (¬ p5315) ∨ (¬ p4326)) : (p4318) ∨ (¬ p4326) ∨ (¬ p5315) := by
  classical
  tauto

theorem initial27467 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 4318) ∨ (¬ (meaning t m 4326)) ∨ (¬ (meaning t m 5315)) := by
  have source := ElevenTheory.theory16723 (m.theta 1 8) (m.theta 2 8) (m.theta 6 8)
  exact rule27467 (meaning t m 4318) (meaning t m 4326) (meaning t m 5315) source

theorem rule27469 (p2122 p4024 p4105 p4427 : Prop) (h : (¬ p4024) ∨ (¬ p4427) ∨ (¬ p2122) ∨ (¬ p4105)) : (¬ p2122) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial27469 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 4024)) ∨ (¬ (meaning t m 4105)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory16725 (m.theta 1 6) (m.theta 1 7) (m.theta 2 6) (m.theta 6 7)
  exact rule27469 (meaning t m 2122) (meaning t m 4024) (meaning t m 4105) (meaning t m 4427) source

theorem rule27472 (p2027 p2187 p2870 p4193 p4358 p4558 : Prop) (h : (¬ p4558) ∨ (¬ p4358) ∨ (¬ p2870) ∨ (¬ p4193) ∨ p2027 ∨ (¬ p2187)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2870) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial27472 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory16728 t (m.theta 2 5) (m.theta 2 6) (m.theta 5 6) (m.theta 5 7) (m.theta 6 8)
  exact rule27472 (meaning t m 2027) (meaning t m 2187) (meaning t m 2870) (meaning t m 4193) (meaning t m 4358) (meaning t m 4558) source

theorem rule27476 (p1975 p2027 p2122 p2699 p3093 p3319 p3917 : Prop) (h : p2699 ∨ (¬ p3917) ∨ (¬ p1975) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p3093) ∨ (¬ p3319)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2122) ∨ (p2699) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3917) := by
  classical
  tauto

theorem initial27476 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3917)) := by
  have source := ElevenTheory.theory16732 t (m.theta 0 1) (m.theta 1 6) (m.theta 2 6) (m.theta 6 7) (m.theta 6 9)
  exact rule27476 (meaning t m 1975) (meaning t m 2027) (meaning t m 2122) (meaning t m 2699) (meaning t m 3093) (meaning t m 3319) (meaning t m 3917) source

theorem rule27477 (p3233 p3379 p3830 : Prop) (h : (¬ p3233) ∨ (¬ p3379) ∨ p3830) : (¬ p3233) ∨ (¬ p3379) ∨ (p3830) := by
  classical
  tauto

theorem initial27477 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3233)) ∨ (¬ (meaning t m 3379)) ∨ (meaning t m 3830) := by
  have source := ElevenTheory.theory16733 (m.theta 0 1) (m.theta 1 4) (m.theta 1 9)
  exact rule27477 (meaning t m 3233) (meaning t m 3379) (meaning t m 3830) source

theorem rule27480 (p2027 p3584 p3683 p4009 p4121 p4286 p4607 p4715 : Prop) (h : (¬ p4009) ∨ (¬ p4715) ∨ (¬ p3584) ∨ (¬ p4607) ∨ p2027 ∨ (¬ p4121) ∨ (¬ p3683) ∨ (¬ p4286)) : (p2027) ∨ (¬ p3584) ∨ (¬ p3683) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286) ∨ (¬ p4607) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial27480 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3683)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4607)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory16736 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 6) (m.theta 4 8) (m.theta 8 10)
  exact rule27480 (meaning t m 2027) (meaning t m 3584) (meaning t m 3683) (meaning t m 4009) (meaning t m 4121) (meaning t m 4286) (meaning t m 4607) (meaning t m 4715) source

theorem rule27483 (p1992 p2027 p2622 p2630 p2657 p2774 p3688 p4236 : Prop) (h : (¬ p1992) ∨ (¬ p2630) ∨ p2622 ∨ (¬ p2774) ∨ (¬ p4236) ∨ (¬ p3688) ∨ (¬ p2657) ∨ p2027) : (¬ p1992) ∨ (p2027) ∨ (p2622) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p3688) ∨ (¬ p4236) := by
  classical
  tauto

theorem initial27483 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4236)) := by
  have source := ElevenTheory.theory16739 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule27483 (meaning t m 1992) (meaning t m 2027) (meaning t m 2622) (meaning t m 2630) (meaning t m 2657) (meaning t m 2774) (meaning t m 3688) (meaning t m 4236) source

theorem rule27484 (p2027 p3055 p3767 p4749 p5352 p5387 p5453 : Prop) (h : (¬ p4749) ∨ (¬ p5352) ∨ p2027 ∨ (¬ p5453) ∨ (¬ p5387) ∨ (¬ p3055) ∨ (¬ p3767)) : (p2027) ∨ (¬ p3055) ∨ (¬ p3767) ∨ (¬ p4749) ∨ (¬ p5352) ∨ (¬ p5387) ∨ (¬ p5453) := by
  classical
  tauto

theorem initial27484 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3767)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5352)) ∨ (¬ (meaning t m 5387)) ∨ (¬ (meaning t m 5453)) := by
  have source := ElevenTheory.theory16740 t (m.theta 0 2) (m.theta 0 9) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 9 10)
  exact rule27484 (meaning t m 2027) (meaning t m 3055) (meaning t m 3767) (meaning t m 4749) (meaning t m 5352) (meaning t m 5387) (meaning t m 5453) source

theorem rule27485 (p2027 p2254 p2518 p3379 p3414 p3947 p4149 p4381 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p2518) ∨ (¬ p3947) ∨ (¬ p2254) ∨ (¬ p3379) ∨ (¬ p4149) ∨ p2027 ∨ (¬ p3414) ∨ (¬ p4381)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3414) ∨ (¬ p3947) ∨ (¬ p4149) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial27485 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory16741 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule27485 (meaning t m 2027) (meaning t m 2254) (meaning t m 2518) (meaning t m 3379) (meaning t m 3414) (meaning t m 3947) (meaning t m 4149) (meaning t m 4381) (meaning t m 5119) source

theorem rule27486 (p2027 p2136 p2619 p2696 p4120 p5049 : Prop) (h : (¬ p4120) ∨ (¬ p2136) ∨ (¬ p5049) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p2619)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2696) ∨ (¬ p4120) ∨ (¬ p5049) := by
  classical
  tauto

theorem initial27486 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 5049)) := by
  have source := ElevenTheory.theory16742 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 2 5) (m.theta 5 8)
  exact rule27486 (meaning t m 2027) (meaning t m 2136) (meaning t m 2619) (meaning t m 2696) (meaning t m 4120) (meaning t m 5049) source

theorem rule27492 (p2922 p3201 p4030 : Prop) (h : (¬ p3201) ∨ (¬ p4030) ∨ p2922) : (p2922) ∨ (¬ p3201) ∨ (¬ p4030) := by
  classical
  tauto

theorem initial27492 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2922) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 4030)) := by
  have source := ElevenTheory.theory16748 (m.theta 1 4) (m.theta 2 4) (m.theta 4 7)
  exact rule27492 (meaning t m 2922) (meaning t m 3201) (meaning t m 4030) source

theorem rule27494 (p2027 p2780 p2946 p3115 p3680 p3822 p4260 p4786 p4831 : Prop) (h : (¬ p2946) ∨ (¬ p4786) ∨ (¬ p3115) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p2780) ∨ (¬ p3822) ∨ (¬ p4831) ∨ (¬ p4260)) : (p2027) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3115) ∨ (¬ p3680) ∨ (¬ p3822) ∨ (¬ p4260) ∨ (¬ p4786) ∨ (¬ p4831) := by
  classical
  tauto

theorem initial27494 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4260)) ∨ (¬ (meaning t m 4786)) ∨ (¬ (meaning t m 4831)) := by
  have source := ElevenTheory.theory16750 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule27494 (meaning t m 2027) (meaning t m 2780) (meaning t m 2946) (meaning t m 3115) (meaning t m 3680) (meaning t m 3822) (meaning t m 4260) (meaning t m 4786) (meaning t m 4831) source

theorem rule27495 (p2027 p2383 p3055 p3323 p3324 p3876 p3987 p4278 p4621 p4786 : Prop) (h : (¬ p4621) ∨ (¬ p3055) ∨ (¬ p3323) ∨ p2027 ∨ (¬ p4786) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p2383) ∨ (¬ p3876) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3055) ∨ (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3876) ∨ (¬ p3987) ∨ (¬ p4278) ∨ (¬ p4621) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial27495 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4621)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory16751 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 6) (m.theta 2 4) (m.theta 3 6) (m.theta 4 7) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9)
  exact rule27495 (meaning t m 2027) (meaning t m 2383) (meaning t m 3055) (meaning t m 3323) (meaning t m 3324) (meaning t m 3876) (meaning t m 3987) (meaning t m 4278) (meaning t m 4621) (meaning t m 4786) source

theorem rule27498 (p2027 p2247 p2588 p2744 p3055 p3093 p3319 p3366 p3584 p4624 : Prop) (h : p2027 ∨ (¬ p2588) ∨ (¬ p4624) ∨ (¬ p3584) ∨ (¬ p3093) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3319) ∨ (¬ p2744) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2588) ∨ (¬ p2744) ∨ (¬ p3055) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p3366) ∨ (¬ p3584) ∨ (¬ p4624) := by
  classical
  tauto

theorem initial27498 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3319)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 4624)) := by
  have source := ElevenTheory.theory16754 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 4) (m.theta 4 6) (m.theta 6 7) (m.theta 6 9)
  exact rule27498 (meaning t m 2027) (meaning t m 2247) (meaning t m 2588) (meaning t m 2744) (meaning t m 3055) (meaning t m 3093) (meaning t m 3319) (meaning t m 3366) (meaning t m 3584) (meaning t m 4624) source

theorem rule27500 (p2027 p3422 p3564 p3874 p4432 p4603 : Prop) (h : (¬ p3874) ∨ (¬ p4432) ∨ (¬ p3422) ∨ (¬ p4603) ∨ p2027 ∨ (¬ p3564)) : (p2027) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p3874) ∨ (¬ p4432) ∨ (¬ p4603) := by
  classical
  tauto

theorem initial27500 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3874)) ∨ (¬ (meaning t m 4432)) ∨ (¬ (meaning t m 4603)) := by
  have source := ElevenTheory.theory16756 t (m.theta 2 4) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 6 9)
  exact rule27500 (meaning t m 2027) (meaning t m 3422) (meaning t m 3564) (meaning t m 3874) (meaning t m 4432) (meaning t m 4603) source

theorem rule27501 (p2210 p3093 p4512 : Prop) (h : (¬ p4512) ∨ (¬ p3093) ∨ p2210) : (p2210) ∨ (¬ p3093) ∨ (¬ p4512) := by
  classical
  tauto

theorem initial27501 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2210) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4512)) := by
  have source := ElevenTheory.theory16757 (m.theta 0 1) (m.theta 1 5) (m.theta 1 6)
  exact rule27501 (meaning t m 2210) (meaning t m 3093) (meaning t m 4512) source

theorem rule27504 (p2027 p2542 p2651 p2780 p2982 p3822 p4107 p4395 p4786 : Prop) (h : p2027 ∨ (¬ p2651) ∨ (¬ p4395) ∨ (¬ p3822) ∨ (¬ p2780) ∨ (¬ p4786) ∨ (¬ p4107) ∨ (¬ p2982) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2982) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4786) := by
  classical
  tauto

theorem initial27504 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4786)) := by
  have source := ElevenTheory.theory16760 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule27504 (meaning t m 2027) (meaning t m 2542) (meaning t m 2651) (meaning t m 2780) (meaning t m 2982) (meaning t m 3822) (meaning t m 4107) (meaning t m 4395) (meaning t m 4786) source

theorem rule27508 (p2027 p2248 p2780 p2946 p3146 p3156 p3822 p3873 p4107 p4669 : Prop) (h : (¬ p2780) ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p3873) ∨ (¬ p2248) ∨ (¬ p2946) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p4669) ∨ (¬ p4107)) : (p2027) ∨ (¬ p2248) ∨ (¬ p2780) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3822) ∨ (¬ p3873) ∨ (¬ p4107) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial27508 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory16764 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule27508 (meaning t m 2027) (meaning t m 2248) (meaning t m 2780) (meaning t m 2946) (meaning t m 3146) (meaning t m 3156) (meaning t m 3822) (meaning t m 3873) (meaning t m 4107) (meaning t m 4669) source

theorem rule27513 (p1985 p2027 p2202 p2911 p3201 p3570 p3684 : Prop) (h : (¬ p1985) ∨ (¬ p3570) ∨ (¬ p3201) ∨ (¬ p3684) ∨ p2202 ∨ p2027 ∨ (¬ p2911)) : (¬ p1985) ∨ (p2027) ∨ (p2202) ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3570) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial27513 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory16769 t (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule27513 (meaning t m 1985) (meaning t m 2027) (meaning t m 2202) (meaning t m 2911) (meaning t m 3201) (meaning t m 3570) (meaning t m 3684) source

theorem rule27514 (p1985 p2027 p2246 p2545 p2807 p2911 p3570 p3579 p4111 : Prop) (h : (¬ p1985) ∨ p2545 ∨ (¬ p2246) ∨ p2027 ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p3570) ∨ (¬ p2807) ∨ (¬ p2911)) : (¬ p1985) ∨ (p2027) ∨ (¬ p2246) ∨ (p2545) ∨ (¬ p2807) ∨ (¬ p2911) ∨ (¬ p3570) ∨ (¬ p3579) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial27514 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory16770 t (m.theta 0 3) (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 5 7) (m.theta 7 8)
  exact rule27514 (meaning t m 1985) (meaning t m 2027) (meaning t m 2246) (meaning t m 2545) (meaning t m 2807) (meaning t m 2911) (meaning t m 3570) (meaning t m 3579) (meaning t m 4111) source

theorem rule27515 (p1990 p2027 p2331 p2545 p2657 p2668 p3989 : Prop) (h : p2027 ∨ (¬ p2657) ∨ p2545 ∨ (¬ p1990) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2331) ∨ (p2545) ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3989) := by
  classical
  tauto

theorem initial27515 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3989)) := by
  have source := ElevenTheory.theory16771 t (m.theta 0 3) (m.theta 3 4) (m.theta 3 6) (m.theta 5 6) (m.theta 6 8)
  exact rule27515 (meaning t m 1990) (meaning t m 2027) (meaning t m 2331) (meaning t m 2545) (meaning t m 2657) (meaning t m 2668) (meaning t m 3989) source

theorem rule27517 (p2299 p2717 p4471 : Prop) (h : (¬ p2299) ∨ (¬ p4471) ∨ (¬ p2717)) : (¬ p2299) ∨ (¬ p2717) ∨ (¬ p4471) := by
  classical
  tauto

theorem initial27517 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 4471)) := by
  have source := ElevenTheory.theory16773 (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27517 (meaning t m 2299) (meaning t m 2717) (meaning t m 4471) source

theorem rule27523 (p2027 p2220 p2579 p3115 p3366 p3370 p3497 p3822 p3905 p4107 p4377 p4390 p4395 : Prop) (h : (¬ p3366) ∨ (¬ p4395) ∨ (¬ p3370) ∨ (¬ p3497) ∨ (¬ p2579) ∨ (¬ p3115) ∨ (¬ p4390) ∨ (¬ p4107) ∨ (¬ p4377) ∨ (¬ p2220) ∨ (¬ p3905) ∨ (¬ p3822) ∨ p2027) : (p2027) ∨ (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3497) ∨ (¬ p3822) ∨ (¬ p3905) ∨ (¬ p4107) ∨ (¬ p4377) ∨ (¬ p4390) ∨ (¬ p4395) := by
  classical
  tauto

theorem initial27523 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4390)) ∨ (¬ (meaning t m 4395)) := by
  have source := ElevenTheory.theory16779 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 6) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule27523 (meaning t m 2027) (meaning t m 2220) (meaning t m 2579) (meaning t m 3115) (meaning t m 3366) (meaning t m 3370) (meaning t m 3497) (meaning t m 3822) (meaning t m 3905) (meaning t m 4107) (meaning t m 4377) (meaning t m 4390) (meaning t m 4395) source

theorem rule27524 (p2012 p2027 p2202 p2579 p3355 p3422 p3684 : Prop) (h : (¬ p2579) ∨ (¬ p3422) ∨ p2202 ∨ (¬ p3684) ∨ (¬ p2012) ∨ p2027 ∨ (¬ p3355)) : (¬ p2012) ∨ (p2027) ∨ (p2202) ∨ (¬ p2579) ∨ (¬ p3355) ∨ (¬ p3422) ∨ (¬ p3684) := by
  classical
  tauto

theorem initial27524 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2012)) ∨ (meaning t m 2027) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3422)) ∨ (¬ (meaning t m 3684)) := by
  have source := ElevenTheory.theory16780 t (m.theta 0 4) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6) (m.theta 4 9)
  exact rule27524 (meaning t m 2012) (meaning t m 2027) (meaning t m 2202) (meaning t m 2579) (meaning t m 3355) (meaning t m 3422) (meaning t m 3684) source

theorem rule27528 (p2027 p2630 p2657 p3471 p4236 p4782 : Prop) (h : (¬ p2657) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p4782) ∨ (¬ p2630) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p3471) ∨ (¬ p4236) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial27528 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory16784 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4)
  exact rule27528 (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 3471) (meaning t m 4236) (meaning t m 4782) source

theorem rule27529 (p2027 p2630 p2657 p2774 p4236 p4845 : Prop) (h : (¬ p4845) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236) ∨ p2027 ∨ (¬ p2774)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p4236) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial27529 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory16785 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule27529 (meaning t m 2027) (meaning t m 2630) (meaning t m 2657) (meaning t m 2774) (meaning t m 4236) (meaning t m 4845) source

theorem rule27535 (p1982 p2027 p2220 p2860 p3146 p3474 p3646 : Prop) (h : (¬ p3646) ∨ (¬ p1982) ∨ p3474 ∨ (¬ p2860) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p2220)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2220) ∨ (¬ p2860) ∨ (¬ p3146) ∨ (p3474) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial27535 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3146)) ∨ (meaning t m 3474) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory16791 t (m.theta 0 5) (m.theta 2 5) (m.theta 5 6) (m.theta 5 8) (m.theta 8 9)
  exact rule27535 (meaning t m 1982) (meaning t m 2027) (meaning t m 2220) (meaning t m 2860) (meaning t m 3146) (meaning t m 3474) (meaning t m 3646) source

theorem rule27536 (p2027 p2156 p2187 p2363 p3055 p3366 p3370 p3876 p4278 p4377 p4669 : Prop) (h : (¬ p3366) ∨ (¬ p4669) ∨ (¬ p2156) ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4278) ∨ (¬ p3876) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2187) ∨ (¬ p3055)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2363) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4377) ∨ (¬ p4669) := by
  classical
  tauto

theorem initial27536 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4669)) := by
  have source := ElevenTheory.theory16792 t (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 2 4) (m.theta 4 7) (m.theta 5 6) (m.theta 6 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27536 (meaning t m 2027) (meaning t m 2156) (meaning t m 2187) (meaning t m 2363) (meaning t m 3055) (meaning t m 3366) (meaning t m 3370) (meaning t m 3876) (meaning t m 4278) (meaning t m 4377) (meaning t m 4669) source

theorem rule27538 (p2027 p2341 p3246 p3365 p3570 p4037 p4195 p4625 p5257 : Prop) (h : (¬ p3246) ∨ (¬ p5257) ∨ (¬ p2341) ∨ (¬ p4037) ∨ (¬ p3365) ∨ (¬ p4195) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p3570)) : (p2027) ∨ (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p5257) := by
  classical
  tauto

theorem initial27538 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5257)) := by
  have source := ElevenTheory.theory16794 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 5 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule27538 (meaning t m 2027) (meaning t m 2341) (meaning t m 3246) (meaning t m 3365) (meaning t m 3570) (meaning t m 4037) (meaning t m 4195) (meaning t m 4625) (meaning t m 5257) source

theorem rule27541 (p2630 p2797 p3019 : Prop) (h : (¬ p3019) ∨ (¬ p2630) ∨ p2797) : (¬ p2630) ∨ (p2797) ∨ (¬ p3019) := by
  classical
  tauto

theorem initial27541 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2630)) ∨ (meaning t m 2797) ∨ (¬ (meaning t m 3019)) := by
  have source := ElevenTheory.theory16797 (m.theta 2 3) (m.theta 3 4) (m.theta 3 6)
  exact rule27541 (meaning t m 2630) (meaning t m 2797) (meaning t m 3019) source

theorem rule27544 (p1976 p2027 p2437 p3008 p3055 p3574 p3876 : Prop) (h : (¬ p3055) ∨ p2027 ∨ (¬ p1976) ∨ (¬ p2437) ∨ p3008 ∨ (¬ p3876) ∨ (¬ p3574)) : (¬ p1976) ∨ (p2027) ∨ (¬ p2437) ∨ (p3008) ∨ (¬ p3055) ∨ (¬ p3574) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial27544 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory16800 t (m.theta 0 2) (m.theta 2 4) (m.theta 3 4) (m.theta 4 6) (m.theta 4 7)
  exact rule27544 (meaning t m 1976) (meaning t m 2027) (meaning t m 2437) (meaning t m 3008) (meaning t m 3055) (meaning t m 3574) (meaning t m 3876) source

theorem rule27545 (p2504 p3923 p3956 : Prop) (h : (¬ p2504) ∨ (¬ p3923) ∨ p3956) : (¬ p2504) ∨ (¬ p3923) ∨ (p3956) := by
  classical
  tauto

theorem initial27545 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 3923)) ∨ (meaning t m 3956) := by
  have source := ElevenTheory.theory16801 (m.theta 1 6) (m.theta 4 6) (m.theta 6 8)
  exact rule27545 (meaning t m 2504) (meaning t m 3923) (meaning t m 3956) source

theorem rule27550 (p1982 p2027 p2406 p2409 p2427 p2459 p2881 : Prop) (h : p2027 ∨ (¬ p1982) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2881) ∨ p2409 ∨ (¬ p2406)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2406) ∨ (p2409) ∨ (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2881) := by
  classical
  tauto

theorem initial27550 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (meaning t m 2409) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2881)) := by
  have source := ElevenTheory.theory16806 t (m.theta 1 4) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule27550 (meaning t m 1982) (meaning t m 2027) (meaning t m 2406) (meaning t m 2409) (meaning t m 2427) (meaning t m 2459) (meaning t m 2881) source

theorem rule27551 (p2027 p2187 p2192 p2210 p2459 p2476 p4133 p4340 p5193 p5373 : Prop) (h : (¬ p5373) ∨ (¬ p2187) ∨ (¬ p2476) ∨ p2027 ∨ (¬ p5193) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2459) ∨ (¬ p2476) ∨ (¬ p4133) ∨ (¬ p4340) ∨ (¬ p5193) ∨ (¬ p5373) := by
  classical
  tauto

theorem initial27551 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5193)) ∨ (¬ (meaning t m 5373)) := by
  have source := ElevenTheory.theory16807 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 2 8) (m.theta 4 8) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27551 (meaning t m 2027) (meaning t m 2187) (meaning t m 2192) (meaning t m 2210) (meaning t m 2459) (meaning t m 2476) (meaning t m 4133) (meaning t m 4340) (meaning t m 5193) (meaning t m 5373) source

theorem rule27552 (p2027 p2088 p2110 p3365 p3685 p4340 p4782 : Prop) (h : (¬ p3685) ∨ (¬ p4782) ∨ p2027 ∨ (¬ p3365) ∨ (¬ p2088) ∨ (¬ p2110) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2110) ∨ (¬ p3365) ∨ (¬ p3685) ∨ (¬ p4340) ∨ (¬ p4782) := by
  classical
  tauto

theorem initial27552 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2110)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3685)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4782)) := by
  have source := ElevenTheory.theory16808 t (m.theta 0 2) (m.theta 0 8) (m.theta 2 3) (m.theta 2 7) (m.theta 2 8) (m.theta 8 9)
  exact rule27552 (meaning t m 2027) (meaning t m 2088) (meaning t m 2110) (meaning t m 3365) (meaning t m 3685) (meaning t m 4340) (meaning t m 4782) source

theorem rule27553 (p1975 p2027 p2307 p2387 p2459 p2633 p3692 p4441 : Prop) (h : (¬ p3692) ∨ p2633 ∨ (¬ p2459) ∨ (¬ p4441) ∨ (¬ p1975) ∨ (¬ p2307) ∨ p2027 ∨ (¬ p2387)) : (¬ p1975) ∨ (p2027) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2459) ∨ (p2633) ∨ (¬ p3692) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial27553 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2459)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory16809 t (m.theta 0 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27553 (meaning t m 1975) (meaning t m 2027) (meaning t m 2307) (meaning t m 2387) (meaning t m 2459) (meaning t m 2633) (meaning t m 3692) (meaning t m 4441) source

theorem rule27555 (p1992 p2027 p2462 p2761 p2785 p3688 p3946 p4191 : Prop) (h : p2027 ∨ (¬ p3946) ∨ (¬ p3688) ∨ p2462 ∨ (¬ p4191) ∨ (¬ p2761) ∨ (¬ p2785) ∨ (¬ p1992)) : (¬ p1992) ∨ (p2027) ∨ (p2462) ∨ (¬ p2761) ∨ (¬ p2785) ∨ (¬ p3688) ∨ (¬ p3946) ∨ (¬ p4191) := by
  classical
  tauto

theorem initial27555 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2462) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4191)) := by
  have source := ElevenTheory.theory16811 t (m.theta 0 6) (m.theta 1 2) (m.theta 2 6) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule27555 (meaning t m 1992) (meaning t m 2027) (meaning t m 2462) (meaning t m 2761) (meaning t m 2785) (meaning t m 3688) (meaning t m 3946) (meaning t m 4191) source

theorem rule27556 (p1985 p2202 p2427 p5119 p5121 : Prop) (h : (¬ p2427) ∨ p2202 ∨ (¬ p1985) ∨ (¬ p5121) ∨ p5119) : (¬ p1985) ∨ (p2202) ∨ (¬ p2427) ∨ (p5119) ∨ (¬ p5121) := by
  classical
  tauto

theorem initial27556 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1985)) ∨ (meaning t m 2202) ∨ (¬ (meaning t m 2427)) ∨ (meaning t m 5119) ∨ (¬ (meaning t m 5121)) := by
  have source := ElevenTheory.theory16812 t (m.theta 4 5) (m.theta 5 7) (m.theta 8 10) (m.theta 9 10)
  exact rule27556 (meaning t m 1985) (meaning t m 2202) (meaning t m 2427) (meaning t m 5119) (meaning t m 5121) source

theorem rule27557 (p1975 p2027 p2148 p2220 p2274 p2563 p3880 : Prop) (h : p2148 ∨ p2027 ∨ (¬ p2220) ∨ (¬ p2563) ∨ (¬ p1975) ∨ (¬ p3880) ∨ (¬ p2274)) : (¬ p1975) ∨ (p2027) ∨ (p2148) ∨ (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3880) := by
  classical
  tauto

theorem initial27557 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1975)) ∨ (meaning t m 2027) ∨ (meaning t m 2148) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3880)) := by
  have source := ElevenTheory.theory16813 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7)
  exact rule27557 (meaning t m 1975) (meaning t m 2027) (meaning t m 2148) (meaning t m 2220) (meaning t m 2274) (meaning t m 2563) (meaning t m 3880) source

theorem rule27558 (p2027 p2247 p2911 p3389 p3568 p3570 p4154 p4556 p5190 : Prop) (h : (¬ p4154) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p3568) ∨ (¬ p2247) ∨ (¬ p3570) ∨ (¬ p4556) ∨ (¬ p3389) ∨ (¬ p2911)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4154) ∨ (¬ p4556) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial27558 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4556)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory16814 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 7) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27558 (meaning t m 2027) (meaning t m 2247) (meaning t m 2911) (meaning t m 3389) (meaning t m 3568) (meaning t m 3570) (meaning t m 4154) (meaning t m 4556) (meaning t m 5190) source

theorem rule27563 (p1997 p2027 p2542 p3441 p4181 p4256 p4286 : Prop) (h : p3441 ∨ (¬ p2542) ∨ (¬ p4286) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4181) ∨ (¬ p4256)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2542) ∨ (p3441) ∨ (¬ p4181) ∨ (¬ p4256) ∨ (¬ p4286) := by
  classical
  tauto

theorem initial27563 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2542)) ∨ (meaning t m 3441) ∨ (¬ (meaning t m 4181)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) := by
  have source := ElevenTheory.theory16819 t (m.theta 1 8) (m.theta 3 4) (m.theta 4 5) (m.theta 4 8) (m.theta 8 10)
  exact rule27563 (meaning t m 1997) (meaning t m 2027) (meaning t m 2542) (meaning t m 3441) (meaning t m 4181) (meaning t m 4256) (meaning t m 4286) source

theorem rule27565 (p3399 p3449 p3544 : Prop) (h : (¬ p3544) ∨ (¬ p3449) ∨ p3399) : (p3399) ∨ (¬ p3449) ∨ (¬ p3544) := by
  classical
  tauto

theorem initial27565 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3399) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3544)) := by
  have source := ElevenTheory.theory16821 (m.theta 0 1) (m.theta 1 7) (m.theta 1 8)
  exact rule27565 (meaning t m 3399) (meaning t m 3449) (meaning t m 3544) source

theorem rule27567 (p2246 p2744 p3366 p4786 : Prop) (h : (¬ p2744) ∨ (¬ p2246) ∨ (¬ p3366) ∨ p4786) : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (p4786) := by
  classical
  tauto

theorem initial27567 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3366)) ∨ (meaning t m 4786) := by
  have source := ElevenTheory.theory16823 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3)
  exact rule27567 (meaning t m 2246) (meaning t m 2744) (meaning t m 3366) (meaning t m 4786) source

theorem rule27569 (p3817 p4324 p4424 : Prop) (h : (¬ p4324) ∨ (¬ p4424) ∨ p3817) : (p3817) ∨ (¬ p4324) ∨ (¬ p4424) := by
  classical
  tauto

theorem initial27569 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 3817) ∨ (¬ (meaning t m 4324)) ∨ (¬ (meaning t m 4424)) := by
  have source := ElevenTheory.theory16825 (m.theta 1 7) (m.theta 2 7) (m.theta 7 9)
  exact rule27569 (meaning t m 3817) (meaning t m 4324) (meaning t m 4424) source

theorem rule27570 (p3461 p3767 p4038 : Prop) (h : (¬ p4038) ∨ (¬ p3461) ∨ p3767) : (¬ p3461) ∨ (p3767) ∨ (¬ p4038) := by
  classical
  tauto

theorem initial27570 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3461)) ∨ (meaning t m 3767) ∨ (¬ (meaning t m 4038)) := by
  have source := ElevenTheory.theory16826 (m.theta 0 9) (m.theta 6 9) (m.theta 9 10)
  exact rule27570 (meaning t m 3461) (meaning t m 3767) (meaning t m 4038) source

theorem rule27572 (p2027 p2136 p2247 p2299 p2744 p3083 p3097 p3366 p3379 p3487 p3646 p4420 : Prop) (h : (¬ p3083) ∨ (¬ p4420) ∨ (¬ p2299) ∨ (¬ p3487) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3646) ∨ (¬ p2136) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3097)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2247) ∨ (¬ p2299) ∨ (¬ p2744) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3646) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial27572 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3487)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory16828 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 4 8) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule27572 (meaning t m 2027) (meaning t m 2136) (meaning t m 2247) (meaning t m 2299) (meaning t m 2744) (meaning t m 3083) (meaning t m 3097) (meaning t m 3366) (meaning t m 3379) (meaning t m 3487) (meaning t m 3646) (meaning t m 4420) source

theorem rule27574 (p1982 p2027 p2363 p2553 p3008 p3063 p3549 : Prop) (h : (¬ p3549) ∨ (¬ p2553) ∨ p3008 ∨ (¬ p2363) ∨ (¬ p1982) ∨ p2027 ∨ (¬ p3063)) : (¬ p1982) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2553) ∨ (p3008) ∨ (¬ p3063) ∨ (¬ p3549) := by
  classical
  tauto

theorem initial27574 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1982)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2553)) ∨ (meaning t m 3008) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) := by
  have source := ElevenTheory.theory16830 t (m.theta 1 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 8 9)
  exact rule27574 (meaning t m 1982) (meaning t m 2027) (meaning t m 2363) (meaning t m 2553) (meaning t m 3008) (meaning t m 3063) (meaning t m 3549) source

theorem rule27576 (p2027 p3591 p3830 p4037 p4761 p5152 : Prop) (h : (¬ p5152) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4037) ∨ p2027 ∨ (¬ p4761)) : (p2027) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p4037) ∨ (¬ p4761) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial27576 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4761)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory16832 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 3 6) (m.theta 6 9)
  exact rule27576 (meaning t m 2027) (meaning t m 3591) (meaning t m 3830) (meaning t m 4037) (meaning t m 4761) (meaning t m 5152) source

theorem rule27577 (p2027 p2247 p2363 p2383 p3266 p3662 p5017 p5405 p5740 : Prop) (h : (¬ p2363) ∨ (¬ p5017) ∨ p2027 ∨ (¬ p5740) ∨ (¬ p3266) ∨ (¬ p5405) ∨ (¬ p3662) ∨ (¬ p2383) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3662) ∨ (¬ p5017) ∨ (¬ p5405) ∨ (¬ p5740) := by
  classical
  tauto

theorem initial27577 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 5017)) ∨ (¬ (meaning t m 5405)) ∨ (¬ (meaning t m 5740)) := by
  have source := ElevenTheory.theory16833 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 5 10) (m.theta 6 8) (m.theta 8 9) (m.theta 9 10)
  exact rule27577 (meaning t m 2027) (meaning t m 2247) (meaning t m 2363) (meaning t m 2383) (meaning t m 3266) (meaning t m 3662) (meaning t m 5017) (meaning t m 5405) (meaning t m 5740) source

theorem rule27580 (p1992 p2027 p2764 p3363 p3540 p3585 p4278 p4381 : Prop) (h : (¬ p3363) ∨ (¬ p1992) ∨ p2764 ∨ (¬ p4278) ∨ p2027 ∨ (¬ p3540) ∨ (¬ p4381) ∨ (¬ p3585)) : (¬ p1992) ∨ (p2027) ∨ (p2764) ∨ (¬ p3363) ∨ (¬ p3540) ∨ (¬ p3585) ∨ (¬ p4278) ∨ (¬ p4381) := by
  classical
  tauto

theorem initial27580 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4381)) := by
  have source := ElevenTheory.theory16836 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 4 7) (m.theta 7 9) (m.theta 9 10)
  exact rule27580 (meaning t m 1992) (meaning t m 2027) (meaning t m 2764) (meaning t m 3363) (meaning t m 3540) (meaning t m 3585) (meaning t m 4278) (meaning t m 4381) source

theorem rule27581 (p3553 p3579 p3644 : Prop) (h : (¬ p3579) ∨ (¬ p3553) ∨ p3644) : (¬ p3553) ∨ (¬ p3579) ∨ (p3644) := by
  classical
  tauto

theorem initial27581 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3553)) ∨ (¬ (meaning t m 3579)) ∨ (meaning t m 3644) := by
  have source := ElevenTheory.theory16837 (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule27581 (meaning t m 3553) (meaning t m 3579) (meaning t m 3644) source

theorem rule27582 (p1984 p2027 p2545 p2707 p2743 p2810 p3425 p3873 : Prop) (h : (¬ p2810) ∨ p2545 ∨ p2027 ∨ (¬ p2743) ∨ (¬ p1984) ∨ (¬ p2707) ∨ (¬ p3425) ∨ (¬ p3873)) : (¬ p1984) ∨ (p2027) ∨ (p2545) ∨ (¬ p2707) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3425) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial27582 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2545) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory16838 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 3 4)
  exact rule27582 (meaning t m 1984) (meaning t m 2027) (meaning t m 2545) (meaning t m 2707) (meaning t m 2743) (meaning t m 2810) (meaning t m 3425) (meaning t m 3873) source

theorem rule27583 (p2810 p3572 p3580 : Prop) (h : (¬ p3572) ∨ (¬ p3580) ∨ p2810) : (p2810) ∨ (¬ p3572) ∨ (¬ p3580) := by
  classical
  tauto

theorem initial27583 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2810) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 3580)) := by
  have source := ElevenTheory.theory16839 (m.theta 2 3) (m.theta 3 4) (m.theta 3 7)
  exact rule27583 (meaning t m 2810) (meaning t m 3572) (meaning t m 3580) source

theorem rule27585 (p2027 p2187 p2248 p2284 p2707 p2946 p3425 p3873 p4242 p4863 : Prop) (h : p2027 ∨ (¬ p2707) ∨ (¬ p2187) ∨ (¬ p4242) ∨ (¬ p3425) ∨ (¬ p2284) ∨ (¬ p3873) ∨ (¬ p4863) ∨ (¬ p2248) ∨ (¬ p2946)) : (p2027) ∨ (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2707) ∨ (¬ p2946) ∨ (¬ p3425) ∨ (¬ p3873) ∨ (¬ p4242) ∨ (¬ p4863) := by
  classical
  tauto

theorem initial27585 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4863)) := by
  have source := ElevenTheory.theory16841 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 2 8) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule27585 (meaning t m 2027) (meaning t m 2187) (meaning t m 2248) (meaning t m 2284) (meaning t m 2707) (meaning t m 2946) (meaning t m 3425) (meaning t m 3873) (meaning t m 4242) (meaning t m 4863) source

theorem rule27586 (p2667 p2782 p4846 : Prop) (h : (¬ p2667) ∨ (¬ p4846) ∨ p2782) : (¬ p2667) ∨ (p2782) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial27586 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2667)) ∨ (meaning t m 2782) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory16842 t (m.theta 0 6) (m.theta 2 6) (m.theta 3 6)
  exact rule27586 (meaning t m 2667) (meaning t m 2782) (meaning t m 4846) source

theorem rule27588 (p2027 p2313 p2598 p2753 p2850 p3204 p3727 p4107 p4381 p4870 p5400 : Prop) (h : (¬ p2313) ∨ (¬ p3727) ∨ (¬ p5400) ∨ p2027 ∨ (¬ p3204) ∨ (¬ p2753) ∨ (¬ p4870) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p2850) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3727) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) := by
  classical
  tauto

theorem initial27588 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3727)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4870)) ∨ (¬ (meaning t m 5400)) := by
  have source := ElevenTheory.theory16844 t (m.theta 0 2) (m.theta 0 6) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 10) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule27588 (meaning t m 2027) (meaning t m 2313) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 3204) (meaning t m 3727) (meaning t m 4107) (meaning t m 4381) (meaning t m 4870) (meaning t m 5400) source

theorem rule27590 (p1998 p2027 p2363 p2819 p2997 p3822 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p2363) ∨ p2997 ∨ p2027 ∨ (¬ p1998) ∨ (¬ p3822) ∨ (¬ p2819)) : (¬ p1998) ∨ (p2027) ∨ (¬ p2363) ∨ (¬ p2819) ∨ (p2997) ∨ (¬ p3822) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial27590 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1998)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2819)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory16846 t (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27590 (meaning t m 1998) (meaning t m 2027) (meaning t m 2363) (meaning t m 2819) (meaning t m 2997) (meaning t m 3822) (meaning t m 4348) source

theorem rule27592 (p2027 p2145 p2685 p2696 p3692 p3931 p4120 p4444 p4826 : Prop) (h : (¬ p2696) ∨ (¬ p2685) ∨ (¬ p4826) ∨ (¬ p2145) ∨ (¬ p3692) ∨ p2027 ∨ (¬ p3931) ∨ (¬ p4120) ∨ (¬ p4444)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3692) ∨ (¬ p3931) ∨ (¬ p4120) ∨ (¬ p4444) ∨ (¬ p4826) := by
  classical
  tauto

theorem initial27592 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3931)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4444)) ∨ (¬ (meaning t m 4826)) := by
  have source := ElevenTheory.theory16848 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 7) (m.theta 5 8) (m.theta 7 10) (m.theta 8 9) (m.theta 9 10)
  exact rule27592 (meaning t m 2027) (meaning t m 2145) (meaning t m 2685) (meaning t m 2696) (meaning t m 3692) (meaning t m 3931) (meaning t m 4120) (meaning t m 4444) (meaning t m 4826) source

theorem rule27593 (p2027 p2579 p2588 p3619 p3670 p4107 p4322 p4395 p4729 : Prop) (h : (¬ p2588) ∨ p2027 ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p2579) ∨ (¬ p4322) ∨ (¬ p4107) ∨ (¬ p4729) ∨ (¬ p4395)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3619) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4322) ∨ (¬ p4395) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial27593 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 3619)) ∨ (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4322)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory16849 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 9) (m.theta 4 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule27593 (meaning t m 2027) (meaning t m 2579) (meaning t m 2588) (meaning t m 3619) (meaning t m 3670) (meaning t m 4107) (meaning t m 4322) (meaning t m 4395) (meaning t m 4729) source

theorem rule27597 (p2011 p2027 p2563 p2938 p3212 p3646 p4235 : Prop) (h : (¬ p2011) ∨ p2027 ∨ (¬ p4235) ∨ (¬ p3212) ∨ p2938 ∨ (¬ p3646) ∨ (¬ p2563)) : (¬ p2011) ∨ (p2027) ∨ (¬ p2563) ∨ (p2938) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4235) := by
  classical
  tauto

theorem initial27597 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (meaning t m 2938) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4235)) := by
  have source := ElevenTheory.theory16853 t (m.theta 0 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 5 9)
  exact rule27597 (meaning t m 2011) (meaning t m 2027) (meaning t m 2563) (meaning t m 2938) (meaning t m 3212) (meaning t m 3646) (meaning t m 4235) source

theorem rule27598 (p2027 p2264 p2459 p2589 p2807 p3744 p4110 p4117 p4604 p4729 : Prop) (h : (¬ p4604) ∨ (¬ p2807) ∨ (¬ p2264) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p4729) ∨ (¬ p2459) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2589) ∨ (¬ p2807) ∨ (¬ p3744) ∨ (¬ p4110) ∨ (¬ p4117) ∨ (¬ p4604) ∨ (¬ p4729) := by
  classical
  tauto

theorem initial27598 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 4729)) := by
  have source := ElevenTheory.theory16854 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule27598 (meaning t m 2027) (meaning t m 2264) (meaning t m 2459) (meaning t m 2589) (meaning t m 2807) (meaning t m 3744) (meaning t m 4110) (meaning t m 4117) (meaning t m 4604) (meaning t m 4729) source

theorem rule27599 (p1983 p2027 p2417 p2437 p2622 p2662 p2743 p3367 p3759 : Prop) (h : (¬ p2662) ∨ (¬ p3367) ∨ (¬ p2417) ∨ (¬ p3759) ∨ (¬ p1983) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2743) ∨ p2622) : (¬ p1983) ∨ (p2027) ∨ (¬ p2417) ∨ (¬ p2437) ∨ (p2622) ∨ (¬ p2662) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3759) := by
  classical
  tauto

theorem initial27599 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1983)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2437)) ∨ (meaning t m 2622) ∨ (¬ (meaning t m 2662)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3367)) ∨ (¬ (meaning t m 3759)) := by
  have source := ElevenTheory.theory16855 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 4 7) (m.theta 7 9)
  exact rule27599 (meaning t m 1983) (meaning t m 2027) (meaning t m 2417) (meaning t m 2437) (meaning t m 2622) (meaning t m 2662) (meaning t m 2743) (meaning t m 3367) (meaning t m 3759) source

theorem rule27605 (p2027 p2406 p2509 p2563 p3693 p4507 : Prop) (h : (¬ p4507) ∨ (¬ p2509) ∨ (¬ p3693) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507) := by
  classical
  tauto

theorem initial27605 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3693)) ∨ (¬ (meaning t m 4507)) := by
  have source := ElevenTheory.theory16861 t (m.theta 1 4) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6) (m.theta 5 8)
  exact rule27605 (meaning t m 2027) (meaning t m 2406) (meaning t m 2509) (meaning t m 2563) (meaning t m 3693) (meaning t m 4507) source

theorem rule27606 (p1997 p2027 p2192 p2764 p4033 p4110 p4191 p4363 : Prop) (h : (¬ p2192) ∨ (¬ p4110) ∨ p2764 ∨ (¬ p4033) ∨ (¬ p1997) ∨ p2027 ∨ (¬ p4191) ∨ (¬ p4363)) : (¬ p1997) ∨ (p2027) ∨ (¬ p2192) ∨ (p2764) ∨ (¬ p4033) ∨ (¬ p4110) ∨ (¬ p4191) ∨ (¬ p4363) := by
  classical
  tauto

theorem initial27606 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (meaning t m 2764) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4363)) := by
  have source := ElevenTheory.theory16862 t (m.theta 1 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9) (m.theta 9 10)
  exact rule27606 (meaning t m 1997) (meaning t m 2027) (meaning t m 2192) (meaning t m 2764) (meaning t m 4033) (meaning t m 4110) (meaning t m 4191) (meaning t m 4363) source

theorem rule27608 (p2027 p2352 p3323 p3568 p4137 p4405 : Prop) (h : p2027 ∨ (¬ p2352) ∨ (¬ p4405) ∨ (¬ p4137) ∨ (¬ p3568) ∨ (¬ p3323)) : (p2027) ∨ (¬ p2352) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4137) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial27608 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3568)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory16864 t (m.theta 3 6) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 6 9)
  exact rule27608 (meaning t m 2027) (meaning t m 2352) (meaning t m 3323) (meaning t m 3568) (meaning t m 4137) (meaning t m 4405) source

theorem rule27612 (p1997 p2027 p2299 p2633 p3791 p4110 p4204 p5660 : Prop) (h : (¬ p3791) ∨ p2027 ∨ (¬ p1997) ∨ (¬ p4110) ∨ (¬ p4204) ∨ (¬ p5660) ∨ (¬ p2299) ∨ p2633) : (¬ p1997) ∨ (p2027) ∨ (¬ p2299) ∨ (p2633) ∨ (¬ p3791) ∨ (¬ p4110) ∨ (¬ p4204) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial27612 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1997)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4204)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory16868 t (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 10) (m.theta 7 8)
  exact rule27612 (meaning t m 1997) (meaning t m 2027) (meaning t m 2299) (meaning t m 2633) (meaning t m 3791) (meaning t m 4110) (meaning t m 4204) (meaning t m 5660) source

theorem rule27614 (p2027 p2138 p2247 p2744 p3063 p3093 p3097 p3366 p3758 p4405 : Prop) (h : (¬ p2247) ∨ (¬ p3063) ∨ (¬ p4405) ∨ (¬ p3366) ∨ (¬ p3093) ∨ (¬ p2744) ∨ (¬ p2138) ∨ (¬ p3097) ∨ p2027 ∨ (¬ p3758)) : (p2027) ∨ (¬ p2138) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3097) ∨ (¬ p3366) ∨ (¬ p3758) ∨ (¬ p4405) := by
  classical
  tauto

theorem initial27614 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2138)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4405)) := by
  have source := ElevenTheory.theory16870 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 6) (m.theta 2 5) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8)
  exact rule27614 (meaning t m 2027) (meaning t m 2138) (meaning t m 2247) (meaning t m 2744) (meaning t m 3063) (meaning t m 3093) (meaning t m 3097) (meaning t m 3366) (meaning t m 3758) (meaning t m 4405) source

theorem rule27617 (p1992 p2027 p2169 p2363 p2608 p3692 p3860 p3906 : Prop) (h : (¬ p3906) ∨ (¬ p1992) ∨ (¬ p3860) ∨ p2169 ∨ p2027 ∨ (¬ p2608) ∨ (¬ p2363) ∨ (¬ p3692)) : (¬ p1992) ∨ (p2027) ∨ (p2169) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3692) ∨ (¬ p3860) ∨ (¬ p3906) := by
  classical
  tauto

theorem initial27617 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2169) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) := by
  have source := ElevenTheory.theory16873 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 8) (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule27617 (meaning t m 1992) (meaning t m 2027) (meaning t m 2169) (meaning t m 2363) (meaning t m 2608) (meaning t m 3692) (meaning t m 3860) (meaning t m 3906) source

theorem rule27620 (p3692 p4347 p4441 : Prop) (h : (¬ p3692) ∨ (¬ p4441) ∨ p4347) : (¬ p3692) ∨ (p4347) ∨ (¬ p4441) := by
  classical
  tauto

theorem initial27620 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3692)) ∨ (meaning t m 4347) ∨ (¬ (meaning t m 4441)) := by
  have source := ElevenTheory.theory16876 (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule27620 (meaning t m 3692) (meaning t m 4347) (meaning t m 4441) source

theorem rule27623 (p2027 p2406 p2651 p2952 p3879 p4814 : Prop) (h : p2027 ∨ (¬ p3879) ∨ (¬ p2952) ∨ (¬ p2651) ∨ (¬ p4814) ∨ (¬ p2406)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4814) := by
  classical
  tauto

theorem initial27623 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 4814)) := by
  have source := ElevenTheory.theory16879 t (m.theta 0 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5)
  exact rule27623 (meaning t m 2027) (meaning t m 2406) (meaning t m 2651) (meaning t m 2952) (meaning t m 3879) (meaning t m 4814) source

theorem rule27629 (p1990 p2027 p2331 p2611 p2685 p3097 p3552 p4117 p4195 : Prop) (h : p2027 ∨ (¬ p3552) ∨ (¬ p2685) ∨ (¬ p4117) ∨ p2611 ∨ (¬ p3097) ∨ (¬ p1990) ∨ (¬ p2331) ∨ (¬ p4195)) : (¬ p1990) ∨ (p2027) ∨ (¬ p2331) ∨ (p2611) ∨ (¬ p2685) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4117) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial27629 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1990)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (meaning t m 2611) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory16885 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 3 6) (m.theta 3 7) (m.theta 5 6) (m.theta 6 7)
  exact rule27629 (meaning t m 1990) (meaning t m 2027) (meaning t m 2331) (meaning t m 2611) (meaning t m 2685) (meaning t m 3097) (meaning t m 3552) (meaning t m 4117) (meaning t m 4195) source

theorem rule27631 (p2027 p3527 p3659 p4173 p4344 p4431 p4558 : Prop) (h : (¬ p4431) ∨ (¬ p4344) ∨ (¬ p4173) ∨ p2027 ∨ (¬ p3659) ∨ (¬ p4558) ∨ (¬ p3527)) : (p2027) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p4173) ∨ (¬ p4344) ∨ (¬ p4431) ∨ (¬ p4558) := by
  classical
  tauto

theorem initial27631 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4344)) ∨ (¬ (meaning t m 4431)) ∨ (¬ (meaning t m 4558)) := by
  have source := ElevenTheory.theory16887 t (m.theta 1 5) (m.theta 1 7) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule27631 (meaning t m 2027) (meaning t m 3527) (meaning t m 3659) (meaning t m 4173) (meaning t m 4344) (meaning t m 4431) (meaning t m 4558) source

theorem rule27633 (p2027 p2641 p2696 p2751 p2780 p4337 : Prop) (h : (¬ p4337) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2641) ∨ p2027 ∨ (¬ p2780)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p2780) ∨ (¬ p4337) := by
  classical
  tauto

theorem initial27633 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 2780)) ∨ (¬ (meaning t m 4337)) := by
  have source := ElevenTheory.theory16889 t (m.theta 0 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 6)
  exact rule27633 (meaning t m 2027) (meaning t m 2641) (meaning t m 2696) (meaning t m 2751) (meaning t m 2780) (meaning t m 4337) source

theorem rule27635 (p2027 p2146 p2220 p3146 p4340 p4359 : Prop) (h : (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) ∨ (¬ p2220) ∨ (¬ p2146) ∨ p2027) : (p2027) ∨ (¬ p2146) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p4359) := by
  classical
  tauto

theorem initial27635 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2146)) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4359)) := by
  have source := ElevenTheory.theory16891 t (m.theta 0 5) (m.theta 2 5) (m.theta 2 8) (m.theta 5 8) (m.theta 8 9)
  exact rule27635 (meaning t m 2027) (meaning t m 2146) (meaning t m 2220) (meaning t m 3146) (meaning t m 4340) (meaning t m 4359) source

theorem rule27636 (p2027 p3548 p3631 p4133 p4347 p4636 p4695 : Prop) (h : (¬ p4347) ∨ (¬ p4695) ∨ (¬ p4636) ∨ (¬ p4133) ∨ (¬ p3631) ∨ p2027 ∨ (¬ p3548)) : (p2027) ∨ (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4636) ∨ (¬ p4695) := by
  classical
  tauto

theorem initial27636 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4636)) ∨ (¬ (meaning t m 4695)) := by
  have source := ElevenTheory.theory16892 t (m.theta 1 7) (m.theta 4 9) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27636 (meaning t m 2027) (meaning t m 3548) (meaning t m 3631) (meaning t m 4133) (meaning t m 4347) (meaning t m 4636) (meaning t m 4695) source

theorem rule27638 (p2241 p2748 p3365 p3873 : Prop) (h : (¬ p3365) ∨ (¬ p3873) ∨ (¬ p2748) ∨ (¬ p2241)) : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3365) ∨ (¬ p3873) := by
  classical
  tauto

theorem initial27638 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) := by
  have source := ElevenTheory.theory16894 (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 3)
  exact rule27638 (meaning t m 2241) (meaning t m 2748) (meaning t m 3365) (meaning t m 3873) source

theorem rule27641 (p1976 p2027 p2633 p2737 p3365 p3588 p3659 : Prop) (h : (¬ p3659) ∨ (¬ p1976) ∨ (¬ p3365) ∨ (¬ p2737) ∨ p2027 ∨ (¬ p3588) ∨ p2633) : (¬ p1976) ∨ (p2027) ∨ (p2633) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3588) ∨ (¬ p3659) := by
  classical
  tauto

theorem initial27641 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1976)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3659)) := by
  have source := ElevenTheory.theory16897 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule27641 (meaning t m 1976) (meaning t m 2027) (meaning t m 2633) (meaning t m 2737) (meaning t m 3365) (meaning t m 3588) (meaning t m 3659) source

theorem rule27642 (p2027 p2191 p2248 p2331 p3506 p3555 p3690 p3747 p4191 p4421 p4621 : Prop) (h : (¬ p3555) ∨ (¬ p3747) ∨ (¬ p2191) ∨ (¬ p3690) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p2248) ∨ (¬ p4621) ∨ (¬ p4421) ∨ (¬ p3506) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2191) ∨ (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3555) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4621) := by
  classical
  tauto

theorem initial27642 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2248)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3506)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 3747)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4421)) ∨ (¬ (meaning t m 4621)) := by
  have source := ElevenTheory.theory16898 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 5) (m.theta 3 6) (m.theta 3 9) (m.theta 5 7) (m.theta 5 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule27642 (meaning t m 2027) (meaning t m 2191) (meaning t m 2248) (meaning t m 2331) (meaning t m 3506) (meaning t m 3555) (meaning t m 3690) (meaning t m 3747) (meaning t m 4191) (meaning t m 4421) (meaning t m 4621) source

theorem rule27647 (p2027 p3073 p4189 p4348 p4442 p5559 : Prop) (h : (¬ p4189) ∨ (¬ p3073) ∨ p2027 ∨ (¬ p5559) ∨ (¬ p4348) ∨ (¬ p4442)) : (p2027) ∨ (¬ p3073) ∨ (¬ p4189) ∨ (¬ p4348) ∨ (¬ p4442) ∨ (¬ p5559) := by
  classical
  tauto

theorem initial27647 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 4189)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4442)) ∨ (¬ (meaning t m 5559)) := by
  have source := ElevenTheory.theory16903 t (m.theta 1 7) (m.theta 1 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 9)
  exact rule27647 (meaning t m 2027) (meaning t m 3073) (meaning t m 4189) (meaning t m 4348) (meaning t m 4442) (meaning t m 5559) source

theorem rule27652 (p2027 p2230 p2563 p3125 p3365 p3877 p4118 p4330 p4419 : Prop) (h : (¬ p4419) ∨ (¬ p3877) ∨ (¬ p3365) ∨ p2027 ∨ (¬ p4330) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p4118) ∨ (¬ p3125)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4330) ∨ (¬ p4419) := by
  classical
  tauto

theorem initial27652 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4330)) ∨ (¬ (meaning t m 4419)) := by
  have source := ElevenTheory.theory16908 t (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9) (m.theta 8 9)
  exact rule27652 (meaning t m 2027) (meaning t m 2230) (meaning t m 2563) (meaning t m 3125) (meaning t m 3365) (meaning t m 3877) (meaning t m 4118) (meaning t m 4330) (meaning t m 4419) source

theorem rule27654 (p2027 p2230 p2274 p2563 p3005 p3172 p3366 p3519 p3572 p4236 p4361 p4376 : Prop) (h : (¬ p3366) ∨ (¬ p4376) ∨ p2027 ∨ (¬ p3519) ∨ (¬ p2230) ∨ (¬ p3005) ∨ (¬ p4361) ∨ (¬ p4236) ∨ (¬ p2274) ∨ (¬ p3172) ∨ (¬ p2563) ∨ (¬ p3572)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3572) ∨ (¬ p4236) ∨ (¬ p4361) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial27654 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4236)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory16910 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7)
  exact rule27654 (meaning t m 2027) (meaning t m 2230) (meaning t m 2274) (meaning t m 2563) (meaning t m 3005) (meaning t m 3172) (meaning t m 3366) (meaning t m 3519) (meaning t m 3572) (meaning t m 4236) (meaning t m 4361) (meaning t m 4376) source

theorem rule27655 (p2027 p3115 p3413 p3684 p4750 p4948 : Prop) (h : (¬ p3413) ∨ p2027 ∨ (¬ p4750) ∨ (¬ p3115) ∨ (¬ p4948) ∨ (¬ p3684)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3413) ∨ (¬ p3684) ∨ (¬ p4750) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial27655 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4750)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory16911 t (m.theta 2 4) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 5 9)
  exact rule27655 (meaning t m 2027) (meaning t m 3115) (meaning t m 3413) (meaning t m 3684) (meaning t m 4750) (meaning t m 4948) source

theorem rule27656 (p2027 p2241 p2750 p3631 p3687 p3821 p5206 : Prop) (h : (¬ p2750) ∨ (¬ p5206) ∨ (¬ p3687) ∨ (¬ p3821) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3631)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p3821) ∨ (¬ p5206) := by
  classical
  tauto

theorem initial27656 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 5206)) := by
  have source := ElevenTheory.theory16912 t (m.theta 0 1) (m.theta 0 7) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 7 9)
  exact rule27656 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 3631) (meaning t m 3687) (meaning t m 3821) (meaning t m 5206) source

theorem rule27662 (p2027 p2891 p3556 p3574 p3948 p4031 p4116 p4715 : Prop) (h : p2027 ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p4116) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4715)) : (p2027) ∨ (¬ p2891) ∨ (¬ p3556) ∨ (¬ p3574) ∨ (¬ p3948) ∨ (¬ p4031) ∨ (¬ p4116) ∨ (¬ p4715) := by
  classical
  tauto

theorem initial27662 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3948)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 4715)) := by
  have source := ElevenTheory.theory16918 t (m.theta 0 5) (m.theta 1 4) (m.theta 1 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule27662 (meaning t m 2027) (meaning t m 2891) (meaning t m 3556) (meaning t m 3574) (meaning t m 3948) (meaning t m 4031) (meaning t m 4116) (meaning t m 4715) source

theorem rule27663 (p1986 p2027 p2114 p2470 p2493 p2579 p3541 p3874 : Prop) (h : (¬ p2493) ∨ (¬ p1986) ∨ p2027 ∨ (¬ p3541) ∨ (¬ p2579) ∨ p2114 ∨ (¬ p2470) ∨ (¬ p3874)) : (¬ p1986) ∨ (p2027) ∨ (p2114) ∨ (¬ p2470) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3541) ∨ (¬ p3874) := by
  classical
  tauto

theorem initial27663 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1986)) ∨ (meaning t m 2027) ∨ (meaning t m 2114) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2493)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3874)) := by
  have source := ElevenTheory.theory16919 t (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 4) (m.theta 4 6) (m.theta 4 8)
  exact rule27663 (meaning t m 1986) (meaning t m 2027) (meaning t m 2114) (meaning t m 2470) (meaning t m 2493) (meaning t m 2579) (meaning t m 3541) (meaning t m 3874) source

theorem rule27668 (p2027 p3365 p3366 p3399 p3452 p3631 p3877 p3950 p4118 p4376 : Prop) (h : p2027 ∨ (¬ p3631) ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p3365) ∨ (¬ p3950) ∨ (¬ p3399) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p3452)) : (p2027) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial27668 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory16924 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 4) (m.theta 1 7) (m.theta 2 3) (m.theta 3 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27668 (meaning t m 2027) (meaning t m 3365) (meaning t m 3366) (meaning t m 3399) (meaning t m 3452) (meaning t m 3631) (meaning t m 3877) (meaning t m 3950) (meaning t m 4118) (meaning t m 4376) source

theorem rule27669 (p2027 p3452 p3998 p4376 p4492 p4874 p5242 p5693 : Prop) (h : (¬ p4376) ∨ p2027 ∨ (¬ p5242) ∨ (¬ p3452) ∨ (¬ p5693) ∨ (¬ p4492) ∨ (¬ p3998) ∨ (¬ p4874)) : (p2027) ∨ (¬ p3452) ∨ (¬ p3998) ∨ (¬ p4376) ∨ (¬ p4492) ∨ (¬ p4874) ∨ (¬ p5242) ∨ (¬ p5693) := by
  classical
  tauto

theorem initial27669 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3998)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4492)) ∨ (¬ (meaning t m 4874)) ∨ (¬ (meaning t m 5242)) ∨ (¬ (meaning t m 5693)) := by
  have source := ElevenTheory.theory16925 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 1 8) (m.theta 8 10)
  exact rule27669 (meaning t m 2027) (meaning t m 3452) (meaning t m 3998) (meaning t m 4376) (meaning t m 4492) (meaning t m 4874) (meaning t m 5242) (meaning t m 5693) source

theorem rule27676 (p1987 p2027 p2651 p2766 p2810 p3172 p4118 : Prop) (h : (¬ p3172) ∨ (¬ p1987) ∨ p2027 ∨ p2766 ∨ (¬ p2651) ∨ (¬ p2810) ∨ (¬ p4118)) : (¬ p1987) ∨ (p2027) ∨ (¬ p2651) ∨ (p2766) ∨ (¬ p2810) ∨ (¬ p3172) ∨ (¬ p4118) := by
  classical
  tauto

theorem initial27676 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1987)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2651)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 2810)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) := by
  have source := ElevenTheory.theory16932 t (m.theta 0 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 8 9)
  exact rule27676 (meaning t m 1987) (meaning t m 2027) (meaning t m 2651) (meaning t m 2766) (meaning t m 2810) (meaning t m 3172) (meaning t m 4118) source

theorem rule27677 (p2027 p2210 p2247 p4154 p4282 p4563 : Prop) (h : p2027 ∨ (¬ p4563) ∨ (¬ p2210) ∨ (¬ p4282) ∨ (¬ p4154) ∨ (¬ p2247)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p4154) ∨ (¬ p4282) ∨ (¬ p4563) := by
  classical
  tauto

theorem initial27677 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4282)) ∨ (¬ (meaning t m 4563)) := by
  have source := ElevenTheory.theory16933 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6)
  exact rule27677 (meaning t m 2027) (meaning t m 2210) (meaning t m 2247) (meaning t m 4154) (meaning t m 4282) (meaning t m 4563) source

theorem rule27679 (p2027 p2254 p2598 p2707 p2952 p3097 p3585 p3589 p3952 p4473 : Prop) (h : (¬ p4473) ∨ p2027 ∨ (¬ p3097) ∨ (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p2707) ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p2254)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2598) ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p3097) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p3952) ∨ (¬ p4473) := by
  classical
  tauto

theorem initial27679 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3589)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4473)) := by
  have source := ElevenTheory.theory16935 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 2 4) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 7)
  exact rule27679 (meaning t m 2027) (meaning t m 2254) (meaning t m 2598) (meaning t m 2707) (meaning t m 2952) (meaning t m 3097) (meaning t m 3585) (meaning t m 3589) (meaning t m 3952) (meaning t m 4473) source

theorem rule27682 (p2254 p2950 p4524 : Prop) (h : (¬ p2254) ∨ (¬ p2950) ∨ p4524) : (¬ p2254) ∨ (¬ p2950) ∨ (p4524) := by
  classical
  tauto

theorem initial27682 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2950)) ∨ (meaning t m 4524) := by
  have source := ElevenTheory.theory16938 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 5)
  exact rule27682 (meaning t m 2254) (meaning t m 2950) (meaning t m 4524) source

theorem rule27687 (p2284 p3758 p5051 : Prop) (h : (¬ p5051) ∨ (¬ p3758) ∨ (¬ p2284)) : (¬ p2284) ∨ (¬ p3758) ∨ (¬ p5051) := by
  classical
  tauto

theorem initial27687 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 5051)) := by
  have source := ElevenTheory.theory16943 (m.theta 2 5) (m.theta 3 5) (m.theta 5 6)
  exact rule27687 (meaning t m 2284) (meaning t m 3758) (meaning t m 5051) source

theorem rule27688 (p2027 p2264 p2363 p3947 p4445 p4503 : Prop) (h : (¬ p4445) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p3947)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27688 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4445)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory16944 t (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9)
  exact rule27688 (meaning t m 2027) (meaning t m 2264) (meaning t m 2363) (meaning t m 3947) (meaning t m 4445) (meaning t m 4503) source

theorem rule27689 (p2245 p3873 p4117 : Prop) (h : p3873 ∨ (¬ p2245) ∨ (¬ p4117)) : (¬ p2245) ∨ (p3873) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial27689 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2245)) ∨ (meaning t m 3873) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory16945 (m.theta 0 1) (m.theta 0 2) (m.theta 0 3)
  exact rule27689 (meaning t m 2245) (meaning t m 3873) (meaning t m 4117) source

theorem rule27693 (p1992 p2027 p2284 p2743 p2950 p3361 p3497 p3578 p3646 : Prop) (h : (¬ p2950) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3361) ∨ (¬ p2743) ∨ (¬ p1992) ∨ (¬ p3646) ∨ p3578 ∨ (¬ p3497)) : (¬ p1992) ∨ (p2027) ∨ (¬ p2284) ∨ (¬ p2743) ∨ (¬ p2950) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (p3578) ∨ (¬ p3646) := by
  classical
  tauto

theorem initial27693 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3497)) ∨ (meaning t m 3578) ∨ (¬ (meaning t m 3646)) := by
  have source := ElevenTheory.theory16949 t (m.theta 0 3) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8)
  exact rule27693 (meaning t m 1992) (meaning t m 2027) (meaning t m 2284) (meaning t m 2743) (meaning t m 2950) (meaning t m 3361) (meaning t m 3497) (meaning t m 3578) (meaning t m 3646) source

theorem rule27694 (p1992 p2027 p2766 p3584 p3585 p3956 p4347 : Prop) (h : (¬ p4347) ∨ (¬ p3956) ∨ p2027 ∨ p2766 ∨ (¬ p1992) ∨ (¬ p3585) ∨ (¬ p3584)) : (¬ p1992) ∨ (p2027) ∨ (p2766) ∨ (¬ p3584) ∨ (¬ p3585) ∨ (¬ p3956) ∨ (¬ p4347) := by
  classical
  tauto

theorem initial27694 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1992)) ∨ (meaning t m 2027) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3584)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4347)) := by
  have source := ElevenTheory.theory16950 t (m.theta 1 2) (m.theta 2 4) (m.theta 4 6) (m.theta 6 8) (m.theta 8 9)
  exact rule27694 (meaning t m 1992) (meaning t m 2027) (meaning t m 2766) (meaning t m 3584) (meaning t m 3585) (meaning t m 3956) (meaning t m 4347) source

theorem rule27699 (p2027 p2177 p2307 p2788 p3659 p3689 : Prop) (h : (¬ p2788) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p3659) ∨ (¬ p3689) ∨ (¬ p2177)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2788) ∨ (¬ p3659) ∨ (¬ p3689) := by
  classical
  tauto

theorem initial27699 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2788)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3689)) := by
  have source := ElevenTheory.theory16955 t (m.theta 0 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27699 (meaning t m 2027) (meaning t m 2177) (meaning t m 2307) (meaning t m 2788) (meaning t m 3659) (meaning t m 3689) source

theorem rule27700 (p2027 p2307 p2504 p2584 p2665 p3549 p3574 : Prop) (h : (¬ p2504) ∨ (¬ p2584) ∨ p2027 ∨ (¬ p2665) ∨ (¬ p3549) ∨ (¬ p2307) ∨ (¬ p3574)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3549) ∨ (¬ p3574) := by
  classical
  tauto

theorem initial27700 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2504)) ∨ (¬ (meaning t m 2584)) ∨ (¬ (meaning t m 2665)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3574)) := by
  have source := ElevenTheory.theory16956 t (m.theta 0 4) (m.theta 0 6) (m.theta 1 6) (m.theta 3 4) (m.theta 4 6) (m.theta 6 7)
  exact rule27700 (meaning t m 2027) (meaning t m 2307) (meaning t m 2504) (meaning t m 2584) (meaning t m 2665) (meaning t m 3549) (meaning t m 3574) source

theorem rule27701 (p2027 p2307 p2506 p3452 p3549 p5020 : Prop) (h : (¬ p5020) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p2506) ∨ (¬ p2307) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2307) ∨ (¬ p2506) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p5020) := by
  classical
  tauto

theorem initial27701 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2307)) ∨ (¬ (meaning t m 2506)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 5020)) := by
  have source := ElevenTheory.theory16957 t (m.theta 0 1) (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 6 7)
  exact rule27701 (meaning t m 2027) (meaning t m 2307) (meaning t m 2506) (meaning t m 3452) (meaning t m 3549) (meaning t m 5020) source

theorem rule27702 (p1989 p2027 p2210 p2766 p3548 p4348 p4366 : Prop) (h : p2766 ∨ (¬ p1989) ∨ (¬ p4366) ∨ (¬ p4348) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p3548)) : (¬ p1989) ∨ (p2027) ∨ (¬ p2210) ∨ (p2766) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial27702 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1989)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2766) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory16958 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 7 8) (m.theta 8 9)
  exact rule27702 (meaning t m 1989) (meaning t m 2027) (meaning t m 2210) (meaning t m 2766) (meaning t m 3548) (meaning t m 4348) (meaning t m 4366) source

theorem rule27703 (p2027 p2387 p3654 p4345 p4348 p4503 : Prop) (h : (¬ p4345) ∨ (¬ p4348) ∨ (¬ p3654) ∨ (¬ p4503) ∨ p2027 ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27703 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 3654)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory16959 t (m.theta 0 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule27703 (meaning t m 2027) (meaning t m 2387) (meaning t m 3654) (meaning t m 4345) (meaning t m 4348) (meaning t m 4503) source

theorem rule27705 (p2027 p2246 p2744 p2946 p3055 p3156 p3366 p3969 p4425 p5119 p5160 : Prop) (h : (¬ p3366) ∨ (¬ p5119) ∨ (¬ p3055) ∨ (¬ p2744) ∨ (¬ p5160) ∨ (¬ p4425) ∨ (¬ p3969) ∨ p2027 ∨ (¬ p2946) ∨ (¬ p2246) ∨ (¬ p3156)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3969) ∨ (¬ p4425) ∨ (¬ p5119) ∨ (¬ p5160) := by
  classical
  tauto

theorem initial27705 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 5119)) ∨ (¬ (meaning t m 5160)) := by
  have source := ElevenTheory.theory16961 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 4) (m.theta 3 5) (m.theta 4 9) (m.theta 5 8) (m.theta 8 10) (m.theta 9 10)
  exact rule27705 (meaning t m 2027) (meaning t m 2246) (meaning t m 2744) (meaning t m 2946) (meaning t m 3055) (meaning t m 3156) (meaning t m 3366) (meaning t m 3969) (meaning t m 4425) (meaning t m 5119) (meaning t m 5160) source

theorem rule27707 (p2027 p2664 p2946 p3156 p3540 p3644 p3969 p4348 p5122 : Prop) (h : (¬ p5122) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p2946) ∨ (¬ p4348) ∨ (¬ p3156) ∨ (¬ p2664) ∨ (¬ p3644) ∨ (¬ p3540)) : (p2027) ∨ (¬ p2664) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p3969) ∨ (¬ p4348) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial27707 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2664)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory16963 t (m.theta 0 3) (m.theta 0 4) (m.theta 3 5) (m.theta 4 7) (m.theta 5 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27707 (meaning t m 2027) (meaning t m 2664) (meaning t m 2946) (meaning t m 3156) (meaning t m 3540) (meaning t m 3644) (meaning t m 3969) (meaning t m 4348) (meaning t m 5122) source

theorem rule27709 (p1984 p2027 p2633 p3434 p3659 p3817 p4366 : Prop) (h : (¬ p3434) ∨ (¬ p1984) ∨ p2027 ∨ (¬ p3817) ∨ (¬ p4366) ∨ p2633 ∨ (¬ p3659)) : (¬ p1984) ∨ (p2027) ∨ (p2633) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3817) ∨ (¬ p4366) := by
  classical
  tauto

theorem initial27709 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1984)) ∨ (meaning t m 2027) ∨ (meaning t m 2633) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) := by
  have source := ElevenTheory.theory16965 t (m.theta 0 1) (m.theta 1 7) (m.theta 2 7) (m.theta 7 8) (m.theta 7 9)
  exact rule27709 (meaning t m 1984) (meaning t m 2027) (meaning t m 2633) (meaning t m 3434) (meaning t m 3659) (meaning t m 3817) (meaning t m 4366) source

theorem rule27716 (p2027 p3063 p3549 p3550 p4107 p4666 : Prop) (h : (¬ p4666) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p4107)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3549) ∨ (¬ p3550) ∨ (¬ p4107) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial27716 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory16972 t (m.theta 1 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule27716 (meaning t m 2027) (meaning t m 3063) (meaning t m 3549) (meaning t m 3550) (meaning t m 4107) (meaning t m 4666) source

theorem rule27722 (p1977 p2027 p2499 p2997 p3097 p3125 p3402 p4137 : Prop) (h : (¬ p1977) ∨ p2027 ∨ (¬ p3125) ∨ (¬ p3097) ∨ p2997 ∨ (¬ p3402) ∨ (¬ p2499) ∨ (¬ p4137)) : (¬ p1977) ∨ (p2027) ∨ (¬ p2499) ∨ (p2997) ∨ (¬ p3097) ∨ (¬ p3125) ∨ (¬ p3402) ∨ (¬ p4137) := by
  classical
  tauto

theorem initial27722 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 1977)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (meaning t m 2997) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 3402)) ∨ (¬ (meaning t m 4137)) := by
  have source := ElevenTheory.theory16978 t (m.theta 1 3) (m.theta 1 4) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 6 9)
  exact rule27722 (meaning t m 1977) (meaning t m 2027) (meaning t m 2499) (meaning t m 2997) (meaning t m 3097) (meaning t m 3125) (meaning t m 3402) (meaning t m 4137) source

theorem rule27723 (p2577 p2786 p3362 : Prop) (h : (¬ p2786) ∨ (¬ p2577) ∨ p3362) : (¬ p2577) ∨ (¬ p2786) ∨ (p3362) := by
  classical
  tauto

theorem initial27723 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2577)) ∨ (¬ (meaning t m 2786)) ∨ (meaning t m 3362) := by
  have source := ElevenTheory.theory16979 (m.theta 0 2) (m.theta 0 4) (m.theta 0 6)
  exact rule27723 (meaning t m 2577) (meaning t m 2786) (meaning t m 3362) source

theorem rule27724 (p2027 p2230 p3055 p3238 p3362 p5214 : Prop) (h : (¬ p2230) ∨ (¬ p3238) ∨ (¬ p3055) ∨ p2027 ∨ (¬ p5214) ∨ (¬ p3362)) : (p2027) ∨ (¬ p2230) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3362) ∨ (¬ p5214) := by
  classical
  tauto

theorem initial27724 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3362)) ∨ (¬ (meaning t m 5214)) := by
  have source := ElevenTheory.theory16980 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 4) (m.theta 4 5)
  exact rule27724 (meaning t m 2027) (meaning t m 2230) (meaning t m 3055) (meaning t m 3238) (meaning t m 3362) (meaning t m 5214) source

theorem rule27728 (p2027 p2254 p2608 p2707 p2717 p2952 p3952 p3989 p4503 : Prop) (h : (¬ p3952) ∨ (¬ p3989) ∨ p2027 ∨ (¬ p2707) ∨ (¬ p2952) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2717) ∨ (¬ p4503)) : (p2027) ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2717) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4503) := by
  classical
  tauto

theorem initial27728 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2254)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2707)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4503)) := by
  have source := ElevenTheory.theory16984 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8) (m.theta 7 8)
  exact rule27728 (meaning t m 2027) (meaning t m 2254) (meaning t m 2608) (meaning t m 2707) (meaning t m 2717) (meaning t m 2952) (meaning t m 3952) (meaning t m 3989) (meaning t m 4503) source

theorem rule27729 (p2027 p2104 p2241 p2264 p2363 p3027 p4340 p4503 p4736 : Prop) (h : (¬ p2363) ∨ (¬ p4503) ∨ (¬ p3027) ∨ (¬ p2264) ∨ (¬ p2104) ∨ (¬ p4736) ∨ (¬ p2241) ∨ p2027 ∨ (¬ p4340)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2363) ∨ (¬ p3027) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4736) := by
  classical
  tauto

theorem initial27729 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4503)) ∨ (¬ (meaning t m 4736)) := by
  have source := ElevenTheory.theory16985 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 3) (m.theta 2 8) (m.theta 3 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 9)
  exact rule27729 (meaning t m 2027) (meaning t m 2104) (meaning t m 2241) (meaning t m 2264) (meaning t m 2363) (meaning t m 3027) (meaning t m 4340) (meaning t m 4503) (meaning t m 4736) source

theorem rule27734 (p2027 p2299 p2589 p3363 p3471 p3527 p3585 p4235 p4424 p4559 p4737 : Prop) (h : (¬ p4424) ∨ (¬ p3471) ∨ (¬ p4559) ∨ (¬ p3527) ∨ (¬ p4235) ∨ (¬ p2299) ∨ (¬ p4737) ∨ p2027 ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p2589)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2589) ∨ (¬ p3363) ∨ (¬ p3471) ∨ (¬ p3527) ∨ (¬ p3585) ∨ (¬ p4235) ∨ (¬ p4424) ∨ (¬ p4559) ∨ (¬ p4737) := by
  classical
  tauto

theorem initial27734 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 3363)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4424)) ∨ (¬ (meaning t m 4559)) ∨ (¬ (meaning t m 4737)) := by
  have source := ElevenTheory.theory16990 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 7) (m.theta 2 4) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27734 (meaning t m 2027) (meaning t m 2299) (meaning t m 2589) (meaning t m 3363) (meaning t m 3471) (meaning t m 3527) (meaning t m 3585) (meaning t m 4235) (meaning t m 4424) (meaning t m 4559) (meaning t m 4737) source

theorem rule27738 (p2156 p3093 p3369 p4516 : Prop) (h : (¬ p3093) ∨ (¬ p3369) ∨ (¬ p4516) ∨ p2156) : (p2156) ∨ (¬ p3093) ∨ (¬ p3369) ∨ (¬ p4516) := by
  classical
  tauto

theorem initial27738 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2156) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4516)) := by
  have source := ElevenTheory.theory16994 (m.theta 0 1) (m.theta 0 5) (m.theta 1 6) (m.theta 5 6)
  exact rule27738 (meaning t m 2156) (meaning t m 3093) (meaning t m 3369) (meaning t m 4516) source

theorem rule27739 (p2011 p2027 p2210 p2699 p2891 p3105 p4244 : Prop) (h : (¬ p4244) ∨ (¬ p3105) ∨ (¬ p2011) ∨ (¬ p2210) ∨ (¬ p2891) ∨ p2027 ∨ p2699) : (¬ p2011) ∨ (p2027) ∨ (¬ p2210) ∨ (p2699) ∨ (¬ p2891) ∨ (¬ p3105) ∨ (¬ p4244) := by
  classical
  tauto

theorem initial27739 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2011)) ∨ (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (meaning t m 2699) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3105)) ∨ (¬ (meaning t m 4244)) := by
  have source := ElevenTheory.theory16995 t (m.theta 0 1) (m.theta 1 5) (m.theta 2 5) (m.theta 5 7) (m.theta 5 9)
  exact rule27739 (meaning t m 2011) (meaning t m 2027) (meaning t m 2210) (meaning t m 2699) (meaning t m 2891) (meaning t m 3105) (meaning t m 4244) source

theorem rule27741 (p3032 p3546 p4155 : Prop) (h : (¬ p4155) ∨ (¬ p3032) ∨ p3546) : (¬ p3032) ∨ (p3546) ∨ (¬ p4155) := by
  classical
  tauto

theorem initial27741 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3032)) ∨ (meaning t m 3546) ∨ (¬ (meaning t m 4155)) := by
  have source := ElevenTheory.theory16997 (m.theta 0 7) (m.theta 1 7) (m.theta 3 7)
  exact rule27741 (meaning t m 3032) (meaning t m 3546) (meaning t m 4155) source

theorem rule27748 (p2027 p2187 p2459 p3986 p4037 p4133 p4171 : Prop) (h : (¬ p4133) ∨ (¬ p2187) ∨ (¬ p4171) ∨ (¬ p4037) ∨ (¬ p2459) ∨ (¬ p3986) ∨ p2027) : (p2027) ∨ (¬ p2187) ∨ (¬ p2459) ∨ (¬ p3986) ∨ (¬ p4037) ∨ (¬ p4133) ∨ (¬ p4171) := by
  classical
  tauto

theorem initial27748 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4171)) := by
  have source := ElevenTheory.theory17004 t (m.theta 3 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule27748 (meaning t m 2027) (meaning t m 2187) (meaning t m 2459) (meaning t m 3986) (meaning t m 4037) (meaning t m 4133) (meaning t m 4171) source

theorem rule27749 (p2027 p2518 p3379 p3425 p3659 p4149 p4348 p4736 p5122 : Prop) (h : (¬ p3379) ∨ (¬ p3425) ∨ (¬ p4348) ∨ (¬ p2518) ∨ (¬ p3659) ∨ p2027 ∨ (¬ p4736) ∨ (¬ p5122) ∨ (¬ p4149)) : (p2027) ∨ (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4149) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial27749 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4736)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory17005 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 4) (m.theta 2 7) (m.theta 4 8) (m.theta 7 8) (m.theta 8 10) (m.theta 8 9)
  exact rule27749 (meaning t m 2027) (meaning t m 2518) (meaning t m 3379) (meaning t m 3425) (meaning t m 3659) (meaning t m 4149) (meaning t m 4348) (meaning t m 4736) (meaning t m 5122) source

theorem rule27750 (p2027 p3644 p3868 p4133 p4441 p5562 p5568 : Prop) (h : (¬ p5562) ∨ (¬ p4441) ∨ (¬ p3868) ∨ (¬ p4133) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p5568)) : (p2027) ∨ (¬ p3644) ∨ (¬ p3868) ∨ (¬ p4133) ∨ (¬ p4441) ∨ (¬ p5562) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial27750 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4133)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 5562)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory17006 t (m.theta 4 7) (m.theta 5 8) (m.theta 6 8) (m.theta 7 10) (m.theta 7 8) (m.theta 8 10)
  exact rule27750 (meaning t m 2027) (meaning t m 3644) (meaning t m 3868) (meaning t m 4133) (meaning t m 4441) (meaning t m 5562) (meaning t m 5568) source

theorem rule27752 (p2027 p3027 p3552 p4037 p4154 p4620 : Prop) (h : (¬ p4037) ∨ (¬ p4154) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4620) ∨ p2027) : (p2027) ∨ (¬ p3027) ∨ (¬ p3552) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial27752 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3552)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory17008 t (m.theta 1 3) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7) (m.theta 6 9)
  exact rule27752 (meaning t m 2027) (meaning t m 3027) (meaning t m 3552) (meaning t m 4037) (meaning t m 4154) (meaning t m 4620) source

theorem rule27753 (p2027 p2246 p2553 p2651 p2744 p2881 p3016 p3366 p3425 p3659 p4559 : Prop) (h : (¬ p2881) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p2246) ∨ (¬ p4559) ∨ (¬ p3016) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2553) ∨ (¬ p2744) ∨ (¬ p3659)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2553) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p2881) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4559) := by
  classical
  tauto

theorem initial27753 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2651)) ∨ (¬ (meaning t m 2744)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3425)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 4559)) := by
  have source := ElevenTheory.theory17009 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 6) (m.theta 5 7) (m.theta 6 7) (m.theta 7 8)
  exact rule27753 (meaning t m 2027) (meaning t m 2246) (meaning t m 2553) (meaning t m 2651) (meaning t m 2744) (meaning t m 2881) (meaning t m 3016) (meaning t m 3366) (meaning t m 3425) (meaning t m 3659) (meaning t m 4559) source

end SunPrize.SMT
