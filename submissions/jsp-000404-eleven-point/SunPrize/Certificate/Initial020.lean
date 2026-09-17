import Mathlib.Tactic.Tauto
import SunPrize.Certificate.Meaning
import SunPrize.Certificate.Theory009
import SunPrize.Certificate.Theory010
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SunPrize.SMT

theorem rule11043 (p2027 p2383 p2786 p3365 p4358 p4845 : Prop) (h : (¬ p4358) ∨ (¬ p2786) ∨ (¬ p2383) ∨ (¬ p4845) ∨ (¬ p3365) ∨ p2027) : (p2027) ∨ (¬ p2383) ∨ (¬ p2786) ∨ (¬ p3365) ∨ (¬ p4358) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11043 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 2786)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory2555 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule11043 (meaning t m 2027) (meaning t m 2383) (meaning t m 2786) (meaning t m 3365) (meaning t m 4358) (meaning t m 4845) source

theorem rule11044 (p2786 p3987 p4117 : Prop) (h : (¬ p4117) ∨ p2786 ∨ (¬ p3987)) : (p2786) ∨ (¬ p3987) ∨ (¬ p4117) := by
  classical
  tauto

theorem initial11044 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2786) ∨ (¬ (meaning t m 3987)) ∨ (¬ (meaning t m 4117)) := by
  have source := ElevenTheory.theory2556 (m.theta 0 2) (m.theta 0 3) (m.theta 0 6)
  exact rule11044 (meaning t m 2786) (meaning t m 3987) (meaning t m 4117) source

theorem rule11045 (p2027 p2177 p3192 p3644 p3947 p4451 p4570 : Prop) (h : (¬ p4570) ∨ (¬ p4451) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3192) ∨ (¬ p3644) ∨ (¬ p3947)) : (p2027) ∨ (¬ p2177) ∨ (¬ p3192) ∨ (¬ p3644) ∨ (¬ p3947) ∨ (¬ p4451) ∨ (¬ p4570) := by
  classical
  tauto

theorem initial11045 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3192)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4451)) ∨ (¬ (meaning t m 4570)) := by
  have source := ElevenTheory.theory2557 t (m.theta 3 7) (m.theta 4 7) (m.theta 4 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11045 (meaning t m 2027) (meaning t m 2177) (meaning t m 3192) (meaning t m 3644) (meaning t m 3947) (meaning t m 4451) (meaning t m 4570) source

theorem rule11046 (p2027 p2922 p3379 p3555 p4034 p4646 : Prop) (h : (¬ p2922) ∨ (¬ p3379) ∨ (¬ p4646) ∨ p2027 ∨ (¬ p3555) ∨ (¬ p4034)) : (p2027) ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4034) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial11046 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4034)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2558 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 7)
  exact rule11046 (meaning t m 2027) (meaning t m 2922) (meaning t m 3379) (meaning t m 3555) (meaning t m 4034) (meaning t m 4646) source

theorem rule11047 (p2027 p3399 p3547 p3591 p4026 p4620 : Prop) (h : (¬ p3399) ∨ (¬ p3547) ∨ p2027 ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4620)) : (p2027) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4620) := by
  classical
  tauto

theorem initial11047 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3547)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4620)) := by
  have source := ElevenTheory.theory2559 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 7) (m.theta 6 9)
  exact rule11047 (meaning t m 2027) (meaning t m 3399) (meaning t m 3547) (meaning t m 3591) (meaning t m 4026) (meaning t m 4620) source

theorem rule11048 (p2027 p2470 p3540 p4278 p4404 p4666 : Prop) (h : (¬ p4404) ∨ (¬ p3540) ∨ (¬ p4666) ∨ (¬ p2470) ∨ (¬ p4278) ∨ p2027) : (p2027) ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11048 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4404)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory2560 t (m.theta 0 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 8) (m.theta 7 9)
  exact rule11048 (meaning t m 2027) (meaning t m 2470) (meaning t m 3540) (meaning t m 4278) (meaning t m 4404) (meaning t m 4666) source

theorem rule11050 (p2027 p2406 p2589 p2655 p3361 p3541 p3688 p4842 : Prop) (h : (¬ p4842) ∨ (¬ p2589) ∨ (¬ p3361) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p3541) ∨ (¬ p3688) ∨ (¬ p2655)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p3541) ∨ (¬ p3688) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11050 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2655)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3541)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2562 t (m.theta 0 3) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 6) (m.theta 4 5)
  exact rule11050 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2655) (meaning t m 3361) (meaning t m 3541) (meaning t m 3688) (meaning t m 4842) source

theorem rule11051 (p2027 p2996 p3189 p3570 p4362 p4804 p4963 : Prop) (h : (¬ p4804) ∨ (¬ p4963) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p2996) ∨ p2027) : (p2027) ∨ (¬ p2996) ∨ (¬ p3189) ∨ (¬ p3570) ∨ (¬ p4362) ∨ (¬ p4804) ∨ (¬ p4963) := by
  classical
  tauto

theorem initial11051 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4804)) ∨ (¬ (meaning t m 4963)) := by
  have source := ElevenTheory.theory2563 t (m.theta 1 3) (m.theta 2 8) (m.theta 3 7) (m.theta 3 8) (m.theta 5 7) (m.theta 7 8)
  exact rule11051 (meaning t m 2027) (meaning t m 2996) (meaning t m 3189) (meaning t m 3570) (meaning t m 4362) (meaning t m 4804) (meaning t m 4963) source

theorem rule11052 (p2027 p2579 p2641 p2659 p3984 p4111 : Prop) (h : (¬ p4111) ∨ (¬ p2659) ∨ p2027 ∨ (¬ p2641) ∨ (¬ p2579) ∨ (¬ p3984)) : (p2027) ∨ (¬ p2579) ∨ (¬ p2641) ∨ (¬ p2659) ∨ (¬ p3984) ∨ (¬ p4111) := by
  classical
  tauto

theorem initial11052 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2659)) ∨ (¬ (meaning t m 3984)) ∨ (¬ (meaning t m 4111)) := by
  have source := ElevenTheory.theory2564 t (m.theta 0 4) (m.theta 1 3) (m.theta 3 4) (m.theta 3 6) (m.theta 4 6)
  exact rule11052 (meaning t m 2027) (meaning t m 2579) (meaning t m 2641) (meaning t m 2659) (meaning t m 3984) (meaning t m 4111) source

theorem rule11053 (p2027 p2531 p3189 p3662 p3988 p4320 p4346 p4555 : Prop) (h : (¬ p4555) ∨ (¬ p4346) ∨ (¬ p3988) ∨ (¬ p2531) ∨ (¬ p4320) ∨ p2027 ∨ (¬ p3189) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2531) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3988) ∨ (¬ p4320) ∨ (¬ p4346) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11053 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2531)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3988)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2565 t (m.theta 1 3) (m.theta 3 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 6) (m.theta 5 7) (m.theta 5 8)
  exact rule11053 (meaning t m 2027) (meaning t m 2531) (meaning t m 3189) (meaning t m 3662) (meaning t m 3988) (meaning t m 4320) (meaning t m 4346) (meaning t m 4555) source

theorem rule11054 (p2027 p3323 p3946 p4110 p4336 p4356 p4705 : Prop) (h : (¬ p4356) ∨ (¬ p4110) ∨ (¬ p4705) ∨ (¬ p3946) ∨ (¬ p3323) ∨ (¬ p4336) ∨ p2027) : (p2027) ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11054 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3946)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2566 t (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 9)
  exact rule11054 (meaning t m 2027) (meaning t m 3323) (meaning t m 3946) (meaning t m 4110) (meaning t m 4336) (meaning t m 4356) (meaning t m 4705) source

theorem rule11055 (p2027 p2641 p3567 p3662 p4110 p4356 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p4356) ∨ (¬ p3567) ∨ (¬ p3662) ∨ (¬ p4110) ∨ (¬ p2641) ∨ p2027) : (p2027) ∨ (¬ p2641) ∨ (¬ p3567) ∨ (¬ p3662) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11055 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2567 t (m.theta 0 6) (m.theta 1 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule11055 (meaning t m 2027) (meaning t m 2641) (meaning t m 3567) (meaning t m 3662) (meaning t m 4110) (meaning t m 4356) (meaning t m 4705) source

theorem rule11056 (p2027 p2331 p2952 p3986 p4110 p4705 : Prop) (h : (¬ p4110) ∨ (¬ p4705) ∨ (¬ p2952) ∨ (¬ p3986) ∨ p2027 ∨ (¬ p2331)) : (p2027) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4110) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11056 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3986)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2568 t (m.theta 0 3) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6)
  exact rule11056 (meaning t m 2027) (meaning t m 2331) (meaning t m 2952) (meaning t m 3986) (meaning t m 4110) (meaning t m 4705) source

theorem rule11057 (p2027 p3189 p3662 p3919 p4066 p4235 p4283 p4705 : Prop) (h : (¬ p4066) ∨ (¬ p4705) ∨ (¬ p3662) ∨ (¬ p3919) ∨ (¬ p3189) ∨ p2027 ∨ (¬ p4283) ∨ (¬ p4235)) : (p2027) ∨ (¬ p3189) ∨ (¬ p3662) ∨ (¬ p3919) ∨ (¬ p4066) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11057 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3919)) ∨ (¬ (meaning t m 4066)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2569 t (m.theta 0 7) (m.theta 1 3) (m.theta 3 5) (m.theta 3 7) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7)
  exact rule11057 (meaning t m 2027) (meaning t m 3189) (meaning t m 3662) (meaning t m 3919) (meaning t m 4066) (meaning t m 4235) (meaning t m 4283) (meaning t m 4705) source

theorem rule11059 (p2027 p2264 p2311 p2995 p3551 p4110 p4356 p4705 : Prop) (h : (¬ p4356) ∨ (¬ p4705) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2995) ∨ (¬ p2311) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2311) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11059 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2571 t (m.theta 0 6) (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 7 8)
  exact rule11059 (meaning t m 2027) (meaning t m 2264) (meaning t m 2311) (meaning t m 2995) (meaning t m 3551) (meaning t m 4110) (meaning t m 4356) (meaning t m 4705) source

theorem rule11060 (p2027 p2737 p2807 p2811 p3585 p4343 p4652 : Prop) (h : (¬ p4343) ∨ (¬ p3585) ∨ (¬ p4652) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2807) ∨ p2027) : (p2027) ∨ (¬ p2737) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11060 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2811)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2572 t (m.theta 0 3) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7)
  exact rule11060 (meaning t m 2027) (meaning t m 2737) (meaning t m 2807) (meaning t m 2811) (meaning t m 3585) (meaning t m 4343) (meaning t m 4652) source

theorem rule11063 (p2027 p2313 p2386 p2505 p3238 p3309 p4717 : Prop) (h : (¬ p2386) ∨ (¬ p2505) ∨ (¬ p2313) ∨ p2027 ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4717)) : (p2027) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2505) ∨ (¬ p3238) ∨ (¬ p3309) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial11063 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2505)) ∨ (¬ (meaning t m 3238)) ∨ (¬ (meaning t m 3309)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2575 t (m.theta 0 6) (m.theta 1 4) (m.theta 1 6) (m.theta 4 5) (m.theta 4 6) (m.theta 6 7)
  exact rule11063 (meaning t m 2027) (meaning t m 2313) (meaning t m 2386) (meaning t m 2505) (meaning t m 3238) (meaning t m 3309) (meaning t m 4717) source

theorem rule11064 (p2027 p2136 p2860 p3471 p3556 p4136 p4555 : Prop) (h : p2027 ∨ (¬ p4136) ∨ (¬ p2860) ∨ (¬ p4555) ∨ (¬ p3556) ∨ (¬ p2136) ∨ (¬ p3471)) : (p2027) ∨ (¬ p2136) ∨ (¬ p2860) ∨ (¬ p3471) ∨ (¬ p3556) ∨ (¬ p4136) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11064 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2136)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 4136)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2576 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 5) (m.theta 2 7) (m.theta 5 6) (m.theta 5 7)
  exact rule11064 (meaning t m 2027) (meaning t m 2136) (meaning t m 2860) (meaning t m 3471) (meaning t m 3556) (meaning t m 4136) (meaning t m 4555) source

theorem rule11065 (p2027 p2177 p2247 p2553 p2573 p3497 p3662 p4905 p5190 : Prop) (h : (¬ p2247) ∨ (¬ p2573) ∨ (¬ p2177) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4905) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p5190)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4905) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11065 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2577 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 8)
  exact rule11065 (meaning t m 2027) (meaning t m 2177) (meaning t m 2247) (meaning t m 2553) (meaning t m 2573) (meaning t m 3497) (meaning t m 3662) (meaning t m 4905) (meaning t m 5190) source

theorem rule11066 (p2027 p2476 p2507 p2573 p3063 p4432 : Prop) (h : (¬ p2476) ∨ (¬ p2507) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p4432) ∨ (¬ p3063)) : (p2027) ∨ (¬ p2476) ∨ (¬ p2507) ∨ (¬ p2573) ∨ (¬ p3063) ∨ (¬ p4432) := by
  classical
  tauto

theorem initial11066 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 2507)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 4432)) := by
  have source := ElevenTheory.theory2578 t (m.theta 0 4) (m.theta 1 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8)
  exact rule11066 (meaning t m 2027) (meaning t m 2476) (meaning t m 2507) (meaning t m 2573) (meaning t m 3063) (meaning t m 4432) source

theorem rule11067 (p2027 p2230 p2247 p3662 p3879 p5190 : Prop) (h : (¬ p2247) ∨ (¬ p3662) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p3879) ∨ (¬ p2230)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11067 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 3879)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2579 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 5)
  exact rule11067 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 3662) (meaning t m 3879) (meaning t m 5190) source

theorem rule11070 (p2027 p2363 p2534 p2668 p3573 p4976 : Prop) (h : (¬ p4976) ∨ (¬ p3573) ∨ (¬ p2363) ∨ (¬ p2668) ∨ p2027 ∨ (¬ p2534)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p3573) ∨ (¬ p4976) := by
  classical
  tauto

theorem initial11070 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 4976)) := by
  have source := ElevenTheory.theory2582 t (m.theta 3 6) (m.theta 4 6) (m.theta 4 8) (m.theta 6 8) (m.theta 8 9)
  exact rule11070 (meaning t m 2027) (meaning t m 2363) (meaning t m 2534) (meaning t m 2668) (meaning t m 3573) (meaning t m 4976) source

theorem rule11071 (p2027 p2387 p2668 p4110 p4336 p4356 p4705 : Prop) (h : p2027 ∨ (¬ p4356) ∨ (¬ p4705) ∨ (¬ p4336) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11071 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2583 t (m.theta 0 6) (m.theta 3 5) (m.theta 3 6) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8)
  exact rule11071 (meaning t m 2027) (meaning t m 2387) (meaning t m 2668) (meaning t m 4110) (meaning t m 4336) (meaning t m 4356) (meaning t m 4705) source

theorem rule11072 (p2027 p2383 p3136 p3567 p4358 p4563 p4841 : Prop) (h : (¬ p2383) ∨ (¬ p3136) ∨ (¬ p4841) ∨ (¬ p4358) ∨ p2027 ∨ (¬ p3567) ∨ (¬ p4563)) : (p2027) ∨ (¬ p2383) ∨ (¬ p3136) ∨ (¬ p3567) ∨ (¬ p4358) ∨ (¬ p4563) ∨ (¬ p4841) := by
  classical
  tauto

theorem initial11072 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2383)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4563)) ∨ (¬ (meaning t m 4841)) := by
  have source := ElevenTheory.theory2584 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 5) (m.theta 3 6) (m.theta 6 8)
  exact rule11072 (meaning t m 2027) (meaning t m 2383) (meaning t m 3136) (meaning t m 3567) (meaning t m 4358) (meaning t m 4563) (meaning t m 4841) source

theorem rule11073 (p2027 p2284 p3063 p3957 p4193 p4358 p4906 : Prop) (h : (¬ p3957) ∨ p2027 ∨ (¬ p2284) ∨ (¬ p3063) ∨ (¬ p4358) ∨ (¬ p4906) ∨ (¬ p4193)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3063) ∨ (¬ p3957) ∨ (¬ p4193) ∨ (¬ p4358) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial11073 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3957)) ∨ (¬ (meaning t m 4193)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2585 t (m.theta 1 6) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 6 8)
  exact rule11073 (meaning t m 2027) (meaning t m 2284) (meaning t m 3063) (meaning t m 3957) (meaning t m 4193) (meaning t m 4358) (meaning t m 4906) source

theorem rule11076 (p2027 p2122 p2573 p3540 p3921 p5225 : Prop) (h : (¬ p3921) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p5225)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial11076 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3540)) ∨ (¬ (meaning t m 3921)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory2588 t (m.theta 0 4) (m.theta 2 6) (m.theta 4 6) (m.theta 4 7) (m.theta 6 7)
  exact rule11076 (meaning t m 2027) (meaning t m 2122) (meaning t m 2573) (meaning t m 3540) (meaning t m 3921) (meaning t m 5225) source

theorem rule11077 (p2027 p2717 p3399 p3542 p3860 p4794 : Prop) (h : (¬ p3542) ∨ (¬ p3399) ∨ (¬ p4794) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3860)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3542) ∨ (¬ p3860) ∨ (¬ p4794) := by
  classical
  tauto

theorem initial11077 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3542)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4794)) := by
  have source := ElevenTheory.theory2589 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 2 7) (m.theta 7 8)
  exact rule11077 (meaning t m 2027) (meaning t m 2717) (meaning t m 3399) (meaning t m 3542) (meaning t m 3860) (meaning t m 4794) source

theorem rule11078 (p2027 p2630 p2741 p2829 p4111 p4845 : Prop) (h : (¬ p4111) ∨ (¬ p4845) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p2829) ∨ (¬ p2630)) : (p2027) ∨ (¬ p2630) ∨ (¬ p2741) ∨ (¬ p2829) ∨ (¬ p4111) ∨ (¬ p4845) := by
  classical
  tauto

theorem initial11078 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4845)) := by
  have source := ElevenTheory.theory2590 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4)
  exact rule11078 (meaning t m 2027) (meaning t m 2630) (meaning t m 2741) (meaning t m 2829) (meaning t m 4111) (meaning t m 4845) source

theorem rule11079 (p2027 p2122 p2298 p2331 p3414 p4846 : Prop) (h : (¬ p3414) ∨ (¬ p2298) ∨ (¬ p2122) ∨ (¬ p2331) ∨ p2027 ∨ (¬ p4846)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2298) ∨ (¬ p2331) ∨ (¬ p3414) ∨ (¬ p4846) := by
  classical
  tauto

theorem initial11079 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2298)) ∨ (¬ (meaning t m 2331)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 4846)) := by
  have source := ElevenTheory.theory2591 t (m.theta 0 3) (m.theta 2 6) (m.theta 3 6) (m.theta 3 7) (m.theta 6 7)
  exact rule11079 (meaning t m 2027) (meaning t m 2122) (meaning t m 2298) (meaning t m 2331) (meaning t m 3414) (meaning t m 4846) source

theorem rule11080 (p2027 p2685 p2696 p2753 p3585 p4343 p4652 : Prop) (h : (¬ p3585) ∨ (¬ p2753) ∨ (¬ p2696) ∨ (¬ p4343) ∨ (¬ p4652) ∨ p2027 ∨ (¬ p2685)) : (p2027) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11080 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4343)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2592 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7)
  exact rule11080 (meaning t m 2027) (meaning t m 2685) (meaning t m 2696) (meaning t m 2753) (meaning t m 3585) (meaning t m 4343) (meaning t m 4652) source

theorem rule11081 (p2027 p3027 p3574 p3579 p3660 p4111 p4646 : Prop) (h : (¬ p3660) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p3579) ∨ p2027 ∨ (¬ p4646) ∨ (¬ p3027)) : (p2027) ∨ (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p3660) ∨ (¬ p4111) ∨ (¬ p4646) := by
  classical
  tauto

theorem initial11081 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3579)) ∨ (¬ (meaning t m 3660)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4646)) := by
  have source := ElevenTheory.theory2593 t (m.theta 1 3) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5) (m.theta 4 6) (m.theta 4 7)
  exact rule11081 (meaning t m 2027) (meaning t m 3027) (meaning t m 3574) (meaning t m 3579) (meaning t m 3660) (meaning t m 4111) (meaning t m 4646) source

theorem rule11082 (p2027 p2220 p2743 p3146 p3877 p3954 p4041 p4348 p4521 : Prop) (h : (¬ p4521) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2743) ∨ (¬ p2220) ∨ (¬ p3146) ∨ (¬ p4348) ∨ (¬ p4041)) : (p2027) ∨ (¬ p2220) ∨ (¬ p2743) ∨ (¬ p3146) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial11082 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory2594 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11082 (meaning t m 2027) (meaning t m 2220) (meaning t m 2743) (meaning t m 3146) (meaning t m 3877) (meaning t m 3954) (meaning t m 4041) (meaning t m 4348) (meaning t m 4521) source

theorem rule11083 (p2027 p2295 p2954 p3097 p3646 p4336 : Prop) (h : (¬ p3097) ∨ (¬ p2954) ∨ (¬ p2295) ∨ (¬ p3646) ∨ (¬ p4336) ∨ p2027) : (p2027) ∨ (¬ p2295) ∨ (¬ p2954) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4336) := by
  classical
  tauto

theorem initial11083 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2295)) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4336)) := by
  have source := ElevenTheory.theory2595 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 7)
  exact rule11083 (meaning t m 2027) (meaning t m 2295) (meaning t m 2954) (meaning t m 3097) (meaning t m 3646) (meaning t m 4336) source

theorem rule11084 (p2027 p2104 p2696 p3537 p3585 p4749 : Prop) (h : (¬ p4749) ∨ (¬ p3585) ∨ (¬ p2696) ∨ p2027 ∨ (¬ p3537) ∨ (¬ p2104)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2696) ∨ (¬ p3537) ∨ (¬ p3585) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial11084 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3537)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2596 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8)
  exact rule11084 (meaning t m 2027) (meaning t m 2104) (meaning t m 2696) (meaning t m 3537) (meaning t m 3585) (meaning t m 4749) source

theorem rule11085 (p2027 p2427 p3516 p3543 p4382 p4914 p4948 : Prop) (h : p2027 ∨ (¬ p4382) ∨ (¬ p3516) ∨ (¬ p4914) ∨ (¬ p3543) ∨ (¬ p4948) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2427) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4382) ∨ (¬ p4914) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11085 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3516)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 4382)) ∨ (¬ (meaning t m 4914)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory2597 t (m.theta 0 7) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule11085 (meaning t m 2027) (meaning t m 2427) (meaning t m 3516) (meaning t m 3543) (meaning t m 4382) (meaning t m 4914) (meaning t m 4948) source

theorem rule11088 (p2027 p2156 p2982 p3954 p4110 p4242 p4340 p4450 p4521 : Prop) (h : (¬ p4450) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2982) ∨ (¬ p4521) ∨ (¬ p4242) ∨ (¬ p3954) ∨ (¬ p2156) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2982) ∨ (¬ p3954) ∨ (¬ p4110) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4450) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial11088 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory2600 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 8) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 8 9)
  exact rule11088 (meaning t m 2027) (meaning t m 2156) (meaning t m 2982) (meaning t m 3954) (meaning t m 4110) (meaning t m 4242) (meaning t m 4340) (meaning t m 4450) (meaning t m 4521) source

theorem rule11089 (p2027 p2749 p3027 p3361 p3414 p3585 p4749 : Prop) (h : (¬ p3361) ∨ (¬ p3027) ∨ (¬ p4749) ∨ (¬ p2749) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p3414)) : (p2027) ∨ (¬ p2749) ∨ (¬ p3027) ∨ (¬ p3361) ∨ (¬ p3414) ∨ (¬ p3585) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial11089 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3027)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 3414)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2601 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule11089 (meaning t m 2027) (meaning t m 2749) (meaning t m 3027) (meaning t m 3361) (meaning t m 3414) (meaning t m 3585) (meaning t m 4749) source

theorem rule11090 (p2027 p2230 p2264 p2274 p2563 p3548 p4361 p4366 p5190 : Prop) (h : (¬ p4361) ∨ (¬ p2230) ∨ (¬ p2264) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p4366) ∨ (¬ p5190) ∨ (¬ p2274) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2264) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3548) ∨ (¬ p4361) ∨ (¬ p4366) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11090 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2274)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2602 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 7) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 6 7) (m.theta 7 8)
  exact rule11090 (meaning t m 2027) (meaning t m 2230) (meaning t m 2264) (meaning t m 2274) (meaning t m 2563) (meaning t m 3548) (meaning t m 4361) (meaning t m 4366) (meaning t m 5190) source

theorem rule11091 (p2027 p2156 p2264 p2427 p3548 p4110 p4362 p4366 p4521 : Prop) (h : (¬ p3548) ∨ (¬ p4521) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4366) ∨ (¬ p4110) ∨ (¬ p2156) ∨ (¬ p4362) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3548) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4366) ∨ (¬ p4521) := by
  classical
  tauto

theorem initial11091 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4521)) := by
  have source := ElevenTheory.theory2603 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 7) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7) (m.theta 7 8)
  exact rule11091 (meaning t m 2027) (meaning t m 2156) (meaning t m 2264) (meaning t m 2427) (meaning t m 3548) (meaning t m 4110) (meaning t m 4362) (meaning t m 4366) (meaning t m 4521) source

theorem rule11092 (p2027 p2449 p2761 p4025 p4191 p4361 : Prop) (h : (¬ p2761) ∨ (¬ p4025) ∨ (¬ p2449) ∨ p2027 ∨ (¬ p4361) ∨ (¬ p4191)) : (p2027) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial11092 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2449)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 4025)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory2604 t (m.theta 3 7) (m.theta 6 7) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule11092 (meaning t m 2027) (meaning t m 2449) (meaning t m 2761) (meaning t m 4025) (meaning t m 4191) (meaning t m 4361) source

theorem rule11093 (p2027 p2192 p2590 p3125 p4137 p4632 : Prop) (h : (¬ p4632) ∨ (¬ p2192) ∨ (¬ p4137) ∨ (¬ p3125) ∨ p2027 ∨ (¬ p2590)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2590) ∨ (¬ p3125) ∨ (¬ p4137) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial11093 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2590)) ∨ (¬ (meaning t m 3125)) ∨ (¬ (meaning t m 4137)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2605 t (m.theta 1 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6) (m.theta 6 9)
  exact rule11093 (meaning t m 2027) (meaning t m 2192) (meaning t m 2590) (meaning t m 3125) (meaning t m 4137) (meaning t m 4632) source

theorem rule11094 (p2027 p2264 p3955 p4019 p4361 p4441 p4800 p5568 : Prop) (h : (¬ p4019) ∨ (¬ p3955) ∨ (¬ p4361) ∨ (¬ p4800) ∨ p2027 ∨ (¬ p5568) ∨ (¬ p2264) ∨ (¬ p4441)) : (p2027) ∨ (¬ p2264) ∨ (¬ p3955) ∨ (¬ p4019) ∨ (¬ p4361) ∨ (¬ p4441) ∨ (¬ p4800) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial11094 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 4800)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory2606 t (m.theta 2 8) (m.theta 3 7) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 8 10)
  exact rule11094 (meaning t m 2027) (meaning t m 2264) (meaning t m 3955) (meaning t m 4019) (meaning t m 4361) (meaning t m 4441) (meaning t m 4800) (meaning t m 5568) source

theorem rule11095 (p2027 p2299 p2737 p2911 p3365 p3389 p3588 p3873 p4477 p5190 : Prop) (h : p2027 ∨ (¬ p4477) ∨ (¬ p3873) ∨ (¬ p2299) ∨ (¬ p5190) ∨ (¬ p3588) ∨ (¬ p3365) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (¬ p3389)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2737) ∨ (¬ p2911) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p3873) ∨ (¬ p4477) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11095 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4477)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2607 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 7) (m.theta 4 7) (m.theta 6 7) (m.theta 7 8)
  exact rule11095 (meaning t m 2027) (meaning t m 2299) (meaning t m 2737) (meaning t m 2911) (meaning t m 3365) (meaning t m 3389) (meaning t m 3588) (meaning t m 3873) (meaning t m 4477) (meaning t m 5190) source

theorem rule11098 (p2027 p2406 p2589 p2608 p4108 p4376 : Prop) (h : p2027 ∨ (¬ p4108) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2406) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p4108) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11098 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 4108)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2610 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 4 5)
  exact rule11098 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2608) (meaning t m 4108) (meaning t m 4376) source

theorem rule11099 (p2027 p2156 p2247 p2427 p2608 p2996 p3519 p4110 p4362 p4376 p4399 : Prop) (h : (¬ p2156) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2247) ∨ (¬ p4362) ∨ p2027 ∨ (¬ p2996) ∨ (¬ p4399) ∨ (¬ p4110)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2996) ∨ (¬ p3519) ∨ (¬ p4110) ∨ (¬ p4362) ∨ (¬ p4376) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial11099 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4362)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory2611 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 7) (m.theta 4 5) (m.theta 5 6) (m.theta 5 7)
  exact rule11099 (meaning t m 2027) (meaning t m 2156) (meaning t m 2247) (meaning t m 2427) (meaning t m 2608) (meaning t m 2996) (meaning t m 3519) (meaning t m 4110) (meaning t m 4362) (meaning t m 4376) (meaning t m 4399) source

theorem rule11101 (p2027 p2396 p2553 p2573 p2608 p3519 p3860 p3950 p4261 p4376 : Prop) (h : (¬ p3519) ∨ (¬ p3860) ∨ (¬ p2553) ∨ (¬ p4261) ∨ (¬ p2396) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p2608) ∨ (¬ p2573)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11101 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2613 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11101 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 2608) (meaning t m 3519) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 4376) source

theorem rule11102 (p2027 p2166 p2608 p3369 p4120 p4377 : Prop) (h : (¬ p2608) ∨ p2027 ∨ (¬ p4120) ∨ (¬ p2166) ∨ (¬ p3369) ∨ (¬ p4377)) : (p2027) ∨ (¬ p2166) ∨ (¬ p2608) ∨ (¬ p3369) ∨ (¬ p4120) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial11102 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3369)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory2614 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 5 8)
  exact rule11102 (meaning t m 2027) (meaning t m 2166) (meaning t m 2608) (meaning t m 3369) (meaning t m 4120) (meaning t m 4377) source

theorem rule11103 (p2027 p2954 p3256 p3692 p4120 p4237 : Prop) (h : (¬ p4237) ∨ (¬ p3256) ∨ (¬ p2954) ∨ p2027 ∨ (¬ p3692) ∨ (¬ p4120)) : (p2027) ∨ (¬ p2954) ∨ (¬ p3256) ∨ (¬ p3692) ∨ (¬ p4120) ∨ (¬ p4237) := by
  classical
  tauto

theorem initial11103 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2954)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4237)) := by
  have source := ElevenTheory.theory2615 t (m.theta 0 5) (m.theta 3 5) (m.theta 3 8) (m.theta 5 8) (m.theta 8 9)
  exact rule11103 (meaning t m 2027) (meaning t m 2954) (meaning t m 3256) (meaning t m 3692) (meaning t m 4120) (meaning t m 4237) source

theorem rule11104 (p2027 p2589 p2839 p3585 p3695 p4727 : Prop) (h : (¬ p3585) ∨ p2027 ∨ (¬ p2589) ∨ (¬ p4727) ∨ (¬ p3695) ∨ (¬ p2839)) : (p2027) ∨ (¬ p2589) ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial11104 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 3695)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory2616 t (m.theta 0 4) (m.theta 1 2) (m.theta 2 4) (m.theta 2 5) (m.theta 4 5)
  exact rule11104 (meaning t m 2027) (meaning t m 2589) (meaning t m 2839) (meaning t m 3585) (meaning t m 3695) (meaning t m 4727) source

theorem rule11105 (p2027 p2247 p2470 p2528 p3497 p3662 p4348 p4905 p5190 : Prop) (h : (¬ p4348) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p2470) ∨ (¬ p2247) ∨ (¬ p4905) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p2528)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11105 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2617 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11105 (meaning t m 2027) (meaning t m 2247) (meaning t m 2470) (meaning t m 2528) (meaning t m 3497) (meaning t m 3662) (meaning t m 4348) (meaning t m 4905) (meaning t m 5190) source

theorem rule11106 (p2027 p2122 p2579 p2588 p4375 p4727 : Prop) (h : p2027 ∨ (¬ p4727) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2122) ∨ (¬ p4375)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p4375) ∨ (¬ p4727) := by
  classical
  tauto

theorem initial11106 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2579)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 4375)) ∨ (¬ (meaning t m 4727)) := by
  have source := ElevenTheory.theory2618 t (m.theta 0 4) (m.theta 2 4) (m.theta 2 6) (m.theta 4 6) (m.theta 6 7)
  exact rule11106 (meaning t m 2027) (meaning t m 2122) (meaning t m 2579) (meaning t m 2588) (meaning t m 4375) (meaning t m 4727) source

theorem rule11107 (p2027 p2177 p2553 p2573 p2743 p3877 p3954 p4041 p5190 : Prop) (h : (¬ p2573) ∨ (¬ p4041) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p3877) ∨ (¬ p2743) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p5190)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2743) ∨ (¬ p3877) ∨ (¬ p3954) ∨ (¬ p4041) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11107 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2743)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2619 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule11107 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 2743) (meaning t m 3877) (meaning t m 3954) (meaning t m 4041) (meaning t m 5190) source

theorem rule11108 (p2027 p2177 p2553 p2573 p2737 p3365 p3873 p4041 p4242 p4963 p5190 : Prop) (h : (¬ p4963) ∨ (¬ p2737) ∨ (¬ p2573) ∨ (¬ p4041) ∨ (¬ p3873) ∨ (¬ p5190) ∨ (¬ p2553) ∨ (¬ p4242) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4242) ∨ (¬ p4963) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11108 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4963)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2620 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule11108 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 2737) (meaning t m 3365) (meaning t m 3873) (meaning t m 4041) (meaning t m 4242) (meaning t m 4963) (meaning t m 5190) source

theorem rule11109 (p2027 p2177 p2553 p2573 p3256 p3365 p3873 p4041 p4340 p4364 p5190 : Prop) (h : (¬ p4364) ∨ (¬ p3365) ∨ (¬ p2573) ∨ (¬ p4041) ∨ (¬ p3873) ∨ (¬ p5190) ∨ (¬ p2553) ∨ (¬ p3256) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3256) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4041) ∨ (¬ p4340) ∨ (¬ p4364) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11109 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4364)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2621 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 3) (m.theta 2 8) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11109 (meaning t m 2027) (meaning t m 2177) (meaning t m 2553) (meaning t m 2573) (meaning t m 3256) (meaning t m 3365) (meaning t m 3873) (meaning t m 4041) (meaning t m 4340) (meaning t m 4364) (meaning t m 5190) source

theorem rule11111 (p2027 p2470 p2528 p3583 p3694 p3954 p4348 p4905 p5190 : Prop) (h : (¬ p4348) ∨ (¬ p2470) ∨ (¬ p3954) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p4905) ∨ (¬ p2528) ∨ (¬ p3583) ∨ (¬ p3694)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3583) ∨ (¬ p3694) ∨ (¬ p3954) ∨ (¬ p4348) ∨ (¬ p4905) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11111 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4905)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2623 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 5) (m.theta 4 8) (m.theta 5 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11111 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3583) (meaning t m 3694) (meaning t m 3954) (meaning t m 4348) (meaning t m 4905) (meaning t m 5190) source

theorem rule11112 (p2027 p2396 p2553 p2573 p3950 p3954 p4242 p4340 p5190 : Prop) (h : (¬ p3950) ∨ (¬ p4340) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p4242) ∨ (¬ p2573) ∨ (¬ p5190)) : (p2027) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11112 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2624 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11112 (meaning t m 2027) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3950) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) (meaning t m 5190) source

theorem rule11113 (p2027 p2318 p2588 p2717 p3426 p3543 p3548 p5225 : Prop) (h : (¬ p3543) ∨ (¬ p2318) ∨ (¬ p2588) ∨ (¬ p2717) ∨ p2027 ∨ (¬ p3548) ∨ (¬ p5225) ∨ (¬ p3426)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2588) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p5225) := by
  classical
  tauto

theorem initial11113 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3426)) ∨ (¬ (meaning t m 3543)) ∨ (¬ (meaning t m 3548)) ∨ (¬ (meaning t m 5225)) := by
  have source := ElevenTheory.theory2625 t (m.theta 0 7) (m.theta 1 7) (m.theta 2 6) (m.theta 2 7) (m.theta 4 6) (m.theta 6 7) (m.theta 7 8)
  exact rule11113 (meaning t m 2027) (meaning t m 2318) (meaning t m 2588) (meaning t m 2717) (meaning t m 3426) (meaning t m 3543) (meaning t m 3548) (meaning t m 5225) source

theorem rule11114 (p2027 p2911 p2922 p3551 p5191 p5197 : Prop) (h : (¬ p5197) ∨ (¬ p2922) ∨ (¬ p3551) ∨ (¬ p2911) ∨ (¬ p5191) ∨ p2027) : (p2027) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3551) ∨ (¬ p5191) ∨ (¬ p5197) := by
  classical
  tauto

theorem initial11114 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 5191)) ∨ (¬ (meaning t m 5197)) := by
  have source := ElevenTheory.theory2626 t (m.theta 0 4) (m.theta 0 7) (m.theta 1 4) (m.theta 4 7) (m.theta 7 8)
  exact rule11114 (meaning t m 2027) (meaning t m 2911) (meaning t m 2922) (meaning t m 3551) (meaning t m 5191) (meaning t m 5197) source

theorem rule11116 (p2027 p2230 p2427 p2608 p3246 p3519 p3860 p3950 p4261 p4376 : Prop) (h : (¬ p3950) ∨ (¬ p3519) ∨ (¬ p2230) ∨ (¬ p3246) ∨ (¬ p4376) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p3860) ∨ (¬ p4261)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3246) ∨ (¬ p3519) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11116 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2628 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11116 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2608) (meaning t m 3246) (meaning t m 3519) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 4376) source

theorem rule11117 (p2027 p2230 p2247 p2427 p2608 p2881 p3519 p4041 p4360 p4376 : Prop) (h : (¬ p2881) ∨ (¬ p3519) ∨ (¬ p4360) ∨ (¬ p2230) ∨ (¬ p4376) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4041) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3519) ∨ (¬ p4041) ∨ (¬ p4360) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11117 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2629 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule11117 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2427) (meaning t m 2608) (meaning t m 2881) (meaning t m 3519) (meaning t m 4041) (meaning t m 4360) (meaning t m 4376) source

theorem rule11118 (p2027 p2373 p2608 p3051 p3370 p3591 p3923 p4235 p4377 p4433 : Prop) (h : (¬ p3591) ∨ (¬ p4433) ∨ (¬ p4377) ∨ (¬ p3923) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p2373) ∨ (¬ p4235) ∨ (¬ p3370)) : (p2027) ∨ (¬ p2373) ∨ (¬ p2608) ∨ (¬ p3051) ∨ (¬ p3370) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4235) ∨ (¬ p4377) ∨ (¬ p4433) := by
  classical
  tauto

theorem initial11118 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3370)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4377)) ∨ (¬ (meaning t m 4433)) := by
  have source := ElevenTheory.theory2630 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 5 7) (m.theta 5 8) (m.theta 6 8)
  exact rule11118 (meaning t m 2027) (meaning t m 2373) (meaning t m 2608) (meaning t m 3051) (meaning t m 3370) (meaning t m 3591) (meaning t m 3923) (meaning t m 4235) (meaning t m 4377) (meaning t m 4433) source

theorem rule11119 (p2027 p2245 p2470 p2528 p2641 p2963 p4041 p4348 p4360 p5190 : Prop) (h : (¬ p2528) ∨ (¬ p2245) ∨ (¬ p4041) ∨ (¬ p2963) ∨ (¬ p2641) ∨ (¬ p4348) ∨ (¬ p5190) ∨ (¬ p2470) ∨ p2027 ∨ (¬ p4360)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2641) ∨ (¬ p2963) ∨ (¬ p4041) ∨ (¬ p4348) ∨ (¬ p4360) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11119 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2631 t (m.theta 0 1) (m.theta 0 3) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11119 (meaning t m 2027) (meaning t m 2245) (meaning t m 2470) (meaning t m 2528) (meaning t m 2641) (meaning t m 2963) (meaning t m 4041) (meaning t m 4348) (meaning t m 4360) (meaning t m 5190) source

theorem rule11120 (p2027 p2230 p2427 p2748 p3246 p3365 p3873 p3950 p4118 p4360 p5190 : Prop) (h : (¬ p5190) ∨ (¬ p4360) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p2748) ∨ (¬ p4118) ∨ (¬ p3950) ∨ (¬ p3873) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2748) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11120 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2632 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 3) (m.theta 2 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11120 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2748) (meaning t m 3246) (meaning t m 3365) (meaning t m 3873) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 5190) source

theorem rule11121 (p2027 p2104 p2187 p2230 p2563 p3256 p3873 p4340 p4774 p5190 : Prop) (h : (¬ p4774) ∨ (¬ p3873) ∨ (¬ p2187) ∨ (¬ p3256) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p4340) ∨ (¬ p2230) ∨ (¬ p2104) ∨ (¬ p2563)) : (p2027) ∨ (¬ p2104) ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3256) ∨ (¬ p3873) ∨ (¬ p4340) ∨ (¬ p4774) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11121 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2104)) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4774)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2633 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 2 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 6) (m.theta 6 8) (m.theta 8 9)
  exact rule11121 (meaning t m 2027) (meaning t m 2104) (meaning t m 2187) (meaning t m 2230) (meaning t m 2563) (meaning t m 3256) (meaning t m 3873) (meaning t m 4340) (meaning t m 4774) (meaning t m 5190) source

theorem rule11122 (p2027 p2553 p2573 p2737 p3097 p3365 p3688 p3873 p4401 p5190 : Prop) (h : p2027 ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p2553) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p5190) ∨ (¬ p2573) ∨ (¬ p3097) ∨ (¬ p4401)) : (p2027) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2737) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3688) ∨ (¬ p3873) ∨ (¬ p4401) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11122 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3097)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3873)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2634 t (m.theta 0 1) (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 2 3) (m.theta 2 6) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7)
  exact rule11122 (meaning t m 2027) (meaning t m 2553) (meaning t m 2573) (meaning t m 2737) (meaning t m 3097) (meaning t m 3365) (meaning t m 3688) (meaning t m 3873) (meaning t m 4401) (meaning t m 5190) source

theorem rule11123 (p2027 p2829 p3583 p4110 p4185 p4316 p4705 : Prop) (h : (¬ p4705) ∨ (¬ p4185) ∨ (¬ p3583) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p2829) ∨ (¬ p4316)) : (p2027) ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4110) ∨ (¬ p4185) ∨ (¬ p4316) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11123 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2635 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6)
  exact rule11123 (meaning t m 2027) (meaning t m 2829) (meaning t m 3583) (meaning t m 4110) (meaning t m 4185) (meaning t m 4316) (meaning t m 4705) source

theorem rule11124 (p2027 p2230 p2247 p2427 p2881 p2996 p3947 p4666 p5190 : Prop) (h : (¬ p2996) ∨ (¬ p4666) ∨ (¬ p2881) ∨ (¬ p2230) ∨ (¬ p3947) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p2247) ∨ (¬ p2427)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4666) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11124 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 2996)) ∨ (¬ (meaning t m 3947)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2636 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11124 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2427) (meaning t m 2881) (meaning t m 2996) (meaning t m 3947) (meaning t m 4666) (meaning t m 5190) source

theorem rule11125 (p2027 p2230 p2427 p3246 p3950 p3954 p4242 p4340 p5190 : Prop) (h : (¬ p3246) ∨ (¬ p2230) ∨ (¬ p2427) ∨ p2027 ∨ (¬ p5190) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11125 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2637 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11125 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 3246) (meaning t m 3950) (meaning t m 3954) (meaning t m 4242) (meaning t m 4340) (meaning t m 5190) source

theorem rule11127 (p2027 p2299 p2313 p2717 p2782 p3426 : Prop) (h : p2027 ∨ (¬ p2717) ∨ (¬ p2782) ∨ (¬ p3426) ∨ (¬ p2299) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2313) ∨ (¬ p2717) ∨ (¬ p2782) ∨ (¬ p3426) := by
  classical
  tauto

theorem initial11127 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 2782)) ∨ (¬ (meaning t m 3426)) := by
  have source := ElevenTheory.theory2639 t (m.theta 0 6) (m.theta 2 6) (m.theta 2 7) (m.theta 6 7) (m.theta 7 8)
  exact rule11127 (meaning t m 2027) (meaning t m 2299) (meaning t m 2313) (meaning t m 2717) (meaning t m 2782) (meaning t m 3426) source

theorem rule11128 (p3201 p3876 : Prop) (h : (¬ p3876) ∨ (¬ p3201)) : (¬ p3201) ∨ (¬ p3876) := by
  classical
  tauto

theorem initial11128 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3201)) ∨ (¬ (meaning t m 3876)) := by
  have source := ElevenTheory.theory2640 (m.theta 2 4) (m.theta 4 7)
  exact rule11128 (meaning t m 3201) (meaning t m 3876) source

theorem rule11129 (p2027 p2220 p3256 p3949 p4032 p4043 : Prop) (h : (¬ p4032) ∨ (¬ p4043) ∨ p2027 ∨ (¬ p2220) ∨ (¬ p3256) ∨ (¬ p3949)) : (p2027) ∨ (¬ p2220) ∨ (¬ p3256) ∨ (¬ p3949) ∨ (¬ p4032) ∨ (¬ p4043) := by
  classical
  tauto

theorem initial11129 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2220)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4043)) := by
  have source := ElevenTheory.theory2641 t (m.theta 0 5) (m.theta 3 8) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule11129 (meaning t m 2027) (meaning t m 2220) (meaning t m 3256) (meaning t m 3949) (meaning t m 4032) (meaning t m 4043) source

theorem rule11130 (p2027 p2246 p2440 p3005 p3361 p4111 p4346 p4610 : Prop) (h : p2027 ∨ (¬ p4346) ∨ (¬ p3005) ∨ (¬ p2440) ∨ (¬ p2246) ∨ (¬ p4610) ∨ (¬ p3361) ∨ (¬ p4111)) : (p2027) ∨ (¬ p2246) ∨ (¬ p2440) ∨ (¬ p3005) ∨ (¬ p3361) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial11130 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2246)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3361)) ∨ (¬ (meaning t m 4111)) ∨ (¬ (meaning t m 4346)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory2642 t (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8)
  exact rule11130 (meaning t m 2027) (meaning t m 2246) (meaning t m 2440) (meaning t m 3005) (meaning t m 3361) (meaning t m 4111) (meaning t m 4346) (meaning t m 4610) source

theorem rule11131 (p2027 p2440 p4009 p4121 p4286 p4610 : Prop) (h : (¬ p4286) ∨ (¬ p2440) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4610) ∨ p2027) : (p2027) ∨ (¬ p2440) ∨ (¬ p4009) ∨ (¬ p4121) ∨ (¬ p4286) ∨ (¬ p4610) := by
  classical
  tauto

theorem initial11131 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 4009)) ∨ (¬ (meaning t m 4121)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4610)) := by
  have source := ElevenTheory.theory2643 t (m.theta 3 4) (m.theta 3 8) (m.theta 4 5) (m.theta 4 8) (m.theta 8 10)
  exact rule11131 (meaning t m 2027) (meaning t m 2440) (meaning t m 4009) (meaning t m 4121) (meaning t m 4286) (meaning t m 4610) source

theorem rule11133 (p2027 p2230 p2656 p2685 p3364 p3684 p4652 : Prop) (h : (¬ p2230) ∨ (¬ p3364) ∨ (¬ p4652) ∨ (¬ p2685) ∨ p2027 ∨ (¬ p2656) ∨ (¬ p3684)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p2685) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11133 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 3364)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2645 t (m.theta 0 4) (m.theta 2 3) (m.theta 2 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 5)
  exact rule11133 (meaning t m 2027) (meaning t m 2230) (meaning t m 2656) (meaning t m 2685) (meaning t m 3364) (meaning t m 3684) (meaning t m 4652) source

theorem rule11134 (p2027 p2191 p2396 p2553 p2573 p3555 p3692 p3950 p5190 : Prop) (h : (¬ p2191) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3555) ∨ (¬ p2573) ∨ (¬ p3692) ∨ (¬ p5190) ∨ (¬ p3950) ∨ p2027) : (p2027) ∨ (¬ p2191) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11134 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2191)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3692)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2646 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 5) (m.theta 4 6) (m.theta 5 8) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11134 (meaning t m 2027) (meaning t m 2191) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3555) (meaning t m 3692) (meaning t m 3950) (meaning t m 5190) source

theorem rule11135 (p2027 p2850 p2891 p3876 p4001 p4632 : Prop) (h : (¬ p3876) ∨ (¬ p4632) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2891) ∨ (¬ p4001)) : (p2027) ∨ (¬ p2850) ∨ (¬ p2891) ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial11135 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2891)) ∨ (¬ (meaning t m 3876)) ∨ (¬ (meaning t m 4001)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2647 t (m.theta 1 5) (m.theta 2 4) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7)
  exact rule11135 (meaning t m 2027) (meaning t m 2850) (meaning t m 2891) (meaning t m 3876) (meaning t m 4001) (meaning t m 4632) source

theorem rule11137 (p2027 p3073 p3486 p4078 p4185 p4340 p4496 p4555 : Prop) (h : (¬ p4185) ∨ (¬ p4340) ∨ (¬ p4496) ∨ (¬ p3073) ∨ (¬ p4555) ∨ p2027 ∨ (¬ p3486) ∨ (¬ p4078)) : (p2027) ∨ (¬ p3073) ∨ (¬ p3486) ∨ (¬ p4078) ∨ (¬ p4185) ∨ (¬ p4340) ∨ (¬ p4496) ∨ (¬ p4555) := by
  classical
  tauto

theorem initial11137 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3486)) ∨ (¬ (meaning t m 4078)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4496)) ∨ (¬ (meaning t m 4555)) := by
  have source := ElevenTheory.theory2649 t (m.theta 1 5) (m.theta 1 8) (m.theta 2 6) (m.theta 2 8) (m.theta 5 6) (m.theta 5 7) (m.theta 8 9)
  exact rule11137 (meaning t m 2027) (meaning t m 3073) (meaning t m 3486) (meaning t m 4078) (meaning t m 4185) (meaning t m 4340) (meaning t m 4496) (meaning t m 4555) source

theorem rule11138 (p2027 p2247 p2396 p2553 p2573 p3950 p4118 p4360 p5190 : Prop) (h : (¬ p3950) ∨ (¬ p2396) ∨ (¬ p2247) ∨ (¬ p4118) ∨ (¬ p2573) ∨ (¬ p4360) ∨ (¬ p2553) ∨ p2027 ∨ (¬ p5190)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11138 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2650 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 6) (m.theta 6 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11138 (meaning t m 2027) (meaning t m 2247) (meaning t m 2396) (meaning t m 2553) (meaning t m 2573) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 5190) source

theorem rule11140 (p2027 p2166 p3371 p3588 p3694 p4392 p4778 : Prop) (h : (¬ p3588) ∨ (¬ p4778) ∨ (¬ p4392) ∨ (¬ p3694) ∨ (¬ p2166) ∨ (¬ p3371) ∨ p2027) : (p2027) ∨ (¬ p2166) ∨ (¬ p3371) ∨ (¬ p3588) ∨ (¬ p3694) ∨ (¬ p4392) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial11140 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2166)) ∨ (¬ (meaning t m 3371)) ∨ (¬ (meaning t m 3588)) ∨ (¬ (meaning t m 3694)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory2652 t (m.theta 1 2) (m.theta 1 5) (m.theta 2 3) (m.theta 2 5) (m.theta 2 7) (m.theta 5 8)
  exact rule11140 (meaning t m 2027) (meaning t m 2166) (meaning t m 3371) (meaning t m 3588) (meaning t m 3694) (meaning t m 4392) (meaning t m 4778) source

theorem rule11141 (p2027 p2247 p2573 p4154 p4389 p5190 : Prop) (h : (¬ p4154) ∨ (¬ p2573) ∨ (¬ p5190) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p4389)) : (p2027) ∨ (¬ p2247) ∨ (¬ p2573) ∨ (¬ p4154) ∨ (¬ p4389) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11141 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 4154)) ∨ (¬ (meaning t m 4389)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2653 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 6) (m.theta 4 6)
  exact rule11141 (meaning t m 2027) (meaning t m 2247) (meaning t m 2573) (meaning t m 4154) (meaning t m 4389) (meaning t m 5190) source

theorem rule11142 (p2027 p2122 p2588 p2696 p2753 p3564 p3583 p4208 p4316 p4368 p4842 : Prop) (h : (¬ p4316) ∨ (¬ p2753) ∨ (¬ p4842) ∨ p2027 ∨ (¬ p2696) ∨ (¬ p4368) ∨ (¬ p3564) ∨ (¬ p2588) ∨ (¬ p4208) ∨ (¬ p3583) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3564) ∨ (¬ p3583) ∨ (¬ p4208) ∨ (¬ p4316) ∨ (¬ p4368) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11142 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2588)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4316)) ∨ (¬ (meaning t m 4368)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2654 t (m.theta 0 2) (m.theta 1 2) (m.theta 2 3) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 4 6) (m.theta 5 9) (m.theta 6 7) (m.theta 6 9)
  exact rule11142 (meaning t m 2027) (meaning t m 2122) (meaning t m 2588) (meaning t m 2696) (meaning t m 2753) (meaning t m 3564) (meaning t m 3583) (meaning t m 4208) (meaning t m 4316) (meaning t m 4368) (meaning t m 4842) source

theorem rule11144 (p2027 p2619 p3949 p3969 p4385 p5122 : Prop) (h : (¬ p3969) ∨ (¬ p4385) ∨ (¬ p2619) ∨ (¬ p5122) ∨ (¬ p3949) ∨ p2027) : (p2027) ∨ (¬ p2619) ∨ (¬ p3949) ∨ (¬ p3969) ∨ (¬ p4385) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial11144 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2619)) ∨ (¬ (meaning t m 3949)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4385)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory2656 t (m.theta 2 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 10) (m.theta 8 9)
  exact rule11144 (meaning t m 2027) (meaning t m 2619) (meaning t m 3949) (meaning t m 3969) (meaning t m 4385) (meaning t m 5122) source

theorem rule11145 (p2027 p3063 p3585 p4358 p4749 p4841 p4869 : Prop) (h : (¬ p4749) ∨ (¬ p4869) ∨ (¬ p4841) ∨ (¬ p3585) ∨ (¬ p3063) ∨ p2027 ∨ (¬ p4358)) : (p2027) ∨ (¬ p3063) ∨ (¬ p3585) ∨ (¬ p4358) ∨ (¬ p4749) ∨ (¬ p4841) ∨ (¬ p4869) := by
  classical
  tauto

theorem initial11145 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3063)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4358)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4841)) ∨ (¬ (meaning t m 4869)) := by
  have source := ElevenTheory.theory2657 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 4) (m.theta 2 6) (m.theta 6 8)
  exact rule11145 (meaning t m 2027) (meaning t m 3063) (meaning t m 3585) (meaning t m 4358) (meaning t m 4749) (meaning t m 4841) (meaning t m 4869) source

theorem rule11146 (p2027 p2230 p2247 p2427 p3246 p3950 p4118 p4360 p5190 : Prop) (h : (¬ p3950) ∨ (¬ p4360) ∨ (¬ p2247) ∨ p2027 ∨ (¬ p3246) ∨ (¬ p2427) ∨ (¬ p4118) ∨ (¬ p2230) ∨ (¬ p5190)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11146 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2247)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2658 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 3) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9) (m.theta 8 9)
  exact rule11146 (meaning t m 2027) (meaning t m 2230) (meaning t m 2247) (meaning t m 2427) (meaning t m 3246) (meaning t m 3950) (meaning t m 4118) (meaning t m 4360) (meaning t m 5190) source

theorem rule11147 (p2027 p2761 p3051 p3246 p3954 p4242 p4521 p5123 p5612 : Prop) (h : (¬ p3246) ∨ p2027 ∨ (¬ p2761) ∨ (¬ p5123) ∨ (¬ p3051) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p5612) ∨ (¬ p4521)) : (p2027) ∨ (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p3954) ∨ (¬ p4242) ∨ (¬ p4521) ∨ (¬ p5123) ∨ (¬ p5612) := by
  classical
  tauto

theorem initial11147 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4521)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5612)) := by
  have source := ElevenTheory.theory2659 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 2 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11147 (meaning t m 2027) (meaning t m 2761) (meaning t m 3051) (meaning t m 3246) (meaning t m 3954) (meaning t m 4242) (meaning t m 4521) (meaning t m 5123) (meaning t m 5612) source

theorem rule11148 (p2027 p2122 p2313 p2696 p2778 p4842 : Prop) (h : (¬ p2696) ∨ (¬ p4842) ∨ (¬ p2122) ∨ p2027 ∨ (¬ p2778) ∨ (¬ p2313)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2696) ∨ (¬ p2778) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11148 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2313)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2660 t (m.theta 0 2) (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 7)
  exact rule11148 (meaning t m 2027) (meaning t m 2122) (meaning t m 2313) (meaning t m 2696) (meaning t m 2778) (meaning t m 4842) source

theorem rule11149 (p2027 p2373 p3549 p4110 p4356 p4405 p4441 p5016 : Prop) (h : (¬ p4356) ∨ (¬ p2373) ∨ (¬ p3549) ∨ (¬ p4405) ∨ (¬ p5016) ∨ p2027 ∨ (¬ p4110) ∨ (¬ p4441)) : (p2027) ∨ (¬ p2373) ∨ (¬ p3549) ∨ (¬ p4110) ∨ (¬ p4356) ∨ (¬ p4405) ∨ (¬ p4441) ∨ (¬ p5016) := by
  classical
  tauto

theorem initial11149 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4356)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4441)) ∨ (¬ (meaning t m 5016)) := by
  have source := ElevenTheory.theory2661 t (m.theta 0 6) (m.theta 1 6) (m.theta 4 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 7) (m.theta 6 8)
  exact rule11149 (meaning t m 2027) (meaning t m 2373) (meaning t m 3549) (meaning t m 4110) (meaning t m 4356) (meaning t m 4405) (meaning t m 4441) (meaning t m 5016) source

theorem rule11150 (p2027 p2406 p2589 p2696 p3590 p3905 p4749 : Prop) (h : (¬ p2589) ∨ (¬ p3590) ∨ (¬ p2696) ∨ (¬ p3905) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p4749)) : (p2027) ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2696) ∨ (¬ p3590) ∨ (¬ p3905) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial11150 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2589)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3905)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2662 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 5)
  exact rule11150 (meaning t m 2027) (meaning t m 2406) (meaning t m 2589) (meaning t m 2696) (meaning t m 3590) (meaning t m 3905) (meaning t m 4749) source

theorem rule11151 (p2027 p2553 p3032 p3527 p3956 p4138 p4361 : Prop) (h : (¬ p3032) ∨ (¬ p3527) ∨ (¬ p4361) ∨ p2027 ∨ (¬ p2553) ∨ (¬ p4138) ∨ (¬ p3956)) : (p2027) ∨ (¬ p2553) ∨ (¬ p3032) ∨ (¬ p3527) ∨ (¬ p3956) ∨ (¬ p4138) ∨ (¬ p4361) := by
  classical
  tauto

theorem initial11151 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3956)) ∨ (¬ (meaning t m 4138)) ∨ (¬ (meaning t m 4361)) := by
  have source := ElevenTheory.theory2663 t (m.theta 1 7) (m.theta 3 7) (m.theta 4 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule11151 (meaning t m 2027) (meaning t m 2553) (meaning t m 3032) (meaning t m 3527) (meaning t m 3956) (meaning t m 4138) (meaning t m 4361) source

theorem rule11152 (p2027 p2807 p3055 p3572 p4117 p4749 : Prop) (h : (¬ p3572) ∨ (¬ p4117) ∨ (¬ p3055) ∨ (¬ p2807) ∨ p2027 ∨ (¬ p4749)) : (p2027) ∨ (¬ p2807) ∨ (¬ p3055) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial11152 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3572)) ∨ (¬ (meaning t m 4117)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2664 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 7)
  exact rule11152 (meaning t m 2027) (meaning t m 2807) (meaning t m 3055) (meaning t m 3572) (meaning t m 4117) (meaning t m 4749) source

theorem rule11154 (p2027 p2696 p2753 p3093 p3115 p3136 p3860 p4261 p4450 p4870 : Prop) (h : (¬ p3115) ∨ (¬ p4450) ∨ (¬ p2696) ∨ (¬ p3860) ∨ (¬ p2753) ∨ (¬ p3136) ∨ p2027 ∨ (¬ p4261) ∨ (¬ p3093) ∨ (¬ p4870)) : (p2027) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3093) ∨ (¬ p3115) ∨ (¬ p3136) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4450) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11154 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3136)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory2666 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 8) (m.theta 2 3) (m.theta 3 5) (m.theta 5 9) (m.theta 8 9)
  exact rule11154 (meaning t m 2027) (meaning t m 2696) (meaning t m 2753) (meaning t m 3093) (meaning t m 3115) (meaning t m 3136) (meaning t m 3860) (meaning t m 4261) (meaning t m 4450) (meaning t m 4870) source

theorem rule11155 (p2027 p2598 p2753 p2850 p2982 p3093 p4107 p4366 p4395 p4427 p4870 : Prop) (h : (¬ p2982) ∨ (¬ p4395) ∨ (¬ p4366) ∨ (¬ p4107) ∨ (¬ p3093) ∨ (¬ p4427) ∨ (¬ p2598) ∨ (¬ p4870) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2753)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3093) ∨ (¬ p4107) ∨ (¬ p4366) ∨ (¬ p4395) ∨ (¬ p4427) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11155 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory2667 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 1 7) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule11155 (meaning t m 2027) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 2982) (meaning t m 3093) (meaning t m 4107) (meaning t m 4366) (meaning t m 4395) (meaning t m 4427) (meaning t m 4870) source

theorem rule11156 (p2027 p2299 p2598 p2753 p2850 p2982 p3549 p4348 p4450 p4870 : Prop) (h : (¬ p4348) ∨ (¬ p2982) ∨ (¬ p2299) ∨ (¬ p3549) ∨ (¬ p4870) ∨ (¬ p4450) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2753) ∨ (¬ p2598)) : (p2027) ∨ (¬ p2299) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p2982) ∨ (¬ p3549) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11156 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2850)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3549)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4450)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory2668 t (m.theta 0 2) (m.theta 1 2) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11156 (meaning t m 2027) (meaning t m 2299) (meaning t m 2598) (meaning t m 2753) (meaning t m 2850) (meaning t m 2982) (meaning t m 3549) (meaning t m 4348) (meaning t m 4450) (meaning t m 4870) source

theorem rule11159 (p2027 p2210 p2373 p3860 p3906 p4629 : Prop) (h : (¬ p3860) ∨ (¬ p4629) ∨ (¬ p2373) ∨ (¬ p2210) ∨ (¬ p3906) ∨ p2027) : (p2027) ∨ (¬ p2210) ∨ (¬ p2373) ∨ (¬ p3860) ∨ (¬ p3906) ∨ (¬ p4629) := by
  classical
  tauto

theorem initial11159 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2373)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3906)) ∨ (¬ (meaning t m 4629)) := by
  have source := ElevenTheory.theory2671 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 4 5) (m.theta 5 8)
  exact rule11159 (meaning t m 2027) (meaning t m 2210) (meaning t m 2373) (meaning t m 3860) (meaning t m 3906) (meaning t m 4629) source

theorem rule11160 (p2027 p2417 p2930 p3399 p3834 p5358 : Prop) (h : (¬ p2930) ∨ (¬ p3834) ∨ (¬ p3399) ∨ (¬ p2417) ∨ p2027 ∨ (¬ p5358)) : (p2027) ∨ (¬ p2417) ∨ (¬ p2930) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p5358) := by
  classical
  tauto

theorem initial11160 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 2930)) ∨ (¬ (meaning t m 3399)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5358)) := by
  have source := ElevenTheory.theory2672 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 4 7) (m.theta 7 9)
  exact rule11160 (meaning t m 2027) (meaning t m 2417) (meaning t m 2930) (meaning t m 3399) (meaning t m 3834) (meaning t m 5358) source

theorem rule11162 (p2027 p2387 p2630 p2668 p2785 p4841 p4972 : Prop) (h : p2027 ∨ (¬ p4841) ∨ (¬ p2387) ∨ (¬ p2630) ∨ (¬ p2785) ∨ (¬ p4972) ∨ (¬ p2668)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2630) ∨ (¬ p2668) ∨ (¬ p2785) ∨ (¬ p4841) ∨ (¬ p4972) := by
  classical
  tauto

theorem initial11162 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2668)) ∨ (¬ (meaning t m 2785)) ∨ (¬ (meaning t m 4841)) ∨ (¬ (meaning t m 4972)) := by
  have source := ElevenTheory.theory2674 t (m.theta 0 6) (m.theta 2 3) (m.theta 2 6) (m.theta 3 4) (m.theta 3 6) (m.theta 6 8)
  exact rule11162 (meaning t m 2027) (meaning t m 2387) (meaning t m 2630) (meaning t m 2668) (meaning t m 2785) (meaning t m 4841) (meaning t m 4972) source

theorem rule11165 (p2177 p3955 p4138 : Prop) (h : (¬ p3955) ∨ (¬ p2177) ∨ (¬ p4138)) : (¬ p2177) ∨ (¬ p3955) ∨ (¬ p4138) := by
  classical
  tauto

theorem initial11165 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 3955)) ∨ (¬ (meaning t m 4138)) := by
  have source := ElevenTheory.theory2677 (m.theta 6 7) (m.theta 6 8) (m.theta 7 8)
  exact rule11165 (meaning t m 2177) (meaning t m 3955) (meaning t m 4138) source

theorem rule11166 (p2027 p3096 p3564 p3989 p4340 p4345 p4859 : Prop) (h : p2027 ∨ (¬ p4345) ∨ (¬ p3989) ∨ (¬ p4859) ∨ (¬ p3564) ∨ (¬ p4340) ∨ (¬ p3096)) : (p2027) ∨ (¬ p3096) ∨ (¬ p3564) ∨ (¬ p3989) ∨ (¬ p4340) ∨ (¬ p4345) ∨ (¬ p4859) := by
  classical
  tauto

theorem initial11166 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3989)) ∨ (¬ (meaning t m 4340)) ∨ (¬ (meaning t m 4345)) ∨ (¬ (meaning t m 4859)) := by
  have source := ElevenTheory.theory2678 t (m.theta 2 8) (m.theta 4 6) (m.theta 5 6) (m.theta 6 8) (m.theta 6 9) (m.theta 8 9)
  exact rule11166 (meaning t m 2027) (meaning t m 3096) (meaning t m 3564) (meaning t m 3989) (meaning t m 4340) (meaning t m 4345) (meaning t m 4859) source

theorem rule11167 (p3546 p3576 p3959 : Prop) (h : p3959 ∨ (¬ p3546) ∨ (¬ p3576)) : (¬ p3546) ∨ (¬ p3576) ∨ (p3959) := by
  classical
  tauto

theorem initial11167 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3546)) ∨ (¬ (meaning t m 3576)) ∨ (meaning t m 3959) := by
  have source := ElevenTheory.theory2679 (m.theta 0 7) (m.theta 1 7) (m.theta 2 7)
  exact rule11167 (meaning t m 3546) (meaning t m 3576) (meaning t m 3959) source

theorem rule11168 (p2027 p2363 p3438 p3449 p3834 p4995 : Prop) (h : (¬ p3834) ∨ (¬ p4995) ∨ (¬ p2363) ∨ p2027 ∨ (¬ p3449) ∨ (¬ p3438)) : (p2027) ∨ (¬ p2363) ∨ (¬ p3438) ∨ (¬ p3449) ∨ (¬ p3834) ∨ (¬ p4995) := by
  classical
  tauto

theorem initial11168 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 3438)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4995)) := by
  have source := ElevenTheory.theory2680 t (m.theta 0 1) (m.theta 1 8) (m.theta 1 9) (m.theta 6 8) (m.theta 8 9)
  exact rule11168 (meaning t m 2027) (meaning t m 2363) (meaning t m 3438) (meaning t m 3449) (meaning t m 3834) (meaning t m 4995) source

theorem rule11169 (p2027 p2532 p2982 p3857 p3880 p4529 : Prop) (h : (¬ p3880) ∨ (¬ p2532) ∨ (¬ p3857) ∨ (¬ p4529) ∨ p2027 ∨ (¬ p2982)) : (p2027) ∨ (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3857) ∨ (¬ p3880) ∨ (¬ p4529) := by
  classical
  tauto

theorem initial11169 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2532)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4529)) := by
  have source := ElevenTheory.theory2681 t (m.theta 0 8) (m.theta 4 5) (m.theta 5 8) (m.theta 5 9) (m.theta 8 9)
  exact rule11169 (meaning t m 2027) (meaning t m 2532) (meaning t m 2982) (meaning t m 3857) (meaning t m 3880) (meaning t m 4529) source

theorem rule11170 (p2027 p2145 p2630 p2696 p3343 p3556 p3570 p4332 p4348 : Prop) (h : (¬ p4348) ∨ (¬ p3570) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2696) ∨ (¬ p2630) ∨ (¬ p2145) ∨ (¬ p4332) ∨ (¬ p3343)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3343) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4332) ∨ (¬ p4348) := by
  classical
  tauto

theorem initial11170 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2630)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3570)) ∨ (¬ (meaning t m 4332)) ∨ (¬ (meaning t m 4348)) := by
  have source := ElevenTheory.theory2682 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 3) (m.theta 3 4) (m.theta 4 9) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11170 (meaning t m 2027) (meaning t m 2145) (meaning t m 2630) (meaning t m 2696) (meaning t m 3343) (meaning t m 3556) (meaning t m 3570) (meaning t m 4332) (meaning t m 4348) source

theorem rule11171 (p2027 p2245 p2406 p3292 p3379 p4949 p5171 : Prop) (h : (¬ p4949) ∨ p2027 ∨ (¬ p2406) ∨ (¬ p2245) ∨ (¬ p5171) ∨ (¬ p3379) ∨ (¬ p3292)) : (p2027) ∨ (¬ p2245) ∨ (¬ p2406) ∨ (¬ p3292) ∨ (¬ p3379) ∨ (¬ p4949) ∨ (¬ p5171) := by
  classical
  tauto

theorem initial11171 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2245)) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 4949)) ∨ (¬ (meaning t m 5171)) := by
  have source := ElevenTheory.theory2683 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 4) (m.theta 3 9) (m.theta 4 5) (m.theta 4 9)
  exact rule11171 (meaning t m 2027) (meaning t m 2245) (meaning t m 2406) (meaning t m 3292) (meaning t m 3379) (meaning t m 4949) (meaning t m 5171) source

theorem rule11172 (p2027 p3093 p3193 p3452 p4210 p4512 p4949 : Prop) (h : (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4512) ∨ (¬ p3093) ∨ p2027 ∨ (¬ p4210) ∨ (¬ p4949)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4512) ∨ (¬ p4949) := by
  classical
  tauto

theorem initial11172 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3193)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4949)) := by
  have source := ElevenTheory.theory2684 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 1 6) (m.theta 4 5) (m.theta 4 9)
  exact rule11172 (meaning t m 2027) (meaning t m 3093) (meaning t m 3193) (meaning t m 3452) (meaning t m 4210) (meaning t m 4512) (meaning t m 4949) source

theorem rule11173 (p3755 p4035 : Prop) (h : (¬ p4035) ∨ (¬ p3755)) : (¬ p3755) ∨ (¬ p4035) := by
  classical
  tauto

theorem initial11173 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3755)) ∨ (¬ (meaning t m 4035)) := by
  have source := ElevenTheory.theory2685 (m.theta 2 3) (m.theta 3 9)
  exact rule11173 (meaning t m 3755) (meaning t m 4035) source

theorem rule11174 (p2027 p2145 p2598 p3556 p3641 p3690 p4149 p4381 p5119 : Prop) (h : (¬ p2145) ∨ (¬ p4381) ∨ (¬ p3641) ∨ (¬ p5119) ∨ (¬ p2598) ∨ p2027 ∨ (¬ p4149) ∨ (¬ p3556) ∨ (¬ p3690)) : (p2027) ∨ (¬ p2145) ∨ (¬ p2598) ∨ (¬ p3556) ∨ (¬ p3641) ∨ (¬ p3690) ∨ (¬ p4149) ∨ (¬ p4381) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11174 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2145)) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3690)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2686 t (m.theta 0 2) (m.theta 0 5) (m.theta 2 4) (m.theta 4 8) (m.theta 5 7) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11174 (meaning t m 2027) (meaning t m 2145) (meaning t m 2598) (meaning t m 3556) (meaning t m 3641) (meaning t m 3690) (meaning t m 4149) (meaning t m 4381) (meaning t m 5119) source

theorem rule11175 (p2027 p2252 p2750 p2753 p2761 p2952 p3434 p3471 p3952 p4393 p5254 : Prop) (h : (¬ p3471) ∨ (¬ p2753) ∨ (¬ p4393) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2761) ∨ p2027 ∨ (¬ p3952) ∨ (¬ p2952) ∨ (¬ p5254) ∨ (¬ p3434)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2761) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p5254) := by
  classical
  tauto

theorem initial11175 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4393)) ∨ (¬ (meaning t m 5254)) := by
  have source := ElevenTheory.theory2687 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 10) (m.theta 7 9) (m.theta 9 10)
  exact rule11175 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2753) (meaning t m 2761) (meaning t m 2952) (meaning t m 3434) (meaning t m 3471) (meaning t m 3952) (meaning t m 4393) (meaning t m 5254) source

theorem rule11176 (p2027 p3093 p4053 p4366 p4427 p5477 : Prop) (h : (¬ p4366) ∨ (¬ p3093) ∨ (¬ p4427) ∨ p2027 ∨ (¬ p4053) ∨ (¬ p5477)) : (p2027) ∨ (¬ p3093) ∨ (¬ p4053) ∨ (¬ p4366) ∨ (¬ p4427) ∨ (¬ p5477) := by
  classical
  tauto

theorem initial11176 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 4053)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4427)) ∨ (¬ (meaning t m 5477)) := by
  have source := ElevenTheory.theory2688 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 7) (m.theta 6 10) (m.theta 6 7)
  exact rule11176 (meaning t m 2027) (meaning t m 3093) (meaning t m 4053) (meaning t m 4366) (meaning t m 4427) (meaning t m 5477) source

theorem rule11178 (p2027 p2252 p2750 p2952 p3434 p3527 p3659 p3687 p3744 p3952 p4625 : Prop) (h : (¬ p2952) ∨ (¬ p3952) ∨ (¬ p3744) ∨ p2027 ∨ (¬ p3434) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p3659) ∨ (¬ p4625) ∨ (¬ p3527) ∨ (¬ p3687)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3434) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3687) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial11178 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3527)) ∨ (¬ (meaning t m 3659)) ∨ (¬ (meaning t m 3687)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory2690 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 7) (m.theta 2 7) (m.theta 3 5) (m.theta 5 6) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule11178 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2952) (meaning t m 3434) (meaning t m 3527) (meaning t m 3659) (meaning t m 3687) (meaning t m 3744) (meaning t m 3952) (meaning t m 4625) source

theorem rule11182 (p2027 p2109 p2839 p3156 p3696 p4242 p4906 : Prop) (h : (¬ p3696) ∨ (¬ p2109) ∨ (¬ p3156) ∨ (¬ p2839) ∨ (¬ p4242) ∨ (¬ p4906) ∨ p2027) : (p2027) ∨ (¬ p2109) ∨ (¬ p2839) ∨ (¬ p3156) ∨ (¬ p3696) ∨ (¬ p4242) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial11182 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2109)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3696)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2694 t (m.theta 0 8) (m.theta 1 2) (m.theta 2 5) (m.theta 2 8) (m.theta 3 5) (m.theta 5 8)
  exact rule11182 (meaning t m 2027) (meaning t m 2109) (meaning t m 2839) (meaning t m 3156) (meaning t m 3696) (meaning t m 4242) (meaning t m 4906) source

theorem rule11183 (p2027 p2098 p2252 p2748 p2950 p3055 p3646 p3744 p4019 p4191 p4749 p5119 : Prop) (h : p2027 ∨ (¬ p2098) ∨ (¬ p3055) ∨ (¬ p4749) ∨ (¬ p4019) ∨ (¬ p2950) ∨ (¬ p3744) ∨ (¬ p4191) ∨ (¬ p2748) ∨ (¬ p2252) ∨ (¬ p3646) ∨ (¬ p5119)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p2950) ∨ (¬ p3055) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4019) ∨ (¬ p4191) ∨ (¬ p4749) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11183 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2695 t (m.theta 0 2) (m.theta 0 3) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 5 6) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11183 (meaning t m 2027) (meaning t m 2098) (meaning t m 2252) (meaning t m 2748) (meaning t m 2950) (meaning t m 3055) (meaning t m 3646) (meaning t m 3744) (meaning t m 4019) (meaning t m 4191) (meaning t m 4749) (meaning t m 5119) source

theorem rule11185 (p2027 p3156 p3204 p3969 p4197 p4512 p4957 p5590 : Prop) (h : (¬ p3204) ∨ (¬ p3156) ∨ p2027 ∨ (¬ p3969) ∨ (¬ p4957) ∨ (¬ p5590) ∨ (¬ p4197) ∨ (¬ p4512)) : (p2027) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3969) ∨ (¬ p4197) ∨ (¬ p4512) ∨ (¬ p4957) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial11185 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3156)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3969)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 4512)) ∨ (¬ (meaning t m 4957)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory2697 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 8) (m.theta 8 10)
  exact rule11185 (meaning t m 2027) (meaning t m 3156) (meaning t m 3204) (meaning t m 3969) (meaning t m 4197) (meaning t m 4512) (meaning t m 4957) (meaning t m 5590) source

theorem rule11186 (p2027 p2284 p3413 p3646 p4031 p4256 p4608 : Prop) (h : (¬ p4256) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4608)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4256) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial11186 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory2698 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule11186 (meaning t m 2027) (meaning t m 2284) (meaning t m 3413) (meaning t m 3646) (meaning t m 4031) (meaning t m 4256) (meaning t m 4608) source

theorem rule11187 (p2027 p2509 p2737 p3641 p4257 p4749 : Prop) (h : (¬ p3641) ∨ (¬ p2509) ∨ (¬ p4749) ∨ p2027 ∨ (¬ p2737) ∨ (¬ p4257)) : (p2027) ∨ (¬ p2509) ∨ (¬ p2737) ∨ (¬ p3641) ∨ (¬ p4257) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial11187 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2699 t (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 4 8)
  exact rule11187 (meaning t m 2027) (meaning t m 2509) (meaning t m 2737) (meaning t m 3641) (meaning t m 4257) (meaning t m 4749) source

theorem rule11188 (p2027 p2098 p2252 p2748 p2963 p3055 p3324 p4019 p4347 p4749 p5122 : Prop) (h : (¬ p3055) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p5122) ∨ p2027 ∨ (¬ p2963) ∨ (¬ p4749) ∨ (¬ p4019) ∨ (¬ p4347) ∨ (¬ p3324) ∨ (¬ p2098)) : (p2027) ∨ (¬ p2098) ∨ (¬ p2252) ∨ (¬ p2748) ∨ (¬ p2963) ∨ (¬ p3055) ∨ (¬ p3324) ∨ (¬ p4019) ∨ (¬ p4347) ∨ (¬ p4749) ∨ (¬ p5122) := by
  classical
  tauto

theorem initial11188 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2098)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2748)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3055)) ∨ (¬ (meaning t m 3324)) ∨ (¬ (meaning t m 4019)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 5122)) := by
  have source := ElevenTheory.theory2700 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 2 8) (m.theta 3 6) (m.theta 6 8) (m.theta 8 10) (m.theta 8 9)
  exact rule11188 (meaning t m 2027) (meaning t m 2098) (meaning t m 2252) (meaning t m 2748) (meaning t m 2963) (meaning t m 3055) (meaning t m 3324) (meaning t m 4019) (meaning t m 4347) (meaning t m 4749) (meaning t m 5122) source

theorem rule11189 (p2027 p3115 p3576 p3817 p4135 p4320 p4895 : Prop) (h : (¬ p4320) ∨ (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4135) ∨ p2027 ∨ (¬ p3115) ∨ (¬ p4895)) : (p2027) ∨ (¬ p3115) ∨ (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4135) ∨ (¬ p4320) ∨ (¬ p4895) := by
  classical
  tauto

theorem initial11189 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3115)) ∨ (¬ (meaning t m 3576)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4135)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4895)) := by
  have source := ElevenTheory.theory2701 t (m.theta 1 7) (m.theta 2 7) (m.theta 3 5) (m.theta 5 7) (m.theta 5 9) (m.theta 7 9)
  exact rule11189 (meaning t m 2027) (meaning t m 3115) (meaning t m 3576) (meaning t m 3817) (meaning t m 4135) (meaning t m 4320) (meaning t m 4895) source

theorem rule11192 (p2027 p2088 p2745 p2797 p3567 p4114 p4261 p4262 : Prop) (h : (¬ p2797) ∨ (¬ p2745) ∨ (¬ p4261) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p4262) ∨ (¬ p3567) ∨ (¬ p4114)) : (p2027) ∨ (¬ p2088) ∨ (¬ p2745) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p4114) ∨ (¬ p4261) ∨ (¬ p4262) := by
  classical
  tauto

theorem initial11192 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2088)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3567)) ∨ (¬ (meaning t m 4114)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4262)) := by
  have source := ElevenTheory.theory2704 t (m.theta 0 6) (m.theta 0 8) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 6) (m.theta 8 9)
  exact rule11192 (meaning t m 2027) (meaning t m 2088) (meaning t m 2745) (meaning t m 2797) (meaning t m 3567) (meaning t m 4114) (meaning t m 4261) (meaning t m 4262) source

theorem rule11193 (p2027 p2406 p2497 p2498 p2573 p3684 p4730 : Prop) (h : (¬ p2573) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p4730) ∨ (¬ p2406) ∨ (¬ p3684) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p2498) ∨ (¬ p2573) ∨ (¬ p3684) ∨ (¬ p4730) := by
  classical
  tauto

theorem initial11193 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 2497)) ∨ (¬ (meaning t m 2498)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3684)) ∨ (¬ (meaning t m 4730)) := by
  have source := ElevenTheory.theory2705 t (m.theta 0 4) (m.theta 1 4) (m.theta 1 6) (m.theta 2 4) (m.theta 4 5) (m.theta 4 6)
  exact rule11193 (meaning t m 2027) (meaning t m 2406) (meaning t m 2497) (meaning t m 2498) (meaning t m 2573) (meaning t m 3684) (meaning t m 4730) source

theorem rule11194 (p2027 p2252 p2459 p2750 p3172 p3379 p3641 p3954 p4030 p4118 p4420 : Prop) (h : (¬ p4420) ∨ (¬ p2750) ∨ (¬ p4118) ∨ (¬ p3641) ∨ (¬ p4030) ∨ p2027 ∨ (¬ p3954) ∨ (¬ p3379) ∨ (¬ p2459) ∨ (¬ p3172) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2459) ∨ (¬ p2750) ∨ (¬ p3172) ∨ (¬ p3379) ∨ (¬ p3641) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4118) ∨ (¬ p4420) := by
  classical
  tauto

theorem initial11194 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4030)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4420)) := by
  have source := ElevenTheory.theory2706 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 2 4) (m.theta 3 8) (m.theta 4 8) (m.theta 7 8) (m.theta 8 9)
  exact rule11194 (meaning t m 2027) (meaning t m 2252) (meaning t m 2459) (meaning t m 2750) (meaning t m 3172) (meaning t m 3379) (meaning t m 3641) (meaning t m 3954) (meaning t m 4030) (meaning t m 4118) (meaning t m 4420) source

theorem rule11197 (p2027 p2717 p3551 p3587 p4235 p4283 p4885 : Prop) (h : (¬ p3551) ∨ p2027 ∨ (¬ p4885) ∨ (¬ p4283) ∨ (¬ p2717) ∨ (¬ p3587) ∨ (¬ p4235)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3587) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial11197 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory2709 t (m.theta 0 7) (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule11197 (meaning t m 2027) (meaning t m 2717) (meaning t m 3551) (meaning t m 3587) (meaning t m 4235) (meaning t m 4283) (meaning t m 4885) source

theorem rule11198 (p2027 p3587 p4235 p4253 p4885 p5660 : Prop) (h : (¬ p5660) ∨ (¬ p3587) ∨ (¬ p4235) ∨ p2027 ∨ (¬ p4885) ∨ (¬ p4253)) : (p2027) ∨ (¬ p3587) ∨ (¬ p4235) ∨ (¬ p4253) ∨ (¬ p4885) ∨ (¬ p5660) := by
  classical
  tauto

theorem initial11198 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3587)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4253)) ∨ (¬ (meaning t m 4885)) ∨ (¬ (meaning t m 5660)) := by
  have source := ElevenTheory.theory2710 t (m.theta 2 5) (m.theta 2 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10)
  exact rule11198 (meaning t m 2027) (meaning t m 3587) (meaning t m 4235) (meaning t m 4253) (meaning t m 4885) (meaning t m 5660) source

theorem rule11199 (p2027 p2563 p3483 p4033 p4208 p4241 p4401 : Prop) (h : (¬ p4033) ∨ p2027 ∨ (¬ p2563) ∨ (¬ p4241) ∨ (¬ p3483) ∨ (¬ p4208) ∨ (¬ p4401)) : (p2027) ∨ (¬ p2563) ∨ (¬ p3483) ∨ (¬ p4033) ∨ (¬ p4208) ∨ (¬ p4241) ∨ (¬ p4401) := by
  classical
  tauto

theorem initial11199 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2563)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4033)) ∨ (¬ (meaning t m 4208)) ∨ (¬ (meaning t m 4241)) ∨ (¬ (meaning t m 4401)) := by
  have source := ElevenTheory.theory2711 t (m.theta 2 6) (m.theta 3 5) (m.theta 4 5) (m.theta 5 6) (m.theta 5 9) (m.theta 6 9)
  exact rule11199 (meaning t m 2027) (meaning t m 2563) (meaning t m 3483) (meaning t m 4033) (meaning t m 4208) (meaning t m 4241) (meaning t m 4401) source

theorem rule11200 (p2027 p3449 p3555 p3880 p4446 p4632 : Prop) (h : p2027 ∨ (¬ p3555) ∨ (¬ p4446) ∨ (¬ p3449) ∨ (¬ p4632) ∨ (¬ p3880)) : (p2027) ∨ (¬ p3449) ∨ (¬ p3555) ∨ (¬ p3880) ∨ (¬ p4446) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial11200 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3880)) ∨ (¬ (meaning t m 4446)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2712 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 8) (m.theta 4 5) (m.theta 5 8)
  exact rule11200 (meaning t m 2027) (meaning t m 3449) (meaning t m 3555) (meaning t m 3880) (meaning t m 4446) (meaning t m 4632) source

theorem rule11201 (p2027 p2474 p2518 p2528 p3857 p5191 : Prop) (h : (¬ p2474) ∨ p2027 ∨ (¬ p2528) ∨ (¬ p5191) ∨ (¬ p2518) ∨ (¬ p3857)) : (p2027) ∨ (¬ p2474) ∨ (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p5191) := by
  classical
  tauto

theorem initial11201 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2474)) ∨ (¬ (meaning t m 2518)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 5191)) := by
  have source := ElevenTheory.theory2713 t (m.theta 0 4) (m.theta 0 8) (m.theta 1 4) (m.theta 4 8) (m.theta 8 9)
  exact rule11201 (meaning t m 2027) (meaning t m 2474) (meaning t m 2518) (meaning t m 2528) (meaning t m 3857) (meaning t m 5191) source

theorem rule11203 (p2027 p2284 p2819 p2957 p4120 p4401 p4506 : Prop) (h : (¬ p4120) ∨ (¬ p2957) ∨ (¬ p2284) ∨ p2027 ∨ (¬ p4506) ∨ (¬ p2819) ∨ (¬ p4401)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2819) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4401) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial11203 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 4120)) ∨ (¬ (meaning t m 4401)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory2715 t (m.theta 0 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 8)
  exact rule11203 (meaning t m 2027) (meaning t m 2284) (meaning t m 2819) (meaning t m 2957) (meaning t m 4120) (meaning t m 4401) (meaning t m 4506) source

theorem rule11206 (p2027 p3599 p4242 p4348 p4807 p5343 : Prop) (h : (¬ p5343) ∨ (¬ p4348) ∨ (¬ p4807) ∨ (¬ p4242) ∨ (¬ p3599) ∨ p2027) : (p2027) ∨ (¬ p3599) ∨ (¬ p4242) ∨ (¬ p4348) ∨ (¬ p4807) ∨ (¬ p5343) := by
  classical
  tauto

theorem initial11206 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 4242)) ∨ (¬ (meaning t m 4348)) ∨ (¬ (meaning t m 4807)) ∨ (¬ (meaning t m 5343)) := by
  have source := ElevenTheory.theory2718 t (m.theta 1 2) (m.theta 2 8) (m.theta 2 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11206 (meaning t m 2027) (meaning t m 3599) (meaning t m 4242) (meaning t m 4348) (meaning t m 4807) (meaning t m 5343) source

theorem rule11209 (p2027 p2608 p3212 p3519 p3680 p3860 p3950 p4261 p4376 p4381 p4399 : Prop) (h : (¬ p4261) ∨ (¬ p3950) ∨ p2027 ∨ (¬ p3680) ∨ (¬ p3860) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p4381) ∨ (¬ p4399) ∨ (¬ p3212)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3212) ∨ (¬ p3519) ∨ (¬ p3680) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) ∨ (¬ p4376) ∨ (¬ p4381) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial11209 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3212)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 3950)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory2721 t (m.theta 0 1) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 8) (m.theta 5 9) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule11209 (meaning t m 2027) (meaning t m 2608) (meaning t m 3212) (meaning t m 3519) (meaning t m 3680) (meaning t m 3860) (meaning t m 3950) (meaning t m 4261) (meaning t m 4376) (meaning t m 4381) (meaning t m 4399) source

theorem rule11211 (p2027 p2406 p3379 p3860 p4370 p4608 : Prop) (h : (¬ p3860) ∨ (¬ p4608) ∨ (¬ p2406) ∨ (¬ p4370) ∨ (¬ p3379) ∨ p2027) : (p2027) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial11211 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2406)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory2723 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 4 5) (m.theta 4 8)
  exact rule11211 (meaning t m 2027) (meaning t m 2406) (meaning t m 3379) (meaning t m 3860) (meaning t m 4370) (meaning t m 4608) source

theorem rule11212 (p2027 p2641 p2749 p3585 p4195 p4749 : Prop) (h : (¬ p4749) ∨ (¬ p3585) ∨ p2027 ∨ (¬ p4195) ∨ (¬ p2641) ∨ (¬ p2749)) : (p2027) ∨ (¬ p2641) ∨ (¬ p2749) ∨ (¬ p3585) ∨ (¬ p4195) ∨ (¬ p4749) := by
  classical
  tauto

theorem initial11212 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2641)) ∨ (¬ (meaning t m 2749)) ∨ (¬ (meaning t m 3585)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4749)) := by
  have source := ElevenTheory.theory2724 t (m.theta 1 2) (m.theta 1 3) (m.theta 2 3) (m.theta 2 4) (m.theta 3 6)
  exact rule11212 (meaning t m 2027) (meaning t m 2641) (meaning t m 2749) (meaning t m 3585) (meaning t m 4195) (meaning t m 4749) source

theorem rule11213 (p2027 p3256 p3266 p3657 p4041 p4191 p4623 : Prop) (h : p2027 ∨ (¬ p4623) ∨ (¬ p3657) ∨ (¬ p3266) ∨ (¬ p4041) ∨ (¬ p3256) ∨ (¬ p4191)) : (p2027) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4041) ∨ (¬ p4191) ∨ (¬ p4623) := by
  classical
  tauto

theorem initial11213 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3657)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4623)) := by
  have source := ElevenTheory.theory2725 t (m.theta 3 8) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9) (m.theta 8 9) (m.theta 9 10)
  exact rule11213 (meaning t m 2027) (meaning t m 3256) (meaning t m 3266) (meaning t m 3657) (meaning t m 4041) (meaning t m 4191) (meaning t m 4623) source

theorem rule11216 (p2027 p2352 p2501 p3093 p3860 p4993 : Prop) (h : (¬ p2501) ∨ (¬ p2352) ∨ p2027 ∨ (¬ p3860) ∨ (¬ p3093) ∨ (¬ p4993)) : (p2027) ∨ (¬ p2352) ∨ (¬ p2501) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial11216 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2352)) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory2728 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 4 6) (m.theta 6 8)
  exact rule11216 (meaning t m 2027) (meaning t m 2352) (meaning t m 2501) (meaning t m 3093) (meaning t m 3860) (meaning t m 4993) source

theorem rule11217 (p2027 p2299 p3449 p4366 p5145 p5307 : Prop) (h : (¬ p2299) ∨ (¬ p4366) ∨ (¬ p5145) ∨ p2027 ∨ (¬ p5307) ∨ (¬ p3449)) : (p2027) ∨ (¬ p2299) ∨ (¬ p3449) ∨ (¬ p4366) ∨ (¬ p5145) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial11217 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2299)) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5145)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory2729 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 6 7) (m.theta 7 8)
  exact rule11217 (meaning t m 2027) (meaning t m 2299) (meaning t m 3449) (meaning t m 4366) (meaning t m 5145) (meaning t m 5307) source

theorem rule11218 (p2027 p3093 p3555 p3952 p4516 p4960 : Prop) (h : (¬ p4516) ∨ (¬ p4960) ∨ p2027 ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3952)) : (p2027) ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p3952) ∨ (¬ p4516) ∨ (¬ p4960) := by
  classical
  tauto

theorem initial11218 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 3952)) ∨ (¬ (meaning t m 4516)) ∨ (¬ (meaning t m 4960)) := by
  have source := ElevenTheory.theory2730 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 6) (m.theta 3 5) (m.theta 5 6)
  exact rule11218 (meaning t m 2027) (meaning t m 3093) (meaning t m 3555) (meaning t m 3952) (meaning t m 4516) (meaning t m 4960) source

theorem rule11219 (p2027 p2501 p3093 p3564 p3834 p5148 : Prop) (h : (¬ p3093) ∨ p2027 ∨ (¬ p2501) ∨ (¬ p5148) ∨ (¬ p3834) ∨ (¬ p3564)) : (p2027) ∨ (¬ p2501) ∨ (¬ p3093) ∨ (¬ p3564) ∨ (¬ p3834) ∨ (¬ p5148) := by
  classical
  tauto

theorem initial11219 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2501)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3564)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 5148)) := by
  have source := ElevenTheory.theory2731 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 4 6) (m.theta 6 9)
  exact rule11219 (meaning t m 2027) (meaning t m 2501) (meaning t m 3093) (meaning t m 3564) (meaning t m 3834) (meaning t m 5148) source

theorem rule11220 (p2027 p2156 p2476 p4110 p4399 p4608 : Prop) (h : (¬ p4110) ∨ (¬ p4608) ∨ p2027 ∨ (¬ p4399) ∨ (¬ p2476) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2476) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial11220 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2476)) ∨ (¬ (meaning t m 4110)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory2732 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 8) (m.theta 5 6)
  exact rule11220 (meaning t m 2027) (meaning t m 2156) (meaning t m 2476) (meaning t m 4110) (meaning t m 4399) (meaning t m 4608) source

theorem rule11221 (p2027 p2210 p2509 p3452 p4210 p4608 : Prop) (h : (¬ p2210) ∨ p2027 ∨ (¬ p4608) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p2509)) : (p2027) ∨ (¬ p2210) ∨ (¬ p2509) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4608) := by
  classical
  tauto

theorem initial11221 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2509)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4210)) ∨ (¬ (meaning t m 4608)) := by
  have source := ElevenTheory.theory2733 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 5) (m.theta 4 5) (m.theta 4 8)
  exact rule11221 (meaning t m 2027) (meaning t m 2210) (meaning t m 2509) (meaning t m 3452) (meaning t m 4210) (meaning t m 4608) source

theorem rule11222 (p2027 p2573 p2982 p3904 p4032 p4717 : Prop) (h : (¬ p2573) ∨ (¬ p2982) ∨ p2027 ∨ (¬ p4717) ∨ (¬ p3904) ∨ (¬ p4032)) : (p2027) ∨ (¬ p2573) ∨ (¬ p2982) ∨ (¬ p3904) ∨ (¬ p4032) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial11222 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 2982)) ∨ (¬ (meaning t m 3904)) ∨ (¬ (meaning t m 4032)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2734 t (m.theta 0 4) (m.theta 0 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 9)
  exact rule11222 (meaning t m 2027) (meaning t m 2573) (meaning t m 2982) (meaning t m 3904) (meaning t m 4032) (meaning t m 4717) source

theorem rule11223 (p2027 p2177 p2210 p2311 p2972 p3204 p3551 p3954 p4107 p4395 p4870 : Prop) (h : (¬ p4870) ∨ (¬ p2177) ∨ (¬ p4395) ∨ (¬ p3204) ∨ (¬ p4107) ∨ (¬ p3954) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2972) ∨ (¬ p3551) ∨ (¬ p2311)) : (p2027) ∨ (¬ p2177) ∨ (¬ p2210) ∨ (¬ p2311) ∨ (¬ p2972) ∨ (¬ p3204) ∨ (¬ p3551) ∨ (¬ p3954) ∨ (¬ p4107) ∨ (¬ p4395) ∨ (¬ p4870) := by
  classical
  tauto

theorem initial11223 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2177)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 2311)) ∨ (¬ (meaning t m 2972)) ∨ (¬ (meaning t m 3204)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4395)) ∨ (¬ (meaning t m 4870)) := by
  have source := ElevenTheory.theory2735 t (m.theta 0 1) (m.theta 0 6) (m.theta 0 7) (m.theta 1 2) (m.theta 1 5) (m.theta 1 6) (m.theta 5 9) (m.theta 6 7) (m.theta 7 8) (m.theta 7 9)
  exact rule11223 (meaning t m 2027) (meaning t m 2177) (meaning t m 2210) (meaning t m 2311) (meaning t m 2972) (meaning t m 3204) (meaning t m 3551) (meaning t m 3954) (meaning t m 4107) (meaning t m 4395) (meaning t m 4870) source

theorem rule11224 (p2027 p3016 p3051 p4109 p4320 p4700 p4717 : Prop) (h : (¬ p4700) ∨ (¬ p4320) ∨ (¬ p4717) ∨ (¬ p4109) ∨ p2027 ∨ (¬ p3051) ∨ (¬ p3016)) : (p2027) ∨ (¬ p3016) ∨ (¬ p3051) ∨ (¬ p4109) ∨ (¬ p4320) ∨ (¬ p4700) ∨ (¬ p4717) := by
  classical
  tauto

theorem initial11224 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3016)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 4109)) ∨ (¬ (meaning t m 4320)) ∨ (¬ (meaning t m 4700)) ∨ (¬ (meaning t m 4717)) := by
  have source := ElevenTheory.theory2736 t (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 4 5) (m.theta 4 6) (m.theta 5 7)
  exact rule11224 (meaning t m 2027) (meaning t m 3016) (meaning t m 3051) (meaning t m 4109) (meaning t m 4320) (meaning t m 4700) (meaning t m 4717) source

theorem rule11225 (p2027 p2696 p2717 p3551 p3820 p4778 : Prop) (h : (¬ p3820) ∨ (¬ p3551) ∨ (¬ p2717) ∨ (¬ p2696) ∨ (¬ p4778) ∨ p2027) : (p2027) ∨ (¬ p2696) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p4778) := by
  classical
  tauto

theorem initial11225 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3820)) ∨ (¬ (meaning t m 4778)) := by
  have source := ElevenTheory.theory2737 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 2 7) (m.theta 7 8)
  exact rule11225 (meaning t m 2027) (meaning t m 2696) (meaning t m 2717) (meaning t m 3551) (meaning t m 3820) (meaning t m 4778) source

theorem rule11226 (p2027 p2264 p2928 p3551 p3580 p4279 p4811 : Prop) (h : p2027 ∨ (¬ p3580) ∨ (¬ p2264) ∨ (¬ p2928) ∨ (¬ p4279) ∨ (¬ p4811) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2928) ∨ (¬ p3551) ∨ (¬ p3580) ∨ (¬ p4279) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial11226 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2928)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3580)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2738 t (m.theta 0 7) (m.theta 1 4) (m.theta 3 4) (m.theta 3 7) (m.theta 4 7) (m.theta 7 8)
  exact rule11226 (meaning t m 2027) (meaning t m 2264) (meaning t m 2928) (meaning t m 3551) (meaning t m 3580) (meaning t m 4279) (meaning t m 4811) source

theorem rule11227 (p2027 p2717 p3551 p3742 p4279 p4753 p5085 : Prop) (h : (¬ p3551) ∨ (¬ p4279) ∨ (¬ p3742) ∨ (¬ p4753) ∨ p2027 ∨ (¬ p5085) ∨ (¬ p2717)) : (p2027) ∨ (¬ p2717) ∨ (¬ p3551) ∨ (¬ p3742) ∨ (¬ p4279) ∨ (¬ p4753) ∨ (¬ p5085) := by
  classical
  tauto

theorem initial11227 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2717)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 3742)) ∨ (¬ (meaning t m 4279)) ∨ (¬ (meaning t m 4753)) ∨ (¬ (meaning t m 5085)) := by
  have source := ElevenTheory.theory2739 t (m.theta 0 7) (m.theta 2 4) (m.theta 2 7) (m.theta 3 4) (m.theta 4 7) (m.theta 7 8)
  exact rule11227 (meaning t m 2027) (meaning t m 2717) (meaning t m 3551) (meaning t m 3742) (meaning t m 4279) (meaning t m 4753) (meaning t m 5085) source

theorem rule11228 (p2027 p2386 p2542 p2860 p3574 p3743 p4885 : Prop) (h : (¬ p2386) ∨ (¬ p3574) ∨ (¬ p3743) ∨ (¬ p4885) ∨ p2027 ∨ (¬ p2860) ∨ (¬ p2542)) : (p2027) ∨ (¬ p2386) ∨ (¬ p2542) ∨ (¬ p2860) ∨ (¬ p3574) ∨ (¬ p3743) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial11228 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2386)) ∨ (¬ (meaning t m 2542)) ∨ (¬ (meaning t m 2860)) ∨ (¬ (meaning t m 3574)) ∨ (¬ (meaning t m 3743)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory2740 t (m.theta 0 6) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 4 6) (m.theta 5 6)
  exact rule11228 (meaning t m 2027) (meaning t m 2386) (meaning t m 2542) (meaning t m 2860) (meaning t m 3574) (meaning t m 3743) (meaning t m 4885) source

theorem rule11229 (p2027 p2440 p2870 p3556 p3582 p4031 p4753 : Prop) (h : (¬ p2440) ∨ p2027 ∨ (¬ p3556) ∨ (¬ p2870) ∨ (¬ p4031) ∨ (¬ p3582) ∨ (¬ p4753)) : (p2027) ∨ (¬ p2440) ∨ (¬ p2870) ∨ (¬ p3556) ∨ (¬ p3582) ∨ (¬ p4031) ∨ (¬ p4753) := by
  classical
  tauto

theorem initial11229 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 3556)) ∨ (¬ (meaning t m 3582)) ∨ (¬ (meaning t m 4031)) ∨ (¬ (meaning t m 4753)) := by
  have source := ElevenTheory.theory2741 t (m.theta 0 5) (m.theta 2 4) (m.theta 2 5) (m.theta 3 4) (m.theta 4 5) (m.theta 5 7)
  exact rule11229 (meaning t m 2027) (meaning t m 2440) (meaning t m 2870) (meaning t m 3556) (meaning t m 3582) (meaning t m 4031) (meaning t m 4753) source

theorem rule11230 (p2027 p2253 p2741 p2946 p3452 p3662 p4376 : Prop) (h : p2027 ∨ (¬ p4376) ∨ (¬ p3452) ∨ (¬ p2253) ∨ (¬ p2946) ∨ (¬ p2741) ∨ (¬ p3662)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p3662) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11230 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 2946)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3662)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2742 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 5)
  exact rule11230 (meaning t m 2027) (meaning t m 2253) (meaning t m 2741) (meaning t m 2946) (meaning t m 3452) (meaning t m 3662) (meaning t m 4376) source

theorem rule11231 (p2027 p2341 p2417 p3365 p3644 p4037 p4195 p4625 p5257 : Prop) (h : (¬ p4037) ∨ (¬ p5257) ∨ (¬ p2417) ∨ (¬ p4195) ∨ (¬ p3644) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p4625) ∨ (¬ p3365)) : (p2027) ∨ (¬ p2341) ∨ (¬ p2417) ∨ (¬ p3365) ∨ (¬ p3644) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p5257) := by
  classical
  tauto

theorem initial11231 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2341)) ∨ (¬ (meaning t m 2417)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3644)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4625)) ∨ (¬ (meaning t m 5257)) := by
  have source := ElevenTheory.theory2743 t (m.theta 0 2) (m.theta 0 7) (m.theta 2 3) (m.theta 3 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 7 9)
  exact rule11231 (meaning t m 2027) (meaning t m 2341) (meaning t m 2417) (meaning t m 3365) (meaning t m 3644) (meaning t m 4037) (meaning t m 4195) (meaning t m 4625) (meaning t m 5257) source

theorem rule11232 (p2027 p2156 p3452 p4172 p4173 p4376 p4874 : Prop) (h : (¬ p4172) ∨ p2027 ∨ (¬ p4376) ∨ (¬ p4874) ∨ (¬ p4173) ∨ (¬ p3452) ∨ (¬ p2156)) : (p2027) ∨ (¬ p2156) ∨ (¬ p3452) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4376) ∨ (¬ p4874) := by
  classical
  tauto

theorem initial11232 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4172)) ∨ (¬ (meaning t m 4173)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4874)) := by
  have source := ElevenTheory.theory2744 t (m.theta 0 1) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 5 6)
  exact rule11232 (meaning t m 2027) (meaning t m 2156) (meaning t m 3452) (meaning t m 4172) (meaning t m 4173) (meaning t m 4376) (meaning t m 4874) source

theorem rule11233 (p2027 p3323 p3645 p3646 p3744 p4336 p4957 : Prop) (h : (¬ p3323) ∨ (¬ p4336) ∨ (¬ p3645) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p4957) ∨ (¬ p3744)) : (p2027) ∨ (¬ p3323) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4336) ∨ (¬ p4957) := by
  classical
  tauto

theorem initial11233 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3323)) ∨ (¬ (meaning t m 3645)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 3744)) ∨ (¬ (meaning t m 4336)) ∨ (¬ (meaning t m 4957)) := by
  have source := ElevenTheory.theory2745 t (m.theta 0 5) (m.theta 1 5) (m.theta 3 5) (m.theta 3 6) (m.theta 5 6) (m.theta 6 9)
  exact rule11233 (meaning t m 2027) (meaning t m 3323) (meaning t m 3645) (meaning t m 3646) (meaning t m 3744) (meaning t m 4336) (meaning t m 4957) source

theorem rule11234 (p2027 p2470 p2528 p3266 p3365 p3366 p3519 p4195 p4376 p5254 p5717 : Prop) (h : (¬ p3519) ∨ (¬ p4376) ∨ (¬ p3266) ∨ (¬ p3366) ∨ (¬ p2470) ∨ (¬ p5717) ∨ (¬ p4195) ∨ (¬ p5254) ∨ (¬ p2528) ∨ p2027 ∨ (¬ p3365)) : (p2027) ∨ (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p4195) ∨ (¬ p4376) ∨ (¬ p5254) ∨ (¬ p5717) := by
  classical
  tauto

theorem initial11234 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2470)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 3266)) ∨ (¬ (meaning t m 3365)) ∨ (¬ (meaning t m 3366)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 4195)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 5254)) ∨ (¬ (meaning t m 5717)) := by
  have source := ElevenTheory.theory2746 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 3 6) (m.theta 4 8) (m.theta 6 10) (m.theta 8 9) (m.theta 9 10)
  exact rule11234 (meaning t m 2027) (meaning t m 2470) (meaning t m 2528) (meaning t m 3266) (meaning t m 3365) (meaning t m 3366) (meaning t m 3519) (meaning t m 4195) (meaning t m 4376) (meaning t m 5254) (meaning t m 5717) source

theorem rule11235 (p2027 p2284 p3497 p3737 p4506 p5586 : Prop) (h : p2027 ∨ (¬ p4506) ∨ (¬ p3737) ∨ (¬ p2284) ∨ (¬ p5586) ∨ (¬ p3497)) : (p2027) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3737) ∨ (¬ p4506) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial11235 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 3737)) ∨ (¬ (meaning t m 4506)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory2747 t (m.theta 3 5) (m.theta 5 6) (m.theta 5 8) (m.theta 6 10) (m.theta 6 8)
  exact rule11235 (meaning t m 2027) (meaning t m 2284) (meaning t m 3497) (meaning t m 3737) (meaning t m 4506) (meaning t m 5586) source

theorem rule11236 (p2027 p2192 p2210 p4366 p4555 p4909 : Prop) (h : (¬ p4366) ∨ p2027 ∨ (¬ p4555) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p4909)) : (p2027) ∨ (¬ p2192) ∨ (¬ p2210) ∨ (¬ p4366) ∨ (¬ p4555) ∨ (¬ p4909) := by
  classical
  tauto

theorem initial11236 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2192)) ∨ (¬ (meaning t m 2210)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4555)) ∨ (¬ (meaning t m 4909)) := by
  have source := ElevenTheory.theory2748 t (m.theta 0 1) (m.theta 1 5) (m.theta 1 7) (m.theta 5 6) (m.theta 5 7)
  exact rule11236 (meaning t m 2027) (meaning t m 2192) (meaning t m 2210) (meaning t m 4366) (meaning t m 4555) (meaning t m 4909) source

theorem rule11237 (p2027 p2797 p3877 p4228 p4769 p5586 : Prop) (h : (¬ p3877) ∨ (¬ p4228) ∨ (¬ p4769) ∨ (¬ p2797) ∨ (¬ p5586) ∨ p2027) : (p2027) ∨ (¬ p2797) ∨ (¬ p3877) ∨ (¬ p4228) ∨ (¬ p4769) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial11237 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2797)) ∨ (¬ (meaning t m 3877)) ∨ (¬ (meaning t m 4228)) ∨ (¬ (meaning t m 4769)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory2749 t (m.theta 2 3) (m.theta 3 6) (m.theta 3 8) (m.theta 6 10) (m.theta 6 8)
  exact rule11237 (meaning t m 2027) (meaning t m 2797) (meaning t m 3877) (meaning t m 4228) (meaning t m 4769) (meaning t m 5586) source

theorem rule11238 (p2027 p2241 p2745 p3005 p3860 p5074 : Prop) (h : (¬ p2745) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p3005) ∨ (¬ p5074)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2745) ∨ (¬ p3005) ∨ (¬ p3860) ∨ (¬ p5074) := by
  classical
  tauto

theorem initial11238 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2745)) ∨ (¬ (meaning t m 3005)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 5074)) := by
  have source := ElevenTheory.theory2750 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 8) (m.theta 2 3) (m.theta 3 8)
  exact rule11238 (meaning t m 2027) (meaning t m 2241) (meaning t m 2745) (meaning t m 3005) (meaning t m 3860) (meaning t m 5074) source

theorem rule11241 (p2027 p2264 p2995 p3551 p4235 p4283 p4705 : Prop) (h : (¬ p4283) ∨ (¬ p2995) ∨ (¬ p4705) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p4235) ∨ (¬ p3551)) : (p2027) ∨ (¬ p2264) ∨ (¬ p2995) ∨ (¬ p3551) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4705) := by
  classical
  tauto

theorem initial11241 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2264)) ∨ (¬ (meaning t m 2995)) ∨ (¬ (meaning t m 3551)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4705)) := by
  have source := ElevenTheory.theory2753 t (m.theta 0 7) (m.theta 3 5) (m.theta 3 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8)
  exact rule11241 (meaning t m 2027) (meaning t m 2264) (meaning t m 2995) (meaning t m 3551) (meaning t m 4235) (meaning t m 4283) (meaning t m 4705) source

theorem rule11242 (p2027 p2499 p2573 p3555 p4079 p4257 p4377 : Prop) (h : (¬ p4079) ∨ (¬ p3555) ∨ (¬ p4257) ∨ (¬ p2573) ∨ (¬ p2499) ∨ p2027 ∨ (¬ p4377)) : (p2027) ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p3555) ∨ (¬ p4079) ∨ (¬ p4257) ∨ (¬ p4377) := by
  classical
  tauto

theorem initial11242 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2499)) ∨ (¬ (meaning t m 2573)) ∨ (¬ (meaning t m 3555)) ∨ (¬ (meaning t m 4079)) ∨ (¬ (meaning t m 4257)) ∨ (¬ (meaning t m 4377)) := by
  have source := ElevenTheory.theory2754 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 1 5) (m.theta 4 6)
  exact rule11242 (meaning t m 2027) (meaning t m 2499) (meaning t m 2573) (meaning t m 3555) (meaning t m 4079) (meaning t m 4257) (meaning t m 4377) source

theorem rule11244 (p2685 p4067 p4195 : Prop) (h : (¬ p2685) ∨ (¬ p4195) ∨ (¬ p4067)) : (¬ p2685) ∨ (¬ p4067) ∨ (¬ p4195) := by
  classical
  tauto

theorem initial11244 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2685)) ∨ (¬ (meaning t m 4067)) ∨ (¬ (meaning t m 4195)) := by
  have source := ElevenTheory.theory2756 (m.theta 2 3) (m.theta 3 6) (m.theta 3 7)
  exact rule11244 (meaning t m 2685) (meaning t m 4067) (meaning t m 4195) source

theorem rule11247 (p2957 p3412 p3645 : Prop) (h : p3645 ∨ (¬ p3412) ∨ (¬ p2957)) : (¬ p2957) ∨ (¬ p3412) ∨ (p3645) := by
  classical
  tauto

theorem initial11247 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 2957)) ∨ (¬ (meaning t m 3412)) ∨ (meaning t m 3645) := by
  have source := ElevenTheory.theory2759 (m.theta 0 5) (m.theta 1 5) (m.theta 3 5)
  exact rule11247 (meaning t m 2957) (meaning t m 3412) (meaning t m 3645) source

theorem rule11250 (p2027 p3032 p3830 p4107 p4361 p4366 p5362 : Prop) (h : (¬ p4361) ∨ (¬ p3032) ∨ p2027 ∨ (¬ p3830) ∨ (¬ p5362) ∨ (¬ p4366) ∨ (¬ p4107)) : (p2027) ∨ (¬ p3032) ∨ (¬ p3830) ∨ (¬ p4107) ∨ (¬ p4361) ∨ (¬ p4366) ∨ (¬ p5362) := by
  classical
  tauto

theorem initial11250 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3032)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 4107)) ∨ (¬ (meaning t m 4361)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 5362)) := by
  have source := ElevenTheory.theory2762 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 9) (m.theta 3 7) (m.theta 6 7) (m.theta 7 9)
  exact rule11250 (meaning t m 2027) (meaning t m 3032) (meaning t m 3830) (meaning t m 4107) (meaning t m 4361) (meaning t m 4366) (meaning t m 5362) source

theorem rule11253 (p2027 p2819 p3093 p3860 p4867 p4993 : Prop) (h : (¬ p4993) ∨ (¬ p4867) ∨ (¬ p3093) ∨ (¬ p3860) ∨ p2027 ∨ (¬ p2819)) : (p2027) ∨ (¬ p2819) ∨ (¬ p3093) ∨ (¬ p3860) ∨ (¬ p4867) ∨ (¬ p4993) := by
  classical
  tauto

theorem initial11253 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3093)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4867)) ∨ (¬ (meaning t m 4993)) := by
  have source := ElevenTheory.theory2765 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 8) (m.theta 2 6) (m.theta 6 8)
  exact rule11253 (meaning t m 2027) (meaning t m 2819) (meaning t m 3093) (meaning t m 3860) (meaning t m 4867) (meaning t m 4993) source

theorem rule11254 (p2027 p2782 p2819 p3979 p4197 p5590 : Prop) (h : (¬ p2782) ∨ (¬ p4197) ∨ p2027 ∨ (¬ p2819) ∨ (¬ p3979) ∨ (¬ p5590)) : (p2027) ∨ (¬ p2782) ∨ (¬ p2819) ∨ (¬ p3979) ∨ (¬ p4197) ∨ (¬ p5590) := by
  classical
  tauto

theorem initial11254 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2782)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4197)) ∨ (¬ (meaning t m 5590)) := by
  have source := ElevenTheory.theory2766 t (m.theta 0 6) (m.theta 0 8) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10)
  exact rule11254 (meaning t m 2027) (meaning t m 2782) (meaning t m 2819) (meaning t m 3979) (meaning t m 4197) (meaning t m 5590) source

theorem rule11255 (p2027 p3449 p3817 p4366 p4666 p5307 : Prop) (h : (¬ p4666) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p5307) ∨ (¬ p3449) ∨ p2027) : (p2027) ∨ (¬ p3449) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4666) ∨ (¬ p5307) := by
  classical
  tauto

theorem initial11255 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3449)) ∨ (¬ (meaning t m 3817)) ∨ (¬ (meaning t m 4366)) ∨ (¬ (meaning t m 4666)) ∨ (¬ (meaning t m 5307)) := by
  have source := ElevenTheory.theory2767 t (m.theta 0 1) (m.theta 1 7) (m.theta 1 8) (m.theta 7 8) (m.theta 7 9)
  exact rule11255 (meaning t m 2027) (meaning t m 3449) (meaning t m 3817) (meaning t m 4366) (meaning t m 4666) (meaning t m 5307) source

theorem rule11256 (p2027 p2387 p2778 p2819 p3276 p3355 p3917 p4381 p4419 p4625 : Prop) (h : (¬ p2819) ∨ (¬ p3355) ∨ (¬ p3917) ∨ (¬ p4419) ∨ (¬ p4381) ∨ p2027 ∨ (¬ p4625) ∨ (¬ p2778) ∨ (¬ p3276) ∨ (¬ p2387)) : (p2027) ∨ (¬ p2387) ∨ (¬ p2778) ∨ (¬ p2819) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3917) ∨ (¬ p4381) ∨ (¬ p4419) ∨ (¬ p4625) := by
  classical
  tauto

theorem initial11256 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2387)) ∨ (¬ (meaning t m 2778)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3276)) ∨ (¬ (meaning t m 3355)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4381)) ∨ (¬ (meaning t m 4419)) ∨ (¬ (meaning t m 4625)) := by
  have source := ElevenTheory.theory2768 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 6) (m.theta 2 6) (m.theta 4 9) (m.theta 6 8) (m.theta 6 9) (m.theta 7 9) (m.theta 9 10)
  exact rule11256 (meaning t m 2027) (meaning t m 2387) (meaning t m 2778) (meaning t m 2819) (meaning t m 3276) (meaning t m 3355) (meaning t m 3917) (meaning t m 4381) (meaning t m 4419) (meaning t m 4625) source

theorem rule11257 (p2027 p2608 p3073 p3857 p4416 p5312 : Prop) (h : (¬ p3073) ∨ (¬ p2608) ∨ p2027 ∨ (¬ p3857) ∨ (¬ p5312) ∨ (¬ p4416)) : (p2027) ∨ (¬ p2608) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4416) ∨ (¬ p5312) := by
  classical
  tauto

theorem initial11257 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 3073)) ∨ (¬ (meaning t m 3857)) ∨ (¬ (meaning t m 4416)) ∨ (¬ (meaning t m 5312)) := by
  have source := ElevenTheory.theory2769 t (m.theta 0 1) (m.theta 0 8) (m.theta 1 2) (m.theta 1 8) (m.theta 8 9)
  exact rule11257 (meaning t m 2027) (meaning t m 2608) (meaning t m 3073) (meaning t m 3857) (meaning t m 4416) (meaning t m 5312) source

theorem rule11258 (p2027 p2253 p2741 p3166 p3452 p4360 p4376 : Prop) (h : (¬ p4376) ∨ (¬ p3166) ∨ (¬ p4360) ∨ (¬ p2741) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p3452)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p3166) ∨ (¬ p3452) ∨ (¬ p4360) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11258 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3166)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4360)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2770 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 8)
  exact rule11258 (meaning t m 2027) (meaning t m 2253) (meaning t m 2741) (meaning t m 3166) (meaning t m 3452) (meaning t m 4360) (meaning t m 4376) source

theorem rule11259 (p2027 p2241 p3189 p3452 p4116 p5011 : Prop) (h : (¬ p3452) ∨ (¬ p4116) ∨ p2027 ∨ (¬ p5011) ∨ (¬ p2241) ∨ (¬ p3189)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p5011) := by
  classical
  tauto

theorem initial11259 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3189)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 5011)) := by
  have source := ElevenTheory.theory2771 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 8)
  exact rule11259 (meaning t m 2027) (meaning t m 2241) (meaning t m 3189) (meaning t m 3452) (meaning t m 4116) (meaning t m 5011) source

theorem rule11260 (p2027 p2253 p2741 p3286 p3452 p3848 p4376 : Prop) (h : (¬ p3452) ∨ (¬ p2253) ∨ p2027 ∨ (¬ p2741) ∨ (¬ p3848) ∨ (¬ p3286) ∨ (¬ p4376)) : (p2027) ∨ (¬ p2253) ∨ (¬ p2741) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3848) ∨ (¬ p4376) := by
  classical
  tauto

theorem initial11260 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2253)) ∨ (¬ (meaning t m 2741)) ∨ (¬ (meaning t m 3286)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3848)) ∨ (¬ (meaning t m 4376)) := by
  have source := ElevenTheory.theory2772 t (m.theta 0 1) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 1 4) (m.theta 3 9)
  exact rule11260 (meaning t m 2027) (meaning t m 2253) (meaning t m 2741) (meaning t m 3286) (meaning t m 3452) (meaning t m 3848) (meaning t m 4376) source

theorem rule11261 (p2027 p2241 p3452 p3842 p4116 p5177 : Prop) (h : (¬ p3452) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p4116) ∨ (¬ p5177) ∨ (¬ p3842)) : (p2027) ∨ (¬ p2241) ∨ (¬ p3452) ∨ (¬ p3842) ∨ (¬ p4116) ∨ (¬ p5177) := by
  classical
  tauto

theorem initial11261 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 3452)) ∨ (¬ (meaning t m 3842)) ∨ (¬ (meaning t m 4116)) ∨ (¬ (meaning t m 5177)) := by
  have source := ElevenTheory.theory2773 t (m.theta 0 1) (m.theta 1 3) (m.theta 1 4) (m.theta 3 4) (m.theta 3 9)
  exact rule11261 (meaning t m 2027) (meaning t m 2241) (meaning t m 3452) (meaning t m 3842) (meaning t m 4116) (meaning t m 5177) source

theorem rule11262 (p2027 p2459 p2911 p3389 p3688 p3917 p3954 p4604 p5190 : Prop) (h : (¬ p3688) ∨ (¬ p3389) ∨ (¬ p3917) ∨ (¬ p5190) ∨ (¬ p2911) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p4604) ∨ (¬ p3954)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3688) ∨ (¬ p3917) ∨ (¬ p3954) ∨ (¬ p4604) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11262 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 3389)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 3954)) ∨ (¬ (meaning t m 4604)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2774 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 2) (m.theta 2 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11262 (meaning t m 2027) (meaning t m 2459) (meaning t m 2911) (meaning t m 3389) (meaning t m 3688) (meaning t m 3917) (meaning t m 3954) (meaning t m 4604) (meaning t m 5190) source

theorem rule11263 (p2027 p2230 p2427 p2881 p3256 p3860 p4041 p4261 p5190 : Prop) (h : (¬ p5190) ∨ p2027 ∨ (¬ p4041) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3860) ∨ (¬ p2230) ∨ (¬ p4261) ∨ (¬ p3256)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3256) ∨ (¬ p3860) ∨ (¬ p4041) ∨ (¬ p4261) ∨ (¬ p5190) := by
  classical
  tauto

theorem initial11263 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3256)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4041)) ∨ (¬ (meaning t m 4261)) ∨ (¬ (meaning t m 5190)) := by
  have source := ElevenTheory.theory2775 t (m.theta 0 1) (m.theta 0 4) (m.theta 1 8) (m.theta 3 8) (m.theta 4 5) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11263 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2881) (meaning t m 3256) (meaning t m 3860) (meaning t m 4041) (meaning t m 4261) (meaning t m 5190) source

theorem rule11264 (p2027 p2363 p2534 p3573 p3888 p5586 : Prop) (h : (¬ p3573) ∨ (¬ p2363) ∨ (¬ p5586) ∨ p2027 ∨ (¬ p3888) ∨ (¬ p2534)) : (p2027) ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3573) ∨ (¬ p3888) ∨ (¬ p5586) := by
  classical
  tauto

theorem initial11264 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2363)) ∨ (¬ (meaning t m 2534)) ∨ (¬ (meaning t m 3573)) ∨ (¬ (meaning t m 3888)) ∨ (¬ (meaning t m 5586)) := by
  have source := ElevenTheory.theory2776 t (m.theta 4 6) (m.theta 4 8) (m.theta 6 10) (m.theta 6 8) (m.theta 8 9)
  exact rule11264 (meaning t m 2027) (meaning t m 2363) (meaning t m 2534) (meaning t m 3573) (meaning t m 3888) (meaning t m 5586) source

theorem rule11265 (p2027 p2230 p2427 p2696 p2753 p3519 p3590 p4129 p4379 p4749 p4826 p5387 : Prop) (h : (¬ p5387) ∨ (¬ p2427) ∨ (¬ p2230) ∨ (¬ p4129) ∨ (¬ p2696) ∨ (¬ p4749) ∨ (¬ p4826) ∨ (¬ p2753) ∨ p2027 ∨ (¬ p3590) ∨ (¬ p4379) ∨ (¬ p3519)) : (p2027) ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3519) ∨ (¬ p3590) ∨ (¬ p4129) ∨ (¬ p4379) ∨ (¬ p4749) ∨ (¬ p4826) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial11265 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2230)) ∨ (¬ (meaning t m 2427)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 4129)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory2777 t (m.theta 0 2) (m.theta 0 4) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 4 5) (m.theta 5 7) (m.theta 7 10) (m.theta 9 10)
  exact rule11265 (meaning t m 2027) (meaning t m 2230) (meaning t m 2427) (meaning t m 2696) (meaning t m 2753) (meaning t m 3519) (meaning t m 3590) (meaning t m 4129) (meaning t m 4379) (meaning t m 4749) (meaning t m 4826) (meaning t m 5387) source

theorem rule11267 (p3519 p3590 p3759 : Prop) (h : (¬ p3519) ∨ p3759 ∨ (¬ p3590)) : (¬ p3519) ∨ (¬ p3590) ∨ (p3759) := by
  classical
  tauto

theorem initial11267 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3590)) ∨ (meaning t m 3759) := by
  have source := ElevenTheory.theory2779 (m.theta 0 4) (m.theta 1 4) (m.theta 2 4)
  exact rule11267 (meaning t m 3519) (meaning t m 3590) (meaning t m 3759) source

theorem rule11268 (p3670 p5387 : Prop) (h : (¬ p5387) ∨ (¬ p3670)) : (¬ p3670) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial11268 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3670)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory2780 (m.theta 2 9) (m.theta 9 10)
  exact rule11268 (meaning t m 3670) (meaning t m 5387) source

theorem rule11269 (p3599 p4379 : Prop) (h : (¬ p4379) ∨ (¬ p3599)) : (¬ p3599) ∨ (¬ p4379) := by
  classical
  tauto

theorem initial11269 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 4379)) := by
  have source := ElevenTheory.theory2781 (m.theta 1 2) (m.theta 2 9)
  exact rule11269 (meaning t m 3599) (meaning t m 4379) source

theorem rule11273 (p2027 p2598 p2963 p3641 p4037 p4149 p4191 p4789 p5119 : Prop) (h : (¬ p5119) ∨ (¬ p4149) ∨ p2027 ∨ (¬ p4037) ∨ (¬ p3641) ∨ (¬ p2598) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p2963)) : (p2027) ∨ (¬ p2598) ∨ (¬ p2963) ∨ (¬ p3641) ∨ (¬ p4037) ∨ (¬ p4149) ∨ (¬ p4191) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11273 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2598)) ∨ (¬ (meaning t m 2963)) ∨ (¬ (meaning t m 3641)) ∨ (¬ (meaning t m 4037)) ∨ (¬ (meaning t m 4149)) ∨ (¬ (meaning t m 4191)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2785 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 4) (m.theta 3 6) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11273 (meaning t m 2027) (meaning t m 2598) (meaning t m 2963) (meaning t m 3641) (meaning t m 4037) (meaning t m 4149) (meaning t m 4191) (meaning t m 4789) (meaning t m 5119) source

theorem rule11274 (p2027 p2459 p2608 p2911 p2922 p3591 p4026 p4376 p4604 : Prop) (h : (¬ p4376) ∨ p2027 ∨ (¬ p2922) ∨ (¬ p4604) ∨ (¬ p2459) ∨ (¬ p4026) ∨ (¬ p3591) ∨ (¬ p2911) ∨ (¬ p2608)) : (p2027) ∨ (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3591) ∨ (¬ p4026) ∨ (¬ p4376) ∨ (¬ p4604) := by
  classical
  tauto

theorem initial11274 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2459)) ∨ (¬ (meaning t m 2608)) ∨ (¬ (meaning t m 2911)) ∨ (¬ (meaning t m 2922)) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 4026)) ∨ (¬ (meaning t m 4376)) ∨ (¬ (meaning t m 4604)) := by
  have source := ElevenTheory.theory2786 t (m.theta 0 1) (m.theta 1 2) (m.theta 1 4) (m.theta 1 6) (m.theta 4 7) (m.theta 6 9) (m.theta 7 8) (m.theta 8 9)
  exact rule11274 (meaning t m 2027) (meaning t m 2459) (meaning t m 2608) (meaning t m 2911) (meaning t m 2922) (meaning t m 3591) (meaning t m 4026) (meaning t m 4376) (meaning t m 4604) source

theorem rule11277 (p2027 p3583 p3599 p4885 p4948 p5030 : Prop) (h : (¬ p3599) ∨ (¬ p4885) ∨ p2027 ∨ (¬ p5030) ∨ (¬ p4948) ∨ (¬ p3583)) : (p2027) ∨ (¬ p3583) ∨ (¬ p3599) ∨ (¬ p4885) ∨ (¬ p4948) ∨ (¬ p5030) := by
  classical
  tauto

theorem initial11277 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3583)) ∨ (¬ (meaning t m 3599)) ∨ (¬ (meaning t m 4885)) ∨ (¬ (meaning t m 4948)) ∨ (¬ (meaning t m 5030)) := by
  have source := ElevenTheory.theory2789 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 9) (m.theta 4 5) (m.theta 5 9)
  exact rule11277 (meaning t m 2027) (meaning t m 3583) (meaning t m 3599) (meaning t m 4885) (meaning t m 4948) (meaning t m 5030) source

theorem rule11278 (p2027 p2156 p2553 p2696 p2753 p3096 p3519 p3590 p3791 p4379 p4399 p4749 p4826 p5387 : Prop) (h : (¬ p2156) ∨ p2027 ∨ (¬ p4826) ∨ (¬ p2696) ∨ (¬ p3096) ∨ (¬ p4379) ∨ (¬ p5387) ∨ (¬ p2753) ∨ (¬ p3590) ∨ (¬ p4749) ∨ (¬ p4399) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p2553)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3096) ∨ (¬ p3519) ∨ (¬ p3590) ∨ (¬ p3791) ∨ (¬ p4379) ∨ (¬ p4399) ∨ (¬ p4749) ∨ (¬ p4826) ∨ (¬ p5387) := by
  classical
  tauto

theorem initial11278 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2553)) ∨ (¬ (meaning t m 2696)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 3096)) ∨ (¬ (meaning t m 3519)) ∨ (¬ (meaning t m 3590)) ∨ (¬ (meaning t m 3791)) ∨ (¬ (meaning t m 4379)) ∨ (¬ (meaning t m 4399)) ∨ (¬ (meaning t m 4749)) ∨ (¬ (meaning t m 4826)) ∨ (¬ (meaning t m 5387)) := by
  have source := ElevenTheory.theory2790 t (m.theta 0 2) (m.theta 0 4) (m.theta 0 5) (m.theta 1 2) (m.theta 1 4) (m.theta 2 3) (m.theta 2 4) (m.theta 2 9) (m.theta 4 6) (m.theta 5 6) (m.theta 6 7) (m.theta 7 10) (m.theta 9 10)
  exact rule11278 (meaning t m 2027) (meaning t m 2156) (meaning t m 2553) (meaning t m 2696) (meaning t m 2753) (meaning t m 3096) (meaning t m 3519) (meaning t m 3590) (meaning t m 3791) (meaning t m 4379) (meaning t m 4399) (meaning t m 4749) (meaning t m 4826) (meaning t m 5387) source

theorem rule11279 (p2027 p2187 p3689 p4075 p4185 p4405 p4423 p4427 : Prop) (h : (¬ p4427) ∨ p2027 ∨ (¬ p4423) ∨ (¬ p3689) ∨ (¬ p4075) ∨ (¬ p4405) ∨ (¬ p2187) ∨ (¬ p4185)) : (p2027) ∨ (¬ p2187) ∨ (¬ p3689) ∨ (¬ p4075) ∨ (¬ p4185) ∨ (¬ p4405) ∨ (¬ p4423) ∨ (¬ p4427) := by
  classical
  tauto

theorem initial11279 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2187)) ∨ (¬ (meaning t m 3689)) ∨ (¬ (meaning t m 4075)) ∨ (¬ (meaning t m 4185)) ∨ (¬ (meaning t m 4405)) ∨ (¬ (meaning t m 4423)) ∨ (¬ (meaning t m 4427)) := by
  have source := ElevenTheory.theory2791 t (m.theta 1 7) (m.theta 2 6) (m.theta 2 7) (m.theta 5 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 10)
  exact rule11279 (meaning t m 2027) (meaning t m 2187) (meaning t m 3689) (meaning t m 4075) (meaning t m 4185) (meaning t m 4405) (meaning t m 4423) (meaning t m 4427) source

theorem rule11280 (p2027 p2137 p2441 p3051 p3246 p4278 p4885 : Prop) (h : (¬ p4885) ∨ (¬ p2441) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4278)) : (p2027) ∨ (¬ p2137) ∨ (¬ p2441) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4278) ∨ (¬ p4885) := by
  classical
  tauto

theorem initial11280 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2137)) ∨ (¬ (meaning t m 2441)) ∨ (¬ (meaning t m 3051)) ∨ (¬ (meaning t m 3246)) ∨ (¬ (meaning t m 4278)) ∨ (¬ (meaning t m 4885)) := by
  have source := ElevenTheory.theory2792 t (m.theta 0 5) (m.theta 2 5) (m.theta 4 5) (m.theta 4 7) (m.theta 5 7) (m.theta 7 9)
  exact rule11280 (meaning t m 2027) (meaning t m 2137) (meaning t m 2441) (meaning t m 3051) (meaning t m 3246) (meaning t m 4278) (meaning t m 4885) source

theorem rule11283 (p2027 p2156 p2656 p2727 p2751 p3758 p4392 p4399 : Prop) (h : (¬ p4392) ∨ (¬ p2156) ∨ (¬ p4399) ∨ p2027 ∨ (¬ p2727) ∨ (¬ p2656) ∨ (¬ p3758) ∨ (¬ p2751)) : (p2027) ∨ (¬ p2156) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2751) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4399) := by
  classical
  tauto

theorem initial11283 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2156)) ∨ (¬ (meaning t m 2656)) ∨ (¬ (meaning t m 2727)) ∨ (¬ (meaning t m 2751)) ∨ (¬ (meaning t m 3758)) ∨ (¬ (meaning t m 4392)) ∨ (¬ (meaning t m 4399)) := by
  have source := ElevenTheory.theory2795 t (m.theta 0 4) (m.theta 0 5) (m.theta 1 3) (m.theta 2 3) (m.theta 2 5) (m.theta 3 4) (m.theta 5 6)
  exact rule11283 (meaning t m 2027) (meaning t m 2156) (meaning t m 2656) (meaning t m 2727) (meaning t m 2751) (meaning t m 3758) (meaning t m 4392) (meaning t m 4399) source

theorem rule11286 (p2027 p3631 p3821 p4235 p4283 p4338 p4452 p4632 : Prop) (h : (¬ p4452) ∨ (¬ p4632) ∨ (¬ p4235) ∨ (¬ p4338) ∨ p2027 ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p3631)) : (p2027) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4235) ∨ (¬ p4283) ∨ (¬ p4338) ∨ (¬ p4452) ∨ (¬ p4632) := by
  classical
  tauto

theorem initial11286 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3631)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 4235)) ∨ (¬ (meaning t m 4283)) ∨ (¬ (meaning t m 4338)) ∨ (¬ (meaning t m 4452)) ∨ (¬ (meaning t m 4632)) := by
  have source := ElevenTheory.theory2798 t (m.theta 0 7) (m.theta 1 5) (m.theta 1 6) (m.theta 1 7) (m.theta 4 5) (m.theta 5 7) (m.theta 7 9)
  exact rule11286 (meaning t m 2027) (meaning t m 3631) (meaning t m 3821) (meaning t m 4235) (meaning t m 4283) (meaning t m 4338) (meaning t m 4452) (meaning t m 4632) source

theorem rule11287 (p2027 p2284 p2839 p3688 p4428 p4906 : Prop) (h : (¬ p3688) ∨ (¬ p4906) ∨ (¬ p4428) ∨ p2027 ∨ (¬ p2839) ∨ (¬ p2284)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2839) ∨ (¬ p3688) ∨ (¬ p4428) ∨ (¬ p4906) := by
  classical
  tauto

theorem initial11287 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2839)) ∨ (¬ (meaning t m 3688)) ∨ (¬ (meaning t m 4428)) ∨ (¬ (meaning t m 4906)) := by
  have source := ElevenTheory.theory2799 t (m.theta 1 2) (m.theta 2 5) (m.theta 2 6) (m.theta 3 5) (m.theta 5 6)
  exact rule11287 (meaning t m 2027) (meaning t m 2284) (meaning t m 2839) (meaning t m 3688) (meaning t m 4428) (meaning t m 4906) source

theorem rule11288 (p2027 p2737 p2819 p3923 p3953 p4842 : Prop) (h : (¬ p2819) ∨ (¬ p2737) ∨ (¬ p4842) ∨ p2027 ∨ (¬ p3923) ∨ (¬ p3953)) : (p2027) ∨ (¬ p2737) ∨ (¬ p2819) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p4842) := by
  classical
  tauto

theorem initial11288 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2737)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3923)) ∨ (¬ (meaning t m 3953)) ∨ (¬ (meaning t m 4842)) := by
  have source := ElevenTheory.theory2800 t (m.theta 1 2) (m.theta 1 6) (m.theta 2 3) (m.theta 2 6) (m.theta 6 8)
  exact rule11288 (meaning t m 2027) (meaning t m 2737) (meaning t m 2819) (meaning t m 3923) (meaning t m 3953) (meaning t m 4842) source

theorem rule11289 (p2027 p2284 p2807 p2950 p3413 p3646 p4652 : Prop) (h : (¬ p2807) ∨ (¬ p2284) ∨ (¬ p2950) ∨ p2027 ∨ (¬ p3646) ∨ (¬ p3413) ∨ (¬ p4652)) : (p2027) ∨ (¬ p2284) ∨ (¬ p2807) ∨ (¬ p2950) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4652) := by
  classical
  tauto

theorem initial11289 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2284)) ∨ (¬ (meaning t m 2807)) ∨ (¬ (meaning t m 2950)) ∨ (¬ (meaning t m 3413)) ∨ (¬ (meaning t m 3646)) ∨ (¬ (meaning t m 4652)) := by
  have source := ElevenTheory.theory2801 t (m.theta 0 3) (m.theta 0 5) (m.theta 3 4) (m.theta 3 5) (m.theta 3 7) (m.theta 5 6)
  exact rule11289 (meaning t m 2027) (meaning t m 2284) (meaning t m 2807) (meaning t m 2950) (meaning t m 3413) (meaning t m 3646) (meaning t m 4652) source

theorem rule11290 (p2027 p2132 p2528 p2870 p2881 p3172 p4118 p4438 p4789 : Prop) (h : (¬ p4438) ∨ (¬ p2881) ∨ (¬ p2132) ∨ p2027 ∨ (¬ p4118) ∨ (¬ p4789) ∨ (¬ p2528) ∨ (¬ p3172) ∨ (¬ p2870)) : (p2027) ∨ (¬ p2132) ∨ (¬ p2528) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4438) ∨ (¬ p4789) := by
  classical
  tauto

theorem initial11290 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2132)) ∨ (¬ (meaning t m 2528)) ∨ (¬ (meaning t m 2870)) ∨ (¬ (meaning t m 2881)) ∨ (¬ (meaning t m 3172)) ∨ (¬ (meaning t m 4118)) ∨ (¬ (meaning t m 4438)) ∨ (¬ (meaning t m 4789)) := by
  have source := ElevenTheory.theory2802 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 5) (m.theta 3 8) (m.theta 4 8) (m.theta 5 7) (m.theta 7 8) (m.theta 8 9)
  exact rule11290 (meaning t m 2027) (meaning t m 2132) (meaning t m 2528) (meaning t m 2870) (meaning t m 2881) (meaning t m 3172) (meaning t m 4118) (meaning t m 4438) (meaning t m 4789) source

theorem rule11291 (p3146 p4347 p4506 : Prop) (h : (¬ p4347) ∨ (¬ p3146) ∨ (¬ p4506)) : (¬ p3146) ∨ (¬ p4347) ∨ (¬ p4506) := by
  classical
  tauto

theorem initial11291 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3146)) ∨ (¬ (meaning t m 4347)) ∨ (¬ (meaning t m 4506)) := by
  have source := ElevenTheory.theory2803 (m.theta 5 8) (m.theta 6 8) (m.theta 8 9)
  exact rule11291 (meaning t m 3146) (meaning t m 4347) (meaning t m 4506) source

theorem rule11292 (p2027 p3227 p3343 p3379 p3834 p4811 : Prop) (h : (¬ p3834) ∨ (¬ p3379) ∨ (¬ p4811) ∨ p2027 ∨ (¬ p3343) ∨ (¬ p3227)) : (p2027) ∨ (¬ p3227) ∨ (¬ p3343) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial11292 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3227)) ∨ (¬ (meaning t m 3343)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2804 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 9) (m.theta 3 4) (m.theta 4 9)
  exact rule11292 (meaning t m 2027) (meaning t m 3227) (meaning t m 3343) (meaning t m 3379) (meaning t m 3834) (meaning t m 4811) source

theorem rule11294 (p2027 p3083 p3379 p3860 p4370 p4811 : Prop) (h : (¬ p3860) ∨ (¬ p4811) ∨ p2027 ∨ (¬ p3083) ∨ (¬ p4370) ∨ (¬ p3379)) : (p2027) ∨ (¬ p3083) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) ∨ (¬ p4811) := by
  classical
  tauto

theorem initial11294 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3083)) ∨ (¬ (meaning t m 3379)) ∨ (¬ (meaning t m 3860)) ∨ (¬ (meaning t m 4370)) ∨ (¬ (meaning t m 4811)) := by
  have source := ElevenTheory.theory2806 t (m.theta 0 1) (m.theta 1 4) (m.theta 1 8) (m.theta 3 4) (m.theta 4 8)
  exact rule11294 (meaning t m 2027) (meaning t m 3083) (meaning t m 3379) (meaning t m 3860) (meaning t m 4370) (meaning t m 4811) source

theorem rule11295 (p2027 p2122 p2252 p2396 p2440 p2657 p2750 p2829 p3951 p4948 : Prop) (h : (¬ p4948) ∨ (¬ p2440) ∨ (¬ p2750) ∨ (¬ p2657) ∨ (¬ p3951) ∨ p2027 ∨ (¬ p2252) ∨ (¬ p2829) ∨ (¬ p2396) ∨ (¬ p2122)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3951) ∨ (¬ p4948) := by
  classical
  tauto

theorem initial11295 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2440)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 4948)) := by
  have source := ElevenTheory.theory2807 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 5) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9)
  exact rule11295 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2396) (meaning t m 2440) (meaning t m 2657) (meaning t m 2750) (meaning t m 2829) (meaning t m 3951) (meaning t m 4948) source

theorem rule11296 (p2027 p2657 p2774 p2819 p3359 p3979 p4425 p4789 p5119 : Prop) (h : p2027 ∨ (¬ p5119) ∨ (¬ p3979) ∨ (¬ p2774) ∨ (¬ p3359) ∨ (¬ p2657) ∨ (¬ p4789) ∨ (¬ p2819) ∨ (¬ p4425)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3359) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p4789) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11296 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3359)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4425)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2808 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 9) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11296 (meaning t m 2027) (meaning t m 2657) (meaning t m 2774) (meaning t m 2819) (meaning t m 3359) (meaning t m 3979) (meaning t m 4425) (meaning t m 4789) (meaning t m 5119) source

theorem rule11297 (p2027 p2241 p2750 p2753 p2774 p2819 p3834 p3979 p4321 p5119 : Prop) (h : p2027 ∨ (¬ p5119) ∨ (¬ p3979) ∨ (¬ p2750) ∨ (¬ p2819) ∨ (¬ p4321) ∨ (¬ p3834) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2241)) : (p2027) ∨ (¬ p2241) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3834) ∨ (¬ p3979) ∨ (¬ p4321) ∨ (¬ p5119) := by
  classical
  tauto

theorem initial11297 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2241)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3834)) ∨ (¬ (meaning t m 3979)) ∨ (¬ (meaning t m 4321)) ∨ (¬ (meaning t m 5119)) := by
  have source := ElevenTheory.theory2809 t (m.theta 0 1) (m.theta 0 2) (m.theta 1 2) (m.theta 1 3) (m.theta 1 9) (m.theta 2 6) (m.theta 6 8) (m.theta 8 10) (m.theta 9 10)
  exact rule11297 (meaning t m 2027) (meaning t m 2241) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 2819) (meaning t m 3834) (meaning t m 3979) (meaning t m 4321) (meaning t m 5119) source

theorem rule11298 (p3830 p3834 : Prop) (h : (¬ p3834) ∨ (¬ p3830)) : (¬ p3830) ∨ (¬ p3834) := by
  classical
  tauto

theorem initial11298 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3834)) := by
  have source := ElevenTheory.theory2810 (m.theta 0 1) (m.theta 1 9)
  exact rule11298 (meaning t m 3830) (meaning t m 3834) source

theorem rule11299 (p2027 p2437 p3868 p4256 p4383 p5564 : Prop) (h : p2027 ∨ (¬ p5564) ∨ (¬ p4256) ∨ (¬ p2437) ∨ (¬ p4383) ∨ (¬ p3868)) : (p2027) ∨ (¬ p2437) ∨ (¬ p3868) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5564) := by
  classical
  tauto

theorem initial11299 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2437)) ∨ (¬ (meaning t m 3868)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4383)) ∨ (¬ (meaning t m 5564)) := by
  have source := ElevenTheory.theory2811 t (m.theta 3 4) (m.theta 4 7) (m.theta 4 8) (m.theta 7 10) (m.theta 7 8)
  exact rule11299 (meaning t m 2027) (meaning t m 2437) (meaning t m 3868) (meaning t m 4256) (meaning t m 4383) (meaning t m 5564) source

theorem rule11300 (p2027 p2657 p2761 p3434 p3471 p4256 p4286 p4789 p5123 : Prop) (h : p2027 ∨ (¬ p2657) ∨ (¬ p4286) ∨ (¬ p3434) ∨ (¬ p4256) ∨ (¬ p3471) ∨ (¬ p4789) ∨ (¬ p2761) ∨ (¬ p5123)) : (p2027) ∨ (¬ p2657) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4789) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial11300 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2761)) ∨ (¬ (meaning t m 3434)) ∨ (¬ (meaning t m 3471)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 4789)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory2812 t (m.theta 0 2) (m.theta 0 3) (m.theta 2 7) (m.theta 3 4) (m.theta 4 8) (m.theta 7 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11300 (meaning t m 2027) (meaning t m 2657) (meaning t m 2761) (meaning t m 3434) (meaning t m 3471) (meaning t m 4256) (meaning t m 4286) (meaning t m 4789) (meaning t m 5123) source

theorem rule11301 (p2027 p2252 p2750 p2829 p2952 p3461 p3483 p3497 p5123 p5568 : Prop) (h : (¬ p5568) ∨ (¬ p2829) ∨ (¬ p5123) ∨ (¬ p2952) ∨ p2027 ∨ (¬ p3497) ∨ (¬ p2252) ∨ (¬ p3483) ∨ (¬ p2750) ∨ (¬ p3461)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3497) ∨ (¬ p5123) ∨ (¬ p5568) := by
  classical
  tauto

theorem initial11301 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 2952)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 3497)) ∨ (¬ (meaning t m 5123)) ∨ (¬ (meaning t m 5568)) := by
  have source := ElevenTheory.theory2813 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 5) (m.theta 5 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11301 (meaning t m 2027) (meaning t m 2252) (meaning t m 2750) (meaning t m 2829) (meaning t m 2952) (meaning t m 3461) (meaning t m 3483) (meaning t m 3497) (meaning t m 5123) (meaning t m 5568) source

theorem rule11302 (p2027 p2252 p2657 p2750 p2829 p3461 p3483 p4256 p4286 p5123 : Prop) (h : (¬ p2750) ∨ (¬ p5123) ∨ (¬ p2829) ∨ (¬ p2657) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p3483) ∨ (¬ p3461) ∨ p2027 ∨ (¬ p2252)) : (p2027) ∨ (¬ p2252) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p5123) := by
  classical
  tauto

theorem initial11302 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2657)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2829)) ∨ (¬ (meaning t m 3461)) ∨ (¬ (meaning t m 3483)) ∨ (¬ (meaning t m 4256)) ∨ (¬ (meaning t m 4286)) ∨ (¬ (meaning t m 5123)) := by
  have source := ElevenTheory.theory2814 t (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 4) (m.theta 4 8) (m.theta 6 9) (m.theta 8 10) (m.theta 9 10)
  exact rule11302 (meaning t m 2027) (meaning t m 2252) (meaning t m 2657) (meaning t m 2750) (meaning t m 2829) (meaning t m 3461) (meaning t m 3483) (meaning t m 4256) (meaning t m 4286) (meaning t m 5123) source

theorem rule11303 (p2027 p3591 p3830 p3917 p4871 p5152 : Prop) (h : (¬ p4871) ∨ (¬ p5152) ∨ (¬ p3591) ∨ (¬ p3917) ∨ p2027 ∨ (¬ p3830)) : (p2027) ∨ (¬ p3591) ∨ (¬ p3830) ∨ (¬ p3917) ∨ (¬ p4871) ∨ (¬ p5152) := by
  classical
  tauto

theorem initial11303 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 3591)) ∨ (¬ (meaning t m 3830)) ∨ (¬ (meaning t m 3917)) ∨ (¬ (meaning t m 4871)) ∨ (¬ (meaning t m 5152)) := by
  have source := ElevenTheory.theory2815 t (m.theta 0 1) (m.theta 1 6) (m.theta 1 9) (m.theta 2 6) (m.theta 6 9)
  exact rule11303 (meaning t m 2027) (meaning t m 3591) (meaning t m 3830) (meaning t m 3917) (meaning t m 4871) (meaning t m 5152) source

theorem rule11304 (p2027 p2318 p2819 p3550 p3821 p3822 p4666 : Prop) (h : (¬ p4666) ∨ p2027 ∨ (¬ p3822) ∨ (¬ p2819) ∨ (¬ p3821) ∨ (¬ p2318) ∨ (¬ p3550)) : (p2027) ∨ (¬ p2318) ∨ (¬ p2819) ∨ (¬ p3550) ∨ (¬ p3821) ∨ (¬ p3822) ∨ (¬ p4666) := by
  classical
  tauto

theorem initial11304 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2318)) ∨ (¬ (meaning t m 2819)) ∨ (¬ (meaning t m 3550)) ∨ (¬ (meaning t m 3821)) ∨ (¬ (meaning t m 3822)) ∨ (¬ (meaning t m 4666)) := by
  have source := ElevenTheory.theory2816 t (m.theta 0 7) (m.theta 2 6) (m.theta 6 7) (m.theta 6 8) (m.theta 7 8) (m.theta 7 9)
  exact rule11304 (meaning t m 2027) (meaning t m 2318) (meaning t m 2819) (meaning t m 3550) (meaning t m 3821) (meaning t m 3822) (meaning t m 4666) source

theorem rule11305 (p2027 p2122 p2252 p2396 p2750 p2753 p2774 p3292 p3680 p3951 p5284 : Prop) (h : p2027 ∨ (¬ p2122) ∨ (¬ p3951) ∨ (¬ p5284) ∨ (¬ p2396) ∨ (¬ p2753) ∨ (¬ p3680) ∨ (¬ p2750) ∨ (¬ p2774) ∨ (¬ p3292) ∨ (¬ p2252)) : (p2027) ∨ (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p3292) ∨ (¬ p3680) ∨ (¬ p3951) ∨ (¬ p5284) := by
  classical
  tauto

theorem initial11305 (t : ℝ) (m : DirectionModel 11 t) (ht : t < 4) :
    (meaning t m 2027) ∨ (¬ (meaning t m 2122)) ∨ (¬ (meaning t m 2252)) ∨ (¬ (meaning t m 2396)) ∨ (¬ (meaning t m 2750)) ∨ (¬ (meaning t m 2753)) ∨ (¬ (meaning t m 2774)) ∨ (¬ (meaning t m 3292)) ∨ (¬ (meaning t m 3680)) ∨ (¬ (meaning t m 3951)) ∨ (¬ (meaning t m 5284)) := by
  have source := ElevenTheory.theory2817 t (m.theta 0 2) (m.theta 0 3) (m.theta 1 2) (m.theta 1 3) (m.theta 2 6) (m.theta 3 9) (m.theta 5 9) (m.theta 6 7) (m.theta 7 9) (m.theta 9 10)
  exact rule11305 (meaning t m 2027) (meaning t m 2122) (meaning t m 2252) (meaning t m 2396) (meaning t m 2750) (meaning t m 2753) (meaning t m 2774) (meaning t m 3292) (meaning t m 3680) (meaning t m 3951) (meaning t m 5284) source

end SunPrize.SMT
